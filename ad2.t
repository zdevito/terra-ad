--[[
--define a primitive, the general case is
ad.primitive(function(x0,x1) --number of input to function 
    return { y0, y1 }, --outputs to the function 
           { dy0dx0, dy0dx1, --jacobian of inputs and outputs
             dy1dx0, dy1dx1 }
end
-- return values are terra quotations.
-- arguments are symbols
-- both lists can be replaced with non-lists if there is one value
]]

--[[

primitive
  xs = list(symbol), input variables 
  vs = list(symbols), result of calculation (used in jacobean)
  ys = list(quotes),  representing forward calculation
  jacobian = list(quotes), representing derivative calculation
   
num
  value = number (refers to paramter) or 
          table { 
            prim = primitive,
            args = list(num)
          }

stmt
  prim = primitive
  args = list(number), arguments to primitive referring to other statements or parameters

op
  nparams = number
  generator = list(num) -> list(num), used in __call to compose operators, 
              defined differently for primitive operators
  stmts = list(stmt)
  results = list(number), index into stmts of output results
  

]]


local C = terralib.includec("math.h")

local function dsym() return symbol(double) end

local ad = {}
local function newtype()
    local t = {}
    t.__index = t
    function t.isinstance(obj)
        return obj and (getmetatable(obj) == t)
    end
    function t.new(obj)
        return setmetatable(obj, t)
    end
    return t
end

-- operator (op) object represents all 
-- operators applied in AD language
-- can be defined as primitives or by composition of other operators
local op = newtype()

-- num object is used as lua object to create composed operators
local num = newtype()

local function aslist(v)
    if terralib.isquote(v) then 
        return terralib.newlist { v }
    else
        assert(type(v) == "table")
        return terralib.newlist(v)
    end
    for i,p in ipairs(v) do
        assert(terralib.isquote(p))
    end
end

local function composeop(np, generator)
    --create number objects representing the parameters
    local params = {}
    for i = 1,np do params[i] = num.new { value = -i } end
    --run the composed set of operators on the numbers creating a DAG of primitive operations
    local results = terralib.newlist { generator(unpack(params)) }
    
    --perform CSE and linearize list of ops
    local stmts = terralib.newlist {}
    local cache = {}
    local function genstmt(n)
        --a parameter, just return the idx (a negative number)
        if type(n.value) == "number" then return n.value end
        
        --CSE the children
        local args = n.value.args:map(genstmt)
        
        --construct key for this op "opname,argid0,...argidn"
        local ident = tostring(n.value.prim) .. "," .. table.concat(args,",")
        if cache[ident] then return cache[ident] end
        stmts:insert { prim = n.value.prim, args = args } 
        cache[ident] = #stmts
        return #stmts
    end
    local resultids = results:map(genstmt)
    return stmts,resultids
end

--define a primitive operator (op)
local function mkop(xs,ys,jacobian,vs)
    local o = op.new { nparams = #xs }
    ys,jacobian = aslist(ys), aslist(jacobian)
    assert(#ys * #xs == #jacobian)
    vs = vs or ys:map(dsym)
    local prim = { xs = xs, ys = ys, jacobian = jacobian, vs = vs}
    function o.generator(...)
        return num.new { value = { prim = prim, args = terralib.newlist {...} } }
    end
    o.stmts,o.results = composeop(o.nparams,o.generator)
    return o
end

function ad.primitiveop(fn)
    local nparams = debug.getinfo(fn,"u").nparams
    local params = terralib.newlist()
    for i = 1,nparams do params[i] = dsym() end
    local ys,j = fn(unpack(params))
    return mkop(params,ys,j)  
end

--primitive op, but derivatives are passed a value of the output 'v'
--used for primitives such as exp, where the derived is expressed in terms of output
function ad.primitiveopv(nresults,fn)
    local nparams = debug.getinfo(fn,"u").nparams - nresults
    local params,results,args = terralib.newlist(),terralib.newlist(),terralib.newlist()
    for i = 1,nresults do results[i] = dsym(); args:insert(results[i]) end
    for i = 1,nparams do  params[i]  = dsym(); args:insert(params[i])  end
    local ys,j = fn(unpack(args))
    return mkop(params,ys,j,results)  
end

local function lift(n)
    assert(type(n) == "number")
    return ad.primitiveop(function() return `n, {} end)
end

function op.__call(self,...)
    local args = terralib.newlist {}
    for i = 1,select("#",...) do
        local v = select(i,...)
        if not num.isinstance(v) then
            v = lift(v)()
        end
        args[i] = v
    end
    assert(self.nparams == #args)
    return self.generator(unpack(args))
end

function  ad.compoundop(fn)
    local o = op.new { generator = fn }
    o.nparams = debug.getinfo(fn,"u").nparams
    o.stmts, o.results = composeop(o.nparams,o.generator)
    return o
end

function op:print()
    print(self.nparams, " parameters.")
    for i,s in ipairs(self.stmts) do
        local args = s.args:map(function(a) return "n["..tonumber(a) .. "]" end)
        io.write("n["..tonumber(i).."] = fn("..table.concat(args,",")..") with fn = ")
        s.prim.ys[1]:printpretty()
    end
end

-- if the op represents the function: y = op(p0,...,pN)
-- then codegen will result in a function 'fn', such that:
-- y,dy/dp0,...,dy/dpN = fn(p0,...,pN)
function op:codegen()
    local function genprim(theop,args)
        return quote
            var [theop.xs] = [args]
            var [theop.vs] = [theop.ys]
        in [theop.vs],[theop.jacobian] end
    end
    local venv,denv,jenv = {},{},{}
    local params,dparams = {},{}
    
    local stmts = terralib.newlist()
    for i = 1,self.nparams do 
        params[i],dparams[i] = dsym(),dsym()
        venv[-i],denv[-i] = params[i],dparams[i]
        stmts:insert(quote var [denv[-i]] = 0.0 end)
    end
    
    local function getvenv(a) return venv[a] end
    for i,s in ipairs(self.stmts) do
        local v,d,js = dsym(), dsym(), s.prim.jacobian:map(dsym)
        stmts:insert(quote
            var [v],[js] = [ genprim(s.prim, s.args:map(getvenv)) ]
            var [d] = 0.0
        end)
        venv[i],denv[i], jenv[i] = v,d,js
    end
    local r = venv[ self.results[1] ] --TODO:multiple params
    denv[self.results[1]] = 1.0  
    --now compute the partials
    for i = #self.stmts,1,-1 do
        local s = self.stmts[i]
        for j,a in ipairs(s.args) do
            local di,dr = denv[a],denv[i]
            stmts:insert(quote
                [di] = [di] + [jenv[i][j]]*[dr] 
            end)
        end
    end
    
    local terra result([params]) stmts return r,dparams end
    --result:printpretty()
    --result:disas()
    return result
end

num.__add = ad.primitiveop(function(a,b) return `a + b, {`1.0, `1.0} end)
num.__sub = ad.primitiveop(function(a,b) return `a - b, {`1.0, `-1.0} end)
num.__mul = ad.primitiveop(function(a,b) return `a * b, {`b, `a} end)
num.__div = ad.primitiveop(function(a,b) return `a / b, {`1.0/b, `-a/(b*b)} end)
local unm = ad.primitiveop(function(a) return `-a, `1.0 end)
num.__unm = function(a) return unm(a) end

ad.acos = ad.primitiveop(function(a) return `C.acos(a),`-1.0/C.sqrt(1.0 - a*a) end)
ad.acosh = ad.primitiveop(function(a) return `C.cosh(a),`1.0/C.sqrt(a*a - 1.0) end)
ad.asin = ad.primitiveop(function(a) return `C.asin(a),`1.0/C.sqrt(1.0 - a*a) end)
ad.asinh = ad.primitiveop(function(a) return `C.asinh(a),`1.0/C.sqrt(a*a + 1.0) end)
ad.atan = ad.primitiveop(function(a) return `C.atan(a),`1.0/(a*a + 1.0) end)
ad.atan2 = ad.primitiveop(function(a,b) 
    local sqnorm = `a*a + b*b
    return `C.atan2(a,b),{`b/sqnorm,`a/sqnorm} 
end)
ad.cos = ad.primitiveop(function(a) return `C.cos(a),`-C.sin(a) end)
ad.cosh = ad.primitiveop(function(a) return `C.cosh(a),`C.sinh(a) end)
ad.exp  = ad.primitiveopv(1,function(v,a) return `C.exp(a), `v end)
ad.log = ad.primitiveop(function(a) return `C.log(a),`1.0/a end)
ad.log10 = ad.primitiveop(function(a) return `C.log10(a),`1.0/(C.log(10.0)*a) end)
ad.pow   = ad.primitiveopv(1,function(v,a,b) return `C.pow(a,b), {`b*v/a,`C.log(a)*v} end)
ad.sin = ad.primitiveop(function(a) return `C.sin(a),`C.cos(a) end)
ad.sinh = ad.primitiveop(function(a) return `C.sinh(a),`C.cosh(a) end)
ad.sqrt = ad.primitiveopv(1,function(v,a) return `C.sqrt(a),`1.0/(2.0*v) end)
ad.tan = ad.primitiveopv(1,function(v,a) return `C.tan(a),`1.0 + v*v end)
ad.tanh = ad.primitiveop(function(a) return `C.tanh(a),quote var c = C.cosh(a) in 1.0/(c*c) end end)

stuff = ad.compoundop(function(a,b)
    return ad.exp(4*a) - -(ad.cos(3*b*b))
end)

stuff2 = ad.compoundop(function(x,y)
    return x*x + y*x + 4
end)
stuff:print()
stuff2:print()

--stuff:codegen()
local f = stuff2:codegen()
--ad.cos:codegen()

print(f(4,3))