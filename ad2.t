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


local C = terralib.includecstring [[
    #include <math.h>
    #include <stdlib.h>
    #include <sys/mman.h>
    #include <stdio.h>
    
    void * mallochigh(size_t len) {
        void * addr = (void*)0x100000000ULL;
        return mmap(addr,len,PROT_READ | PROT_WRITE, MAP_ANON | MAP_PRIVATE, -1,0);
    }
]]

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
function op:getimpl()
    if not self.impl then
        self.impl = self:codegen()
    end
    return self.impl
end

-- Primitives ----------------------------------------------------------------------------

num.__add = ad.primitiveop(function(a,b) return `a + b, {`1.0, `1.0} end)
num.__sub = ad.primitiveop(function(a,b) return `a - b, {`1.0, `-1.0} end)
num.__mul = ad.primitiveop(function(a,b) return `a * b, {`b, `a} end)
num.__div = ad.primitiveop(function(a,b) return `a / b, {`1.0/b, `-a/(b*b)} end)
local unm = ad.primitiveop(function(a) return `-a, `1.0 end)
num.__unm = function(a) return unm(a) end

ad.acos = ad.primitiveop(function(a) return `C.acos(a),`-1.0/C.sqrt(1.0 - a*a) end)
ad.acosh = ad.primitiveop(function(a) return `C.acosh(a),`1.0/C.sqrt(a*a - 1.0) end)
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
ad.fmin = ad.primitiveop(function(a,b) 
    local less = `a < b
    return `terralib.select(less,a,b),
          {`terralib.select(less,1.0,0.0),
           `terralib.select(less,0.0,1.0) }
end)
ad.fmax = ad.primitiveop(function(a,b) 
    local less = `a < b
    return `terralib.select(less,b,a),
          {`terralib.select(less,0.0,1.0),
           `terralib.select(less,1.0,0.0) }
end)

-- Tape Management -----------------------------------------------------------------------

--store dy/dn for each ad.num type n
local idxtype = uint32
local derivs = global(&double)
local derivnparams = global(&idxtype)
local tapeidx = global(&idxtype)
local tapeval = global(&double)
local tapepos = global(idxtype)
local derivpos = global(idxtype)
local MAX_SIZE = 1024*1024*512 --four gigs of doubles

local MallocArray = macro(function(T,N)
    T = T:astype()
    return `[&T](C.mallochigh(sizeof(T)*N))
end)

local maxmem = global(uint32,0)

terra ad.initGlobals()
    maxmem = 0
    derivs = MallocArray(double,MAX_SIZE)
    derivnparams = MallocArray(idxtype,MAX_SIZE)
    tapeidx = MallocArray(idxtype,MAX_SIZE)
    tapeval = MallocArray(double,MAX_SIZE)
    tapepos,derivpos = 0,0
end
ad.initGlobals()

struct Num {
    value : double;
    idx : idxtype; --index into derivs storing dy/dself
}

--returns idx of derivative, and idx in to tape to store the parameters
local terra tapealloc(np : uint32)
    var d,t = derivpos,tapepos
    derivs[d] = 0.0
    derivnparams[d] = np 
    derivpos,tapepos = derivpos+1,tapepos + np
    if derivpos >= MAX_SIZE or tapepos >= MAX_SIZE then
        C.printf("EXCEEDED MAX SIZE\n")
    end
    return d,t
end

terra createnum(v : double)
    var d,t = tapealloc(0)
    return Num { v, d }
end

Num.metamethods.__cast = function(from, to, exp)
	if from == double and to == Num then
		return `createnum(exp)
	else
		error(string.format("ad.t: Cannot cast '%s' to '%s'", tostring(from), tostring(to)))
	end
end

function op:macro()
    return macro(function(...)
        local impl = self:getimpl()
        local args = terralib.newlist {}
        local argsym = terralib.newlist {}
        for i = 1,self.nparams do
            local a = select(i,...)
            if a:gettype() == double then
                --TODO: regenerate op with fewer arguments, do not promote 'a' into the tape
                a = `ad.num(a)
            end
            args[i],argsym[i] = a, symbol(Num)
        end
        local function partialaddr(base,p)
            local r = {}
            for i = 1, self.nparams do
                r[i] = `base[p + [i-1]]
            end
            assert(terralib.israwlist(r))
            return r
        end
        local values = argsym:map(function(a) return `a.value end)
        local idxs = argsym:map(function(a) return `a.idx end)
        local r = quote
            var [argsym] = [args]
            var d,t = tapealloc(self.nparams)
            var v : double
            v,[partialaddr(tapeval,t)] = impl(values)
            [partialaddr(tapeidx,t)] = idxs
        in Num { v, d } end
        --r:printpretty()
        return r
    end)
end

terra resetTape()
    var memallocated = (derivpos + tapepos) * 12
    if maxmem < memallocated then
        maxmem = memallocated
    end
    derivpos,tapepos = 0,0
end

terra ad.maxTapeMemUsed()
    return maxmem
end


-- Compute the gradient dself/dv for other variables v
terra Num:grad() : {}
    derivs[self.idx] = 1.0
    var t = tapepos
    for i_ = derivpos, 0, -1 do
        var i = i_ - 1 
        var dydv = derivs[i]
        var np = derivnparams[i]
        if np > 2 then
            C.printf("np = %d\n",int(np))
        end
        for j = 0,np do
            t = t - 1
            var idx,val = tapeidx[t],tapeval[t]
            derivs[idx] = derivs[idx] + val*dydv
        end
    end
    resetTape()
end

local Vector = terralib.require("vector")
-- Compute the gradient of self w.r.t the given vector of
-- variables and store the result in the given vector of doubles
terra Num:grad(indeps: &Vector(Num), gradient: &Vector(double)) : {}
	self:grad()
	gradient:resize(indeps.size)
	for i=0,indeps.size do
		gradient:set(i, derivs[indeps:get(i).idx])
	end
end
terra Num:val() return self.value end
terra Num:adj() return derivs[self.idx] end

local arith = { "__add", "__sub", "__mul", "__div" }
for i,a in ipairs(arith) do
    Num.metamethods[a] = num[a]:macro()
end
Num.metamethods.__unm = unm:macro()

ad.math = {}

ad.num = Num

for k,v in pairs(ad) do
    if op.isinstance(v) then
        ad.math[k] = v:macro()
    end
end

return ad