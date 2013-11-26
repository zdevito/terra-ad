local ad = terralib.require("ad2")

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

local a,b,c = f(4,3)
assert(a == 32)
assert(b == 11)
assert(c == 4)
print(a,b,c)