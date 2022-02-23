
//Compute resolution of cusp at infinity following the examples in Van
//der Geer, pp. 189 and following.

function EqUpToCyclicPermutation(L1, L2)
    n := #L1;
    if n ne #L2 then return false; end if;
    for k := 1 to n do
	if L1 eq L2 then return true; end if;
	L1 := L1[2..n] cat [L1[1]];
    end for;
    return false;
end function;

//p.189: Discriminant 5, level Gamma(2)                                                
F := QuadraticField(5);
ZF := Integers(F);
L := CuspResolutionIntersections(F, 1*ZF, 2*ZF, F!1, F!0);
test := [-3,-3,-3];
assert EqUpToCyclicPermutation(L, test);

//p.193: Same field, Gamma(3) 
L := CuspResolutionIntersections(F, 1*ZF, 3*ZF, F!1, F!0);
test := [-3,-3,-3,-3];
assert EqUpToCyclicPermutation(L, test);

