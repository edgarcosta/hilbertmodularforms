
//Compute resolution of cusp at infinity following the examples in Van
//der Geer, starting p.189

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

//p.195: Discriminant 8, Level Gamma(p7)
F := QuadraticField(8);
ZF := Integers(F);
p7 := Decomposition(ZF, 7)[1][1];
L := CuspResolutionIntersections(F, 1*ZF, p7, F!1, F!0);
test := [-2,-4,-2,-4,-2,-4];
assert EqUpToCyclicPermutation(L, test);

//p.197: Discriminant 13, not quite Gamma(2) but close  
F := QuadraticField(13);
ZF := Integers(F);
p := 2*ZF;
L := CuspResolutionIntersections(F, 1*ZF, p, F!1, F!0: flag:=2);
test := RepeatSequence([-2,-5,-2], 3); //this is a typo in the book: quadratic number with periodic continued fraction [2,3,2] lies in field of discriminant 21, not 13
assert EqUpToCyclicPermutation(L, test);

//p.198: Discriminant 17, level Gamma(2)
F := QuadraticField(17);
ZF := Integers(F);
p := 2*ZF;
L := CuspResolutionIntersections(F, 1*ZF, p, F!1, F!0);
test := [-2,-3,-5,-3,-2];
assert EqUpToCyclicPermutation(L, test);

//p.199: Discriminant 24, level Gamma(3+sqrt(6))
F := QuadraticField(24);
ZF := Integers(F);
p := (3 + SquareRoot(ZF!6))*ZF;
L := CuspResolutionIntersections(F, 1*ZF, p, F!1, F!0);
test := RepeatSequence([-2,-2,-2,-4], 2);
assert EqUpToCyclicPermutation(L, test);

//p.201: Discriminant 40, level Gamma(p2)
F := QuadraticField(40);
ZF := Integers(F);
p := Factorization(2*ZF)[1][1];
L := CuspResolutionIntersections(F, 1*ZF, p, F!1, F!0);
test := [-2,-3,-4,-3];
assert EqUpToCyclicPermutation(L, test);
