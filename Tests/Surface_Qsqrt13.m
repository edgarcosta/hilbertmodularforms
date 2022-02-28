printf "Check computation of surface for Q(sqrt(13)) with trivial level...";
F := QuadraticField(13);
ZF := Integers(F);
S := HilbertModularSurface(F, 1*ZF, 8, 16 : Precision := 5);
assert Dimension(S) eq 2;
assert ArithmeticGenus(S) eq 1;
Fp := GF(13);
Sp := ChangeRing(S, Fp);
R := CoordinateRing(AmbientSpace(Sp));
mon8 := MonomialsOfWeightedDegree(R, 8);
m := map<Sp->ProjectiveSpace(Fp, #mon8 - 1) | SetToSequence(mon8)>;
im := Image(m);
assert #RationalPoints(im) eq 212;
// this might fail in the future if the equations change...
assert [[[c], [Exponents(m) : m in mon]] where c, mon := CoefficientsAndMonomials(elt) : elt in DefiningEquations(S)] eq
[[[[-1,1,4,-4]],[[0,3,0,0,0],[1,1,0,1,0],[0,0,1,1,0],[0,0,0,2,0]]],[[[-1,4,816,-16,-3456,1,-4,2932,-784,-9872,-2948,11600,-912,64,912,-64]],[[4,2,0,0,0],[3,1,1,0,0],[1,2,1,0,0],[2,0,2,0,0],[0,1,2,0,0],[5,0,0,1,0],[3,1,0,1,0],[1,2,0,1,0],[2,0,1,1,0],[0,1,1,1,0],[2,0,0,2,0],[0,1,0,2,0],[0,2,0,0,1],[1,0,1,0,1],[1,0,0,1,1],[0,0,0,0,2]]]];
return true;

