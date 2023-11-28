printf "Check computation of surface for Q(sqrt(13)) with trivial level...";
F := QuadraticField(13);
ZF := Integers(F);
NN := 1*ZF;
gen_bd := 8;
rel_bd := 2*gen_bd;
prec := ComputePrecisionFromHilbertSeries(NN, gen_bd);
S := HilbertModularSurface(F, NN, gen_bd, rel_bd : Precision := prec);
assert Dimension(S) eq 2;
assert ArithmeticGenus(S) eq 1;
Fp := GF(13);
Sp := ChangeRing(S, Fp);
R := CoordinateRing(AmbientSpace(Sp));
mon8 := MonomialsOfWeightedDegree(R, 8);
m := map<Sp->ProjectiveSpace(Fp, #mon8 - 1) | SetToSequence(mon8)>;
im := Image(m);
assert #RationalPoints(im) eq 212;

// NOTE: This test cannot recognize if the surface is the same up to linear change
// of coordinates. Thus, this might fail in the future if the equations change...

StoredAmbient<[x]> := ProjectiveSpace(Rationals(), [1,2,3,3,4]);

storedEquations := [
    x[2]^3 - x[1]*x[2]*x[4] - 4*x[3]*x[4] + 4*x[4]^2,
    x[1]^4*x[2]^2 - 4*x[1]^3*x[2]*x[3] - 176*x[1]*x[2]^2*x[3] + 16*x[1]^2*x[3]^2 + 3456*x[2]*x[3]^2 - x[1]^5*x[4] + 4*x[1]^3*x[2]*x[4] - 212*x[1]*x[2]^2*x[4] + 144*x[1]^2*x[3]*x[4] - 1008*x[2]*x[3]*x[4] + 228*x[1]^2*x[4]^2 - 720*x[2]*x[4]^2 - 368*x[2]^2*x[5] - 64*x[1]*x[3]*x[5] + 368*x[1]*x[4]*x[5] + 64*x[5]^2];

storedS := Scheme(StoredAmbient, storedEquations);
comparisonHom := map<S->storedS | x>;
assert comparisonHom(S) eq storedS;
