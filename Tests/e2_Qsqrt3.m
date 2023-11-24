printf "Testing Eisenstein series over Q(sqrt(3))..."; //use printf with no \n
prec := 125;
D := 12;
F:=QuadraticField(D);
ZF := Integers(F);
GrRing := GradedRingOfHMFs(F, prec);
N := 1*ZF;
M2 := HMFSpace(GrRing, N, [2, 2]);
B2 := Basis(M2); // EisensteinBasis
assert #B2 eq 2;
assert EisensteinBasis(M2) eq B2;
E1, E2 := Explode(B2);
bb1, bb2 := Explode(NarrowClassGroupReps(GrRing));
f1 := E1 - E2;
f2 := E1 + E2;
assert IsZero(Components(f1)[bb1]);
assert IsZero(Components(f2)[bb2]);
assert IsZero(f1*f2);

M4 := HMFSpace(GrRing, N, [4, 4]);
B4 := Basis(M4);
assert #B4 eq 4;

assert LinearDependence([f1*f1] cat B4) eq [[ 23, -46, 46, -1728, 0 ]];
assert LinearDependence([f2*f2] cat B4) eq [[ 23, -46, -46, 0, -192 ]];
