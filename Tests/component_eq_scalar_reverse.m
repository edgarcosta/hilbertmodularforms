// Regression test: 'eq' between ModFrmHilDEltComp and a scalar must be
// symmetric. Magma does not auto-commute user-defined 'eq' intrinsics, so
// both (f, c) and (c, f) argument orders need their own intrinsic.
printf "Testing symmetric scalar equality for ModFrmHilDEltComp...";
D := 12;
F := QuadraticField(D);
prec := 125;
ZF := Integers(F);
GrRing := GradedRingOfHMFs(F, prec);
N := 1*ZF;
M2 := HMFSpace(GrRing, N, [2, 2]);
B2 := Basis(M2); // EisensteinBasis
E1 := B2[1];
bb1 := NarrowClassGroupReps(GrRing)[1];
comp := Components(E1)[bb1];
assert (0 eq comp) eq (comp eq 0);
