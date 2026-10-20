// test-time: ~11s
// (2,2) * (2,4) lands in (4,6) over Q(sqrt17), N=2, where the (2,4) space is 4-dimensional.
F := QuadraticField(17);
ZF := Integers(F);
M := GradedRingOfHMFs(F, 120);
N := 2*ZF;

S22 := CuspFormBasis(HMFSpace(M, N, [2,2]));
S24 := CuspFormBasis(HMFSpace(M, N, [2,4]));
S46 := CuspFormBasis(HMFSpace(M, N, [4,6]));

assert #S24 eq 4;
assert #LinearDependence(S46) eq 0;

prods := [S22[1] * f : f in S24];
assert #LinearDependence(S46 cat prods) eq #prods;
