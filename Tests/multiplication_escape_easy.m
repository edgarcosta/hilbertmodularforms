// test-time: ~14s
// (2,2) * (2,4) lands in (4,6) over Q(sqrt5), N=7 (the (2,4) space is a dim-2 Hecke orbit).
F := QuadraticField(5);
ZF := Integers(F);
M := GradedRingOfHMFs(F, 100);
N := 7*ZF;

S22 := CuspFormBasis(HMFSpace(M, N, [2,2]));
S24 := CuspFormBasis(HMFSpace(M, N, [2,4]));
S46 := CuspFormBasis(HMFSpace(M, N, [4,6]));

assert #S24 eq 2;
assert #LinearDependence(S46) eq 0;

prods := [S22[1] * f : f in S24];
assert #LinearDependence(S46 cat prods) eq #prods;
