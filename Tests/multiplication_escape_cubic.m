// test-time: ~40s
// (2,2,2) * (2,2,4) lands in (4,4,6) over the cubic Q(zeta_7)^+, N=3 (a dim-15 multi-orbit target).
R<x> := PolynomialRing(Rationals());
F := NumberField(x^3 - x^2 - 2*x + 1);
ZF := Integers(F);
M := GradedRingOfHMFs(F, 100);
N := 3*ZF;

S222 := CuspFormBasis(HMFSpace(M, N, [2,2,2]));
S224 := CuspFormBasis(HMFSpace(M, N, [2,2,4]));
S446 := CuspFormBasis(HMFSpace(M, N, [4,4,6]));

assert #LinearDependence(S446) eq 0;

prods := [f * g : f in S222, g in S224];
assert #LinearDependence(S446 cat prods) eq #prods;
