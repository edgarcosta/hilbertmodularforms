// Test whether the square of a [2,2,3] form is in the [4,4,6] space

R<x> := PolynomialRing(Rationals());
F := NumberField(x^3-x^2-2*x+1);
ZF := Integers(F);

N := ideal<ZF | [43, 0, 0], [15, 1, 0]>;
k := [2,2,3];
H := HeckeCharacterGroup(N, [1,2,3]);
chi := H.1;
assert Order(chi) eq 2;
assert HeckeCharLabel(chi) eq "1.-2.-1.1_43.2_2u1u1.2.3u";

M := GradedRingOfHMFs(F, 111);
Mk := HMFSpace(M, N, k, chi);
Sk := CuspFormBasis(Mk);

M446 := HMFSpace(M, N, [4,4,6]);
S446 := CuspFormBasis(M446);

assert #LinearDependence(S446) eq 0;
Sk_squared := [Sk[1]^2, Sk[1] * Sk[2], Sk[2]^2];
assert #LinearDependence(Sk_squared) eq 0;
assert #Intersection(Sk_squared, S446) eq #Sk_squared;
