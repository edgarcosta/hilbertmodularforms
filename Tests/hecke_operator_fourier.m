// Tests that a cusp space is stable under the Fourier coefficient Hecke operators

R<x> := PolynomialRing(Rationals());
F := NumberField(x^3-x^2-2*x+1);
ZF := Integers(F);

N := ideal<ZF | [43, 0, 0], [15, 1, 0]>;
k := [2,2,3];
H := HeckeCharacterGroup(N, [1,2,3]);
chi := H.1;
assert Order(chi) eq 2;
assert HeckeCharLabel(chi) eq "1.-2.-1.1_43.2_2u1u1.2.3u";

M := GradedRingOfHMFs(F, 200);
Mk := HMFSpace(M, N, k, chi);
Sk := CuspFormBasis(Mk);
assert #LinearDependence(Sk) eq 0;

for pp in PrimesUpTo(20, F) do
  _, pi := IsNarrowlyPrincipal(pp);
  TpSk := [HeckeOperatorFourier(f, F!pi) : f in Sk];
  // in principle TpSk could be lower dimensional but I don't think it
  // is in this example
  assert #Intersection(TpSk, Sk) eq #TpSk;
end for;
