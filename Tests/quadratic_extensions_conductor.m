// The unramified extension F(sqrt(2))/F comes from the nontrivial ideal class.
F := QuadraticField(10);
ZF := Integers(F);
assert ClassNumber(F) eq 2;
P<x> := PolynomialRing(F);
K := ext<F | x^2 - 2>;
ff, oo := Conductor(AbelianExtension(K));
assert ff eq 1*ZF and IsEmpty(oo);

for infinity in [[], [1,2]] do
  Ks := QuadraticExtensionsWithConductor(1*ZF, infinity);
  assert #Ks eq 1;
  assert IsSquare(Ks[1]!2);
end for;

Ks := QuadraticExtensionsWithConductor(7*ZF, [1,2]);
assert &or[IsSquare(L!2) : L in Ks];
