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

// Over Q(sqrt(5)), the quadratic extensions with finite conductor (4) are
// ramified at the real places {1}, {2}, and {1,2}.
F := QuadraticField(5);
ZF := Integers(F);
for infinity in [[], [1], [2], [1,2], [2,1]] do
  Ks := QuadraticExtensionsWithConductor(4*ZF, infinity);
  expected_counts := [0, 1, 3];
  assert #Ks eq expected_counts[#infinity + 1];
  for K in Ks do
    ff, oo := Conductor(AbelianExtension(K));
    assert &and[place in infinity : place in oo];
  end for;

  Ks := QuadraticExtensionsWithConductor(4*ZF, infinity : Dividing := false);
  assert #Ks eq (#infinity eq 0 select 0 else 1);
  for K in Ks do
    ff, oo := Conductor(AbelianExtension(K));
    assert ff eq 4*ZF and Seqset(oo) eq Seqset(infinity);
  end for;
end for;
