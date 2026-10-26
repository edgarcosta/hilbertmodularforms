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

// Q(sqrt(30)) has real and CM extensions with the same finite conductor.
// Ray class groups count extensions allowed by each infinite modulus.
// Inclusion-exclusion counts those ramified at exactly the requested places.
procedure test_infinite_conductor(dividing)
  F := QuadraticField(30);
  NN := 1*Integers(F);
  for infinity in [[], [1], [2], [1,2], [2,1]] do
    G := RayClassGroup(NN, Sort(infinity));
    expected := #quo<G | 2*G> - 1;
    if not dividing then
      expected := 0;
      for places in Subsets(Seqset(infinity)) do
        G := RayClassGroup(NN, Sort(Setseq(places)));
        expected +:= (-1)^(#infinity - #places) * (#quo<G | 2*G> - 1);
      end for;
    end if;
    Ks := QuadraticExtensionsWithConductor(NN, infinity : Dividing := dividing);
    error if #Ks ne expected,
      Sprintf("Wrong extension count for infinity %o, Dividing := %o: %o, expected %o",
        infinity, dividing, #Ks, expected);
    for K in Ks do
      ff, oo := Conductor(AbelianExtension(K));
      assert ff eq NN;
      if dividing then
        assert Seqset(oo) subset Seqset(infinity);
      else
        assert Seqset(oo) eq Seqset(infinity);
      end if;
    end for;
  end for;
end procedure;

test_infinite_conductor(true);
test_infinite_conductor(false);
