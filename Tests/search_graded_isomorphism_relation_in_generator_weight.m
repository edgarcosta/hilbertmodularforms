// A target relation in a generator weight leaves free image coefficients.
// The search must find a map modulo that relation.
procedure test_relation_in_generator_weight()
  R<a, b, c> := PolynomialRing(Rationals(), [2, 4, 8]);
  // The relation b^2 - a^4 has the weight of c.
  I := ideal<R | b^2 - a^4, c^2 - a^2*b*c - a^8>;
  phi0 := [R | 2*a, 4*b + a^2, 8*c + a^2*b + a^4];
  h := hom<R -> R | phi0>;
  J := ideal<R | [h(g) : g in Basis(I)]>;
  assert VerifyGradedIsomorphism(I, J, phi0, GradedInverseImages(R, phi0));

  found, Phi, Psi := SearchGradedIsomorphism(I, J);
  assert found;
  assert VerifyGradedIsomorphism(I, J, Phi, Psi);
end procedure;

test_relation_in_generator_weight();
