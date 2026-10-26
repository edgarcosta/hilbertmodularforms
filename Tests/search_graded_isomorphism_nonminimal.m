// Reducing y + 2*x^2 modulo the target ideal changes its diagonal coefficient.
// The default search must retain an isomorphism of these nonminimal presentations.
procedure test_nonminimal_presentations()
  R<x, y, z> := PolynomialRing(Rationals(), [2, 4, 5]);
  I := ideal< R | y - 3*x^2, z^2 - x^5 >;
  J := ideal< R | y - x^2, z^2 - x^5 >;
  assert VerifyGradedIsomorphism(I, J,
    [R | x, y + 2*x^2, z], [R | x, y - 2*x^2, z]);

  found, Phi, Psi := SearchGradedIsomorphism(I, J);
  assert found;
  assert VerifyGradedIsomorphism(I, J, Phi, Psi);
end procedure;

// A redundant target variable must remain available in every image of its weight.
// Swapping y and z needs it off the diagonal of the equal-weight block.
procedure test_nonminimal_equal_weight_block()
  R<x, y, z, t> := PolynomialRing(Rationals(), [2, 4, 4, 5]);
  I := ideal< R | y, z^2 - x^4 >;
  J := ideal< R | z, y^2 - x^4 >;
  phi := [R | x, z, y, t];
  assert VerifyGradedIsomorphism(I, J, phi, phi);

  found, Phi, Psi := SearchGradedIsomorphism(I, J);
  assert found;
  assert VerifyGradedIsomorphism(I, J, Phi, Psi);
end procedure;

test_nonminimal_presentations();
test_nonminimal_equal_weight_block();
