// Diagonal pins leave a torus parameter in the first ring and free shifts in the second.
// The search must specialize those directions and still certify the recovered maps.
SetSeed(1);
Q := Rationals();

procedure test_round_trip(name, I, phi0)
  R := Generic(I);
  h := hom<R -> R | phi0>;
  J := ideal<R | [h(g) : g in Basis(I)]>;
  assert VerifyGradedIsomorphism(I, J, phi0, GradedInverseImages(R, phi0));
  found, Phi, Psi := SearchGradedIsomorphism(I, J : Candidates := [1], MaxAttempts := 1);
  error if not found, name cat ": no map found";
  assert VerifyGradedIsomorphism(I, J, Phi, Psi);
end procedure;

// The all-ones slice has no rational point; a later specialization must be tried.
R<u, v, w> := PolynomialRing(Q, [2, 4, 4]);
I := ideal<R | v^2 - 2*w^2 - u^4>;
test_round_trip("torus", I, [R | u, v + u^2, 2*w + u^2]);

// c is in no relation, so its scaling and its shifts by weight-8 monomials in a, b stay free.
S<a, b, c> := PolynomialRing(Q, [2, 4, 8]);
I := ideal<S | b^2>;
test_round_trip("free shifts and top scaling", I, [S | a, b + a^2, c + a^2*b + a^4]);
