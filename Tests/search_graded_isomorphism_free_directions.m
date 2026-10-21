// Diagonal pins leave a torus parameter in the first ring and free shifts in the second.
// The search must specialize those directions and still certify the recovered maps.
printf "SearchGradedIsomorphism with free automorphism parameters...\n";
SetSeed(1);
Q := Rationals();

procedure RoundTrip(name, I, phi0)
  R := Generic(I);
  h := hom< R -> R | phi0 >;
  J := ideal< R | [h(g) : g in Basis(I)] >;
  assert VerifyGradedIsomorphism(I, J, phi0, GradedInverseImages(R, phi0));
  found, Phi, Psi := SearchGradedIsomorphism(I, J : Candidates := [1], MaxAttempts := 1);
  assert found;
  assert VerifyGradedIsomorphism(I, J, Phi, Psi);
  printf "  %o: found and certified\n", name;
end procedure;

// The all-ones slice has no rational point; a later specialization must be tried.
R<u, v, w> := PolynomialRing(Q, [2, 4, 4]);
I := ideal< R | v^2 - 2*w^2 - u^4 >;
RoundTrip("torus", I, [R | u, v + u^2, 2*w + u^2]);

S<a, b, c> := PolynomialRing(Q, [2, 4, 8]);
I := ideal< S | b^2 >;
RoundTrip("free shifts and top scaling", I, [S | a, b + a^2, c + a^2*b + a^4]);

printf "free-directions search test passed.\n";
