// SearchGradedIsomorphism (Verification/IsIsomorphic.m) on rings where maps that are not
// isomorphisms satisfy every membership equation phi(I) in J. Such maps form a
// positive-dimensional family in every pinned system, so the search must exclude them
// before solving, or it finds nothing.
printf "SearchGradedIsomorphism with noninvertible maps in every pinned system...\n";
Q := Rationals();

procedure RoundTrip(name, I, phi0)
  R := Generic(I);
  h := hom< R -> R | phi0 >;
  J := ideal< R | [h(g) : g in Basis(I)] >;
  assert VerifyGradedIsomorphism(I, J, phi0, GradedInverseImages(R, phi0));
  found, Phi, Psi := SearchGradedIsomorphism(I, J);
  assert found;
  assert VerifyGradedIsomorphism(I, J, Phi, Psi);
  printf "  %o: found and certified\n", name;
end procedure;

// Weights [2,4,4,6]: only the weight-2 scaling is pinned. For each point c of the cone
// over V(I), a -> c1*a, b -> c2*a^2, c -> c3*a^2, d -> c4*a^3 maps I to 0.
R<a, b, c, d> := PolynomialRing(Q, [2, 4, 4, 6]);
I := ideal< R | b*c - a*d - a^4, d^2 - b^3 + c^3 - a^2*b^2 >;
RoundTrip("weights [2,4,4,6]", I, [R | 2*a, b + c, b - c + a^2, 4*d + a*b]);

// Weights [2,2,6]: the relation has no w^2 term, so u, v -> 0 and w -> p*w + (any cubic
// in u, v) maps I to 0 for every pinned weight-6 scaling p.
S<u, v, w> := PolynomialRing(Q, [2, 2, 6]);
I := ideal< S | w*(u^3 - v^3 + u*v^2) + u^6 + v^6 - u^2*v^4 >;
RoundTrip("weights [2,2,6]", I, [S | 2*u + v, u - v, -2*w + u^3 + u*v^2]);

printf "noninvertible-maps search test passed.\n";
