// Singular maps can satisfy all membership equations. The search must
// exclude these families to recover an isomorphism.
procedure test_round_trip(name, I, phi0)
  R := Generic(I);
  h := hom<R -> R | phi0>;
  J := ideal<R | [h(g) : g in Basis(I)]>;
  assert VerifyGradedIsomorphism(I, J, phi0, GradedInverseImages(R, phi0));
  found, Phi, Psi := SearchGradedIsomorphism(I, J);
  error if not found, name cat ": no map found";
  assert VerifyGradedIsomorphism(I, J, Phi, Psi);
end procedure;

// Weights [2,4,4,6]: only the weight-2 scaling is pinned. For each point c of the cone
// over V(I), a -> c1*a, b -> c2*a^2, c -> c3*a^2, d -> c4*a^3 maps I to 0.
procedure test_singular_weight_blocks()
  R<a, b, c, d> := PolynomialRing(Rationals(), [2, 4, 4, 6]);
  I := ideal<R | b*c - a*d - a^4, d^2 - b^3 + c^3 - a^2*b^2>;
  test_round_trip("weights [2,4,4,6]", I, [R | 2*a, b + c, b - c + a^2, 4*d + a*b]);
end procedure;

test_singular_weight_blocks();

// Weights [2,2,6]: the relation has no w^2 term, so u, v -> 0 and w -> p*w + (any cubic
// in u, v) maps I to 0 for every pinned weight-6 scaling p.
procedure test_singular_cubic_images()
  S<u, v, w> := PolynomialRing(Rationals(), [2, 2, 6]);
  I := ideal<S | w*(u^3 - v^3 + u*v^2) + u^6 + v^6 - u^2*v^4>;
  test_round_trip("weights [2,2,6]", I, [S | 2*u + v, u - v, -2*w + u^3 + u*v^2]);
end procedure;

test_singular_cubic_images();
