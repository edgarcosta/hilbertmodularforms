// SearchGradedIsomorphism (Verification/IsIsomorphic.m) when the target ideal J has a
// nonzero element f in the weight of a generator x. The image of x is only defined
// modulo J. If x -> phi(x) + t*f stays a free direction of the coefficient system, every
// pinned system is positive-dimensional and the search fails.
printf "SearchGradedIsomorphism with a relation in a generator weight...\n";
Q := Rationals();

R<a, b, c> := PolynomialRing(Q, [2, 4, 8]);
// b^2 - a^4 has the weight of c. Once the scalings of a and b are fixed, R/I has finitely
// many graded automorphisms, so the relations determine phi(c) modulo I.
I := ideal< R | b^2 - a^4, c^2 - a^2*b*c - a^8 >;
phi0 := [ R | 2*a, 4*b + a^2, 8*c + a^2*b + a^4 ];
h := hom< R -> R | phi0 >;
J := ideal< R | [h(g) : g in Basis(I)] >;
assert VerifyGradedIsomorphism(I, J, phi0, GradedInverseImages(R, phi0));

found, Phi, Psi := SearchGradedIsomorphism(I, J);
assert found;
assert VerifyGradedIsomorphism(I, J, Phi, Psi);

printf "relation-in-generator-weight search test passed.\n";
