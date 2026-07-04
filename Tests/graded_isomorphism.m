// Regression for VerifyGradedIsomorphism / SearchGradedIsomorphism (Verification/IsIsomorphic.m).
// Small synthetic weighted rings so it runs fast in CI. Exercises:
//  (1) VerifyGradedIsomorphism true for a genuine graded iso and false for a bogus map;
//  (2) SearchGradedIsomorphism recovering a scaling + lower-order-mixing iso whose target
//      is written in a different monomial order than the source;
//  (3) an equal-weight block where the iso PERMUTES two same-weight generators.
printf "Testing graded isomorphism finder/certifier...\n";
Q := Rationals();

// ---- (1)+(2): distinct weights [2,4,6], single relation, target via a graded iso ----
R<a2, a4, a6> := PolynomialRing(Q, [2, 4, 6]);
f := a6^2 - a2^3*a6 - a4^3 + a2*a4*a6;             // some weight-12 relation
I := ideal< R | f >;
// a genuine graded automorphism phi of R: scalings are powers of two (the default
// finder search set), with arbitrary lower-order mixing (solved linearly, not searched)
phi := [ R | 2*a2, -4*a4 + a2^2, a6 - a2*a4 + 2*a2^3 ];
psi := GradedInverseImages(R, phi);
// build the target ideal J = phi(I) (so I and J ARE graded-isomorphic by construction)
h := hom< R -> R | phi >;
J := ideal< R | h(f) >;

// certifier: the constructed map certifies I -> J
assert VerifyGradedIsomorphism(I, J, phi, psi);
// bogus map (wrong scaling) must be rejected
bogus := [ R | 2*a2, -3*a4, a6 ];
assert not VerifyGradedIsomorphism(I, J, bogus, GradedInverseImages(R, bogus));
// non-homogeneous input is rejected up front
Inh := ideal< R | a2 + 1 >;
assert not VerifyGradedIsomorphism(Inh, Inh, [R| a2, a4, a6], [R| a2, a4, a6]);

// finder: recover SOME verified map I -> J (need not equal the constructed one)
found, PhiF, PsiF := SearchGradedIsomorphism(I, J);
assert found;
assert VerifyGradedIsomorphism(I, J, PhiF, PsiF);

// ---- (3): equal-weight block; iso swaps the two weight-2 generators ----
S<x, y, z> := PolynomialRing(Q, [2, 2, 4]);
g := z^2 - x*y*z + x^3*y - x*y^3;                  // symmetric-ish weight-8 relation
IS := ideal< S | g >;
// swap x<->y (a graded automorphism), producing a differently-written target
sw := hom< S -> S | [y, x, z] >;
JS := ideal< S | sw(g) >;
foundS, PhiS, PsiS := SearchGradedIsomorphism(IS, JS);
assert foundS;
assert VerifyGradedIsomorphism(IS, JS, PhiS, PsiS);

printf "graded isomorphism tests passed.\n";
