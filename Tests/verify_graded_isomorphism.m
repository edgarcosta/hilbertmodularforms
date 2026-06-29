// Tests for VerifyGradedIsomorphism: a deterministic, inverse-composition-checked
// certifier that a stored graded-ring map is an isomorphism of weighted quotient rings.
// It replaces the version-fragile SolveZeroDimIdeal search on the CI verify path.
// These are synthetic cases; the real literature witness maps arrive in plan 4.
printf "VerifyGradedIsomorphism...";

// P(2,4) with one relation; the identity map is an isomorphism (positive case).
R<x2,x4> := PolynomialRing(Rationals(), [2,4], <"grevlexw", [2,4]>);
I := ideal< R | x4^2 - x2^4 >;
assert VerifyGradedIsomorphism(I, I, [R | x2, x4], [R | x2, x4]);

// A nontrivial graded automorphism phi: x4 -> x4 + x2^2 (weight 4), with inverse
// psi: x4 -> x4 - x2^2, carrying I to its image J in a fresh ring (positive case).
S<y2,y4> := PolynomialRing(Rationals(), [2,4], <"grevlexw", [2,4]>);
phiR := hom< R -> S | [y2, y4 + y2^2] >;
J := ideal< S | [ phiR(g) : g in Generators(I) ] >;
assert VerifyGradedIsomorphism(I, J, [S | y2, y4 + y2^2], [R | x2, x4 - x2^2]);

// SOUNDNESS GATE: containments hold (zero ideal) but the maps are NOT mutual inverses
// (scaling z2 -> 2 z2 gives psi.phi = 4 z2 != z2). The old containments-only check
// wrongly accepted this; the inverse-composition checks (3),(4) must reject it.
Z<z2> := PolynomialRing(Rationals(), [2], <"grevlexw", [2]>);
zero := ideal< Z | Z!0 >;
assert not VerifyGradedIsomorphism(zero, zero, [Z | 2*z2], [Z | 2*z2]);

// Negative: phi does not map I into J (homogeneous, but breaks containment (1)).
J2 := ideal< S | y4^2 >;
assert not VerifyGradedIsomorphism(I, J2, [S | y2, y4], [R | x2, x4]);

// Negative: non-homogeneous image x4 -> x4 + x2 (weight 4 vs 2) must fail grading check (5).
assert not VerifyGradedIsomorphism(I, I, [R | x2, x4 + x2], [R | x2, x4 - x2]);

// GATE for check (2): psi(J) not subset I. Zero ideal I0 in P(1), J = (x^2), phi = psi = id.
// (1) holds vacuously (phi(0)=0 in J), (3) holds (psi(phi(x))-x=0 in I0), but psi(x^2)=x^2
// is not in I0, so only check (2) can reject this. Without (2) it would wrongly verify.
Rw1<x> := PolynomialRing(Rationals(), [1], <"grevlexw", [1]>);
I0 := ideal< Rw1 | Rw1!0 >;
Jx2 := ideal< Rw1 | x^2 >;
assert not VerifyGradedIsomorphism(I0, Jx2, [Rw1 | x], [Rw1 | x]);

// GATE for check (4): phi is only a retract, not an isomorphism. I0 zero in P(1), J0 zero in
// P(1,1); phi: x -> u, psi: u -> x, v -> x. Then phi(psi(v)) - v = u - v is not in J0, so only
// check (4) can reject this. Without (4) it would wrongly verify.
Sw<u,v> := PolynomialRing(Rationals(), [1,1], <"grevlexw", [1,1]>);
J0 := ideal< Sw | Sw!0 >;
assert not VerifyGradedIsomorphism(I0, J0, [Sw | u], [Rw1 | x, x]);

// GATE for the homogeneous-ideal guard: a non-homogeneous ideal has no graded quotient,
// so even the identity map must return false.
Inh := ideal< R | x4 - 1 >;
assert not VerifyGradedIsomorphism(Inh, Inh, [R | x2, x4], [R | x2, x4]);

printf "PASSED\n";
