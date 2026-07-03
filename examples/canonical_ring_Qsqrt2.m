// Worked example: the Hilbert modular surface for Q(sqrt 2) = Q(sqrt 8) at level (1).
//
// Certifies that our computed canonical ring (the stored single source of truth in
// Verification/CanonicalRingEquations/2.2.8.1-1.1-gl-0.m) is isomorphic, as a graded
// ring over Q, to Hirzebruch's double-cover equation (with the rational sign c^2 = -C).
// The isomorphism is a stored witness map checked deterministically by
// VerifyGradedIsomorphism (no version-dependent search).
//
// Literature equation, citation, and the witness map (including the sign discussion):
//   Verification/LiteratureEquations/2.2.8.1-1.1-Hirzebruch.m
//
// Written flat (no procedure wrapper): the test runner evaluates this file inside an
// `eval`, and Magma segfaults on an `eval` nested inside a procedure inside that eval.

label := "2.2.8.1-1.1";
J := LoadStoredCanonicalRing(label);          // our computed canonical ring (SSoT)
R := Generic(J);
assert VariableWeights(R) eq [2, 4, 6, 14];

litfile := "Verification/LiteratureEquations/2.2.8.1-1.1-Hirzebruch.m";
LitData := eval (Read(litfile) cat "\nreturn LitData;");
I, PhiImages, PsiImages, citation := LitData(R, R);   // literature ideal + witness map

assert VerifyGradedIsomorphism(I, J, PhiImages, PsiImages);
printf "Q(sqrt2) level 1: our canonical ring is graded-isomorphic over Q to %o.\n", citation;
