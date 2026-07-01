// Worked example: the Hilbert modular surface for Q(sqrt 5) at level (1).
//
// Certifies that our computed canonical ring (the stored single source of truth in
// Verification/CanonicalRingEquations/2.2.5.1-1.1-gl-0.m) is isomorphic, as a graded
// ring over Q, to Hirzebruch's equations, via a stored witness map checked
// deterministically by VerifyGradedIsomorphism (no version-dependent search).
//
// Literature equation, citation, and the witness map:
//   Verification/LiteratureEquations/2.2.5.1-1.1-Hirzebruch.m
//
// Written flat (no procedure wrapper): the test runner evaluates this file inside an
// `eval`, and Magma segfaults on an `eval` nested inside a procedure inside that eval.

label := "2.2.5.1-1.1";
J := LoadStoredCanonicalRing(label);          // our computed canonical ring (SSoT)
R := Generic(J);
assert VariableWeights(R) eq [2, 6, 10, 20];

litfile := "Verification/LiteratureEquations/2.2.5.1-1.1-Hirzebruch.m";
LitData := eval (Read(litfile) cat "\nreturn LitData;");
I, PhiImages, PsiImages, citation := LitData(R, R);   // literature ideal + witness map

assert VerifyGradedIsomorphism(I, J, PhiImages, PsiImages);
printf "Q(sqrt5) level 1: our canonical ring is graded-isomorphic over Q to %o.\n", citation;
