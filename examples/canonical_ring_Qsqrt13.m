// Worked example: the Hilbert modular surface for Q(sqrt 13) at level (1).
//
// Certifies that our computed canonical ring (the stored single source of truth in
// Verification/CanonicalRingEquations/2.2.13.1-1.1-gl-0.m) is isomorphic, as a graded
// ring over Q, to the equations of van der Geer and Zagier. The isomorphism is given
// by a witness map stored alongside the literature equations and checked
// deterministically by VerifyGradedIsomorphism (no version-dependent search).
//
// Literature equations, citation, and the witness map:
//   Verification/LiteratureEquations/2.2.13.1-1.1-vdGZagier.m
//
// Written flat (no procedure wrapper): the test runner evaluates this file inside an
// `eval`, and Magma segfaults on an `eval` nested inside a procedure inside that eval.

label := "2.2.13.1-1.1";
J := LoadStoredCanonicalRing(label);          // our computed canonical ring (SSoT)
R := Generic(J);
assert VariableWeights(R) eq [2, 4, 6, 6, 8];

litfile := "Verification/LiteratureEquations/2.2.13.1-1.1-vdGZagier.m";
LitData := eval (Read(litfile) cat "\nreturn LitData;");
I, PhiImages, PsiImages, citation := LitData(R, R);   // literature ideal + witness map

assert VerifyGradedIsomorphism(I, J, PhiImages, PsiImages);
printf "Q(sqrt13) level 1: our canonical ring is graded-isomorphic over Q to %o.\n", citation;
