// Literature equations and a deterministic witness map for the Hilbert modular
// surface over Q(sqrt 13) at level (1), matched to the stored canonical ring
// Verification/CanonicalRingEquations/2.2.13.1-1.1-gl-0.m.
//
// Source: G. van der Geer and D. Zagier, "The Hilbert modular group for the field
// Q(sqrt 13)", Invent. Math. 42 (1977), 93-133; equations on p. 120.
//
// Generators in our canonical weights [2, 4, 6, 6, 8] (call them X2, X4, X6, Y6, X8).
// The two van der Geer-Zagier relations:
//   F = X4^3 - X6*Y6
//   G = X8^2 - ( 256 X2^5 X6 - 128 X2^4 X4^2 + 16 X2^3 X4 Y6 - 656 X2^3 X4 X6
//               + 776 X2^2 X4^3 - 261 X2 X4^2 Y6 + 27 X4 Y6^2 - 27 X2^2 X6^2
//               + 495/2 X2 X4^2 X6 - 947/16 X4^4 + 54 X4 X6^2 )
//
// The witness map phi carries the vdG presentation onto our stored presentation.
// The paper's own "ours" presentation and our stored SSoT presentation differ only
// in the choice of weight-8 generator, X8_paper = X8_stored + (25/4)(X4^2 - X2 Y6);
// the phi below already targets the stored generators, so no rescaling is needed at
// load. psi = phi^{-1} is recovered by GradedInverseImages, and VerifyGradedIsomorphism
// checks the pair deterministically (no SolveZeroDimIdeal search).
//
// eval-loaded: `LitData := eval (Read(<this file>) cat "return LitData;");`
// Call with a single loaded ring R (= Generic(J)) for both arguments:
// `I, PhiImages, PsiImages, citation := LitData(R, R);`
LitData := function(Rsrc, Rtgt)
  X2 := Rsrc.1; X4 := Rsrc.2; X6 := Rsrc.3; Y6 := Rsrc.4; X8 := Rsrc.5;
  F := X4^3 - X6*Y6;
  G := X8^2 - (256*X2^5*X6 - 128*X2^4*X4^2 + 16*X2^3*X4*Y6 - 656*X2^3*X4*X6
              + 776*X2^2*X4^3 - 261*X2*X4^2*Y6 + 27*X4*Y6^2 - 27*X2^2*X6^2
              + 495/2*X2*X4^2*X6 - 947/16*X4^4 + 54*X4*X6^2);
  I := ideal< Rsrc | F, G >;

  y2 := Rtgt.1; y4 := Rtgt.2; y6 := Rtgt.3; z6 := Rtgt.4; y8 := Rtgt.5;
  PhiImages := [ Rtgt |
    (1/4)*y2,
    -2*y4,
    4*z6,
    -2*(y2*y4 + 4*y6 - 4*z6),
    8*y8 - 4*y2*y6 + 57*y4^2 - 57*y2*z6 ];
  PsiImages := [ Rsrc | p : p in GradedInverseImages(Rtgt, PhiImages) ];

  citation := "van der Geer & Zagier, Invent. Math. 42 (1977), 93-133, p. 120";
  return I, PhiImages, PsiImages, citation;
end function;
return LitData;
