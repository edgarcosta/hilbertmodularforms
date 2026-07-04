// Literature equations and a deterministic witness map for the Hilbert modular
// surface over Q(sqrt 5) at level (1), matched to the stored canonical ring
// Verification/CanonicalRingEquations/2.2.5.1-1.1-gl-0.m.
//
// Sources: K.-B. Gundlach, Math. Ann. 152 (1963), 226-256 (original determination of
// the ring for Q(sqrt 5)); F. Hirzebruch, "The ring of Hilbert modular forms for real
// quadratic fields of small discriminant", LNM 627 (1977), 287-323 (the presentation
// used here).
//
// Generators in weights [2, 6, 10, 20] (w, x, y, z for the literature; X2, X6, X10,
// X20 for ours). Hirzebruch's single relation for the surface:
//   fH = z^2 - y (3125 y^3 + 2000 y^2 x w^2 + 256 y^2 w^5 - 900 y x^3 w
//                 - 128 y x^2 w^4 + 16 x^4 w^3 + 108 x^5).
//
// The witness map phi carries fH onto our stored relation; psi = phi^{-1} is
// recovered by GradedInverseImages, and VerifyGradedIsomorphism checks the pair
// deterministically (no SolveZeroDimIdeal search).
//
// eval-loaded: `LitData := eval (Read(<this file>) cat "return LitData;");`
// Call with a single loaded ring R (= Generic(J)) for both arguments:
// `I, PhiImages, PsiImages, citation := LitData(R, R);`
LitData := function(Rsrc, Rtgt)
  w := Rsrc.1; x := Rsrc.2; y := Rsrc.3; z := Rsrc.4;
  fH := z^2 - y*(3125*y^3 + 2000*y^2*x*w^2 + 256*y^2*w^5 - 900*y*x^3*w
                 - 128*y*x^2*w^4 + 16*x^4*w^3 + 108*x^5);
  I := ideal< Rsrc | fH >;

  X2 := Rtgt.1; X6 := Rtgt.2; X10 := Rtgt.3; X20 := Rtgt.4;
  PhiImages := [ Rtgt |
    X2,
    -128*X6,
    4096*X10,
    -4194304*X2^2*X6*X10 + 4194304*X2*X6^3 - 33554432*X20 + 218103808*X10^2 ];
  PsiImages := [ Rsrc | p : p in GradedInverseImages(Rtgt, PhiImages) ];

  citation := "Gundlach, Math. Ann. 152 (1963); Hirzebruch, LNM 627 (1977), 287-323 (Q(sqrt 5))";
  return I, PhiImages, PsiImages, citation;
end function;
return LitData;
