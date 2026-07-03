// Literature equations and a deterministic witness map for the Hilbert modular
// surface over Q(sqrt 2) = Q(sqrt 8) at level (1), matched to the stored canonical
// ring Verification/CanonicalRingEquations/2.2.8.1-1.1-gl-0.m.
//
// Source: F. Hirzebruch, "The ring of Hilbert modular forms for real quadratic
// fields of small discriminant", LNM 627 (1977), 287-323, Sec. 4 (p. 314-316).
//
// Hirzebruch works with G = SL_2(O)/{+-1} and the extended principal congruence
// subgroup for (2), with G/Gamma = S_4 permuting weight-1 forms x_1..x_4 (sigma_1 = 0).
// Writing sigma_i for the elementary symmetric functions and Delta = prod_{i<j}(x_i-x_j):
//   branch locus  C = sigma_4 (sigma_3^2 - 4 sigma_2 sigma_4)  (degree 10),
//   and H^2/Gamma-bar is the double cover  c^2 = C,  c a weight-5 skew form.
// Our canonical generators in weights [2,4,6,14] are
//   X2 = sigma_2,  X4 = sigma_4,  X6 = sigma_3^2,  X14 = sigma_3 * Delta * c,
// so  X14^2 = sigma_3^2 Delta^2 c^2.  Our forms realize the sign  c^2 = -C  (the
// Gundlach/Hirzebruch "sign question"); with the quartic-discriminant identity
//   27 Delta^2 = 4(sigma_2^2 + 12 sigma_4)^3 - (27 sigma_3^2 + 2 sigma_2^3 - 72 sigma_2 sigma_4)^2
// this gives the rational relation
//   SF = 27 X14^2 - X4(X6 - 4 X2 X4) X6 ( -4(X2^2 + 12 X4)^3 + (27 X6 + 2 X2^3 - 72 X2 X4)^2 ).
// (The opposite sign c^2 = +C forces X14 -> i X14; that mis-sign, not any real twist,
//  is what makes this surface look as if it needed Q(i).)
//
// The witness map phi carries the Hirzebruch relation SF onto our stored relation.
// psi = phi^{-1} is recovered by GradedInverseImages, and VerifyGradedIsomorphism
// checks the pair deterministically (no SolveZeroDimIdeal search).
//
// eval-loaded: `LitData := eval (Read(<this file>) cat "return LitData;");`
// Call with a single loaded ring R (= Generic(J)) for both arguments:
// `I, PhiImages, PsiImages, citation := LitData(R, R);`
LitData := function(Rsrc, Rtgt)
  X2 := Rsrc.1; X4 := Rsrc.2; X6 := Rsrc.3; X14 := Rsrc.4;
  disc := (X4*(X6 - 4*X2*X4))*X6*(-4*(X2^2 + 12*X4)^3 + (27*X6 + 2*X2^3 - 72*X2*X4)^2);
  SF := 27*X14^2 - disc;
  I := ideal< Rsrc | SF >;

  y2 := Rtgt.1; y4 := Rtgt.2; y6 := Rtgt.3; y14 := Rtgt.4;
  PhiImages := [ Rtgt |
    -1/8*y2,
    -1/4*y4,
    1/8*y2*y4 + 1/2*y6,
    1/64*y2*y4^3 + 1/128*y2^2*y4*y6 + 5/32*y4^2*y6 + 1/64*y2*y6^2 - 1/64*y14 ];
  PsiImages := [ Rsrc | p : p in GradedInverseImages(Rtgt, PhiImages) ];

  citation := "Hirzebruch, LNM 627 (1977), 287-323, Sec. 4 (double cover c^2 = -C)";
  return I, PhiImages, PsiImages, citation;
end function;
return LitData;
