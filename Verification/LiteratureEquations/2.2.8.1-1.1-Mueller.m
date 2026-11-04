// Rolf Mueller, "Hilbertsche Modulformen und Modulfunktionen zu Q(sqrt8)",
// Math. Ann. 266 (1983), 83-103, Satz 1, equation (31), p.98.
//
// The even-weight generators (g2, s4, s6, s5*s9) have weights [2, 4, 6, 14].
// In Mueller's notation s5 = s2*hat(s3) and s9 = s3*hat(s6).
// Thus, s5^2 = s4*(4*s6 + g2*s4) and s9^2 = s6*P, with P = hat(s6)^2 below.
//
// eval-loaded as LitData(Rsrc, Rtgt); returns the literature ideal, forward and
// inverse images, and citation. Rtgt is the ring of the stored presentation
// Verification/CanonicalRingEquations/2.2.8.1-1.1-gl-0.m.
LitData := function(Rsrc, Rtgt)
  w := Rsrc.1; x := Rsrc.2; y := Rsrc.3; z := Rsrc.4;
  P := -1728*y^2 - 288*w*x*y + w^3*y - 1024*x^3 + 4*w^2*x^2;
  I := ideal< Rsrc | z^2 - x*y*(4*y + w*x)*P >;

  X2 := Rtgt.1; X4 := Rtgt.2; X6 := Rtgt.3; X14 := Rtgt.4;
  PhiImages := [ Rtgt | X2, X4, X6,
    -2*X2*X4^3 - X2^2*X4*X6 - 20*X4^2*X6 - 2*X2*X6^2 + 2*X14 ];
  PsiImages := [ Rsrc | w, x, y,
    w*x^3 + 1/2*w^2*x*y + 10*x^2*y + w*y^2 + 1/2*z ];

  citation := "Mueller, Math. Ann. 266 (1983), Satz 1, equation (31)";
  return I, PhiImages, PsiImages, citation;
end function;
return LitData;
