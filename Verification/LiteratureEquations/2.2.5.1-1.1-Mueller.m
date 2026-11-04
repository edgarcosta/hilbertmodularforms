// Rolf Mueller, "Hilbertsche Modulformen und Modulfunktionen zu Q(sqrt5)",
// Arch. Math. 45 (1985), 239-251, Satz 1, equation (12), p.247.
//
// The even-weight generators (g2, s6, s10, s5*s15) have weights [2, 6, 10, 20].
// Here s10 = s5^2, and s15^2 is the polynomial P below.
// Mueller's unique even-weight decomposition gives the relation z^2 = y*P.
//
// eval-loaded as LitData(Rsrc, Rtgt); returns the literature ideal, forward and
// inverse images, and citation. Rtgt is the ring of the stored presentation
// Verification/CanonicalRingEquations/2.2.5.1-1.1-gl-0.m.
LitData := function(Rsrc, Rtgt)
  w := Rsrc.1; x := Rsrc.2; y := Rsrc.3; z := Rsrc.4;
  P := 3125*y^3 - 125/2*w^2*x*y^2 + 1/16*w^5*y^2
       + 225/2*w*x^3*y - 1/8*w^4*x^2*y - 54*x^5 + 1/16*w^3*x^4;
  I := ideal< Rsrc | z^2 - y*P >;

  X2 := Rtgt.1; X6 := Rtgt.2; X10 := Rtgt.3; X20 := Rtgt.4;
  PhiImages := [ Rtgt | X2, X6, X10,
    1/4*X2*X6^3 - 1/4*X2^2*X6*X10 + 13*X10^2 - 2*X20 ];
  PsiImages := [ Rsrc | w, x, y,
    1/8*w*x^3 - 1/8*w^2*x*y + 13/2*y^2 - 1/2*z ];

  citation := "Mueller, Arch. Math. 45 (1985), Satz 1, equation (12)";
  return I, PhiImages, PsiImages, citation;
end function;
return LitData;
