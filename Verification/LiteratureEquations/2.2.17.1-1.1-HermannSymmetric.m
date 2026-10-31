// Hermann, Math. Ann. 256 (1981), Satz 5-6, pp. 195-196.
// The images do not identify his normalized theta series.
symmetric_lit_data := function(R)
  assert VariableWeights(R) eq [2, 4, 4, 6, 6, 6, 8];
  S<G2, G4, H4, G6, H6> := PolynomialRing(Rationals(), [2, 4, 4, 6, 6]);
  I := ideal<S | G4*G6 - H4*H6,
    G4^3 - G6*H6/4 + G4*G6*G2/4,
    G6^2 - 4*H4*G4^2 - G6*H4*G2>;
  images := [-16*R.1, -16*R.2 + 16*R.3, R.2, 64*R.6, 1024*R.5 - 1024*R.6];
  citation := "Hermann, Math. Ann. 256 (1981), Satz 5-6, pp. 195-196";
  return I, images, citation;
end function;
