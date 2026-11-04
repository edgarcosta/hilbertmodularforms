// Nagaoka, J. Math. Soc. Japan 35 (1983), Theorems 1-2, (5.2), (5.6), Lemma 5.2.
symmetric_lit_data := function(R)
  assert VariableWeights(R)[1..3] eq [2, 6, 10];
  P<G2, J6, J10, J12> := PolynomialRing(Rationals(), [2, 6, 10, 12]);
  I := ideal<P | 4*J12 - J6^2 + G2*J10>;
  images := [R.1, R.2, R.3, (R.2^2 - R.1*R.3)/4];
  citation := "Nagaoka, J. Math. Soc. Japan 35 (1983), Theorems 1-2 and 5.1-5.2";
  return I, images, citation;
end function;
