// Nagaoka, J. Math. Soc. Japan 35 (1983), Theorems 1-2, (5.2), (5.6), Lemma 5.2.
symmetric_lit_data := function(R)
  assert VariableWeights(R)[1..3] eq [2, 4, 6];
  P<G2, H4, H6> := PolynomialRing(Rationals(), [2, 4, 6]);
  I := ideal<P |>;
  images := [R.1, R.2, R.3];
  citation := "Nagaoka, J. Math. Soc. Japan 35 (1983), Theorems 1-2 and 5.1-5.2";
  return I, images, citation;
end function;
