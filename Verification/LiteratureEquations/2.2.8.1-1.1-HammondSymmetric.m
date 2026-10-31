// Hammond, Amer. J. Math. 88 (1966), Theorem 6.2, p. 514.
// The images do not identify his normalized Siegel restrictions.
symmetric_lit_data := function(R)
  assert VariableWeights(R)[1..3] eq [2, 4, 6];
  P := PolynomialRing(Rationals(), [2, 4, 6]);
  citation := "Hammond, Amer. J. Math. 88 (1966), 497-516, Theorem 6.2, p. 514";
  return ideal<P |>, [R | R.1, R.2, R.3], citation;
end function;
