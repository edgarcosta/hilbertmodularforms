// Gundlach, Math. Ann. 152 (1963), Satz 5-6, p. 241; Hammond, Amer. J. Math. 88 (1966), pp. 507-508.
// Gundlach's dimension -k is weight k. The images are abstract generators.
symmetric_lit_data := function(R)
  assert VariableWeights(R)[1..3] eq [2, 6, 10];
  P := PolynomialRing(Rationals(), [2, 6, 10]);
  citation := "Gundlach, Math. Ann. 152 (1963), 226-256, Satz 5-6, p. 241; " cat
    "Hammond, Amer. J. Math. 88 (1966), 497-516, pp. 507-508";
  return ideal<P |>, [R | R.1, R.2, R.3], citation;
end function;
