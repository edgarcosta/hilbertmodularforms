// van der Geer and Zagier, Invent. Math. 42 (1977), Theorem 7, p. 119.
symmetric_lit_data := function(R)
  assert VariableWeights(R) eq [2, 4, 6, 6, 8];
  P<A, B, C, Cprime> := PolynomialRing(Rationals(), [2, 4, 6, 6]);
  I := ideal<P | B^3 - C*Cprime>;
  images := [R.1/4, -2*R.2, 4*R.4, -2*(R.1*R.2 + 4*R.3 - 4*R.4)];
  citation := "van der Geer and Zagier, Invent. Math. 42 (1977), Theorem 7, p. 119";
  return I, images, citation;
end function;
