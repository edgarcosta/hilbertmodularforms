// HilbertSeries caches higher-degree relations in the source ideal. The search must
// use the short input basis to keep the added memory below 32 MiB.
procedure test_search_after_hilbert_series()
  R<a, b, c, d> := PolynomialRing(Rationals(), [1, 1, 1, 5]);
  relations := [a*b^5 - c^6, a*c^5 - b*d, d^2 - b^10];
  I := ideal<R | relations>;
  J := ideal<R | relations>;
  hs := HilbertSeries(I);
  ResetMaximumMemoryUsage();
  before := GetMemoryUsage();
  found, Phi, Psi := SearchGradedIsomorphism(I, J : Candidates := [1], MaxAttempts := 1);
  assert found;
  assert VerifyGradedIsomorphism(I, J, Phi, Psi);
  // The bound excludes expansion of the cached Groebner basis.
  assert GetMaximumMemoryUsage() - before lt 32*1024^2;
end procedure;

// The ideal equals <x^2, x*y + y^2>, but SmallBasis keeps its first relation, which
// mixes degrees 2 and 3.
procedure test_search_with_mixed_degree_relation()
  R<x, y, z> := PolynomialRing(Rationals(), [1, 1, 1]);
  I := ideal<R | x^2 + z*(x*y + y^2), x*y + y^2>;
  found, Phi, Psi := SearchGradedIsomorphism(I, I : Candidates := [1], MaxAttempts := 1);
  assert found;
  assert VerifyGradedIsomorphism(I, I, Phi, Psi);
end procedure;

test_search_after_hilbert_series();
test_search_with_mixed_degree_relation();
