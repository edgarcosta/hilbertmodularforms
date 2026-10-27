SetNthreads(1);
SetSeed(1);

// The scroll S(1,13) needs sums for its parameters. Exhausting coordinate
// triples must leave time for CertifyGradedDomain to try other systems.
procedure test_scroll_domain_within_budget()
  R<[x]> := PolynomialRing(Rationals(), 16);
  M := Matrix(R, 2, 14,
      [x[1]] cat [x[i] : i in [3..15]] cat
      [x[2]] cat [x[i] : i in [4..16]]);
  I := ideal<R | Minors(M, 2)>;
  assert Dimension(I) eq 3;
  Alarm(30);
  proved, proof := CertifyGradedDomain(I : PrimeTimeLimit := 0);
  Alarm(0);
  assert proved and proof`Status eq "domain proved";
  assert proof`Ideal eq I;
end procedure;

test_scroll_domain_within_budget();
