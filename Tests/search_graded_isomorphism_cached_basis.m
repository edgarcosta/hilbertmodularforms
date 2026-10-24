// HilbertSeries caches higher-degree relations in the source ideal. Expanding them
// in the generic map adds about 150 MiB to peak memory; the original three add almost nothing.
printf "SearchGradedIsomorphism after HilbertSeries.\n";
SetNthreads(4);
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
assert GetMaximumMemoryUsage() - before lt 32*1024^2;
printf "Cached-basis search found and certified.\n";
