// Hilbert-series equality and independence leave the domain condition open.
SetNthreads(4);
F := QuadraticField(13);
N := 1*Integers(F);
M := GradedRingOfHMFs(F, ComputePrecisionFromHilbertSeries(N, 16));
dict := ConstructGeneratorsAndRelations(M, N, 8, 16);
Gens := dict[1];
R := ConstructWeightedPolynomialRing(Gens);
assert [WeightedDegree(R.i) : i in [1..Rank(R)]] eq [2,4,6,6,8];
bad := AssociativeArray();
for pair in [<12,R.3^2>, <16,R.5^2>] do
  mons := MonomialsOfWeightedDegree(R, pair[1]);
  bad[pair[1]] := [[Rationals() | MonomialCoefficient(pair[2], m) : m in mons]];
end for;
I := ConstructIdeal(R, bad);
assert HilbertSeriesSanityCheck(M, N, [I]);
assert CertifyAlgIndependent(Gens, bad, 3);
assert R.3 notin I and R.3^2 in I;
printf "Hilbert-series and independence gates alone accept a non-domain\n";
proved, proof := CertifyGradedDomain(I);
assert not proved and proof`Status eq "not a domain";
printf "Domain gate refuses the non-domain: PASSED\n";
