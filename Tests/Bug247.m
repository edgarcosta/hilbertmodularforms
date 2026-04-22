K := QuadraticField(193);
ZK := Integers(K);
f := Eigenforms(HilbertCuspForms(K, 1*ZK, [2,2]))[1];
f_evs := [[HeckeEigenvalue(f, P) : P in PrimeIdealsOverPrime(K,p)] : p in PrimesUpTo(10)];