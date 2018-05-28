load "config.m";

F := QuadraticField(8);
ZF<w> := Integers(F);
N := ideal<ZF | {3}>;
K := Rationals();
prec := 200;
M := HMFSpace(F, N, prec);

time CacheHeckeEigenvalues(M, [2,2]);
time CacheHeckeEigenvalues(M, [4,4]);
time CacheHeckeEigenvalues(M, [8,8]);

Save(M, "save_test.m");
