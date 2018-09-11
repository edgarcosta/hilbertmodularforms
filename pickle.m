load "config.m";

F := QuadraticField(8);
ZF<w> := Integers(F);
N := ideal<ZF | {3}>;
K := Rationals();
prec := 200;
M := HMFSpace(F, prec);

time HeckeEigenvalues(M, N, [2,2]);
time HeckeEigenvalues(M, N, [4,4]);
// time HeckeEigenvalues(M, N, [8,8]);

Save(M, "save_test.m");
M := Load("save_test.m");
