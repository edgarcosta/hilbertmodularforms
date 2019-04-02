load "config.m";

F := QuadraticField(12);
ZF<w> := Integers(F);
N := ideal<ZF | {11}>;
K := Rationals();
prec := 50;
M := HMFSpace(F, prec);

time basis := Basis(M, N, [2,2]);

/*
time HeckeEigenvalues(M, N, [2,2]);
time HeckeEigenvalues(M, N, [4,4]);
// time HeckeEigenvalues(M, N, [8,8]);
// test edit

// comment
Save(M, "save_test.m");
M := Load("save_test.m");
*/
