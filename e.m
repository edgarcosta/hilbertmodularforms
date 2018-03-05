load "config.m";

F<nu> := QuadraticField(5);
ZF := Integers(F);
// N := (-5*nu+2)*ZF;
N := ideal<ZF|[1]>;
prec := 100;
M := HMFSpace(F, N, prec);

X := HeckeCharacterGroup(N);
triv := X!1;
eta := Random(X);
psi := Random(X);

// E := EisensteinSeries(M, triv, triv, k);
E2 := 120*EisensteinSeries(M, eta, psi, [2,2]);
E4 := 240*EisensteinSeries(M, eta, psi, [4,4]);

assert E2*E2 eq E4;
