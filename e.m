load "config.m";

F := QuadraticField(5);
ZF := Integers(F);
N := (2^3*3^2)*ZF;
prec := 100;
M := HMFSpace(F, N, prec);

k := [4,4];

X := HeckeCharacterGroup(N);

triv := X!1;
eta := Random(X);
psi := Random(X);

E := EisensteinSeries(M, eta, psi, k);
