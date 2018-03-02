load "config.m";

F := QuadraticField(23);
ZF := Integers(F);
// N := 1*ZF;
N := 3^2*ZF;
prec := 100;
M := HMFSpace(F, N, prec);

k := [4,4];

// X := DirichletGroup(N);
X := HeckeCharacterGroup(N);

triv := X!1;
eta := Random(X);
psi := Random(X);
