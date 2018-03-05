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

E6 := 2520*EisensteinSeries(M, eta, psi, [6,6]);
E8 := EisensteinSeries(M, eta, psi, [8,8]);
E8 := (1/Coefficients(E8)[1])*E8;

cusp_forms8 := CuspFormBasis(M, [8,8]);

g := E8-(E4*E4);
g_test := (1/Coefficients(g)[2])*g;
assert g_test eq cusp_forms8[1];
