load "config.m";

F<nu> := QuadraticField(5);
ZF := Integers(F);
N := ideal<ZF|[1]>;
prec := 100;
M := HMFSpace(F, N, prec);
X := HeckeCharacterGroup(N);
triv := X!1;
eta := Random(X);
psi := Random(X);

E2 := EisensteinSeries(M, eta, psi, [2,2]);
E4 := EisensteinSeries(M, eta, psi, [4,4]);

assert E2*E2 eq E4;

E8 := EisensteinSeries(M, eta, psi, [8,8]);
// E8 := (1/Coefficients(E8)[1])*E8;

time cusp_forms8 := CuspFormBasis(M, [8,8]);

g := E8-(E4*E4);
g_normalized := (1/Coefficients(g)[2])*g;
assert g_normalized eq cusp_forms8[1];

E6 := EisensteinSeries(M, eta, psi, [6,6]);
// E6 := (1/Coefficients(E6)[1])*E6;
time cusp_forms6 := CuspFormBasis(M,[6,6]);

f := E6-(E2*E4);
f_normalized := (1/Coefficients(f)[2])*f;
assert f_normalized eq cusp_forms6[1];

// TODO Hirzebruch
