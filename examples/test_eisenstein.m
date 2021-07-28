load "config.m";

F := QuadraticField(5);
prec := 20;
M := GradedRingOfHMFs(F,20);
N := 1*Integers(M);
X := HeckeCharacterGroup(N);
triv := X!1;
eta := Random(X);
psi := Random(X);

M2 := HMFSpace(M, [2,2]);
M4 := HMFSpace(M, [4,4]);
M6 := HMFSpace(M, [6,6]);
M8 := HMFSpace(M, [8,8]);

E2 := EisensteinSeries(M2, eta, psi);
E4 := EisensteinSeries(M4, eta, psi);

assert E2*E2 eq E4;

E8 := EisensteinSeries(M8, eta, psi);

time cusp_forms8 := CuspFormBasis(M8);

g := E8-(E4*E4);
g_normalized := (1/Coefficients(g)[N][N])*g;
assert g_normalized eq cusp_forms8[1];

E6 := EisensteinSeries(M6, eta, psi);
time cusp_forms6 := CuspFormBasis(M6);

f := E6-(E2*E4);
f_normalized := (1/Coefficients(f)[N][N])*f;
assert f_normalized eq cusp_forms6[1];
