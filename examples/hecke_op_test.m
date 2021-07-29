// These are tests
load "config.m";

// Narrow class number 1
//Basis for level 1 weight [4,4] consists of an eigenstein series and an eigenform
D := 13;
F := QuadraticField(D);
ZF := Integers(F);
k := [4,4];
prec := 20;
M := GradedRingOfHMFs(F, prec);
M4 := HMFSpace(M, 1*ZF, k);
I:=AllIdeals(M);
B:=Basis(M4);
f:=B[1];
g:=B[2];
L:=LinearDependence([HeckeOperator(f, 2*ZF), 65*f]);
assert L eq [[1, -1]]; // f is an Eisenstein series and is indeed an eigenvalue
for x:=2 to 7 do
  Lx:=LinearDependence([HeckeOperator(g, I[x]), Coefficients(g)[1*ZF][I[x]]*g]);
  assert Lx eq [[1, -1]];
end for;




// Narrow class number > 1
D := 12;
F := QuadraticField(D);
ZF := Integers(F);
k := [4,4];
prec := 40;
M := GradedRingOfHMFs(F, prec);
N:=1*ZF;
M4 := HMFSpace(M, N, k);
X:=HeckeCharacterGroup(1*ZF);
triv:=X!1;
eta:=Random(X);
psi:=Random(X);
E4:=EisensteinSeries(M4, eta, psi);
nn:=Factorisation(11*ZF)[1][1];
f:=HeckeOperator(E4, nn);
L:=LinearDependence([f, E4]);
assert L eq [[ 1, -1332 ]]; // f is an Eisenstein series and is indeed an eigenvalue



// Tests for characters?
