load "config.m";

F<nu> := QuadraticField(5);
ZF := Integers(F);
N := ideal<ZF|[1]>;
prec := 50;
M := HMFSpace(F, N, prec);
X := HeckeCharacterGroup(N);
triv := X!1;
eta := triv;
psi := triv;

E2 := EisensteinSeries(M, eta, psi, [2,2]);
E6 := EisensteinSeries(M, eta, psi, [4,4]);
E10 := EisensteinSeries(M, eta, psi, [10,10])

B2 := Basis(M, [2,2]);
B4 := Basis(M, [4,4]);
B6 := Basis(M, [6,6]);
B8 := Basis(M, [8,8]);
B10 := Basis(M, [10,10]);

E2 := B2[1];
E4 := B4[1];

// E2 generate everything at weight 4

assert E2^2 eq E4;


// E2, E6 generate everything at weight 6
assert #B6 eq 2;
E6 := B6[1];
cusp_forms6 := B6[2];

f := E6 - E2^3;
f_normalized := (1/Coefficients(f)[2])*f;
assert f_normalized eq cusp_forms6;


// E2, E6 generate everything at weight 8
assert #B8 eq 2;
E8 := B8[1];

assert 536 * E2 * E6 -  175 * E2^4  eq  361 * E8;

cusp_forms8 := B8[2];

g := E8- E2^4;
g_normalized := (1/Coefficients(g)[2])*g;
assert g_normalized eq cusp_forms8;

// E2, E6, E10 generate everything at weight 8
assert #B10 eq 3;
E10 := B10[1];

mon := MonomialsOfWeightedDegree([[2,6,10]],[10]);
Es := [E2, E6, E10];
Epowers := [ &*[Es[i]^(Integers() ! m[i]) : i in [1..#Es]] : m in mon];

//E10 is linear independent from the rest
assert Rank(CoefficientsMatrix(Epowers)) eq #Epowers;
//the cusp forms can be written with E2, E6 and E10
assert Rank(CoefficientsMatrix(Epowers cat B10)) eq #Epowers;
