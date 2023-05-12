// These are tests
load "config.m";

prec := 20;

F := QuadraticField(5);
ZF<w> := Integers(F);
//primes over 31
for i in [1, 2] do
  N := Factorization(ideal<ZF| {31}>)[i][1];
  M := GradedRingOfHMFs(F, prec);
  M2 := HMFSpace(M, N, [2, 2]);
  B2 := CuspFormBasis(M2);
  f := B2[1];
  M4 := HMFSpace(M, N, [4, 4]);
  B4 := CuspFormBasis(M4);
  f2 := f*f;
  L := [f2] cat B4;
  linear_relation := Matrix(LinearDependence(L));
  assert linear_relation eq Matrix(Rationals(), [[383928, 0, 110028,  -7271,  -1117]])/383928;
end for;


// the prime 7
N := Factorization(ideal<ZF| {7}>)[1][1];
M := GradedRingOfHMFs(F, prec);
M2 := HMFSpace(M, N, [2, 2]);
B2 := CuspFormBasis(M2);
f := B2[1];
M4 := HMFSpace(M, N, [4, 4]);
B4 := CuspFormBasis(M4);
f2 := f*f;
L := [f2] cat B4;
linear_relation := Matrix(LinearDependence(L));
assert linear_relation eq Matrix(Rationals(), [[ 42663882912, 0, 0, 0, -700670208, 7592051824, -818977424, -53676527, 5398145 ]])/42663882912;

// prime over 61
F := QuadraticField(5);
ZF<w> := Integers(F);
N := Factorization(ideal<ZF| {61}>)[1][1];
M := GradedRingOfHMFs(F, prec);
M2 := HMFSpace(M, N, [2, 2]);
B2 := CuspFormBasis(M2);
M4 := HMFSpace(M, N, [4, 4]);
B4 := CuspFormBasis(M4);
L := [B2[1]*B2[2]] cat B4;
linear_relation := Matrix(LinearDependence(L));
assert linear_relation eq Matrix(Rationals(), [[ 877662264369325680, 0, 0, 0, 519050077358728320, -472319620197220136, 11118590450791488, 8474915051240108, -35130721934473, -29202404404537 ]])/877662264369325680;




/* "Coefficients(theta) eq" doesnt make sense at the moment
//ThetaSeries
F := QuadraticField(5);
ZF<w> := Integers(F);
GM := Matrix(ZF, [[1,1],[1,2]]);
N := ideal<ZF| 4* Determinant(GM)>;
prec := 10;
M := HMFSpace(F, prec);
theta := ThetaSeries(M, GM);
assert Coefficients(theta) eq [1,4,4,8,8];

GM := Matrix(F, [[1,-1/2],[-1/2,1]]);
theta := ThetaSeries(M, GM);
assert Coefficients(theta) eq [1,6,12,0,6];
*/

//Multiplication + ThetaSeries
D := 13;
F := QuadraticField(D);
ZF<w> := Integers(F);
k := [2, 2];
prec := 20;
M := GradedRingOfHMFs(F, prec);
M1 := Matrix(ZF,[[1,0],[0,1]]);
M2 := Matrix(ZF,[[1,0,0,0],[0,1,0,0],[0,0,1,0],[0,0,0,1]]);
f := ThetaSeries(M, M1);
g := ThetaSeries(M, M2);
assert f*f eq g;

/*
Broken because Basis
//Hecke Operator
//Basis for level 1 weight [4,4] consists of an eigenstein series and an eigenform
D := 13;
F := QuadraticField(D);
ZF := Integers(F);
k := [4,4];
prec := 20;
M := GradedRingOfHMFs(F, prec);
M4 := HMFSpace(M, 1*ZF, k);
I:=Ideals(M);
B:=Basis(M4);
f:=B[1];
g:=B[2];
assert HeckeOperator(f, 2*ZF : Basis:=B) eq 65*f; // f is an Eisenstein series and is indeed an eigenvalue
for x:=2 to 7 do
	assert HeckeOperator(g, I[x] : Basis:=B) eq Coefficients(g)[x]*g; //g is an eigenform
end for;
*/
