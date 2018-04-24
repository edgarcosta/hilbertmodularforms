load "config.m";

prec := 200;

F := QuadraticField(5);
ZF<w> := Integers(F);
N := Factorization(ideal<ZF| {31}>)[1][1];
M := HMFSpace(F, N, prec);
B2 := CuspFormBasis(M, [2,2]);
f := B2[1];
B4 := CuspFormBasis(M, [4,4]);
f2 := f*f;
L := [f2] cat B4;
linear_relation := Matrix(LinearDependence(L));
assert linear_relation eq Matrix([[383928, 0, 110028,  -7271,  -1117]]);

//the other prime over 31
N := Factorization(ideal<ZF| {31}>)[2][1];
M := HMFSpace(F, N, prec);
B2 := CuspFormBasis(M, [2,2]);
f := B2[1];
B4 := CuspFormBasis(M, [4,4]);
f2 := f*f;
L := [f2] cat B4;
linear_relation := Matrix(LinearDependence(L));
assert linear_relation eq Matrix([[383928, 0, 110028,  -7271,  -1117]]);

// the prime 7
N := Factorization(ideal<ZF| {7}>)[1][1];
M := HMFSpace(F, N, prec);
B2 := CuspFormBasis(M, [2,2]);
f := B2[1];
B4 := CuspFormBasis(M, [4,4]);
f2 := f*f;
L := [f2] cat B4;
linear_relation := Matrix(LinearDependence(L));
assert linear_relation eq Matrix([[ 42663882912, 0, 0, 0, -700670208, 7592051824, -818977424, -53676527, 5398145 ]]);

// prime over 61
N := Factorization(ideal<ZF| {61}>)[1][1];
M := HMFSpace(F, N, prec);
B2 := CuspFormBasis(M, [2,2]);
assert #B2 eq 2;
f2 := B2[1]*B2[2];
B4 := CuspFormBasis(M, [4,4]);
L := [f2] cat B4;
linear_relation := Matrix(LinearDependence(L));
assert linear_relation eq Matrix([[ 877662264369325680, 0, 0, 0, 519050077358728320, -472319620197220136, 11118590450791488, 8474915051240108, -35130721934473, -29202404404537 ]]);





//ThetaSeries
F := QuadraticField(5);
ZF<w> := Integers(F);
GM := Matrix(ZF, [[1,1],[1,2]]);
N := ideal<ZF| 4* Determinant(GM)>;
prec := 10;
M := HMFSpace(F, N, prec);
theta := ThetaSeries(M, GM);
assert Coefficients(theta) eq [1,4,4,8,8];

GM := Matrix(F, [[1,-1/2],[-1/2,1]]);
N := ideal<ZF| 4* Determinant(GM)>;
prec := 10;
M := HMFSpace(F, N, prec);
theta := ThetaSeries(M, GM);
assert Coefficients(theta) eq [1,6,12,0,6];

//Multiplication + ThetaSeries
D := 13;
F := QuadraticField(D);
ZF<w> := Integers(F);
N := 4*ZF;
k := [2, 2];
prec := 100;
M := HMFSpace(F, N, prec);
M1 := Matrix(ZF,[[1,0],[0,1]]);
M2 := Matrix(ZF,[[1,0,0,0],[0,1,0,0],[0,0,1,0],[0,0,0,1]]);
f := ThetaSeries(M, M1);
g := ThetaSeries(M, M2);
assert f*f eq g;


