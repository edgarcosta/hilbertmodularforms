load "config.m";

F := QuadraticField(5);
prec := 100;
ZF<w> := Integers(F);
N := Factorization(ideal<ZF| {31}>)[1][1];
M := HMFSpace(F, N, prec);
B2 := CuspFormBasis(M, [2,2]);
f := B2[1];
B4 := CuspFormBasis(M, [4,4]);
f2 := f*f;
L := [f2] cat B4;
linear_relation := Matrix(LinearDepedence(L));
assert linear_relation eq Matrix([[383928, 0, 110028,  -7271,  -1117]]);


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
