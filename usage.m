/*****
examples using ModFrmHilD, ModFrmHilDElt
*****/

SetDebugOnError(true);
// load configuration, spec file, printing, etc.
load "config.m";

// basic inputs to creation functions
F := QuadraticField(8);
ZF<w> := Integers(F);
N := ideal<ZF | { 3}>;
k := [2, 2];
K := Rationals();
prec := 200;

// ModFrmHilD creation and access to attributes
M := HMFSpace(F, N, prec);
BaseField(M); // F
Level(M); // N
Precision(M); // prec
//Ideals(M); // ideals of ZF (including 0) up to norm max_prec
// Dictionary(M); // internal

// ModFrmHilDElt can be made by providing space and coefficients
// WARNING: no checking is done to verify result is a modular form
num_ideals := #Ideals(M);
random_coeffs_f := [];
random_coeffs_g := [];
for i := 1 to num_ideals do
  Append(~random_coeffs_f, Random(1,100000));
  Append(~random_coeffs_g, Random(1,100000));
end for;
f := HMF(M, k, random_coeffs_f);
g := HMF(M, k, random_coeffs_g);

// addition and scalar multiplication
h := 12351426*(f+g);

// http://www.lmfdb.org/L/EllipticCurve/2.2.8.1/9.1/a/
MF := HilbertCuspForms(F, N);
S := NewSubspace(MF);
newspaces := NewformDecomposition(S);
newforms := [Eigenform(U) : U in newspaces];
eigenvalues := AssociativeArray();
primes := PrimesUpTo(prec, F);
print primes;
for pp in primes do
    eigenvalues[pp] := HeckeEigenvalue(newforms[1],pp);
end for;

ef := EigenformToHMF(M, k, eigenvalues);
print ef;
// Compare with http://www.lmfdb.org/L/EllipticCurve/2.2.8.1/9.1/a/
// a_n = \sum a_nn where Norm(nn) = n

// basic inputs to creation functions
F := QuadraticField(5);
ZF<w> := Integers(F);
N := ideal<ZF | {11}>;
k := [2, 2];
prec := 100;
M := HMFSpace(F, N, prec);
orbit_representatives := NewformsToHMF(M, k);
print "Do we have two Galois orbits?", #orbit_representatives eq 2;
print "One of dimension 1 and another of dimension 2";
orbits := [GaloisOrbit(elt) : elt in orbit_representatives];
printf "Orbits dimensions = %o\n", [#o : o in orbits];
if #orbits[1] eq 2 then
  k := 1;
else
  k := 2;
  assert #orbits[2] eq 2;
end if;
print "If we add the two elements in the two dimensional orbit, we obtain something integral";
f1 := orbits[k][1];
f2 := orbits[k][2];
f3 := f1 + f2;
f3;
print "And we may coerce its coefficients";
f3ZZ := Integers() ! f3;
f3ZZ;

HMFEquipWithMultiplication(M);
f12 := f1*f2;
//Sanity check
squarediff1 := (f1 - f2) * (f1 + f2);
squarediff2 := f1*f1 - f2*f2;
assert squarediff1 eq  squarediff2;
squaresum := f3*f3;
assert squaresum eq f1*f1 + 2*f1*f2 + f2*f2;

imwillingtowait8min := false;
if imwillingtowait8min then
  prec := 1000;
else
  prec := 100;
end if;
F := QuadraticField(5);
ZF<w> := Integers(F);
N := Factorization(ideal<ZF| {31}>)[1][1];
k := [2, 2];
M := HMFSpace(F, N, prec);
B2 := CuspFormBasis(M, [2,2]);
f := B2[1];
B4 := CuspFormBasis(M, [4,4]);
f2 := f*f;
L := [f2] cat B4;
linear_relation := Matrix(LinearDepedence(L));
print linear_relation eq Matrix([[383928, 0, 110028,  -7271,  -1117]]);



//ThetaSeries
if false then
  F := QuadraticField(5);
  ZF<w> := Integers(F);
  GM := DiagonalMatrix(ZF, [2,2,2,2]);
  N := ideal<ZF| Determinant(GM)>;
  prec := 100;
  M := HMFSpace(F, N, prec);
  HMFEquipWithMultiplication(M);
  theta := ThetaSeries(M, GM);
end if;
