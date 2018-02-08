/*****
examples using ModFrmHilD, ModFrmHilDElt
*****/

// load configuration, spec file, printing, etc.
load "config.m";

// basic inputs to creation functions
F := QuadraticField(8);
ZF<w> := Integers(F);
N := ideal<ZF | { 3}>;
k := [2, 2];
K := Rationals();
prec := 100;

// creation
M := HMFSpace(F, N, k, K);
f := HMFZero(F, N, k, K, prec);
g := HMFZero(F, N, k, K, 200);

// arithmetic (currently only scalar multiplication and addition are implemented)

// http://www.lmfdb.org/L/EllipticCurve/2.2.8.1/9.1/a/
MF := HilbertCuspForms(F, N);
S := NewSubspace(MF);
newspaces := NewformDecomposition(S);
newforms := [Eigenform(U) : U in newspaces];
eigenvalues := AssociativeArray();
primes := PrimesUpTo(prec, F);
for pp in primes do
    eigenvalues[pp] := HeckeEigenvalue(newforms[1],pp);
end for;

ef := EigenformToHMF(M, k, eigenvalues, prec);
print ef;
// Compare with http://www.lmfdb.org/L/EllipticCurve/2.2.8.1/9.1/a/
// a_n = \sum a_nn where Norm(nn) = n



// http://www.lmfdb.org/L/EllipticCurve/2.2.5.1/31.1/a/
F := QuadraticField(5);
ZF<w> := Integers(F);
N := ideal<ZF | {31, -5*a + 2}>;
k := [2, 2];
K := Rationals();
M := HMFSpace(F, N, k, K);
prec := 100;
MF := HilbertCuspForms(F, N);
S := NewSubspace(MF);

newspaces  := NewformDecomposition(S);
newforms := [Eigenform(U) : U in newspaces];
eigenvalues := AssociativeArray();
primes := PrimesUpTo(prec, F);
for pp in primes do
    eigenvalues[pp] := HeckeEigenvalue(newforms[1],pp);
end for;

ef2 := EigenformToHMF(M, k, eigenvalues, prec);
print ef2;
