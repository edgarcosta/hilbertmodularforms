/*****
examples using ModFrmHilD, ModFrmHilDElt
*****/

// load configuration, spec file, printing, etc.
load "config.m";

// basic inputs to creation functions
F := QuadraticField(8);
ZF<w> := Integers(F);
N := ideal<ZF | {9, 3, 3}>;
k := [2, 2];
K := Rationals();
prec := 100;

// creation
M := HMFSpace(F, N, k, K);
f := HMFZero(F, N, k, K, prec);
g := HMFZero(F, N, k, K, 200);

// arithmetic (currently only scalar multiplication and addition are implemented)


M2 := HilbertCuspForms(F, N);
S := NewSubspace(M2);
prec := 100;
newspaces := NewformDecomposition(S);
newforms := [Eigenform(U) : U in newspaces];
eigenvalues := AssociativeArray();
primes := PrimesUpTo(prec, F);
for pp in primes do
    eigenvalues[pp] := HeckeEigenvalue(newforms[1],pp);
end for;

ef := EigenformToHMF(M, eigenvalues, prec);
print ef;
