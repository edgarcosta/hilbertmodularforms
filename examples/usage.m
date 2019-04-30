/*****
examples using ModFrmHilD, ModFrmHilDElt
*****/

SetDebugOnError(true);
load "config.m";

// http://www.lmfdb.org/L/EllipticCurve/2.2.8.1/9.1/a/
F := QuadraticField(8);
ZF<w> := Integers(F);
N := ideal<ZF | {9, 3, 3}>;
k := [2, 2];
K := Rationals();
prec := 30;
M := GradedRingOfHMFs(F, prec);
M2 := HMFSpace(M, N, k);
// built in magma
MF := HilbertCuspForms(F, N);
S := NewSubspace(MF);
newspaces := NewformDecomposition(S);
newforms := [Eigenform(U) : U in newspaces];
// convert ModFrmHilElt -> ModFrmHilDElt
print newforms[1];
ef := NewformToHMF(M2, newforms[1]);
print ef;
// Compare with http://www.lmfdb.org/L/EllipticCurve/2.2.8.1/9.1/a/
// a_n = \sum a_nn where Norm(nn) = n

// basic inputs to creation functions
F := QuadraticField(5);
ZF<w> := Integers(F);
N := ideal<ZF | {11}>;
k := [2, 2];
prec := 30;
M := GradedRingOfHMFs(F, prec);
M2 := HMFSpace(M, N, k);
//About 15s
time orbit_representatives := NewformsToHMF(M2);
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
M := GradedRingOfHMFs(F, prec);
B2 := CuspFormBasis(M, N, [2,2]);
f := B2[1];
B4 := CuspFormBasis(M, N, [4,4]);
f2 := f*f;
L := [f2] cat B4;
linear_relation := Matrix(LinearDependence(L));
assert linear_relation eq Matrix([[383928, 0, 110028,  -7271,  -1117]]);


//ThetaSeries
F := QuadraticField(5);
ZF<w> := Integers(F);
GM := Matrix(ZF, [[1,1],[1,2]]);
prec := 10;
M := GradedRingOfHMFs(F, prec);
theta := ThetaSeries(M, GM);
assert Coefficients(theta) eq [1,4,4,8,8];

GM := Matrix(F, [[1,-1/2],[-1/2,1]]);
prec := 10;
M := GradedRingOfHMFs(F, prec);
theta := ThetaSeries(M, GM);
assert Coefficients(theta) eq [1,6,12,0,6];
