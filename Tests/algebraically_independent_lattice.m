// The second D=76 component has exponent lattice of index 13.
// Its weight-2 Eisenstein series and two trace forms are independent, but
// lattice holes must not discard their exact nonzero Jacobian coefficient.
// Resources: about 1 s.
SetNthreads(1);
F := QuadraticField(19);
M := GradedRingOfHMFs(F, 20);
bb := NarrowClassGroupReps(M)[2];
assert LMFDBLabel(bb) eq "2.1";
L := NarrowClassGroupRepsToIdealDual(M)[bb];
exponents := Matrix(Rationals(), [Eltseq(F!nu) : nu in Basis(L)]) * NuToExpMatrices(M)[bb];
assert Abs(Determinant(exponents)) eq 13;
hole := F!Eltseq(Vector(Rationals(), [1,1]) * ExpToNuMatrices(M)[bb]);
assert IsTotallyPositive(hole) and hole notin L;

Mk := HMFSpace(M, [2,2]);
fs := EisensteinBasis(Mk);
for mm in [1*Integers(F), 2*Integers(F)] do
  PrecomputeTraceForms(M, [mm]);
  Append(~fs, TraceForm(Mk, mm));
end for;
forms := [];
for f in fs do
  cs := Components(f);
  for cc in Keys(cs) do
    if cc ne bb then cs[cc] := 0*cs[cc]; end if;
  end for;
  Append(~forms, HMFSumComponents(Mk, cs));
end for;
forms := Basis(forms);
assert #forms eq 3;
g := AssociativeArray(); g[2] := forms;
r := AssociativeArray();
assert CertifyAlgIndependent(g, r, 3 : IdealClassesSupport := [bb], MaxAttempts := 1);
assert AlgebraicallyIndependent(forms : IdealClassesSupport := [bb]);

// The middle form squared equals the product of the other two.
dependent := [forms[1]^2, forms[1]*forms[2], forms[2]^2];
assert not AlgebraicallyIndependent(dependent : IdealClassesSupport := [bb]);
g[4] := dependent; Remove(~g, 2);
assert not CertifyAlgIndependent(g, r, 3 : IdealClassesSupport := [bb], MaxAttempts := 1);
