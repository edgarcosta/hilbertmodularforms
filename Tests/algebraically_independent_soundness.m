// Soundness of the AlgebraicallyIndependent Jacobian certificate.
//
// The quadruple [E2^4, E2^2*E4, E4^2, E8] over F = Q(zeta_7)^+ is provably
// algebraically dependent: (E2^2*E4)^2 = E2^4 * E4^2 identically, so the
// Jacobian determinant of the ratios vanishes as a power series and any
// nonzero reading can only come from coefficients outside the reliable
// truncation region.  Before the lower-set pruning fix, this call returned
// true at every precision (the determinant was tested as a raw polynomial,
// whose coefficients beyond the lower set carry garbage cross terms).
//
// The quadruple [E2^4, E2^2*E4, E2*E6, E8] has ratios E4/E2^2, E6/E2^3,
// E8/E2^4, so it is algebraically independent (E2, E4, E6, E8 generate a
// polynomial ring through weight 8), and the certificate must still succeed
// once the reliable region is large enough.

R<x> := PolynomialRing(Rationals());
F := NumberField(x^3 - x^2 - 2*x + 1);

for prec in [100, 200] do
  M := GradedRingOfHMFs(F, prec);
  E := AssociativeArray();
  for k in [2, 4, 6, 8] do
    Ek := EisensteinBasis(HMFSpace(M, [k, k, k]));
    assert #Ek eq 1;
    E[k] := Ek[1];
  end for;

  dependent := [E[2]^4, E[2]^2*E[4], E[4]^2, E[8]];
  assert not AlgebraicallyIndependent(dependent);

  dependent2 := [E[2]^4, E[2]^2*E[4], E[2]*E[6], E[4]^2];
  assert not AlgebraicallyIndependent(dependent2);
end for;

// Certification of a true independence needs enough reliable coefficients;
// precision 200 suffices for this quadruple (100 does not, and the intrinsic
// must then return false rather than guess).
M := GradedRingOfHMFs(F, 200);
E := AssociativeArray();
for k in [2, 4, 6, 8] do
  E[k] := EisensteinBasis(HMFSpace(M, [k, k, k]))[1];
end for;
independent := [E[2]^4, E[2]^2*E[4], E[2]*E[6], E[8]];
assert AlgebraicallyIndependent(independent);
