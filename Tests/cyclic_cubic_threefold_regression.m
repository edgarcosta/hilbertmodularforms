// Regression guard for the cyclic cubic threefold example (F = Q(zeta_7)^+).
//
// The pre-repair example asserted that the three degree-16 products
//   (E_2^3 - 10428/3035 E_2 E_4 + 7393/3035 E_6) * (T_i - T_j)
// vanish as syzygies of the threefold map, where T_1, T_2, T_3 are the Hecke
// translates of E_2^5 at the primes above 13.  Those "equations" were artifacts
// of Hecke-translate precision truncation (base 1000 gives translate precision
// 1000 div 13 = 76, and every coefficient of the products up to norm 76
// vanishes).  Each product is a product of nonzero forms in an integral domain,
// hence nonzero: the first discrepancy sits at norm 83, just beyond the old
// truncation window.  Base precision 2000 gives translate precision 153, enough
// to expose it.
//
// This test pins that refutation so the false equations cannot silently return:
// at nu0 with Norm(nu0 * different) = 83, the three products have coefficients
// (v, v, 0) up to relabeling of the split primes, with v as below, and the
// product vanishing at nu0 is nonzero at a Galois conjugate of the same norm.

R<x> := PolynomialRing(Rationals());
F := NumberField(x^3 - x^2 - 2*x + 1);
ZF := Integers(F);

M := GradedRingOfHMFs(F, 2000);
E := AssociativeArray();
for k in [2, 4, 6] do
  Ek := EisensteinBasis(HMFSpace(M, [k, k, k]));
  assert #Ek eq 1;
  E[k] := Ek[1];
end for;

E2p5 := ((E[2]^2)^2) * E[2];
ps13 := [fac[1] : fac in Factorization(13*ZF)];
assert #ps13 eq 3;
T := [HeckeOperator(E2p5, pp) : pp in ps13];
assert Precision(T[1]) ge 83;

w6f := E[2]^3 - 10428/3035*E[2]*E[4] + 7393/3035*E[6];
assert not IsZero(w6f);

// h+ = 1: a single narrow class group component.
bb := NarrowClassGroupReps(M)[1];
assert #NarrowClassGroupReps(M) eq 1;

nu0 := (3*F.1^2 + F.1 + 4)/7;
assert Norm(nu0*Different(ZF)) eq 83;

v := 155467758903094149120/607;
witness := [];
for pair in [<1, 2>, <1, 3>, <2, 3>] do
  diff_form := T[pair[1]] - T[pair[2]];
  assert not IsZero(diff_form);
  prod := w6f * diff_form;
  // The old example asserted these products were zero (memberships in its
  // syzygy ideal); they are nonzero.
  assert not IsZero(prod);
  Append(~witness, Abs(Rationals()!Coefficient(prod, bb, nu0)));
end for;
assert Sort(witness) eq [0, v, v];
