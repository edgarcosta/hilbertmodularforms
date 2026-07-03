// Slow driver for the cyclic cubic threefold model (see
// examples/cyclic_cubic_threefold.m): regenerates the unconditional
// relation-freeness certificates at precision 450 and the dimension bookkeeping
// through degree 40.  Runtime: roughly 5-10 minutes on a workstation (the
// trace precompute for the three split primes above 13 is disk-cached under
// Precomputations/ after the first run).
//
// What is certified and how:
//   - For each even degree k <= 24, the monomials of weighted degree k in the
//     seven generators E2, E4, E6, E8, E10, T(p13_1), T(p13_2) evaluate to
//     forms of FULL rank.  Full rank at any precision is exact (a true linear
//     relation would depress the rank at every precision), so the relation
//     ideal of the model is zero in degrees <= 24 unconditionally.
//   - The free monomial counts never exceed dim M_k (trace formula) through
//     degree 40 (equality up to weight 10, strictly below from weight 12 on),
//     so no pigeonhole effect can force relations anywhere in this range; the
//     first relations of the model lie in degree >= 28.
//   - The dependence of the third split-prime trace form is pinned exactly
//     (truncation is injective on M_10 since rank = dim = 9, conditional only
//     on the trace-formula value dim M_10 = 9; builtin quaternionic dimensions
//     confirm the trace formula at weights 4, 6, and 8, the last in a ~28
//     minute run not repeated here).
//
// History: earlier versions of the example displayed degree-16 "syzygies" of
// an 8-coordinate model using Hecke translates at the primes above 13.  Hecke
// translation divides precision by Norm(p) = 13 and every one of those
// equations was a truncation artifact; Tests/cyclic_cubic_threefold_regression.m
// pins the refutation witness.  The same phantom-kernel effect recurs at the
// truncation frontier of every precision, well below the pigeonhole bound:
//   precision 300 (89 columns):  4 spurious relations in degree 22
//   precision 450 (137 columns): degree 22 clean, 9 spurious in degree 26
//   precision 700 (210 columns): degree 26 clean
// Rank-full results, by contrast, are precision-independent facts; the
// precision-700 section below re-certifies degrees 22 and 26 and reports the
// degree-28 frontier without asserting it.

R<x> := PolynomialRing(Rationals());
F := NumberField(x^3 - x^2 - 2*x + 1);
ZF := Integers(F);

assert NarrowClassNumber(F) eq 1;

prec := 450;
t_start := Cputime();
M := GradedRingOfHMFs(F, prec);

// Trace-formula dimensions and free monomial counts through degree 40.
P<t> := PowerSeriesRing(Integers(), 42);
gf := 1/((1-t^2)*(1-t^4)*(1-t^6)*(1-t^8)*(1-t^10)^3);
expected_dims := AssociativeArray();
pinned := [<2,1>, <4,2>, <6,3>, <8,5>, <10,9>, <12,17>, <14,27>, <16,41>,
           <18,60>, <20,83>, <22,111>, <24,146>, <26,186>, <28,236>, <30,291>,
           <32,356>, <34,429>, <36,512>, <38,603>, <40,707>];
for pair in pinned do
  k, d := Explode(pair);
  Mk := HMFSpace(M, [k, k, k]);
  assert Dimension(Mk) eq d;
  free := Coefficient(gf, k);
  assert free lt d or k le 16;
  printf "deg %2o: free=%4o dim=%4o\n", k, free, d;
end for;

E := AssociativeArray();
for k in [2, 4, 6, 8, 10] do
  Ek := EisensteinBasis(HMFSpace(M, [k, k, k]));
  assert #Ek eq 1;
  E[k] := Ek[1];
end for;

ps13 := [fac[1] : fac in Factorization(13*ZF)];
assert #ps13 eq 3;
t0 := Cputime();
PrecomputeTraceForms(M, ps13);
printf "trace precompute (3 ideals, prec %o): %o s\n", prec, Cputime()-t0;
M10 := HMFSpace(M, [10, 10, 10]);
T := [TraceForm(M10, pp) : pp in ps13];
assert &and[Precision(f) eq prec : f in T];

products10 := [E[2]^5, E[2]^3*E[4], E[2]^2*E[6], E[2]*E[4]^2, E[2]*E[8],
               E[4]*E[6], E[10]];
assert #LinearDependence(products10 cat T[1..2]) eq 0;

// Exact dependence of the third trace form (Galois-symmetric normalization).
e1 := T[1] + T[2] + T[3];
dep := LinearDependence([e1] cat products10);
assert #dep eq 1;
v := dep[1];
assert v[1] ne 0;
w := v[1] lt 0 select [-a : a in Eltseq(v)] else Eltseq(v);
assert w eq [685308991651200, -77043333364867880775, 1579817724442250301030,
             -4300751463006555390880, -4792030832740917362883,
             9099773869074851707780, 8505396441101601977996,
             -10015162405506363352268];

// The invariant e2 = T1 T2 + T1 T3 + T2 T3 is NOT an Eisenstein polynomial:
// the invariant subring needs a new weight-20 generator.
Egens := [* E[2], E[4], E[6], E[8], E[10] *];
RE := ConstructWeightedPolynomialRing(Egens);
emons20 := [m : m in MonomialsOfWeightedDegree(RE, 20)];
assert #emons20 eq 30;
ev20 := EvaluateMonomials(Egens, emons20);
e2 := T[1]*T[2] + T[1]*T[3] + T[2]*T[3];
assert #LinearDependence([e2] cat ev20) eq 0;

// Jacobian threefold certificate (sound version) and the dependent quadruple
// that earlier versions mistakenly certified.
assert AlgebraicallyIndependent([E[2]^4, E[2]^2*E[4], E[2]*E[6], E[8]]);
assert not AlgebraicallyIndependent([E[2]^4, E[2]^2*E[4], E[2]*E[6], E[4]^2]);

// Unconditional relation-freeness through degree 24.
gens := [* E[2], E[4], E[6], E[8], E[10], T[1], T[2] *];
Rpoly := ConstructWeightedPolynomialRing(gens);
for k in [2..24 by 2] do
  mons := [m : m in MonomialsOfWeightedDegree(Rpoly, k)];
  assert #mons eq Coefficient(gf, k);
  t0 := Cputime();
  ev := EvaluateMonomials(gens, mons);
  null := #LinearDependence(ev);
  printf "deg %2o: %3o monomials, nullity %o (%o s)\n", k, #mons, null, Cputime()-t0;
  assert null eq 0;
end for;

// Public-API form of the same statement: the syzygy ideal is zero in every
// degree through 24.
syz := Syzygies(gens, [2..24 by 2]);
assert #Basis(syz) eq 0;

// Precision-700 section: re-certify the phantom degrees and extend to 26.
// The 9 degree-26 vectors seen at precision 450 must disappear here; the
// degree-28 nullity is reported but NOT asserted (its 131 monomials sit close
// enough to the 210-column budget that phantoms are plausible either way).
prec2 := 700;
t0 := Cputime();
M2 := GradedRingOfHMFs(F, prec2);
E2a := AssociativeArray();
for k in [2, 4, 6, 8, 10] do
  E2a[k] := EisensteinBasis(HMFSpace(M2, [k, k, k]))[1];
end for;
PrecomputeTraceForms(M2, ps13[1..2]);
M10b := HMFSpace(M2, [10, 10, 10]);
Tb := [TraceForm(M10b, pp) : pp in ps13[1..2]];
assert &and[Precision(f) eq prec2 : f in Tb];
gens2 := [* E2a[2], E2a[4], E2a[6], E2a[8], E2a[10], Tb[1], Tb[2] *];
Rpoly2 := ConstructWeightedPolynomialRing(gens2);
printf "precision-700 setup: %o s\n", Cputime()-t0;
for k in [22, 26] do
  mons := [m : m in MonomialsOfWeightedDegree(Rpoly2, k)];
  t0 := Cputime();
  ev := EvaluateMonomials(gens2, mons);
  null := #LinearDependence(ev);
  printf "prec 700, deg %2o: %3o monomials, nullity %o (%o s)\n",
      k, #mons, null, Cputime()-t0;
  assert null eq 0;
end for;
mons28 := [m : m in MonomialsOfWeightedDegree(Rpoly2, 28)];
t0 := Cputime();
ev28 := EvaluateMonomials(gens2, mons28);
null28 := #LinearDependence(ev28);
printf "prec 700, deg 28 (frontier, unasserted): %o monomials, nullity %o (%o s)\n",
    #mons28, null28, Cputime()-t0;

printf "total: %o s\n", Cputime()-t_start;
