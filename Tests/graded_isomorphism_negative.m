// Negative / no-false-positive tests for the graded-isomorphism tools
// (Verification/IsIsomorphic.m).  Because SearchGradedIsomorphism is SOUND (every map it
// returns is re-checked by VerifyGradedIsomorphism) a "false" here means the search space
// contained no isomorphism; combined with a Hilbert-series or weight-multiset obstruction
// these are genuine non-isomorphisms, so the finder must NOT claim success.
//
// The heavy exhaustive negative (the D=8 "+disc" sign flip) is CI-run from
// examples/graded_isomorphism_D8_disc_negative.m.  This file keeps the cheaper checks; the
// two non-cheap ones are on the small D=13 ring.  NEG(a2) is a full exhaustive search whose
// "false" verdict costs a whole sweep of the candidate diagonals (~15s).  NEG(a3) is a
// regression for a positive-dimensional pinned system that used to make the search throw
// inside Variety; it must now return false with no error, capped at the single (first)
// pinning that triggered the bug (~30s, dominated by that one system's setup and solve).
// Resources: ~45s CPU.
printf "Graded isomorphism negative / no-false-positive tests...\n";
t0 := Cputime(); walltime := Time();
Q := Rationals();

// ---- NEG(a1): two stored rings with DIFFERENT generator-weight multisets are not
//      graded-isomorphic; IsIsomorphic returns false at the (proportional) grading guard,
//      before any search.  D=8 has weights [2,4,6,14]; D=5 has weights [2,6,10,20]. ----
procedure test_neg_different_weights()
  I8 := LoadStoredCanonicalRing("2.2.8.1-1.1");
  I5 := LoadStoredCanonicalRing("2.2.5.1-1.1");
  S8 := Scheme(Proj(Generic(I8)), Basis(I8));
  S5 := Scheme(Proj(Generic(I5)), Basis(I5));
  assert not IsIsomorphic(S8, S5);
  assert not IsIsomorphic(S5, S8);
end procedure;

// ---- NEG(a2): same ambient ring [2,4,6,6,8], genuinely non-isomorphic quotients, exercising
//      SearchGradedIsomorphism returning false (not just a guard).  Against the real D=13
//      canonical ring we place an unrelated complete intersection of the SAME relation
//      degrees (12 and 16) and the SAME Hilbert series.  Sharing the relation-degree
//      structure keeps the finder's pinned membership system zero-dimensional (so it returns
//      a clean "false" rather than erroring); sharing the Hilbert series means there is no
//      cheap obstruction, so the finder must run its full search and still find no map. ----
procedure test_neg_unrelated_complete_intersection()
  I13 := LoadStoredCanonicalRing("2.2.13.1-1.1");
  R := Generic(I13);
  // weights: R.1=2, R.2=4, R.3=6, R.4=6, R.5=8.
  h12 := R.2^3 - 2*R.3*R.4 + 7*R.4^2 - R.1*R.2*R.4;               // weight 12
  h16 := R.5^2 - R.1^4*R.5 + R.2^4 - 5*R.1^2*R.3*R.4;             // weight 16
  Junrel := ideal< R | h12, h16 >;
  assert IsHomogeneous(Junrel);
  assert HilbertSeries(Junrel) eq HilbertSeries(I13);            // no cheap obstruction
  foundA, _, _ := SearchGradedIsomorphism(I13, Junrel);
  assert not foundA;
end procedure;

// ---- NEG(a3): REGRESSION -- the pinned membership system is POSITIVE-dimensional and the
//      search must still return false (not throw).  Against the real D=13 canonical ring
//      (a codimension-2 complete intersection) we place a single hypersurface J = <X4^3>.
//      With only one relation the pinned coefficient system does not cut the target's
//      automorphism scalings down to finitely many points: the very first (all-ones) pinning
//      leaves a 2-dimensional solution set, on which the pre-fix code called Variety and hit
//      "Argument 1 is not zero-dimensional".  SearchGradedIsomorphism must instead skip that
//      pinning and, finding no certified map, return its ordinary false -- with no error.  (A
//      single hypersurface is genuinely non-isomorphic to a codim-2 complete intersection, so
//      false is the correct verdict.)  MaxAttempts := 1 caps this at the one pinning that
//      triggered the bug: it exercises the exact throwing path without the multi-minute sweep
//      a "false" over the full candidate set would cost here (~30s as capped). ----
procedure test_neg_positive_dimensional_regression()
  I13 := LoadStoredCanonicalRing("2.2.13.1-1.1");
  R := Generic(I13);
  Jhyp := ideal< R | R.2^3 >;                                   // X4^3, a weight-12 hypersurface
  assert IsHomogeneous(Jhyp);
  foundHyp, _, _ := SearchGradedIsomorphism(I13, Jhyp : MaxAttempts := 1);   // must not throw
  assert not foundHyp;
end procedure;

// ---- NEG(b): VerifyGradedIsomorphism rejects deliberately wrong witnesses. ----
// Build a genuine graded-iso target J = phi0(I13) with an in-scope automorphism, then feed
// the certifier maps that are NOT isomorphisms I13 -> J.
procedure test_neg_wrong_witnesses()
  I13 := LoadStoredCanonicalRing("2.2.13.1-1.1");
  R := Generic(I13);
  h := hom< R -> R | [2*R.1, 4*R.2, -2*R.3, 8*R.4, 16*R.5] >;
  J := ideal< R | [h(f) : f in Basis(I13)] >;

  // (b1) the identity map does not send I13's relations into J (wrong scalings), so it is not
  //      even a ring map I13/I13 -> R/J; the containment check (1) fails.
  idmap := [R | R.1, R.2, R.3, R.4, R.5];
  assert not VerifyGradedIsomorphism(I13, J, idmap, idmap);

  // (b2) a map violating the grading: send the weight-2 variable to the weight-4 variable.
  //      Check (5) (weighted-homogeneity of each variable image) must reject it.
  gradviol := [R | R.2, R.2, R.3, R.4, R.5];
  assert not VerifyGradedIsomorphism(I13, I13, gradviol, gradviol);

  // (b3) a weight-homogeneous but NON-invertible endomorphism: collapse the two independent
  //      weight-6 variables to one (R.4 |-> R.3).  It passes the grading check (5) but is not
  //      an isomorphism; used as its own "inverse" it fails the mutual-inverse checks (3)/(4)
  //      because R.3 - R.4 is not in the D=13 ideal.
  collapse := [R | R.1, R.2, R.3, R.3, R.5];
  assert not VerifyGradedIsomorphism(I13, I13, collapse, collapse);

  // (b4) non-homogeneous ideals are rejected up front regardless of the map.
  Inh := ideal< R | R.1 + 1 >;
  assert not VerifyGradedIsomorphism(Inh, Inh, [R | R.1, R.2, R.3, R.4, R.5],
                                               [R | R.1, R.2, R.3, R.4, R.5]);
end procedure;

test_neg_different_weights();
test_neg_unrelated_complete_intersection();
test_neg_positive_dimensional_regression();
test_neg_wrong_witnesses();

printf "PASSED (CPU: %os, Wall: %os, Mem: %oMB)\n", Cputime(t0), Time(walltime), GetMemoryUsage() div (1024^2);
