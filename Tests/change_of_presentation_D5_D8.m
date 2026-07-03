// ChangeOfPresentation (ModFrmHilD/CanonicalRing/ChangeOfPresentation.m) on real
// canonical rings for Q(sqrt(5)) and Q(sqrt(8)), level 1.  Companion to
// Tests/ChangeOfPresentation.m (which covers Q(sqrt(13)) with an equal-weight block).
//
// At generator-weight bound 8 the fast generating sets are:
//   D=5:  weights [2, 6]      (no equal-weight generators)
//   D=8:  weights [2, 4, 6]   (no equal-weight generators)
// so we exercise the two change-of-presentation flavours that do NOT need an
// equal-weight block: (a) diagonal rescalings and (c) a genuinely polynomial change
// where the top-weight generator gains a product of lower-weight generators.  The
// same-weight linear-mixing flavour (b) needs equal-weight generators and is covered
// by Tests/ChangeOfPresentation.m on Q(sqrt(13)).
//
// Each case asserts EXACT recovery of a known change-of-basis (as polynomials in the
// old ring) and the intrinsic's own q-expansion verification.  Resources: ~5s CPU.
printf "ChangeOfPresentation on Q(sqrt(5)) and Q(sqrt(8)), level 1...";
t0 := Cputime(); walltime := Time();

QQ := Rationals();

// ---- CASE (a): diagonal rescaling (each generator scaled by a nonzero rational). ----
procedure test_diagonal_rescaling(OldGens, R, oldVarPos, flatten, gen_weights)
  scalvals := [3, -2, 5, 7, -4, 2, 9];  // deterministic, consumed in flattened order
  NewGensA := AssociativeArray();
  KnownA := AssociativeArray();
  cnt := 0;
  for wt in gen_weights do
    NewGensA[wt] := [];
    KnownA[wt] := [];
    for j in [1..#OldGens[wt]] do
      cnt +:= 1;
      s := scalvals[cnt];
      Append(~NewGensA[wt], s * OldGens[wt][j]);
      Append(~KnownA[wt], s * oldVarPos[<wt, j>]);
    end for;
  end for;

  PhiA, RoutA := ChangeOfPresentation(OldGens, NewGensA);
  assert Grading(RoutA) eq Grading(R) and Rank(RoutA) eq Rank(R);
  expA := [RoutA!p : p in flatten(KnownA)];
  assert #expA eq #PhiA;
  assert &and[PhiA[i] eq expA[i] : i in [1..#PhiA]];
  assert VerifyChangeOfPresentation(OldGens, NewGensA, PhiA);
end procedure;

// ---- CASE (c): polynomial change; the top-weight generator gains a product of ----
// ---- lower-weight generators (a weight-6 generator gains old_2^3, and old_2*old_4 ----
// ---- when a weight-4 generator is present).  All other generators are unchanged. ----
procedure test_polynomial_change(OldGens, R, oldVarPos, flatten, gen_weights)
  topwt := gen_weights[#gen_weights];
  NewGensC := AssociativeArray();
  KnownC := AssociativeArray();
  for wt in gen_weights do
    NewGensC[wt] := OldGens[wt];
    KnownC[wt] := [oldVarPos[<wt, j>] : j in [1..#OldGens[wt]]];
  end for;

  o2 := OldGens[2][1];
  v2 := oldVarPos[<2, 1>];
  poly_old := 2 * OldGens[topwt][1] + 5 * o2^3;
  poly_var := 2 * oldVarPos[<topwt, 1>] + 5 * v2^3;
  if IsDefined(OldGens, 4) then
    poly_old +:= o2 * OldGens[4][1];
    poly_var +:= v2 * oldVarPos[<4, 1>];
  end if;
  NewGensC[topwt] := [poly_old] cat OldGens[topwt][2..#OldGens[topwt]];
  KnownC[topwt] := [poly_var] cat [oldVarPos[<topwt, j>] : j in [2..#OldGens[topwt]]];

  PhiC, RoutC := ChangeOfPresentation(OldGens, NewGensC);
  expC := [RoutC!p : p in flatten(KnownC)];
  assert #expC eq #PhiC;
  assert &and[PhiC[i] eq expC[i] : i in [1..#PhiC]];
  assert VerifyChangeOfPresentation(OldGens, NewGensC, PhiC);
end procedure;

// Run the (a) diagonal and (c) polynomial checks for a single field D with the
// generating set produced at generator/relation bounds (maxg, maxr).
procedure RunField(D, maxg, maxr)
  F := QuadraticField(D);
  ZF := Integers(F);
  NN := 1*ZF;

  M := GradedRingOfHMFs(F, 100);
  dict := ConstructGeneratorsAndRelations(M, NN, maxg, maxr);
  OldGens := dict[1];

  gen_weights := Sort(SetToSequence(Keys(OldGens)));
  R := ConstructWeightedPolynomialRing(OldGens);

  // (weight, index) -> ring variable, in the intrinsic's FlattenGens order.
  oldVarPos := AssociativeArray();
  idx := 0;
  for wt in gen_weights do
    for j in [1..#OldGens[wt]] do
      idx +:= 1;
      oldVarPos[<wt, j>] := R.idx;
    end for;
  end for;
  flatten := func< A | &cat[[* y : y in A[k] *] : k in Sort(Setseq(Keys(A)))] >;

  test_diagonal_rescaling(OldGens, R, oldVarPos, flatten, gen_weights);
  test_polynomial_change(OldGens, R, oldVarPos, flatten, gen_weights);
end procedure;

RunField(8, 8, 16);   // generators [2, 4, 6]
RunField(5, 8, 16);   // generators [2, 6]

printf "PASSED (CPU: %os, Wall: %os, Mem: %oMB)\n", Cputime(t0), Time(walltime), GetMemoryUsage() div (1024^2);
