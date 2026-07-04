// ChangeOfPresentation on a real canonical ring: Q(sqrt(13)), level 1.
// Generators have weights [2,4,6,6,8] (two weight-6 -> same-weight mixing).
// We define a SECOND presentation by a KNOWN graded change of basis on the
// generators and assert ChangeOfPresentation recovers it, verifies it on
// q-expansions, and (ideal level) that VerifyGradedIsomorphism certifies it.
// Resources: ~10s CPU.
printf "ChangeOfPresentation on Q(sqrt(13)), level 1...";
t0 := Cputime(); walltime := Time();

QQ := Rationals();
F := QuadraticField(13);
ZF := Integers(F);
NN := 1*ZF;

M := GradedRingOfHMFs(F, 100);
dict := ConstructGeneratorsAndRelations(M, NN, 8, 16);
OldGens := dict[1];
Rels := dict[2];

gen_weights := Sort(SetToSequence(Keys(OldGens)));
assert Sort(&cat[[wt : j in [1..#OldGens[wt]]] : wt in gen_weights]) eq [2,4,6,6,8];

// The old ring and a map (weight, index) -> its variable, matching the
// intrinsic's FlattenGens iteration order.
R := ConstructWeightedPolynomialRing(OldGens);
oldVarPos := AssociativeArray();
idx := 0;
for wt -> g in OldGens do
  for j in [1..#g] do
    idx +:= 1;
    oldVarPos[<wt, j>] := R.idx;
  end for;
end for;
flatten := func< A | &cat[[* y : y in A[k] *] : k -> v in A] >;

// ---- CASE 1: linear same-weight change of basis (rescale + mix weight-6). ----
procedure test_linear_same_weight(OldGens, R, oldVarPos, flatten, gen_weights)
  scalars := AssociativeArray();
  scalars[2] := [3]; scalars[4] := [-2]; scalars[8] := [5];
  wt6mix := Matrix(QQ, 2, 2, [1, 2, 3, 7]); // det 1

  NewGens := AssociativeArray();
  KnownImg := AssociativeArray();
  for wt in gen_weights do
    old := OldGens[wt];
    if wt eq 6 then
      NewGens[6] := [wt6mix[1][1]*old[1] + wt6mix[1][2]*old[2],
                     wt6mix[2][1]*old[1] + wt6mix[2][2]*old[2]];
      v1 := oldVarPos[<6,1>]; v2 := oldVarPos[<6,2>];
      KnownImg[6] := [wt6mix[1][1]*v1 + wt6mix[1][2]*v2,
                      wt6mix[2][1]*v1 + wt6mix[2][2]*v2];
    else
      cs := scalars[wt];
      NewGens[wt] := [cs[i]*old[i] : i in [1..#old]];
      KnownImg[wt] := [cs[i]*oldVarPos[<wt,i>] : i in [1..#old]];
    end if;
  end for;

  PhiImages, Rout := ChangeOfPresentation(OldGens, NewGens);
  assert Grading(Rout) eq Grading(R) and Rank(Rout) eq Rank(R);
  expected := [Rout!p : p in flatten(KnownImg)];
  assert #expected eq #PhiImages;
  assert &and[PhiImages[i] eq expected[i] : i in [1..#PhiImages]];
  ok := VerifyChangeOfPresentation(OldGens, NewGens, PhiImages);
  assert ok;
end procedure;

// ---- CASE 2: genuine polynomial image (weight-4 gains a (weight-2)^2 term). ----
procedure test_polynomial_image(OldGens, R, oldVarPos, flatten, gen_weights)
  NewGens2 := AssociativeArray();
  KnownImg2 := AssociativeArray();
  for wt in gen_weights do
    NewGens2[wt] := OldGens[wt];
    KnownImg2[wt] := [oldVarPos[<wt,j>] : j in [1..#OldGens[wt]]];
  end for;
  NewGens2[4] := [2*OldGens[4][1] + 5*(OldGens[2][1])^2] cat OldGens[4][2..#OldGens[4]];
  KnownImg2[4] := [2*oldVarPos[<4,1>] + 5*oldVarPos[<2,1>]^2]
                  cat [oldVarPos[<4,j>] : j in [2..#OldGens[4]]];

  PhiImages2, Rout2 := ChangeOfPresentation(OldGens, NewGens2);
  expected2 := [Rout2!p : p in flatten(KnownImg2)];
  assert #expected2 eq #PhiImages2;
  assert &and[PhiImages2[i] eq expected2[i] : i in [1..#PhiImages2]];
  ok2 := VerifyChangeOfPresentation(OldGens, NewGens2, PhiImages2);
  assert ok2;
end procedure;

// ---- CASE 3: ideal-level check via VerifyGradedIsomorphism (case 1 iso). ----
procedure test_ideal_level_iso(OldGens, Rels, R, oldVarPos, flatten, gen_weights)
  // Rebuild the case-1 same-weight change of basis so we have its PhiImages.
  scalars := AssociativeArray();
  scalars[2] := [3]; scalars[4] := [-2]; scalars[8] := [5];
  wt6mix := Matrix(QQ, 2, 2, [1, 2, 3, 7]); // det 1

  NewGens := AssociativeArray();
  KnownImg := AssociativeArray();
  for wt in gen_weights do
    old := OldGens[wt];
    if wt eq 6 then
      NewGens[6] := [wt6mix[1][1]*old[1] + wt6mix[1][2]*old[2],
                     wt6mix[2][1]*old[1] + wt6mix[2][2]*old[2]];
      v1 := oldVarPos[<6,1>]; v2 := oldVarPos[<6,2>];
      KnownImg[6] := [wt6mix[1][1]*v1 + wt6mix[1][2]*v2,
                      wt6mix[2][1]*v1 + wt6mix[2][2]*v2];
    else
      cs := scalars[wt];
      NewGens[wt] := [cs[i]*old[i] : i in [1..#old]];
      KnownImg[wt] := [cs[i]*oldVarPos[<wt,i>] : i in [1..#old]];
    end if;
  end for;
  PhiImages, Rout := ChangeOfPresentation(OldGens, NewGens);

  Iold := ConstructIdeal(Rout, Rels);
  newList := flatten(NewGens);
  maxRelDeg := Maximum([Degree(b) : b in Basis(Iold)]);
  Inew := Syzygies(newList, [2..maxRelDeg by 2]);
  okiso := VerifyGradedIsomorphism(Iold, Inew, PhiImages);
  assert okiso;
end procedure;

test_linear_same_weight(OldGens, R, oldVarPos, flatten, gen_weights);
test_polynomial_image(OldGens, R, oldVarPos, flatten, gen_weights);
test_ideal_level_iso(OldGens, Rels, R, oldVarPos, flatten, gen_weights);

printf "PASSED (CPU: %os, Wall: %os, Mem: %oMB)\n", Cputime(t0), Time(walltime), GetMemoryUsage() div (1024^2);
