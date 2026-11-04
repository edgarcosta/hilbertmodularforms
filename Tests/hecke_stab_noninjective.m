F := QuadraticField(5);
ZF := Integers(F);
M := GradedRingOfHMFs(F, 120);
pp := 2*ZF;

// These spaces are U_2-stable, with nonzero kernel. Changing the
// basis must preserve the whole space, including nilpotent directions.
for level in [4, 8] do
  B := Basis(HMFSpace(M, level*ZF, [2,2]));
  n := (level eq 4) select 3 else 5;
  assert #B eq n;
  TB := [HeckeOperator(f, pp) : f in B];
  assert #LinearDependence(B cat TB) eq n;
  assert #LinearDependence(TB) eq ((level eq 4) select 1 else 2);

  rebased := [B[i] + B[n] : i in [1..n-1]] cat [B[n]];
  for V in [rebased, B] do
    W := HeckeStableSubspace(V, pp);
    printf "Level %o: expected %o stable forms, got %o\n", level, n, #W;
    assert #W eq n;
    assert #LinearDependence(W) eq 0;
    assert #LinearDependence(W cat B) eq n;
  end for;
  if level eq 4 then
    f := rebased[1];
    assert #LinearDependence([f, HeckeOperator(f, pp)]) eq 0;
    assert #HeckeStableSubspace([f], pp) eq 0;
  end if;
end for;
