// test-time: ~40s
// The Jacobian option preserves the certified level-one surface presentation.
// Generator weights are given by Hammond (1973) and Hirzebruch (1977).
procedure test_surface_qsqrt2_jacobian()
  F := QuadraticField(2);
  N := 1*Integers(F);
  data, schemes, certified := HilbertModularVariety(F, N
      : MaxB := 30, JacobianGenerator := true);
  assert certified;
  assert #Keys(data) eq 1 and #schemes eq 1;
  assert Dimension(schemes[1]) eq 2;
  M := GradedRingOfHMFs(F, 1);
  assert HilbertSeriesSanityCheck(M, N, schemes);
  gens := data[NarrowClassGroupReps(M)[1]][1];
  R := ConstructWeightedPolynomialRing(gens);
  assert [WeightedDegree(R.i) : i in [1..Rank(R)]] eq [2, 4, 6, 14];
end procedure;

test_surface_qsqrt2_jacobian();
