// The literature examples import this helper; there is no public entry point.
import "Verification/SymmetricSubring.m" : is_geometric_swap;

// Over Q(sqrt(5)) at level one, distinguish geometric swap from another graded
// involution: an algebraic involution alone does not identify symmetric forms.
procedure test_level_one_swap()
  F := QuadraticField(5);
  N := 1*Integers(F);
  M := GradedRingOfHMFs(F, 12);
  data := ConstructGeneratorsAndRelations(M, N, 6, 6);
  G := data[1];
  R := ConstructWeightedPolynomialRing(G);
  I := ConstructIdeal(R, data[2]);
  swapped := AssociativeArray();
  assert not IsEmpty(Keys(G));
  for w in Keys(G) do
    swapped[w] := [Swap(g) : g in G[w]];
  end for;
  tau, _ := ChangeOfPresentation(G, swapped : Prec := 12, Verify := true);
  tau := [R!f : f in tau];
  assert is_geometric_swap(M, N, G, I, tau, [2, 4, 6], 12);
  other := [-R.1] cat [R.i : i in [2..Rank(R)]];
  assert VerifyGradedIsomorphism(I, I, other, other);
  assert not is_geometric_swap(M, N, G, I, other, [2, 4, 6], 12);
end procedure;

test_level_one_swap();
