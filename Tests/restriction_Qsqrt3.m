procedure test_nonprincipal_diagonal_restriction()
  F := QuadraticField(3);
  ZF := Integers(F);
  M := GradedRingOfHMFs(F, 100);
  Mk := HMFSpace(M, [2, 2]);
  X := HeckeCharacterGroup(1*ZF, [1, 2]);
  triv := X!1;
  f := EisensteinSeries(Mk, triv, triv);
  bb := NarrowClassGroupReps(M)[2];
  assert Norm(bb) eq 2;

  coeffs := RestrictionToDiagonal(f, M, bb : AsCoefficients := true);
  assert #coeffs ge 5;
  // This nonprincipal component restricts to (E4(z) + 4*E4(2*z))/5.
  assert coeffs[1..5] eq [1, 48, 624, 1344, 5232];
  g := RestrictionToDiagonal(f, M, bb);
  R<q> := PowerSeriesRing(Rationals());
  expected := ModularForms(Gamma0(2), 4)!(1 + 48*q + 624*q^2 + 1344*q^3 + 5232*q^4 + O(q^5));
  assert g eq expected;
  assert [Coefficient(qExpansion(g, #coeffs), j) : j in [0..#coeffs - 1]] eq coeffs;
end procedure;

test_nonprincipal_diagonal_restriction();
