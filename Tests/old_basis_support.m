SetNthreads(1);
SetSeed(1);

procedure TestOldSupport(old_basis, name)
  F := QuadraticField(3);
  ZF := Integers(F);
  pp := Decomposition(ZF, 2)[1][1];

  M := GradedRingOfHMFs(F, 30);
  bbs := NarrowClassGroupReps(M);
  assert #bbs eq 2;
  assert Order(pp @@ NarrowClassGroupMap(M)) eq 2;
  Mk := HMFSpace(M, pp, [4,4]);
  full := old_basis(Mk);
  restricted := old_basis(Mk : IdealClassesSupport := [bbs[1]]);

  // A fresh graded ring keeps this request independent of the cached full basis.
  M2 := GradedRingOfHMFs(F, 30);
  bbs2 := NarrowClassGroupReps(M2);
  Mk2 := HMFSpace(M2, pp, [4,4]);
  direct := old_basis(Mk2 : IdealClassesSupport := [bbs2[1]]);
  printf "Old %o support: full %o, restricted %o, direct %o\n",
      name, #full, #restricted, #direct;
  assert #full eq 4;
  assert #restricted eq 2;
  assert #direct eq #restricted;
  assert RowSpace(CoefficientsMatrix(direct)) eq
      RowSpace(CoefficientsMatrix(restricted));
  assert IsZero(CoefficientsMatrix(direct : IdealClasses := [bbs2[2]]));

  after := old_basis(Mk2);
  assert #after eq #full;
  assert RowSpace(CoefficientsMatrix(after)) eq RowSpace(CoefficientsMatrix(full));
  other := old_basis(Mk2 : IdealClassesSupport := [bbs2[2]]);
  reference := old_basis(Mk : IdealClassesSupport := [bbs[2]]);
  assert #other eq 2;
  assert RowSpace(CoefficientsMatrix(other)) eq
      RowSpace(CoefficientsMatrix(reference));
end procedure;

TestOldSupport(OldEisensteinBasis, "Eisenstein");
TestOldSupport(OldCuspFormBasis, "cusp");
