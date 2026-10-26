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

// A first symmetric request must leave nonsymmetric oldforms available in the cache.
procedure TestOldSymmetricCache(old_basis, d, n, k)
  F := QuadraticField(d);
  ZF := Integers(F);
  M := GradedRingOfHMFs(F, 30);
  Mk := HMFSpace(M, n*ZF, [k,k]);
  full := old_basis(Mk);
  symmetric := old_basis(Mk : Symmetric := true);
  assert #full gt #symmetric;
  assert #symmetric gt 0;
  assert &and[IsSymmetric(f) : f in symmetric];

  M2 := GradedRingOfHMFs(F, 30);
  Mk2 := HMFSpace(M2, n*ZF, [k,k]);
  direct := old_basis(Mk2 : Symmetric := true);
  after := old_basis(Mk2);
  assert #after eq #full;
  assert RowSpace(CoefficientsMatrix(after)) eq RowSpace(CoefficientsMatrix(full));
  assert #direct eq #symmetric;
  assert RowSpace(CoefficientsMatrix(direct)) eq
      RowSpace(CoefficientsMatrix(symmetric));
  again := old_basis(Mk2 : Symmetric := true);
  assert #again eq #symmetric;
  assert RowSpace(CoefficientsMatrix(again)) eq
      RowSpace(CoefficientsMatrix(symmetric));
end procedure;

TestOldSymmetricCache(OldEisensteinBasis, 5, 32, 4);
