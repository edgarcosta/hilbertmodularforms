SetNthreads(1);
SetSeed(1);

// Support requests must use the requested component even when the basis is cached.
procedure TestCachedSupport(basis)
  F := QuadraticField(3);
  ZF := Integers(F);
  M := GradedRingOfHMFs(F, 30);
  bbs := NarrowClassGroupReps(M);
  assert #bbs eq 2;
  Mk := HMFSpace(M, 1*ZF, [4,4]);
  full := basis(Mk);
  restricted := basis(Mk : IdealClassesSupport := [bbs[1]]);
  assert #full eq 2;
  assert #restricted eq 1;
  assert IsZero(CoefficientsMatrix(restricted : IdealClasses := [bbs[2]]));

  M2 := GradedRingOfHMFs(F, 30);
  bbs2 := NarrowClassGroupReps(M2);
  Mk2 := HMFSpace(M2, 1*ZF, [4,4]);
  direct := basis(Mk2 : IdealClassesSupport := [bbs2[1]]);
  assert #direct eq 1;
  assert RowSpace(CoefficientsMatrix(direct)) eq
      RowSpace(CoefficientsMatrix(restricted));
  after := basis(Mk2);
  assert #after eq 2;
  assert RowSpace(CoefficientsMatrix(after)) eq RowSpace(CoefficientsMatrix(full));
  other := basis(Mk2 : IdealClassesSupport := [bbs2[2]]);
  assert #other eq 1;
  assert IsZero(CoefficientsMatrix(other : IdealClasses := [bbs2[1]]));
end procedure;

TestCachedSupport(NewEisensteinBasis);
