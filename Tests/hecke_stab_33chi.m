// Given a [1,1] Eisenstein series E of (nonquadratic) nebentypus chi
// and cusp spaces S_22 and S_44 of weights [2,2] and [4,4]
// respectively, checks that S_22*f is the Hecke stable subspace of
// S_44/f

PREC := 17;

function test(F, N, chi)
  // F - number field
  // N - level
  // chi - nebentypus, of modulus N

  ZF := Integers(F);
  M := GradedRingOfHMFs(F, PREC);
  triv_char := HeckeCharacterGroup(1*ZF, [1,2]).0;

  M11chi := HMFSpace(M, N, [1,1], chi);
  E := EisensteinSeries(M11chi, chi, triv_char);

  M11chiinv := HMFSpace(M, N, [1,1], chi^-1);
  Einv := EisensteinSeries(M11chiinv, chi^-1, triv_char);

  M22 := HMFSpace(M, N, [2,2]);
  B22 := CuspFormBasis(M22);

  M44 := HMFSpace(M, N, [4,4]);
  B44 := CuspFormBasis(M44);

  W := [f * E : f in B22];
  V := [f / Einv : f in B44];

  // TODO abhijitm should rework the weight 1 code
  // into code that computes spaces with nontrivial nebentypus,
  // should be fairly easy. This is a stopgap I guess.
  pp := 3*ZF;
  U := HeckeStableSubspace(V, pp);

  // want all of W to be in the Hecke stable subspace of V
  assert #LinearDependence(U cat W) eq #W;
end function;


F := QuadraticField(5);

N := 14*ZF;
H := HeckeCharacterGroup(N, [1,2]);
chi := H.1; // order 6
test(F, N, chi);

N := 5*Factorization(5*ZF)[1][1]; 
H := HeckeCharacterGroup(N, [1,2]);
chi := H.1; // order 5
test(F, N, chi);
