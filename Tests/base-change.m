PRECISION := 180;

procedure test(F, N, k : psi := false)
  // F - FldNum, number field to base change to
  // N - RngIntElt, an integer specifying the level
  // k - RngIntElt, an integer specifying the weight
  // psi - Dirichlet character of f, since Magma is dumb
  //    and DirichletCharacter(f) fails on weight 1 forms

  M := GradedRingOfHMFs(F, PRECISION);
  ZF := Integers(F);
  N_F := N * ZF;
  k_par := [k : _ in [1 .. Degree(F)]];

  H := HeckeCharacterGroup(N_F, [1 .. Degree(F)]);

  if psi cmpne false then
    M_Q := ModularForms(psi, k);
    chi := Extend(NormInduction(F, psi), H);
    Mk := HMFSpace(M, N_F, k_par, chi);
  else
    M_Q := ModularForms(N, k);
    Mk := HMFSpace(M, N_F, k_par);
  end if;

  S_Q := Basis(CuspidalSubspace(M_Q));
  f := S_Q[1];
  g := BaseChange(M, f : psi:=psi);

  Sk := CuspFormBasis(Mk);
  assert #LinearDependence(Append(Sk, g)) eq 1;
end procedure;

F := QuadraticField(5);

N := 23;
k := 1;
psi := DirichletGroup(N).1;
test(F, N, k : psi:=psi);

N := 11;
k := 2;
test(F, N, k);
