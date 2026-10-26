// The level-23 weight-one base change needs a costly Hecke-stability proof.
// Share that proof between the base-change and dihedrality checks.
procedure test_base_change_weight_one()
    F := QuadraticField(5);
    ZF := Integers(F);
    M := GradedRingOfHMFs(F, 200);
    psi := DirichletGroup(23).1;
    S_Q := Basis(CuspidalSubspace(ModularForms(psi, 1)));
    assert #S_Q eq 1;
    g := BaseChange(M, S_Q[1] : psi := psi);

    N := 23*ZF;
    H := HeckeCharacterGroup(N, [1,2]);
    chi := Extend(NormInduction(F, psi), H);
    Mk := HMFSpace(M, N, [1,1], chi);
    Sk := CuspFormBasis(Mk : Prove := true);
    assert #Sk eq 1;
    assert #LinearDependence(Append(Sk, g)) eq 1;
    assert ProbabilisticDihedralTest(Sk[1]);
end procedure;

test_base_change_weight_one();
