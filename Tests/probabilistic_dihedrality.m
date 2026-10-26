// The norm-241 weight-one cusp space consists of one dihedral form.
procedure test_probabilistic_dihedrality()
    F := QuadraticField(5);
    ZF := Integers(F);
    M := GradedRingOfHMFs(F, 100);
    N := ideal<ZF | 241, 2*ZF.2 + 137>;
    H := HeckeCharacterGroup(N, [1,2]);
    Mk := HMFSpace(M, N, [1,1], H.1^11);
    Sk := CuspFormBasis(Mk : Prove := true);
    assert #Sk eq 1;
    assert ProbabilisticDihedralTest(Sk[1]);
end procedure;

test_probabilistic_dihedrality();
