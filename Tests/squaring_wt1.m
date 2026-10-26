procedure test_squaring_certified_weight_one_completes()
    F := QuadraticField(5);
    prec := 81;
    M := GradedRingOfHMFs(F, prec);
    ZF := Integers(F);
    N := ideal<ZF | 241, 2*ZF.2 + 137>;
    H := HeckeCharacterGroup(N, [1,2]);
    chi := H.1^11;
    Mchi := HMFSpace(M, N, [1,1], chi);
    B := HeckeStabilityCuspBasis(Mchi : Proof := true);
    assert #B eq 1;
    f := B[1];
    g := f^2;
end procedure;

test_squaring_certified_weight_one_completes();
