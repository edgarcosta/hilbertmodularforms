// Insufficient coefficients must give a usable lower bound before the
// expensive proof-space basis is built (issue #576).
procedure test_hecke_proof_precision_lower_bound()
    F := QuadraticField(5);
    ZF := Integers(F);
    M := GradedRingOfHMFs(F, 50);
    N := ideal<ZF | 241, 2*ZF.2 + 137>;
    H := HeckeCharacterGroup(N, [1,2]);
    Mk := HMFSpace(M, N, [1,1], H.1^11);

    raised := false;
    try
        _ := CuspFormBasis(Mk : Prove := true);
    catch e
        message := Sprint(e);
        assert "working precision 50" in message;
        assert "23 coefficients" in message;
        assert "dimension 38" in message;
        assert "at least precision 81" in message;
        assert "this lower bound does not guarantee linear independence" in message;
        assert "Prove := false" in message;
        raised := true;
    end try;
    assert raised;
    assert Precision(M) eq 50;

    // Both entry points must accept the precision named by the diagnostic.
    raised := false;
    try
        _ := HeckeStabilityCuspBasis(Mk);
    catch e
        message := Sprint(e);
        assert "working precision 50" in message;
        assert "Prove := false" in message;
        raised := true;
    end try;
    assert raised;
    Mhigh := GradedRingOfHMFs(F, 81);
    Mkhigh := HMFSpace(Mhigh, N, [1,1], H.1^11);
    Sk := CuspFormBasis(Mkhigh : Prove := true);
    assert #Sk eq 1;
    assert #HeckeStabilityCuspBasis(Mkhigh : prove := true) eq 1;
    assert Precision(Mhigh) eq 81;
    assert Precision(M) eq 50;
end procedure;

// An empty weight-one cusp space needs no proof-space precision check.
procedure test_hecke_proof_empty_space()
    F := QuadraticField(5);
    ZF := Integers(F);
    M := GradedRingOfHMFs(F, 50);
    N := ideal<ZF | 149, 2*ZF.2 + 67>;
    H := HeckeCharacterGroup(N, [1,2]);
    characters := [c : c in Elements(H) |
        Order(c) eq 2 and IsGamma1EisensteinWeight(c, 1)];
    assert #characters gt 0;
    Mk := HMFSpace(M, N, [1,1], characters[1]);
    assert IsEmpty(CuspFormBasis(Mk : Prove := true));
    assert Precision(M) eq 50;
end procedure;

test_hecke_proof_precision_lower_bound();
test_hecke_proof_empty_space();
