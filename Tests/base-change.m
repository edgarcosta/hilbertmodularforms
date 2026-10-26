// The level-11 weight-two newform base changes into the Hilbert cusp space.
procedure test_base_change_weight_two()
    F := QuadraticField(5);
    M := GradedRingOfHMFs(F, 50);
    Mk := HMFSpace(M, 11*Integers(F), [2,2]);
    S_Q := Basis(CuspidalSubspace(ModularForms(11, 2)));
    assert #S_Q eq 1;
    g := BaseChange(M, S_Q[1]);

    Sk := CuspFormBasis(Mk : Proof := true);
    assert #Sk gt 0;
    assert #LinearDependence(Append(Sk, g)) eq 1;
end procedure;

test_base_change_weight_two();
