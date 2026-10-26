SetNthreads(1);

// The Fourier coefficient path must work across distinct narrow classes.
procedure test_inclusion_coeff_path_nonprincipal_ideal()
    F := QuadraticField(229);
    ZF := Integers(F);
    M := GradedRingOfHMFs(F, 30);
    mm := Decomposition(ZF, 3)[1][1];
    assert Order(mm @@ NarrowClassGroupMap(M)) eq 3;
    H := HeckeCharacterGroup(1*ZF);
    eta := AssociatedPrimitiveCharacter(H.1);
    assert Order(eta) eq 3;
    source := HMFSpace(M, 1*ZF, [2,2]);
    target := HMFSpace(M, mm, [2,2]);
    f := EisensteinSeries(source, eta, eta^-1);
    direct := EisensteinSeries(target, eta, eta^-1 : dd := mm);

    image := Inclusion(f, target, mm : ForceCoeffPath := true);
    assert image eq direct;
    assert Coefficient(f, 1*ZF) ne 0;
    assert Coefficient(image, mm) eq Coefficient(f, 1*ZF);
    bbs := NarrowClassGroupReps(M);
    assert #bbs eq 3;
    for bb in bbs do
        g := Inclusion(Components(f)[bb], target, mm : ForceCoeffPath := true);
        target_bb := NarrowClassRepresentative(M, bb/mm);
        assert ComponentIdeal(g) eq target_bb;
        assert g eq Components(direct)[target_bb];
    end for;
end procedure;

test_inclusion_coeff_path_nonprincipal_ideal();
