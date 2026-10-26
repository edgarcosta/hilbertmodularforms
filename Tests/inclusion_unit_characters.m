SetNthreads(1);

// Inclusion must compare unit characters on the components it connects.
procedure test_inclusion_unit_characters()
    F := QuadraticField(229);
    ZF := Integers(F);
    M := GradedRingOfHMFs(F, 30);
    mm := Decomposition(ZF, 3)[1][1];
    assert Order(mm @@ NarrowClassGroupMap(M)) eq 3;
    bbs := NarrowClassGroupReps(M);
    bb := bbs[1];
    target_bb := NarrowClassRepresentative(M, bb/mm);
    assert bb ne target_bb;

    ucs := AssociativeArray();
    for cc in bbs do
        ucs[cc] := TrivialUnitCharacter(F);
    end for;
    ucs[bb] := UnitCharacter(F, [-1]);
    source := HMFSpace(M, 1*ZF, [2,2] : unitcharacters := ucs);
    target := HMFSpace(M, mm, [2,2] : unitcharacters := ucs);
    f := HMFZero(source);

    for g in [* Components(f)[bb], f *] do
        rejected := false;
        try
            _ := Inclusion(g, target, mm);
        catch e
            rejected := "Unit characters of source and target components do not match" in Sprint(e);
        end try;
        error if not rejected, "Inclusion accepted incompatible shifted unit characters";
    end for;

    shifted_ucs := AssociativeArray();
    for cc in bbs do
        shifted_ucs[NarrowClassRepresentative(M, cc/mm)] := ucs[cc];
    end for;
    target := HMFSpace(M, mm, [2,2] : unitcharacters := shifted_ucs);
    g := Inclusion(Components(f)[bb], target, mm);
    assert ComponentIdeal(g) eq target_bb;
    assert IsZero(g);
    image := Inclusion(f, target, mm);
    assert Parent(image) eq target;
    assert IsZero(image);
end procedure;

test_inclusion_unit_characters();
