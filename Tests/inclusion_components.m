SetNthreads(1);

F := QuadraticField(229);
ZF := Integers(F);
M := GradedRingOfHMFs(F, 30);
assert Invariants(NarrowClassGroup(M)) eq [3];
mm := Decomposition(ZF, 3)[1][1];
assert Order(mm @@ NarrowClassGroupMap(M)) eq 3;

Mk0 := HMFSpace(M, 1*ZF, [2,2]);
chi := AssociatedPrimitiveCharacter(Character(Mk0));
E := EisensteinSeries(Mk0, chi, chi);
Mk := HMFSpace(M, mm, [2,2]);
Eold := EisensteinSeries(Mk, chi, chi : dd := mm);

// Compare with an Eisenstein series constructed directly at the target level.
for bb in NarrowClassGroupReps(M) do
    f := Components(E)[bb];
    g := Inclusion(f, Mk, mm);
    full_g := Inclusion(HMF(f), Mk, mm);
    target_bb := NarrowClassRepresentative(M, bb/mm);
    assert ComponentIdeal(g) eq target_bb;
    assert Components(full_g)[target_bb] eq g;
    assert Precision(g) eq Precision(M);
    nonzero := 0;
    for nn in Ideals(M) do
        if not IsZero(nn) then
            if IdealToNarrowClassRep(M, nn) eq target_bb then
                expected := Coefficient(Eold, nn);
                assert Coefficient(g, nn) eq expected;
                nonzero +:= (expected ne 0) select 1 else 0;
            else
                expected := 0;
            end if;
            assert Coefficient(full_g, nn) eq expected;
        end if;
    end for;
    assert nonzero gt 0;
end for;

assert Coefficient(Inclusion(E, Mk, mm), mm) eq Coefficient(E, 1*ZF);
print "Order-three component inclusions agree with target-level Eisenstein coefficients.";
