SetNthreads(1);

F := QuadraticField(229);
ZF := Integers(F);
M := GradedRingOfHMFs(F, 30);
assert Invariants(NarrowClassGroup(M)) eq [3];
mm := Decomposition(ZF, 3)[1][1];
assert Order(mm @@ NarrowClassGroupMap(M)) eq 3;

H := HeckeCharacterGroup(1*ZF);
eta := AssociatedPrimitiveCharacter(H.1);
assert Order(eta) eq 3;
assert IsOne(Modulus(eta));
Mk0 := HMFSpace(M, 1*ZF, [2,2]);
E := EisensteinSeries(Mk0, eta, eta^-1);

// Distinct constants detect a component permutation that trivial characters hide.
bbs := NarrowClassGroupReps(M);
assert #SequenceToSet([Coefficients(E)[bb][0] : bb in bbs]) eq 3;
Mk := HMFSpace(M, mm, [2,2]);
included := Inclusion(E, Mk, mm);
direct := EisensteinSeries(Mk, eta, eta^-1 : dd := mm);

for nn in Ideals(M) do
    if not IsZero(nn) then
        assert Coefficient(direct, nn) eq Coefficient(included, nn);
    end if;
end for;
print "Direct and included Eisenstein series agree on positive coefficients.";
for bb in bbs do
    assert Coefficients(direct)[bb][0] eq Coefficients(included)[bb][0];
end for;
print "Direct and included Eisenstein series agree on every component constant.";
