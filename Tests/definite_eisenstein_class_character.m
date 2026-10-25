F := QuadraticField(12);
N := 1*Integers(F);
R := GradedRingOfHMFs(F, 1);
X := HeckeCharacterGroup(N, [1,2]);
chi := X.1;
assert Order(chi) eq 2;
assert Conductor(chi) eq N;
assert not IsTrivial(DirichletRestriction(chi));
M := HilbertCuspForms(HMFSpace(R, N, [2,2], chi));
assert IsDefinite(M);
dim := Dimension(M);
printf "Sign character: dimension %o (expected 0)\n", dim;
assert dim eq 0;

F := QuadraticField(316);
N := 1*Integers(F);
R := GradedRingOfHMFs(F, 1);
X := HeckeCharacterGroup(N, [1,2]);
chis := [chi : chi in Elements(X) | IsTrivial(DirichletRestriction(chi))];
assert #chis eq 3;
assert Sort([Order(chi) : chi in chis]) eq [1,3,3];

for chi in chis do
    M := HilbertCuspForms(HMFSpace(R, N, [2,2], chi));
    assert IsDefinite(M);
    dim := Dimension(M);
    printf "Class character of order %o: dimension %o (expected 21)\n", Order(chi), dim;
    assert dim eq 21;
end for;
