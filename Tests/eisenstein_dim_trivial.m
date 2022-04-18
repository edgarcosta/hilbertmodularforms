printf "Testing Eisenstein dimension formulas for trivial level... d=";
DS := [5, 8, 12, 442, 577, 1155, 1297, 1495];
function check(D)
    printf "%o ", D;
    F := QuadraticField(D);
    ZF := Integers(F);
    prec := 1;
    M := GradedRingOfHMFs(F, prec);
    N := 1*ZF;
    X := HeckeCharacterGroup(N, [1,2]);
    squares := {* elt^2 : elt in Elements(X) *};
    characters := Elements(X);
    elt := Random(Elements(X));
    if IsOddAtoo(elt) then
        M1 := HMFSpace(M, N, [1,1], elt);
        if elt in squares then
            assert #EisensteinAdmissibleCharacterPairs(M1) eq #X/2 + Multiplicity(squares, elt)/2;
        else
            assert #EisensteinAdmissibleCharacterPairs(M1) eq Floor(#X/2);
        end if;
        _ := EisensteinBasis(M1); // this tests that the basis gets computed and dimension matches
    end if;
    if IsEvenAtoo(elt) then
        M2 := HMFSpace(M, N, [2, 2], elt);
        assert #EisensteinAdmissibleCharacterPairs(M2) eq #X;
        _ := EisensteinBasis(M2); // this tests that the basis gets computed and dimension matches
    end if;
    if NarrowClassNumber(F) eq 1 then
        assert NumberOfCusps(HMFSpace(M, N, [2, 2])) eq #X;
    end if;
    return true;
end function;

ds := [];
t := Time();
for counter in [1..5] do
    if StringToInteger(Split(Time(t), ".")[1]) ge 30 then
        break;
    end if;
    if Set(ds) eq SequenceToSet(DS) then
        break;
    end if;
    d := Random(DS);
    while d in ds do
        d := Random(DS);
    end while;
    Append(~ds, d);
    _ := check(d);
end for;

return true;
