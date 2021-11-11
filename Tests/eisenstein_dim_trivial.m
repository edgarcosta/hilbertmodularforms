printf "Testing Eisenstein dimension formulas for trivial level...";
for D in [5, 8, 12, 442, 577, 1155, 1297, 1495] do
    F := QuadraticField(D);
    ZF := Integers(F);
    prec:=1;
    M := GradedRingOfHMFs(F, prec);
    N := 1*ZF;
    X := HeckeCharacterGroup(N, [1,2]);
    squares := {* elt^2 : elt in Elements(X) *};
    for elt in Elements(X) do
        // check if elt is Totally odd
        c:=Components(elt);
        if &and[IsOdd(c[v]) : v in InfinitePlaces(F)] then
            if elt in squares then
                assert EisensteinDimension(HMFSpace(M, N, [1,1], elt)) eq #X/2 + Multiplicity(squares, elt)/2;
            else
                assert EisensteinDimension(HMFSpace(M, N, [1,1], elt)) eq Floor(#X/2);
            end if;
        end if;
    end for;
    for elt in Elements(X) do
        // check if elt is totally even
        c:=Components(elt);
        if &and[IsEven(c[v]) : v in InfinitePlaces(F)] then
            assert EisensteinDimension(HMFSpace(M, N, [2, 2], elt)) eq #X;
        end if;
    end for;
    if NarrowClassNumber(F) eq 1 then
        assert NumberOfCusps(HMFSpace(M, N, [2, 2])) eq #X;
    end if;
end for;
return true;
