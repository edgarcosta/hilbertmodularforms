
/*
Generated with
foo.m:
d := StringToInteger(d);
F := QuadraticField(d);
ZF := Integers(F);
print Sprintf("dimensions[%o] := %o;\n", d, [[[ Dimension(U) : U in NewformDecomposition(NewSubspace(HilbertCuspForms(F, n*ZF, [k, k]))) ] : n in [1..5]]: k in [4..16 by 2]]);
exit;

and
parallel --eta magma -b d:={1} foo.m ::: 5 8 12 13 17 20 21 24 28 29 32 33 37 40 41 44 45 48 52 53 56 57 60 61 65 68 69 72 73 76 77 80 84 85 88 89 92 93 96 97
*/
dimensions := AssociativeArray();



weights := [4..16 by 2];
levels := [1..5];

printf "Testing the computation of the HilbertCuspForms mod p gives same dimensions...d=";

function check(d)
    printf "%o ", d;
    F := QuadraticField(d);
    ZF := Integers(F);
    prec := 1;
    R := GradedRingOfHMFs(F, prec);
    dims := [[[ Dimension(U) : U in NewformDecomposition(NewSubspace(HilbertCuspFormsFiniteField(F, n*ZF, [k, k]))) ] : n in levels]: k in weights]);
    assert dimensions[d] eq dims;
    // one could also check that the eigenforms agree modulo p
    // another day
    return true;
end function;

ds := [];
for counter in [1..5] do
    if Set(ds) eq Keys(dimensions) then
        break;
    end if;
    d := Random(Keys(dimensions));
    while d in ds do
        d := Random(Keys(dimensions));
    end while;
    Append(~ds, d);
    _ := check(d);
end for;
return true;
