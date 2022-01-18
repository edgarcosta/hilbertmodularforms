
/*
Generated with
foo.m:
d := StringToInteger(d);
F := QuadraticField(d);
ZF := Integers(F);
print Sprintf("newdimensions[%o] := %o;\n", d, [[Dimension(NewSubspace(HilbertCuspForms(F, n*ZF, [k, k]))) : n in [1..5]]: k in [4..16 by 2]]);
exit;

and
parallel --eta magma -b d:={1} foo.m ::: 5 8 12 13 17 20 21 24 28 29 32 33 37 40 41 44 45 48 52 53 56 57 60 61 65 68 69 72 73 76 77 80 84 85 88 89 92 93 96 97
*/
newdimensions := AssociativeArray();

newdimensions[8] := [
[ 1, 0, 3, 2, 9 ],
[ 2, 1, 8, 6, 25 ],
[ 3, 2, 16, 12, 49 ],
[ 4, 3, 27, 20, 81 ],
[ 6, 5, 40, 30, 121 ],
[ 8, 7, 56, 42, 169 ],
[ 10, 9, 75, 56, 225 ]
];

newdimensions[72] := [
[ 1, 0, 3, 2, 9 ],
[ 2, 1, 8, 6, 25 ],
[ 3, 2, 16, 12, 49 ],
[ 4, 3, 27, 20, 81 ],
[ 6, 5, 40, 30, 121 ],
[ 8, 7, 56, 42, 169 ],
[ 10, 9, 75, 56, 225 ]
];

newdimensions[32] := [
[ 1, 0, 3, 2, 9 ],
[ 2, 1, 8, 6, 25 ],
[ 3, 2, 16, 12, 49 ],
[ 4, 3, 27, 20, 81 ],
[ 6, 5, 40, 30, 121 ],
[ 8, 7, 56, 42, 169 ],
[ 10, 9, 75, 56, 225 ]
];

newdimensions[20] := [
[ 0, 1, 2, 1, 3 ],
[ 1, 1, 3, 4, 8 ],
[ 1, 3, 7, 8, 16 ],
[ 2, 3, 10, 15, 25 ],
[ 3, 5, 15, 22, 38 ],
[ 3, 9, 23, 30, 54 ],
[ 4, 11, 30, 41, 71 ]
];

newdimensions[80] := [
[ 0, 1, 2, 1, 3 ],
[ 1, 1, 3, 4, 8 ],
[ 1, 3, 7, 8, 16 ],
[ 2, 3, 10, 15, 25 ],
[ 3, 5, 15, 22, 38 ],
[ 3, 9, 23, 30, 54 ],
[ 4, 11, 30, 41, 71 ]
];

newdimensions[5] := [
[ 0, 1, 2, 1, 3 ],
[ 1, 1, 3, 4, 8 ],
[ 1, 3, 7, 8, 16 ],
[ 2, 3, 10, 15, 25 ],
[ 3, 5, 15, 22, 38 ],
[ 3, 9, 23, 30, 54 ],
[ 4, 11, 30, 41, 71 ]
];

newdimensions[45] := [
[ 0, 1, 2, 1, 3 ],
[ 1, 1, 3, 4, 8 ],
[ 1, 3, 7, 8, 16 ],
[ 2, 3, 10, 15, 25 ],
[ 3, 5, 15, 22, 38 ],
[ 3, 9, 23, 30, 54 ],
[ 4, 11, 30, 41, 71 ]
];



weights := [4..16 by 2];
levels := [1..5];

printf "Testing the computation of the HilbertCuspForms mod p gives same dimensions...d=";

function check(d)
    printf "%o ", d;
    F := QuadraticField(d);
    ZF := Integers(F);
    prec := 1;
    R := GradedRingOfHMFs(F, prec);
    dims := [[ Dimension(NewSubspace(HilbertCuspFormsFiniteField(F, n*ZF, [k, k]))) : n in levels]: k in weights];
    assert newdimensions[d] eq dims;
    // one could also check that the eigenforms agree modulo p
    // however, that would require computing over characteristic 0
    return true;
end function;

ds := [];
for counter in [1..5] do
    if Set(ds) eq Keys(newdimensions) then
        break;
    end if;
    d := Random(Keys(newdimensions));
    while d in ds do
        d := Random(Keys(newdimensions));
    end while;
    Append(~ds, d);
    _ := check(d);
end for;
return true;
