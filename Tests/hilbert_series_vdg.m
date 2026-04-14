printf "Checking HilbertSeriesVdG against HilbertSeries(Gamma) per component...D=";

// Test discriminants:
//   h+ = 1: 5, 8, 13, 17, 29, 37, 41
//   h+ = 2: 12, 24, 40, 60
//   h+ = 4: 120, 145
Ds := [5, 8, 12, 13, 17, 24, 29, 37, 40, 41, 60, 120, 145];

for D in Ds do
    printf "%o ", D;
    F := QuadraticField(D);
    ZF := Integers(F);
    NCl, mp := NarrowClassGroup(F);
    for el in NCl do
        bb := mp(el);
        G := CongruenceSubgroup("GL+", "Gamma0", F, 1*ZF, bb);
        H_vdg := HilbertSeriesVdG(G);
        H_gen := HilbertSeries(G);
        assert H_vdg eq H_gen;
    end for;
end for;

// Also test the FldNum version that returns a sequence over all components
printf "\nChecking HilbertSeriesVdG(F) sequence version...D=";
for D in Ds do
    printf "%o ", D;
    F := QuadraticField(D);
    ZF := Integers(F);
    NCl, mp := NarrowClassGroup(F);
    series := HilbertSeriesVdG(F);
    assert #series eq #NCl;
    for i -> el in [el : el in NCl] do
        bb := mp(el);
        G := CongruenceSubgroup("GL+", "Gamma0", F, 1*ZF, bb);
        assert series[i] eq HilbertSeries(G);
    end for;
end for;

printf "\n";
