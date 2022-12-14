printf "Checking HilbertSeries against Thomas--Vasquez formulae...D=";
// [D : D in [1..500] | IsFundamentalDiscriminant(D) and NarrowClassNumber(QuadraticField(D)) eq 1];
Ds := [ 5, 8, 13, 17, 29, 37, 41, 53, 61, 73, 89, 97, 101, 109, 113, 137, 149, 157, 173, 181, 193, 197, 233, 241, 269, 277, 281, 293, 313, 317, 337, 349, 353, 373, 389, 397, 409, 421, 433, 449, 457, 461 ];


for D in Ds do
    printf "%o ", D;
    F := QuadraticField(D);
    ZF := Integers(F);
    level := 1*ZF;
    M := GradedRingOfHMFs(F, 0);
    M2 := HMFSpace(M, level, [2,2]);
    HC := HilberSeriesCuspSpace(M, level);
    R<T> := Parent(HC);
    HE := EisensteinDimension(M2)*T^2/(1-T^2);
    H := HC + HE + NarrowClassNumber(M);
    assert H eq HilbertSeriesVasquez(F);
end for;
