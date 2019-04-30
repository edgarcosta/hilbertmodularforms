SetDebugOnError(true);
load "config.m";

F := QuadraticField(13);
ZF<w> := Integers(F);
N := ideal<ZF | {1}>;
k := [2, 2];
K := Rationals();
prec := 50; // This gives 295 coefficients which is overkill (need only 50-100 for this graded ring). Can be safely set to 30
M := GradedRingOfHMFs(F, prec);

time g, r := ConstructGeneratorsAndRelations(M, N, 8);
time g1, r1 := Relations(g, r, 20);

X := MakeScheme(g1, r1);

print X;
