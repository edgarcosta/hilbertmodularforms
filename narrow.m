load "config.m";

F<nu> := QuadraticField(6);
ZF := Integers(F);
NN := ideal<ZF|[1]>;
prec := 50;
t := 50;

Cl, mp := NarrowClassGroup(F);
bb0 := mp(Cl!0);
bb1 := mp(Cl!1);
shindom0 := Shintani_Domain(bb0, t);
shindom1 := Shintani_Domain(bb1, t);
nus0 := PositiveElementsOfTraceForIdealOfGivenTraceUpTo(bb0, t);
nus1 := PositiveElementsOfTraceForIdealOfGivenTraceUpTo(bb1, t);

// space
M := HMFSpace(F, prec);
bbs := ClassGroupReps(M);
positive_reps := PositiveElementReps(M);
shintani_reps := ShintaniReps(M);

/* HMFEquipWithMultiplication(M); */

// Attach("ModFrmHilD/deprecated/ModFrmHilDMult.m");
