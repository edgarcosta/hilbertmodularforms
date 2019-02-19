// load this file to test code for narrow class number > 1

load "config.m";

F<nu> := QuadraticField(6);
ZF := Integers(F);
NN := ideal<ZF|[1]>;
prec := 12;

// space
M := HMFSpace(F, prec);
class_group_reps := ClassGroupReps(M);
bbs := class_group_reps;
positive_reps := PositiveReps(M);
shintani_reps := ShintaniReps(M);
pairs := GetIndexPairs(class_group_reps[1], M);

// nu is specified by ideal class bbs[1]
// and is the first element of trace 8
// in the shintani domain
// below are the pairs for this nu
pairs[ shintani_reps[bbs[1]][8][1] ];
