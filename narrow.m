// load this file to test code for narrow class number > 1

SetDebugOnError(true);

load "config.m";

F<nu> := QuadraticField(6);
/* F<nu> := QuadraticField(5); */
ZF := Integers(F);
NN := ideal<ZF|[1]>;
prec := 20;

// space
M := HMFSpace(F, prec);
class_group_reps := ClassGroupReps(M);
bbs := class_group_reps;
positive_reps := PositiveReps(M);
shintani_reps := ShintaniReps(M);

nu := shintani_reps[bbs[1]][12][1];

SetDebugOnError(true);
ReduceShintani(nu, bbs[1], shintani_reps);



/* nus := positive_reps[bbs[1]][5]; */
/* nu := nus[1]; */
/* nu in shintani_reps[bbs[1]][Trace(nu)]; */
/* ReduceShintani(nu, shintani_reps); */

/* for i := 1 to #bbs do */
/*   printf "%o:\n", bbs[i]; */
/*   bb := bbs[i]; */
/*   for t := 2 to prec do */
/*     printf "\tt=%o:\n", t; */
/*     pos_reps := positive_reps[bb][t]; */
/*     if #pos_reps gt 0 then */
/*       printf "\t#pos_reps=%o:\n", #pos_reps; */
/*       for j := 1 to #pos_reps do */
/*         printf "\t\tpos_reps[%o]=%o\n", j, pos_reps[j]; */
/*         new_nu := ReduceShintani(pos_reps[j]); */
/*         printf "new_nu = %o\n", new_nu; */
/*         assert new_nu in shintani_reps[bb][Trace(new_nu)]; */
/*       end for; */
/*     end if; */
/*   end for; */
/* end for; */

/* pairs := GetIndexPairs(class_group_reps[1], M); */

// nu is specified by ideal class bbs[1]
// and is the first element of trace 8
// in the shintani domain
// below are the pairs for this nu

/* pairs[ shintani_reps[bbs[1]][8][1] ]; */
