load "config.m";

F<nu> := QuadraticField(6);
ZF := Integers(F);
NN := ideal<ZF|[1]>;
prec := 50;
t := 50;

// space
M := HMFSpace(F, prec);
class_group_reps := ClassGroupReps(M);
positive_reps := PositiveReps(M);
shintani_reps := ShintaniReps(M);
pairs := GetIndexPairs(class_group_reps[1], M);

// test the pairs
keys := Keys(pairs);
all_pairs := [];
for key in keys do
  pairs_for_key := pairs[key];
  for pair_for_key in pairs_for_key do
    Append(~all_pairs, SequenceToSet(pair_for_key));
    /* Append(~all_pairs, pair_for_key); */
  end for;
end for;

for i := 1 to #all_pairs do
  number_same := 0;
  for j := 1 to #all_pairs do
    if all_pairs[i] eq all_pairs[j] then
      number_same +:= 1;
      printf "i=%o, j=%o\n", i, j;
    end if;
  end for;
  if number_same gt 1 then
    printf "pair %o sux : number_same = %o\n", all_pairs[i], number_same;
  end if;
end for;

/* HMFEquipWithMultiplication(M); */

// Attach("ModFrmHilD/deprecated/ModFrmHilDMult.m");
