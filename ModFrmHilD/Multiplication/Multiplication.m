
// TODO: optimize 
intrinsic GetIndexPairs(bb::RngOrdFracIdl, M::ModFrmHilD) -> Any
  {returns list (assoc array) of [nu, [[nu1,nu2],...] ] such that nu1+nu2 = nu up to trace bound Precision(M).}
  assert bb in NarrowClassGroupReps(M); 
  TraceBound := Precision(M);
  positive_reps := PositiveRepsByTrace(M); // indexed by ideal class and then trace
  shintani_reps := ShintaniRepsByTrace(M); // indexed by ideal class and then trace
  pairs := AssociativeArray(); // indexed by Shintani representatives 
  for nu in ShintaniReps(M)[bb] do
    pairs[nu] := [];
  end for; 
  // Add pairs of elements lexicographically by trace 
  for i := 0 to TraceBound do // loop over trace 
    for j in [0..Min(i, TraceBound - i)] do // this min guarantees Tr(nu1+nu2) < trace bound
      for nu1 in positive_reps[bb][i] do
        for nu2 in positive_reps[bb][j] do
          nu := nu1 + nu2;
          if IsDefined(pairs, nu) then
            pairs[nu] cat:= [[nu1,nu2],[nu2,nu1]]; // add both [nu1,nu2] and [nu2,nu1]
          end if;
        end for;
      end for;
    end for;
  end for; 
  pairs_with_redundancies_eliminated := AssociativeArray();
  pairs_shintani := AssociativeArray();
  // I've turned off asserts since they slow the code down by a lot. Can put back on since we are still testing
  for key in Keys(pairs) do
    // first eliminate multiple pairs [nu1,nu2],[nu1,nu2]
    pairs_with_redundancies_eliminated[key] := SetToSequence(SequenceToSet(pairs[key]));
    // at this point pairs[nu] = [[nu1,nu2],...] with nu in the Shintani domain
    // and nu1,nu2,... totally positive (not necessarily in Shintani)
    //assert IsShintaniReduced(key);
    pairs_shintani[key] := [[ReduceShintani(pair[1], bb, M),ReduceShintani(pair[2], bb, M)] : pair in pairs_with_redundancies_eliminated[key]];
  end for;
  return pairs_shintani, pairs_with_redundancies_eliminated, pairs;
end intrinsic;
