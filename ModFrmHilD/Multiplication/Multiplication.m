
intrinsic GetIndexPairs(bb::RngOrdFracIdl, M::ModFrmHilDGRng)
  {sets M`MultiplicationTables[bb]  list (assoc array) of [nu, [[nu1,nu2],...] ] such that nu1+nu2 = nu up to trace bound Precision(M).}
  require bb in NarrowClassGroupReps(M): "bb must be a represetative of a narrow class";

  TraceBound := Precision(M);
  positive_reps := PositiveRepsByTrace(M); // indexed by ideal class and then trace
  shintani_reps := ShintaniRepsByTrace(M); // indexed by ideal class and then trace
  pairs := AssociativeArray(); // indexed by Shintani representatives
  for nu in ShintaniReps(M)[bb] do
    pairs[nu] := [];
  end for;
  // Add pairs of elements lexicographically by trace
  nus := [];
  for i := 0 to TraceBound do // loop over trace
    for k := 1 to #positive_reps[bb][i] do
      nu1 := positive_reps[bb][i][k];
      lennus := #nus;
      // first different traces
      for j in [0 .. Min(i - 1, TraceBound - i)] do // this min guarantees Tr(nu1+nu2) < trace bound
        for nu2 in positive_reps[bb][j] do
          nu := nu1 + nu2;
          if IsDefined(pairs, nu) then
            // add both [nu1,nu2] and [nu2,nu1]
            pairs[nu] cat:= [[nu1, nu2], [nu2, nu1]];
            nus cat:= [nu, nu2];
          end if;
        end for;
      end for;
      // tr(nu1) = tr(nu2), and nu1 != nu2
      for l in [1 .. k - 1] do
        nu2 := positive_reps[bb][i][l];
        nu := nu1 + nu2;
        if IsDefined(pairs, nu) then
          // add both [nu1,nu2] and [nu2,nu1]
          pairs[nu] cat:= [[nu1, nu2], [nu2, nu1]];
          nus cat:= [nu, nu2];
        end if;
      end for;
      // Finally, nu1 = nu2
      nu := 2*nu1; // nu1 + nu1;
      if IsDefined(pairs, nu) then
          Append(~pairs[nu], [nu1, nu1]);
          Append(~nus, nu);
      end if;
      if lennus lt #nus then
        Append(~nus, nu1);
      end if;
    end for;
  end for;
  PopulateShintaniRepsIdeal(M, bb, SequenceToSet(nus));
  M`MultiplicationTables[bb] := AssociativeArray();
  // I've turned off asserts since they slow the code down by a lot. Can put back on since we are still testing
  for key in Keys(pairs) do
    // and nu1,nu2,... totally positive (not necessarily in Shintani)
    //assert IsShintaniReduced(key);
    // above we populated M`ShintaniRepsIdeal[bb][nu] for any nu
    M`MultiplicationTables[bb][M`ShintaniRepsIdeal[bb][key]] := [[M`ShintaniRepsIdeal[bb][pair[1]], M`ShintaniRepsIdeal[bb][pair[2]]] : pair in pairs[key]];
  end for;
end intrinsic;
