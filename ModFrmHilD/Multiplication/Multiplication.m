intrinsic GetIndexPairs(bb::RngOrdFracIdl, M::ModFrmHilDGRng)
  {assigns M`MultiplicationTables[bb]  list (assoc array) of [nu, [[mu,mup],...] ] such 
   that mu+mup = nu up to trace bound Precision(M).}

  require bb in NarrowClassGroupReps(M): 
      "bb must be among the fixed set of representatives of the narrow class group";

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
      mu := positive_reps[bb][i][k];
      lennus := #nus;
      // first different traces
      for j in [0 .. Min(i - 1, TraceBound - i)] do 
              // this min guarantees Tr(mu+mup) < trace bound
        for mup in positive_reps[bb][j] do
          nu := mu + mup;
          if IsDefined(pairs, nu) then
            // add both [mu,mup] and [mup,mu]
            pairs[nu] cat:= [[mu, mup], [mup, mu]];
            nus cat:= [nu, mup];
          end if;
        end for;
      end for;
      // tr(mu) = tr(mup), and mu != mup
      for l in [1 .. k - 1] do
        mup := positive_reps[bb][i][l];
        nu := mu + mup;
        if IsDefined(pairs, nu) then
          // add both [mu,mup] and [mup,mu]
          pairs[nu] cat:= [[mu, mup], [mup, mu]];
          nus cat:= [nu, mup];
        end if;
      end for;
      // Finally, mu = mup
      nu := 2*mu; // mu + mu;
      if IsDefined(pairs, nu) then
          Append(~pairs[nu], [mu, mu]);
          Append(~nus, nu);
      end if;
      if lennus lt #nus then
        Append(~nus, mu);
      end if;
    end for;
  end for;
  
  PopulateShintaniRepsIdeal(M, bb, SequenceToSet(nus));
  M`MultiplicationTables[bb] := AssociativeArray();

  for key in Keys(pairs) do
    // and mu,mup,... totally positive (not necessarily in Shintani)
    // assert IsShintaniReduced(key);
    // above we populated M`ShintaniRepsIdeal[bb][nu] for any nu
    M`MultiplicationTables[bb][M`ShintaniRepsIdeal[bb][key]] := 
      [[M`ShintaniRepsIdeal[bb][pair[1]], M`ShintaniRepsIdeal[bb][pair[2]]] : pair in pairs[key]];
  end for;
end intrinsic;
