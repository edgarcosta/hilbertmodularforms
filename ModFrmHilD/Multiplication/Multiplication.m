intrinsic ComputeMPairs(bb::RngOrdFracIdl, M::ModFrmHilDGRng)
  {sets M`MultiplicationTables[bb]  list (assoc array) of [nu, [[nu1,nu2],...] ] such that nu1+nu2 = nu up to trace bound Precision(M).}
  require bb in NarrowClassGroupReps(M): "bb must be a represetative of a narrow class";
  // Preliminaries
  ZF := Integers(M);
  TraceBound := Precision(M);
  positive_reps := PositiveRepsByTrace(M); // indexed by ideal class and then trace
  shintani_reps := ShintaniReps(M)[bb]; // List of Shintani reps for bb
  pairs := AssociativeArray(); // keys = shintani_reps // For each nu, this stores lists of of [nu1,nu2].
  for nu in shintani_reps do 
    pairs[nu] := [];
  end for;

  //////// Algorithm : nu = nu1 + nu2  /////////
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
  /////// Populating multiplication table ////////////
  /* We have nu1 + nu2 = nu where nu1,nu2 are totally positive (not necessarily Shintani reduced). 
  Write nui = mui*ei where ei is a tot. pos. unit and mui is Shintani reduced and then for each nu we will store a list of the [[mu1,e1],[mu2,e2]] */
  M`MPairs[bb] := AssociativeArray(); // keys = shintani_reps, For each nu, this stores [[mu1,e1],[mu2,e2]].
  for nu in shintani_reps do
      M`MPairs[bb][nu] := [[ReduceShintaniMinimizeTrace(i) : i in pair] : pair in pairs[nu]];
  end for;
end intrinsic;

intrinsic ConvertIdealArrayToShintaniArray(M::ModFrmHilDGRng, bb::RngOrdFracIdl, coeffs::Assoc) -> Assoc
  {}
  coeffs_nu := AssociativeArray();
  nus := ShintaniReps(M);
end intrinsic;
