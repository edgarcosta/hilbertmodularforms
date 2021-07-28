intrinsic ComputeMPairs(bb::RngOrdFracIdl, M::ModFrmHilDGRng)
  {Assigns M`MultiplicationTables[bb] an associative array with nu entry 
   [[[mu,eps],[mup,eps]] : mu*eps + mup*epsp = nu]] 
   for nu with trace up to Precision(M).}

  require bb in NarrowClassGroupReps(M): "bb must be among a fixed set of narrow class representatives";

  // Preliminaries
  ZF := Integers(M);
  TraceBound := Precision(M);
  positive_reps := PositiveRepsByTrace(M); // indexed by ideal class and then trace
  shintani_reps := ShintaniReps(M)[bb]; // List of Shintani reps for bb
  pairs := AssociativeArray(); // keys = shintani_reps 
  for nu in shintani_reps do 
    pairs[nu] := [];
  end for;

  //////// Algorithm : nu = mu + mup  /////////
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
  /* We have mu + mup = nu where mu, mup are totally positive 
     (not necessarily Shintani reduced). 
  
     Write mu = s(mu)*eps and 
           mup = s(mup)*epsp
     where eps,epsp are totally positive units and
     s(mu), s(mup) are Shintani reduced.
     Store the list of pairs [[s(mu),eps],[s(mup),epsp]]. */

  M`MPairs[bb] := AssociativeArray(); 
     // keys = shintani_reps, 
  for nu in shintani_reps do
      M`MPairs[bb][nu] := [[ReduceShintaniMinimizeTrace(i) : i in pair] : pair in pairs[nu]];
  end for;
end intrinsic;

intrinsic ConvertIdealArrayToShintaniArray(M::ModFrmHilDGRng, bb::RngOrdFracIdl, coeffs::Assoc) -> Assoc
  {}
  coeffs_nu := AssociativeArray();
  nus := ShintaniReps(M);
end intrinsic;
