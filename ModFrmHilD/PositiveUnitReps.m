/////// **************** PUBLIC FUNCTIONS **************** /////// 

intrinsic FunDomainRep(M::ModFrmHilDGRng, bb::RngOrdFracIdl, nu::FldNumElt : Precision := 100) -> FldNumElt, FldNumElt
  {
    inputs:
      M: A graded ring of HMFs
      bb: A narrow class representative
      nu: Number field element
    returns: 
      An element nu' in the fundamental domain and a 
      totally positive unit eps such that nu = eps * nu'

    Prefer this version of FunDomainRep because it checks to see
    if nu is already known to be a fundamental domain 
    representative before attempting to reduce.
  }

  F := NumberField(Parent(nu));
  if nu in FunDomainReps(M)[bb] then
    // TODO abhijitm is it safe to just return 1
    // instead of F!1? 
    return nu, F!1;
  else
    return FunDomainRep(nu : Precision := Precision);
  end if;
end intrinsic;

intrinsic FunDomainRep(M::ModFrmHilDGRng, bb::RngOrdFracIdl, nu::FldOrdElt : Precision := 100) -> FldNumElt, FldNumElt
  {
    inputs:
      M: A graded ring of HMFs
      bb: A narrow class representative
      nu: Element of ring of integers of a field
    returns: 
      An element nu' in the fundamental domain and a 
      totally positive unit eps such that nu = eps * nu'

    Prefer this version of FunDomainRep because it checks to see
    if nu is already known to be a fundamental domain 
    representative before attempting to reduce.
  }

  F := NumberField(Parent(nu));
  return FunDomainRep(M, bb, F!nu);
end intrinsic;

intrinsic FunDomainRep(nu::FldNumElt : lattice := "tot_pos", Precision := 100) -> FldNumElt, FldNumElt
  {
    inputs:
      nu: Number field element
    returns: 
      An element nu' in the fundamental domain and a 
      totally positive unit eps such that nu = eps * nu'

    We compute this by passing to the log-Minkowski domain,
    writing the log-embedding of nu in a basis spanned by 
    the log-positive units (which lie on the trace-zero 
    hyperplane) and (1 ... 1). We can forget the last coordinate
    because we are interested in the log-positive unit action.
    We add 1/2 to everything and then take floor function - this serves
    to find the product of positive units necessary to bring the 
    log-embedding of nu into the balanced fundamental parallelepiped 
    spanned by the log-positive units. 
  }
  F := NumberField(Parent(nu));

  if IsZero(nu) then
    return F!0, F!1;
  end if;

  n := Degree(F);
  if lattice eq "tot_pos" then
    epses := TotallyPositiveUnitsGenerators(F);
  elif lattice eq "squares" then
    epses := [eps^2 : eps in UnitsGenerators(F)];
  else
    require 0 eq 1 : "Invalid option for lattice - the options are 'tot_pos' and 'squares'.";
  end if;

  log_nu := ForgetTraceLogEmbed(nu, epses : Precision := Precision);

  THRESHOLD := 10^-10;
  nu_prime := nu;
  for i in [1 .. (n-1)] do
    // we add a threshold because Magma does some silly things
    // with 0.9999999 != 1 and we want points on the 
    // "upper wall" to be reduced to the lower wall
    eps_i_shift := Floor(log_nu[i] + 1/2 + THRESHOLD);
    nu_prime :=  nu_prime * epses[i] ^ -eps_i_shift;
  end for;
  eps := nu/nu_prime;
  return nu_prime, eps;
end intrinsic;

intrinsic FunDomainRep(nu::RngElt : lattice := "tot_pos", Precision := 100) -> FldNumElt, FldNumElt
  {
    inputs:
      nu: Element of the ring of integers of a number field.
    returns: 
      An element nu' in the fundamental domain and a 
      totally positive unit eps such that nu = eps * nu'
  }
  ZF := Parent(nu);
  F := NumberField(ZF);
  return FunDomainRep(F!nu : lattice := lattice, Precision := Precision); 
end intrinsic;

intrinsic IdealToRep(M::ModFrmHilDGRng) -> Assoc
  {getter}
  return M`IdealToRep;
end intrinsic;

intrinsic RepToIdeal(M::ModFrmHilDGRng) -> Assoc
  {getter}
  return M`RepToIdeal;
end intrinsic;

intrinsic IdealToRep(M::ModFrmHilDGRng, nn::RngOrdIdl) -> FldNumElt
  {
    inputs: 
      M: A graded ring of Hilbert modular forms
      nn: A integral ideal of the base field of M
      bb: A narrow class representative
    returns:
      An totally positive element nu in the fundamental domain 
      corresponding to the ideal nn.
  }

  if IsZero(nn) then 
    return BaseField(M)!0;
  end if;

  require Norm(nn) le Precision(M) : "Beyond known precision, sorry!";

  bb := IdealToNarrowClassRep(M, nn);
  return M`IdealToRep[bb][nn];
end intrinsic;

intrinsic RepToIdeal(M::ModFrmHilDGRng, nu::FldNumElt, bb::RngOrdFracIdl) -> RngOrdIdl
  {
    inputs:
      M: A graded ring of Hilbert modular forms
      nu: A fundamental domain representative field element
      bb: A narrow class representative
    returns:
      An integral ideal nn corresponding to the representative nu on the component bb.
  }

  return M`RepToIdeal[bb][nu];
end intrinsic;

intrinsic RepIdealConversion(M::ModFrmHilDGRng) -> Assoc, Assoc
  {
    inputs:
      M: A graded ring of Hilbert modular forms
    returns:
      Two 2D associative arrays,
        - IdealToRep
        - RepToIdeal,
      which cache the conversion of nn to nu. 
      Precisely, for each nn in the ideal class 
      [bbp]^-1, the ideal nn * bbp is narrowly
      principal, and we can use FunDomainRep
      to get a totally positive generator.
      We have IdealToRep[bb][nu] = nn
      and RepToIdeal[bb][nu] = nn

      // TODO we could combine this function into
      // FunDomainRepsUpToNorm and maybe save a loop
      // or two, but because narrow principalizing
      // is probably the most expensive step anyways
      // I figured code readability/cleanliness was
      // worth more. There is a known optimization here
      // if this step is too slow though. 
  }
  
  if assigned M`IdealToRep and M`RepToIdeal then
    return M`RepToIdeal, M`IdealToRep;
  end if;

  M`IdealToRep := AssociativeArray();
  M`RepToIdeal := AssociativeArray();

  F := BaseField(M);
  ZF := Integers(M);
  dd := Different(ZF);

  for bb in NarrowClassGroupReps(M) do
    M`IdealToRep[bb] := AssociativeArray();
    M`RepToIdeal[bb] := AssociativeArray();

    // dealing with the zero ideal, which lives
    // on every component
    M`IdealToRep[bb][0*ZF] := F!0;
    M`RepToIdeal[bb][F!0] := 0*ZF;
  end for;

  for nn in IdealsUpTo(M`Precision, ZF) do
    // we've already dealt with the zero ideal
    if IsZero(nn) then
      continue;
    end if;
    bb := IdealToNarrowClassRep(M, nn);
    bbp := bb * dd^-1;
    _, nu := IsNarrowlyPrincipal(nn * bbp);
    nu, _ := FunDomainRep(nu);
    M`IdealToRep[bb][nn] := nu;
    M`RepToIdeal[bb][nu] := nn;
  end for;

  return M`RepToIdeal, M`IdealToRep;
end intrinsic;

intrinsic FunDomainReps(M::ModFrmHilDGRng) -> Assoc
  {getter}
  return M`FunDomainReps;
end intrinsic;

intrinsic FunDomainRepsOfNorm(M::ModFrmHilDGRng, bb::RngOrdFracIdl, x::RngIntElt) -> SeqEnum
  {
    inputs:
      M: A graded ring of Hilbert modular forms
      bb: An ideal class representative of M
      x: An integer norm
    returns:
      The fundamental domain representatives nu such that the integral ideal
      nn associated to nu has norm x.
  }
  return FunDomainRepsOfNorm(M)[bb][x];
end intrinsic;

intrinsic FunDomainRepsUpToNorm(M::ModFrmHilDGRng, bb::RngOrdFracIdl, x::RngIntElt) -> SetEnum
  {
    inputs:
      M: A graded ring of Hilbert modular forms
      bb: An ideal class representative of M
      x: An integer norm
    returns:
      The fundamental domain representatives nu such that the integral ideal
      nn associated to nu has norm at most x.
  }
  
  return FunDomainRepsUpToNorm(M)[bb][x];
end intrinsic;

intrinsic FunDomainRepsUpToNorm(M::ModFrmHilDGRng) -> Assoc
  {
    inputs:
      M: A graded ring of Hilbert modular forms
    returns:
      A 2D associative arrays, M`FunDomainRepsUpToNorm,
      keyed by narrow class group representatives bb (these are fractional ideals)
      and nonnegative integers up to prec with values 
      FunDomainIdlReps[bb][x] a SeqEnum.

      The elements of FunDomainRepsOfNorm[bb][x] are the nu corresponding
      to integral ideals nn with norm up to x lying in the narrow class
      of [bbp]^-1, i.e. such that nn * bbp = (nu) for some 
      integral ideal nn of norm at most x.
  }
  PopulateFunDomainRepsArrays(M);
  return M`FunDomainRepsUpToNorm;
end intrinsic;

intrinsic FunDomainRepsOfNorm(M::ModFrmHilDGRng) -> Assoc
  {
    inputs:
      M: A graded ring of Hilbert modular forms
    returns:
      A 2D associative arrays, M`FunDomainRepsUpToNorm,
      keyed by narrow class group representatives bb (these are fractional ideals)
      and nonnegative integers up to prec with values 
      FunDomainIdlReps[bb][x] a SeqEnum.

      The elements of FunDomainRepsOfNorm[bb][x] are the nu corresponding
      to integral ideals nn with norm up to x lying in the narrow class
      of [bbp]^-1, i.e. such that nn * bbp = (nu) for some 
      integral ideal nn of norm equal to x.
  }
  PopulateFunDomainRepsArrays(M);
  return M`FunDomainRepsOfNorm;
end intrinsic;

intrinsic PopulateFunDomainRepsArrays(M::ModFrmHilDGRng)
  {
    inputs:
      M: A graded ring of Hilbert modular forms
    returns:
      A 2D associative arrays, M`FunDomainRepsUpToNorm,
      keyed by narrow class group representatives bb (these are fractional ideals)
      and nonnegative integers up to prec with values 
      FunDomainIdlReps[bb][x] a SeqEnum.

      The elements of FunDomainRepsOfNorm[bb][x] are the nu corresponding
      to integral ideals nn with norm up to x lying in the narrow class
      of [bbp]^-1, i.e. such that nn * bbp = (nu) for some 
      integral ideal nn of norm equal to x.
  }

  if (assigned M`FunDomainRepsOfNorm) and (assigned M`FunDomainRepsUpToNorm) then
    return;
  end if;

  F := BaseField(M);
  ZF := Integers(M);
  dd := Different(ZF);

  M`FunDomainRepsOfNorm := AssociativeArray();
  M`FunDomainRepsUpToNorm := AssociativeArray();
  
  for bb in NarrowClassGroupReps(M) do
    M`FunDomainRepsOfNorm[bb] := AssociativeArray();
    M`FunDomainRepsUpToNorm[bb] := AssociativeArray();
    // since IdealsUpTo doesn't include 1
    M`FunDomainRepsOfNorm[bb][0] := [F!0];
    M`FunDomainRepsUpToNorm[bb][0] := [F!0];
  end for;

  // In this loop, we have FunDomainRepsOfNorm[bb][x]
  // store the reps of norm x (rather than up to x). 
  // We will update it with the correct values afterwards.
  //
  // TODO abhijitm this can be improved, but I figured
  // the looping wasn't the expensive part and wrote it this way for
  // readability. If it matters, I can make it faster instead.
  for nn in IdealsUpTo(M`Precision, ZF) do
    bb := IdealToNarrowClassRep(M, nn);
    nu := M`IdealToRep[bb][nn];

    if IsDefined(M`FunDomainRepsOfNorm[bb], Norm(nn)) then 
      Append(~M`FunDomainRepsOfNorm[bb][Norm(nn)], nu);
    else
      M`FunDomainRepsOfNorm[bb][Norm(nn)] := [nu];
    end if;
  end for;

  for x in [1 .. M`Precision] do
    for bb in NarrowClassGroupReps(M) do
      // It's already defined if there were some nus associated to nn of this norm
      if IsDefined(M`FunDomainRepsOfNorm[bb], x) then
        M`FunDomainRepsUpToNorm[bb][x] := M`FunDomainRepsUpToNorm[bb][x-1] cat M`FunDomainRepsOfNorm[bb][x];
      else
        M`FunDomainRepsUpToNorm[bb][x] := M`FunDomainRepsUpToNorm[bb][x-1];
        M`FunDomainRepsOfNorm[bb][x] := [];
      end if;
    end for;
  end for;
end intrinsic;

intrinsic ComputeShadows(M::ModFrmHilDGRng, bb::RngOrdFracIdl) -> Assoc
  {
    inputs:
      M: A graded ring of Hilbert modular forms
      bb: Fractional ideal of the ring of integers of the number field underlying M
    returns: 
      An associative array shadows_bb keyed by norm x whose values at x is an enumerated set
      storing pairs (eps, nu), where eps is a totally positive unit and nu
      a fundamental domain representative, such that the element nu*eps is dominated by 
      (totally less than) some fundamental domain representative nu' with norm at most x. 

      Practically, the elements eps*nu coming from shadows_bb[x] are the extra indices
      which must be accounted for when multiplying ModFrmHilDEltComps of precision x.


    Let log_max_coord be the logarithm of the largest coordinate entry appearing
    in any representative nu. The algorithm enumerates totally positive elements
    of the field lying in the intersection of the n-dimensional hypercube with 
    opposite corners (0, .., 0) and (log_max_coord, .., log_max_coord) with the 
    region of the totally positive orthant with norm at most M`Precision. 

    For each such point (which we call a candidate shadow), it then checks 
    if it is dominated by some representative. If it is, then we call it a shadow
    and add it to our output. 

    TODO abhijitm Needing to check domination after the fact is an annoying requirement
    arising because this hypercube intersect small norm region is generally bigger than 
    the correct region. I think I know of a better search algorithm but it'd be a lot of 
    work so I feel this is good enough for now. 
  }

  RR_PREC := 100;
  FUZZ := 10^-29;
  RR := RealField(RR_PREC);

  F := BaseField(M);
  epses := TotallyPositiveUnitsGenerators(F);
  ZF := Integers(F);
  n := Degree(F);
  places := InfinitePlaces(F);
  bbp := NarrowClassGroupRepsToIdealDual(M)[bb];

  reps := FunDomainRepsUpToNorm(M)[bb][M`Precision];
  nu_norms := {Norm(nu) : nu in reps | not IsZero(nu)}; 
  min_norm := Min(nu_norms);

  // The largest coordinate entry appearing in any representative nu.
  // This determines the hypercube we work with
  max_coord := Max(&cat[[Evaluate(nu, v) : v in places] : nu in reps]) + FUZZ;

  // **Construct the simplex**
  //
  // In the norm x iteration, nm_smplx will store an (n-1)-simplex in R^(n-1),
  // which we will use to compute shadows_bb which are translates of nu of norm x.
  //
  //
  // Concretely, in the norm x iteration, the ith vertex of nm_smplx,
  // prior to applying ForgetTraceLogBasis, will be the vector
  // [log(max_coord), ..., log(max_coord)] + e_i * log(max_coord^n/x)
  // in R^n. 
  //
  // ForgetTraceLogBasis does not care about trace, so we can treat
  // this as the vector whose ith vertex is e_i * -n * log(max_coord/x)
  // in R^n.
  //
  // Because ForgetTraceLogBasis is a linear transformation from
  // R^n to R^(n-1), it commutes with rescaling, so it is enough to 
  // construct the (n-1) simplex in R^n with vertices
  // (1, 0, ..., 0), (0, 1, 0, ..., 0), ..., (0, ..., 0, 1),
  // apply ForgetTraceLogBasis to get our initial nm_smplx, and then 
  // dynamically rescale it when processing each x. This avoids repeatedly creating
  // the simplex object. 
  
  z := Vector([RealField(100)!0 : _ in [1 .. n]]);
  nm_splx_vtxs := [];
  for i in [1 .. n] do
    v := z;
    v[i] := -1.0 * Log(max_coord^n / min_norm);

    // after projecting onto the trace-zero hyperplane 
    // (i.e. forgetting the trace)
    // this will be n points in (n-1)-dimensional space
    Append(~nm_splx_vtxs, Rationalize(ForgetTraceLogBasis(F, ElementToSequence(v), epses)));
  end for;

  epses := TotallyPositiveUnitsGenerators(F);
  nm_splx := Polyhedron(nm_splx_vtxs);

  prev_x := min_norm;
  cand_shadows_bb := {<F!0, F!1>};
  for x in nu_norms do 
    // rescale nm_splx for this x
    nm_splx := BestApproximation(Log(max_coord^n / x) / Log(max_coord^n / prev_x), 10^100) * nm_splx; 
    nn_norm := Integers()!(Norm(x)/Norm(bbp));
    for nu in FunDomainRepsOfNorm(M, bb, nn_norm) do
      if IsZero(nu) then
        continue;
      end if;
      splx := nm_splx;
      // center the simplex at nu 
      P := Polyhedron([Rationalize(ForgetTraceLogEmbed(nu^-1, epses))]);
      splx +:= Polyhedron([Rationalize(ForgetTraceLogEmbed(nu^-1, epses))]);

      // process each point
      for pt in Points(splx) do
        v := Vector(pt);
        eps := ZF!1;
        for i in [1 .. n-1] do
          eps *:= (epses[i] ^ (IntegerRing()!v[i]));
        end for;
        Include(~cand_shadows_bb, <nu, eps>);
      end for;
    end for;
    prev_x := x;
  end for;

  // Now that we have candidate shadows_bb, we want to prune the list
  // to leave only the actual shadows_bb.
  //
  // We also want to group each shadow eps*nu by the smallest norm of a rep nu'
  // such that nu' dominates eps*nu. This allows us to restrict the set of shadows_bb
  // we keep track of if we are working with forms of lesser precision.

  // TODO abhijitm can definitely do this more efficiently
  shadows_bb := AssociativeArray();

  for x in [0 .. M`Precision] do
    shadows_bb[x] := {};
  end for;

  for cand_shadow in cand_shadows_bb do
    nu, eps := Explode(cand_shadow);
    for nup in reps do
      nn_norm := Integers()!(Norm(nup)/Norm(bbp));
      if IsDominatedBy(eps * nu, nup) then 
        Include(~shadows_bb[nn_norm], <nu, eps>); 
        Exclude(~cand_shadows_bb, cand_shadow);
        break;
      end if;
    end for;
  end for;

  for nn_norm in [1 .. M`Precision] do
    if IsDefined(shadows_bb, nn_norm) then
      shadows_bb[nn_norm] join:= shadows_bb[nn_norm - 1];
    else
      shadows_bb[nn_norm] := shadows_bb[nn_norm - 1];
    end if;
  end for;

  return shadows_bb;
end intrinsic;

intrinsic ComputeMPairs(M::ModFrmHilDGRng, bb::RngOrdFracIdl) -> Any
  {temporary function, just to ensure compatibility}

  MPairs_bb := AssociativeArray();
  shadows_bb := ComputeShadows(M, bb)[M`Precision];
  for nu in FunDomainRepsUpToNorm(M)[bb][M`Precision] do
    MPairs_bb[nu] := [];
    for nu_1eps_1 in shadows_bb do
      nu_1, eps_1 := Explode(nu_1eps_1);
      if IsDominatedBy(eps_1*nu_1, nu) then
        nu_2eps_2 := nu - eps_1*nu_1;
        nu_2, eps_2 := FunDomainRep(nu_2eps_2);
        assert <nu_2, eps_2> in shadows_bb;
        Append(~MPairs_bb[nu], [<nu_1, eps_1>, <nu_2, eps_2>]);
      end if;
    end for;
  end for;

  return MPairs_bb;
end intrinsic;

intrinsic ComputeShadows(M::ModFrmHilDGRng) -> Assoc
  {}
  if not assigned M`Shadows then
    M`Shadows := AssociativeArray();
    for bb in M`NarrowClassGroupReps do
      M`Shadows[bb] := ComputeShadows(M, bb);
    end for;
  end if;

  return M`Shadows;
end intrinsic;

intrinsic ComputeMPairs(M::ModFrmHilDGRng) -> Any
  {temporary function, just to test}
  if not assigned M`MPairs then
    M`MPairs := AssociativeArray();
    for bb in M`NarrowClassGroupReps do
      M`MPairs[bb] := ComputeMPairs(M, bb);
    end for;
  end if;

  return M`MPairs;
end intrinsic;

/////// **************** HELPER FUNCTIONS **************** /////// 

intrinsic EmbedNumberFieldElement(nu::FldNumElt : Precision := 100) -> SeqEnum
  {}
  F := Parent(nu);
  return [Evaluate(nu, place : Precision := Precision) : place in InfinitePlaces(F)];
end intrinsic;

intrinsic EmbedNumberFieldElement(nu::RngOrdElt : Precision := 100) -> SeqEnum
  {}
  F := Parent(nu);
  return [Evaluate(F!nu, place : Precision := Precision) : place in InfinitePlaces(F)];
end intrinsic;

intrinsic ForgetTraceLogBasis(F::FldNum, A::SeqEnum[FldReElt], epses::SeqEnum[RngOrdElt] : Precision := 100) -> SeqEnum
  {
    input: 
      A: A sequence of real numbers [a_1, ..., a_n],
         thought of as a point in log-Minkowski space
           of the field F. 
      epses: A sequence of (n-1) totally positive units which span a lattice
        in the trace-zero hyperplane of log-Minkowski space
    returns: 
      The first (n-1) coordinates of the A 
      after writing it in the basis spanned by
      the log-Minkowski embeddings of eps_1, eps_2, ..., eps_(n-1),
      and [1, 1, ..., 1, 1], where eps_i is the ith 
      generator of the group totally positive units. 
      
      Essentially, we forget about the trace of A
      and write the 'trace zero' part using the given
      units as a basis. 
  }
  B_rows := [[Log(x) : x in EmbedNumberFieldElement(eps : Precision := Precision)] : eps in epses];
  Append(~B_rows, [1 : i in [1 .. #A]]);
  B := Matrix(B_rows);
  v := Vector(A) * B^-1;

  return Prune([v[i] : i in [1 .. Dimension(Parent(v))]]);
end intrinsic;

intrinsic ForgetTraceLogEmbed(nu::FldNumElt, epses::SeqEnum[RngOrdElt] : Precision := 100) -> SeqEnum[ModTupFldElt]
  {
    input:
      nu: a totally positive element of a totally real number field F.
      epses: a sequence of (n-1) totally positive units which span a lattice
        in the trace-zero hyperplane of Log-Minkowski space
    returns:
      If n is the degree of F, the (n-1)-dimensional vector corresponding to 
      taking the log-Minkowski embedding of nu and applying ForgetTraceLogBasis.
  }
  F := Parent(nu);
  return ForgetTraceLogBasis(F, [Log(x) : x in EmbedNumberFieldElement(F!nu : Precision := Precision)], epses);
end intrinsic;

intrinsic IsDominatedBy(alpha::FldNumElt, beta::FldNumElt) -> BoolElt
  {
    input:
      alpha: an element of a totally real number field F
      beta: an element of a totally real number field F
   returns:
      true if and only if every coordinate of the embedding of alpha in R^n
      is less than or equal to corresponding coordinate in the embedding of
      beta in R^n
  }
  alpha_embed := EmbedNumberFieldElement(alpha);
  beta_embed := EmbedNumberFieldElement(beta);
  for i in [1 .. #alpha_embed] do
    if alpha_embed[i] gt beta_embed[i] then
      return false;
    end if;
  end for;
  return true;
end intrinsic;

intrinsic Rationalize(A::SeqEnum[FldReElt] : Precision := 100) -> SeqEnum[FldRatElt]
  {
    input:
      A: A sequence of real numbers
    returns:
      A sequence of rational numbers approximating
      the real number. 

      We use this to construct polyhedra since the polyhedron
      constructor only accepts rational numbers.
  }
  // TODO I have no clue why it fails sometimes on the input -0.5000...
  // if Precision is 100 but not if it's 99...
  return [BestApproximation(A[i], 10^(Precision - 1)) : i in [1 .. #A]];
end intrinsic;

intrinsic Rationalize(v::ModTupFldElt : Precision := 100) -> SeqEnum[FldRatElt]
  {
    input:
      v: A vector of real numbers
      Precision: The number of decimal places we preserve when
        rationalizing real numbers
    returns:
      A sequence of rational numbers
  }
  return Rationalize(ElementToSequence(v) : Precision := Precision);
end intrinsic;
