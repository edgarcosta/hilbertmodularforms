intrinsic EmbedNumberField(nu::RngOrdElt, places::SeqEnum) -> SeqEnum
  {
    Input: nu an element of ZF where F is totally real
    Output: A tuple of the real embeddings of nu in RR
  }
  return [Evaluate(nu, pl) : pl in places];
end intrinsic;

intrinsic Slope_F(alpha::RngOrdElt, places::SeqEnum) -> FldReElt
  {
	Input:  alpha, an element of ZF for F a totally real quadratic number field
	Output: The "slope" defined by alpha: sigma_2(alpha)/sigma_1(alpha) where sigma_i is the ith embedding of F
  }
  return Evaluate(alpha, places[2]) / Evaluate(alpha, places[1]);
end intrinsic;

// TODO: need to generalize this
intrinsic IndicesByTrace(d::RngIntElt, g1::RngQuadElt, T::RngIntElt) -> SeqEnum
  {
    Input: ZF ring of integers of a number field (currently just for Q(sqrt(5))), T nonnegative integer
    Output: All elements of ZFgeq0 with trace T
  }

  I := [];
  if d mod 4 eq 1 then
    L := Ceiling((1 - 1 / Sqrt(d)) * T / 2);
    U := Floor((1 + 1 / Sqrt(d)) * T / 2);
    for a in [L..U] do
      Append(~I, a + (T - 2 * a) * g1);
    end for;
  else
    if T mod 2 eq 1 then
      return I;
    else
      L := Ceiling(-T / (2 * Sqrt(d)));
      U := Floor(T / (2 * Sqrt(d)));
      for a in [L..U] do
        Append(~I, T / 2 + a * g1);
      end for;
    end if;
  end if;
  return I;
end intrinsic;

intrinsic ReduceShintani(nu::RngOrdElt, eps::RngQuadElt, log_slope_funu::FldReElt, places::SeqEnum) -> FldNumElt
  {
    Input: nu a totally nonnegative element of ZF
    Output: a representative for nu in the Shintani cone
  }

  assert (IsTotallyPositive(nu) or (nu eq 0)); // only for totally nonnegative elements
  if nu eq 0 then
    return 0;
  else
    m_nu := Slope_F(nu, places);
    r := -Floor(RealField(100) ! (Log(m_nu) / log_slope_funu));
    return nu * (eps^2)^r;
  end if;
end intrinsic;

intrinsic TotallyPositiveAssociate(alpha::RngOrdElt, eps::RngQuadElt, places::SeqEnum) -> RngOrdElt
  {
	Input: alpha an element of F a totally real quadratic number field
	Output: A totally positive element of F associate to alpha
  }
  alpha_RR := EmbedNumberField(alpha, places);
  if Norm(alpha) ge 0 then
    if alpha_RR[1] lt 0 then
      alpha *:= -1;
    end if;
  else
    alpha := alpha * eps;
    if alpha_RR[1] * EmbedNumberField(eps, places)[1] lt 0 then
      alpha *:= -1;
    end if;
  end if;
  return alpha;
end intrinsic;

intrinsic ShintaniGenerator(I::RngOrdIdl, eps::RngQuadElt, log_slope_funu::FldReElt, places::SeqEnum) -> RngOrdElt
  {
    Input: An ideal
    Output: The unique generator for I contained in the Shintani cone
  }
  bool, gen := IsPrincipal(I);
  assert bool eq true;
  gen_reduced := ReduceShintani(TotallyPositiveAssociate(gen, eps, places), eps, log_slope_funu, places);
  return gen_reduced;
end intrinsic;

intrinsic GetIndexPairs(M::ModFrmHilD) -> SeqEnum
  {returns list of [nu, [[nu1,nu2],...] ] such that nu1+nu2 = nu up to precision.}
  if NarrowClassNumber(BaseField(M)) ne 1 then
    print "WARNING: currently only works for narrow class number 1.\n";
    assert false;
  end if;

  ZF := Integers(BaseField(M));
  d := Discriminant(ZF);
  if d mod 4 eq 0 then
    d := d div 4;
  end if;

  places := InfinitePlaces(BaseField(M));
  eps := FundamentalUnit(ZF);
  log_slope_funu := Log(Slope_F(eps^2, places));

  ideals := Ideals(M);
  trace_bound := 0; gens := [];
  result := AssociativeArray();
  for I in ideals do
    nu := ZF ! ShintaniGenerator(I, eps, log_slope_funu, places);
    Append(~gens, nu);
    result[nu] := [];
    trace_bound := Max(Trace(nu), trace_bound);
  end for;

  by_trace := AssociativeArray();
  for i in [0..trace_bound] do
    s_1 := IndicesByTrace(d, ZF.2, i);
    by_trace[i] := s_1;

    for j in [0..Min(i, trace_bound - i)] do
      for nu_1 in s_1 do
        for nu_2 in by_trace[j] do
          nu := nu_1 + nu_2;
          if IsDefined(result, nu) then
            Append(~result[nu], [nu_1, nu_2]);
            Append(~result[nu], [nu_2, nu_1]);
          end if;
        end for;
      end for;
    end for;
  end for;

  indices_list := [];
  shintani_reps := AssociativeArray();
  for nu in gens do
    sums_up := [];
    for x in Set(result[nu]) do
      if not IsDefined(shintani_reps, x[1]) then
        shintani_reps[x[1]] := ZF ! ReduceShintani(ZF ! x[1], eps, log_slope_funu, places);
      end if;
      if not IsDefined(shintani_reps, x[2]) then
        shintani_reps[x[2]] := ZF ! ReduceShintani(ZF ! x[2], eps, log_slope_funu, places);
      end if;
      Append(~sums_up, [shintani_reps[x[1]], shintani_reps[x[2]]]);
    end for;
    Append(~indices_list, [* nu, sums_up *]);
  end for;
  return indices_list;
end intrinsic;
