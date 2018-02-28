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
intrinsic IndicesByTrace(ZF::RngOrd, eps::RngQuadElt, T::RngIntElt) -> SeqEnum
  {
    Input: ZF ring of integers of a number field (currently just for Q(sqrt(5))), T nonnegative integer
    Output: All elements of ZFgeq0 with trace T
  }
  d := Discriminant(ZF);
  if d mod 4 eq 0 then
    d := d div 4;
  end if;
  I := [];
  if d mod 4 eq 1 then
    L := Ceiling((1 - 1/Sqrt(d))*T/2);
    U := Floor((1 + 1/Sqrt(d))*T/2);
    for a in [L..U] do
      Append(~I, ZF ! (a+(T-2*a)*eps));
    end for;
  else
    if T mod 2 eq 1 then
      return I;
    else
      L := Ceiling(-T/(2*Sqrt(d)));
      U := Floor(T/(2*Sqrt(d)));
      for a in [L..U] do
        Append(~I, ZF ! (T/2 + a*eps));
      end for;
    end if;
  end if;
  return I;
end intrinsic;

intrinsic ReduceShintani(nu::RngOrdElt, eps::RngQuadElt, places::SeqEnum) -> FldNumElt
  {
    Input: nu a totally nonnegative element of ZF
    Output: a representative for nu in the Shintani cone
  }
  assert (IsTotallyPositive(nu) or (nu eq 0)); //only for totally nonnegative elements
  if nu eq 0 then
    return 0;
  else
    m := Slope_F(eps^2, places); // slope of fundamental positive unit
    m_nu := Slope_F(nu, places);
    r := -Floor(RealField(100) ! (Log(m_nu) / Log(m)));
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
    if EmbedNumberField(alpha, places)[1] ge 0 then
      alpha := alpha;
    else
      alpha := -alpha;
    end if;
  else
    if EmbedNumberField(alpha, places)[1]*EmbedNumberField(eps, places)[1] ge 0 then
      alpha := alpha*eps;
    else
      alpha := -alpha*eps;
    end if;
  end if;
  return alpha;
end intrinsic;

// intrinsic MinTraceAssociate(alpha::RngOrdElt) -> RngOrdElt
//   {
//  Input: F a totally real number field (currently just QQ(sqrt(5))), alpha an element of ZF
//  Output: A totally nonnegative associate of alpha with minimal trace
//   }
//   F := Parent(alpha);
//   ZF := Integers(F);
//   e := FundamentalUnit(ZF);
//   e_RR := EmbedNumberField(e);
//   if alpha eq 0 then
//     return 0;
//   else
//     alpha := TotallyPositiveAssociate(alpha);
//     alpha_RR := EmbedNumberField(alpha);
//     r := (1/4)*Log(alpha_RR[2]/alpha_RR[1])/Log(e_RR[1]);
//     alpha_news := [e^(2*Floor(r))*alpha, e^(2*Ceiling(r))*alpha];
//     traces := [Trace(a) : a in alpha_news];
//     _, ind := Minimum(traces);
//     return alpha_news[ind], Trace(alpha_news[ind]);
//   end if;
// end intrinsic;

intrinsic ShintaniGenerator(I::RngOrdIdl, eps::RngQuadElt, places::SeqEnum) -> RngOrdElt
  {
    Input: An ideal
    Output: The unique generator for I contained in the Shintani cone
  }
  bool, gen := IsPrincipal(I);
  assert bool eq true;
  gen_reduced := ReduceShintani(TotallyPositiveAssociate(gen, eps, places), eps, places);
  return gen_reduced;
end intrinsic;

intrinsic GetIndexPairs(M::ModFrmHilD) -> SeqEnum
  {returns list of [nu, [[nu1,nu2],...] ] such that nu1+nu2 = nu up to precision.}
  printf "WARNING: currently only works for narrow class number 1.\n";

  begin := Cputime();
  ZF := Integers(BaseField(M));
  places := InfinitePlaces(BaseField(M));
  eps := FundamentalUnit(ZF);

  ideals := Ideals(M); trace_bound := 0; gens := [];
  result := AssociativeArray();
  for I in ideals do 
    nu := ZF ! ShintaniGenerator(I, eps, places);
    Append(~gens, nu); result[nu] := {};
    trace_bound := Max(Trace(nu), trace_bound);
  end for;

  by_trace := AssociativeArray();
  for i in [0..trace_bound] do
    s_1 := IndicesByTrace(ZF, eps, i);
    by_trace[i] := s_1;

    for j in [0..Min(i, trace_bound - i)] do 
      for nu_1 in s_1 do
        for nu_2 in by_trace[j] do 
          nu := nu_1 + nu_2;
          if IsDefined(result, nu) then
            Include(~result[nu], [nu_1, nu_2]);
            Include(~result[nu], [nu_2, nu_1]);
          end if;
        end for;
      end for;
    end for;
  end for;

  indices_list := [ [* nu, [ [ZF ! ReduceShintani(x[1], eps, places), ZF ! ReduceShintani(x[2], eps, places)] : x in result[nu] ] *] : nu in gens ];
  print Cputime(begin);

  print indices_list;
  return indices_list;
end intrinsic;