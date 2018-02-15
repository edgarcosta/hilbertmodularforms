intrinsic EmbedNumberField(nu::RngOrdElt) -> SeqEnum
  {
    Input: nu an element of ZF where F is totally real
    Output: A tuple of the real embeddings of nu in RR
  }
  ZF := Parent(nu);
  F := NumberField(ZF);
  places := InfinitePlaces(F);
  return [Evaluate(nu,pl) : pl in places];
end intrinsic;

intrinsic Slope_F(alpha::RngOrdElt) -> FldReElt
  {
	Input:  alpha, an element of ZF for F a totally real quadratic number field
	Output: The "slope" defined by alpha: sigma_2(alpha)/sigma_1(alpha) where sigma_i is the ith embedding of F
  }
  ZF := Parent(alpha);
  F := NumberField(ZF);
  places := InfinitePlaces(F);
  alpha_RR := [Evaluate(alpha,pl) : pl in places];
  m := alpha_RR[2]/alpha_RR[1];
  return m;
end intrinsic;

// TODO: need to generalize this
// IndicesByTrace := function(ZF,T)
intrinsic IndicesByTrace(ZF::RngOrd, T::RngIntElt) -> SeqEnum
  {
    Input: ZF ring of integers of a number field (currently just for Q(sqrt(5))), T nonnegative integer
    Output: All elements of ZFgeq0 with trace T
  }
  d := Discriminant(ZF);
  if d mod 4 eq 0 then
    d := d div 4;
  end if;
  eps := FundamentalUnit(ZF);
  I := [];
  if d mod 4 eq 1 then
    L := Ceiling((1 - 1/Sqrt(d))*T/2);
    U := Floor((1 + 1/Sqrt(d))*T/2);
    for a in [L..U] do
      Append(~I,ZF!(a+(T-2*a)*eps));
    end for;
  else
    if T mod 2 eq 1 then
      return I;
    else
      L := Ceiling(-T/(2*Sqrt(d)));
      U := Floor(T/(2*Sqrt(d)));
      for a in [L..U] do
        Append(~I,ZF!(T/2 + a*eps));
      end for;
    end if;
  end if;
  return I;
end intrinsic;

intrinsic ReduceShintani(nu::RngOrdElt) -> FldNumElt
  {
    Input: nu a totally nonnegative element of ZF
    Output: a representative for nu in the Shintani cone
  }
  assert (IsTotallyPositive(nu) or (nu eq 0)); //only for totally nonnegative elements
  ZF := Parent(nu);
  F := NumberField(ZF);
  if nu eq 0 then
    return 0;
  else
    eps := FundamentalUnit(ZF);
    m := Slope_F(eps^2); // slope of fundamental positive unit
    m_nu := Slope_F(nu);
    r := -Floor(RealField(100)!(Log(m_nu)/Log(m)));
    return ZF!(nu*(eps^2)^r);
  end if;
end intrinsic;

intrinsic TotallyPositiveAssociate(alpha::RngOrdElt) -> RngOrdElt
  {
	Input: alpha an element of F a totally real quadratic number field
	Output: A totally positive element of F associate to alpha
  }
  ZF := Parent(alpha);
  eps := FundamentalUnit(ZF);
  alpha_RR := EmbedNumberField(alpha);
  if Norm(alpha) ge 0 then
    if EmbedNumberField(alpha)[1] ge 0 then
      alpha := alpha;
    else
      alpha := -alpha;
    end if;
  else
    if EmbedNumberField(alpha)[1]*EmbedNumberField(eps)[1] ge 0 then
      alpha := alpha*eps;
    else
      alpha := -alpha*eps;
    end if;
  end if;
  return ZF!alpha;
end intrinsic;

intrinsic MinTraceAssociate(alpha::RngOrdElt) -> RngOrdElt
  {
	Input: F a totally real number field (currently just QQ(sqrt(5))), alpha an element of ZF
	Output: A totally nonnegative associate of alpha with minimal trace
  }
  F := Parent(alpha);
  ZF := Integers(F);
  e := FundamentalUnit(ZF);
  e_RR := EmbedNumberField(e);
  if alpha eq 0 then
    return 0;
  else
    alpha := TotallyPositiveAssociate(alpha);
    alpha_RR := EmbedNumberField(alpha);
    r := (1/4)*Log(alpha_RR[2]/alpha_RR[1])/Log(e_RR[1]);
    alpha_news := [e^(2*Floor(r))*alpha, e^(2*Ceiling(r))*alpha];
    traces := [Trace(a) : a in alpha_news];
    _, ind := Minimum(traces);
    return alpha_news[ind], Trace(alpha_news[ind]);
  end if;
end intrinsic;

intrinsic ShintaniGenerator(I::RngOrdIdl) -> RngOrdElt
  {
    Input: An ideal
    Output: The unique generator for I contained in the Shintani cone
  }
  bool, gen := IsPrincipal(I);
  assert bool eq true;
  gen_reduced := ReduceShintani(TotallyPositiveAssociate(gen));
  return gen_reduced;
end intrinsic;

intrinsic GetIndexPairs(M::ModFrmHilD) -> SeqEnum
  {returns list of [nu, [[nu1,nu2],...] ] such that nu1+nu2 = nu up to precision.}
  ZF := Integers(BaseField(M));
  HMFIndicesList := [];
  ideals := Ideals(M);
  gens := [ZF!ShintaniGenerator(I) : I in ideals];
  IndexList := [];
  T_lower := 0;
  for nu in gens do
    pairs_nu := [];
    T_upper := Ceiling(Trace(ZF!nu)/2);
    if T_upper gt T_lower then
      for T in [T_lower..T_upper] do
        IndexList := IndexList cat IndicesByTrace(ZF, T);
      end for;
      T_lower := T_upper;
    end if;
    for nu1 in IndexList do
      nu2 := nu - nu1;
      //if IsTotallyPositive(nu2) then
      if nu2 in IndexList then
        nu1_red := ReduceShintani(nu1);
        nu2_red := ReduceShintani(nu2);
        Append(~pairs_nu, [nu1_red, nu2_red]);
        if nu1 ne nu2 then // only computing up to half the trace, so have to append reverse pairs, too.  But if nu1 = nu2, don't append twice.
          Append(~pairs_nu, [nu2_red, nu1_red]);
        end if;
      end if;
    end for;
    Append(~HMFIndicesList, [* nu, pairs_nu *]);
  end for;
  return HMFIndicesList;
end intrinsic;
