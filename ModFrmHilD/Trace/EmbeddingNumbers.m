declare attributes FldNum: EmbeddingNumberCache, LocalSquareCache;

function local_square(F, d, pp)
  if not assigned F`LocalSquareCache then
    F`LocalSquareCache := AssociativeArray();
  end if;
  key := <F!d, pp>;
  if not IsDefined(F`LocalSquareCache, key) then
    F`LocalSquareCache[key] := IsLocalSquare(d, pp) select 1 else -1;
  end if;
  return F`LocalSquareCache[key];
end function;

function fast_artin_symbol(F, D, pp, DD)
  if Valuation(DD, pp) gt 0 then
    return 0;
  elif local_square(F, D, pp) eq 1 then
    return 1;
  else
    return -1;
  end if;
end function;

function class_number_over_unit_index(F, K)
  UF, mUF := UnitGroup(F);
  Kabs := AbsoluteField(K);
  ZKabs := Integers(Kabs);
  UK, mUK := UnitGroup(ZKabs);
  _, mKabstoK := IsIsomorphic(Kabs, K);
  hK := ClassNumber(Kabs);
  UnitIndex := 2 * #quo<UK | [(mKabstoK(mUF(u)))@@mUK : u in Generators(UF)]>;
  return hK / UnitIndex;
end function;

intrinsic EmbeddingNumberOverUnitIndex(F::FldNum, D::RngOrdElt, level::RngOrdIdl,
  diamond_ideal::RngOrdIdl) -> FldRatElt
  {The unit-normalized Eichler embedding count for the CM order discriminant D over
  totally real F, with level and diamond ideal diamond_ideal. D is totally negative in
  Integers(F); level and diamond_ideal are nonzero ideals of Integers(F).
  See also OptimalEmbeddings}
  ZF := Integers(F);
  require IsTotallyReal(F) and Parent(D) eq ZF and IsTotallyPositive(-D) :
    "D must be a totally negative element of the integers of a totally real F";
  require Order(diamond_ideal) eq ZF and not IsZero(diamond_ideal) :
    "diamond_ideal must be a nonzero ideal of the integers of F";
  require Order(level) eq ZF and not IsZero(level) :
    "level must be a nonzero ideal of the integers of F";
  if not assigned F`EmbeddingNumberCache then
    F`EmbeddingNumberCache := AssociativeArray();
  end if;
  key := <F!D, level, diamond_ideal>;
  if IsDefined(F`EmbeddingNumberCache, key) then
    return F`EmbeddingNumberCache[key];
  end if;
  FactNN := Factorization(level);
  _<x> := PolynomialRing(ZF);
  K := ext<F | x^2 - D>;
  ZK := Integers(K);
  DD := Discriminant(ZK);
  ff := Sqrt((D*ZF)/DD);
  require IsIntegral(ff) : "D must be a quadratic-order discriminant over F";
  hw := class_number_over_unit_index(F, K);

  conductorsum := 0;
  if ff subset diamond_ideal then
    conductorsum := &+[Rationals() | Norm(bb) * euler_factor * level_factor
      where level_factor := &*[Rationals() | OptimalEmbeddings(e, 2*f, g, A, pp)
        where A := (g eq 0) select local_square(F, D, pp) else 0
        where g := Valuation(DD, pp)
        where f := Valuation(bb, pp)
        where e := pair[2]
        where pp := pair[1] : pair in FactNN]
      where euler_factor := &*[Rationals() |
        1 - fast_artin_symbol(F, D, pp[1], DD) / Norm(pp[1]) : pp in Factorization(bb)]
      : bb in Divisors(ideal<ZF | ff * diamond_ideal^(-1)>)];
  end if;

  embeds := hw * conductorsum;

  F`EmbeddingNumberCache[key] := embeds;
  return embeds;
end intrinsic;

function optimal_embeddings_odd(e, f, g, A, pp)
  q := Norm(pp);

  if f + g ge e then
    N := q^(Floor(e/2));
  else
    N := q^(ExactQuotient(f, 2)) * A * (1 + A);
  end if;
  return N;
end function;

function optimal_embeddings_even(e, f, g, A, pp)
  q := Norm(pp);
  ZF := Order(pp);
  v := Valuation(2*ZF, pp);

  if g + f ge (e + 2*v) then
    N := q^(Floor(e/2));
  else
    if IsOdd(g) then
      N := 0;
    else
      if e le (f + 1 - A^2) then
        N := q^(Floor(e/2));
      else
        N := q^(ExactQuotient(f, 2)) * A * (1 + A);
      end if;
    end if;
  end if;
  return N;
end function;

intrinsic OptimalEmbeddings(level_exponent::RngIntElt, twice_conductor_exponent::RngIntElt,
  discriminant_exponent::RngIntElt, artin_symbol::RngIntElt, pp::RngOrdIdl) -> RngIntElt
  {The local optimal-embedding factor at the prime ideal pp with level exponent
  level_exponent > 0, twice the conductor exponent twice_conductor_exponent >= 0,
  maximal-order discriminant exponent discriminant_exponent >= 0 and Artin symbol
  artin_symbol equal to -1, 0 or 1. See also EmbeddingNumberOverUnitIndex}

  q := Norm(pp);

  if IsOdd(q) then
    N := optimal_embeddings_odd(level_exponent, twice_conductor_exponent, discriminant_exponent,
      artin_symbol, pp);
    if twice_conductor_exponent ne 0 then
      N +:= ExactQuotient(optimal_embeddings_odd(level_exponent + 1, twice_conductor_exponent,
        discriminant_exponent, artin_symbol, pp), q);
    end if;
  else
    N := optimal_embeddings_even(level_exponent, twice_conductor_exponent, discriminant_exponent,
      artin_symbol, pp);
    if twice_conductor_exponent + discriminant_exponent ne 0 then
      N +:= ExactQuotient(optimal_embeddings_even(level_exponent + 1, twice_conductor_exponent,
        discriminant_exponent, artin_symbol, pp), q);
    end if;
  end if;
  return N;
end intrinsic;
