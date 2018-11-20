intrinsic ShintaniWalls(bb::RngOrdFracIdl) -> Any
  {returns lower, upper}
  F := NumberField(Parent(Order(bb).1));
  assert Degree(F) le 2;
  places := InfinitePlaces(F);
  eps := FundamentalUnit(F);
  if not IsTotallyPositive(eps) then
    eps := eps^2;
  end if;
  eps1 := Evaluate(eps, places[1]);
  eps2 := Evaluate(eps, places[2]);
  if eps1/eps2 le eps2/eps1 then
    return Sqrt(eps1/eps2), Sqrt(eps2/eps1);
  else
    return Sqrt(eps2/eps1), Sqrt(eps1/eps2);
  end if;
end intrinsic;

// TODO
intrinsic ShintaniCone(bb::RngOrdFracIdl, t::RngIntElt) -> SeqEnum[RngOrdFracIdl]
  {Given bb and element of the narrow class group, t a trace, }
  F := NumberField(Parent(Order(bb).1));
  basis := Basis(bb);
end intrinsic;

// TODO
intrinsic ShintaniCone(bb::RngOrdFracIdl, t::RngIntElt) -> Any
  {returns all totally positive elements in the shintani cone for bb up to trace t}
end intrinsic;
