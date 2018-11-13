intrinsic ShintaniCone(bb::RngOrdFracIdl, t::RngIntElt, lower::RngIntElt, upper::RngIntElt) -> SeqEnum[RngOrdFracIdl]
  {}
  F := NumberField(Parent(Order(bb).1));
  basis := Basis(bb);
  eps := FundamentalUnit(F);
  if not IsTotallyPositive(eps) then
    eps := eps^2;
  end if;
end intrinsic;
