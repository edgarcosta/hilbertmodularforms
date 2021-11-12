intrinsic Values(a::Assoc) -> List
  {return the values of an associative array}
  return [* a[k] : k in Keys(a) *];
end intrinsic;

intrinsic '+'(S::List, T::List) -> List
  {Concatenation of S and T}
  return S cat T;
end intrinsic;


intrinsic Product(list::List: empty:=1) -> Any
  {return the product of the elements of a list}
  res := empty;
  for x in list do
    res *:= x;
  end for;
  return res;
end intrinsic;

intrinsic Sum(list::List: empty:=0) -> Any
  {return the sum of the elements of a list}
  res := empty;
  for x in list do
    res +:= x;
  end for;
  return res;
end intrinsic;

intrinsic Sum(list::List, empty::Any) -> Any
  {return the sum of the elements of a list}
  return Sum(list: empty:=empty);
end intrinsic;

intrinsic 'eq'(a::Assoc, b::Assoc) -> BoolElt
  {return if two associative arrays are equal}
  if Universe(a) ne Universe(b) then
    return false;
  end if;
  ka := Keys(a);
  kb := Keys(b);
  if not ka cmpeq kb then
    return false;
  end if;
  for k in ka do
    if not a[k] cmpeq b[k] then
      return false;
    end if;
  end for;
  return true;
end intrinsic;


intrinsic IsEvenAtoo(chi:GrpHeckeElt) -> BoolElt
{return if the components of the Dirichlet restriction at the infinity places are all even}
  F := NumberField(Ring(Domain(Parent(chi))));
  return &and[IsEven(c[v]) : v in InfinitePlaces(F)] where c:=Components(chi);
end intrinsic;

intrinsic IsOddAtoo(chi:GrpHeckeElt) -> BoolElt
{return if the components of the Dirichlet restriction at the infinity places are all odd}
  F := NumberField(Ring(Domain(Parent(chi))));
  return &and[IsOdd(c[v]) : v in InfinitePlaces(F)] where c:=Components(chi);
end intrinsic;
