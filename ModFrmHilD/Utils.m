intrinsic Values(a::Assoc) -> List
  {return the values of an associative array}
  return [* a[k] : k in Keys(a) *];
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
