intrinsic QuadraticConjugate(elt::FldNumElt) -> FldNumElt
 {}
  if Type(elt) eq FldQuadElt then
    return Conjugate(elt);
  end if;
  F := Parent(elt);
  require Degree(F) eq 2: "only supports quadratic fields";
  G, _, mp := AutomorphismGroup(F);
  return mp(G.1)(elt);
end intrinsic;

intrinsic CanonicalCyclicShift(s::SeqEnum[RngIntElt]) -> SeqEnum[RngIntElt]
 { return the minimal lexicographic cyclic shift }
 if #s eq 0 then return s; end if;
 return Sort([s[k+1..#s] cat s[1..k] : k in [1..#s]])[1];
end intrinsic;

intrinsic Values(a::Assoc) -> List
  {Return the values of an associative array}
  return [* a[k] : k in Keys(a) *];
end intrinsic;

intrinsic '+'(S::List, T::List) -> List
  {Concatenation of S and T}
  return S cat T;
end intrinsic;

intrinsic Product(list::SeqEnum: empty:=1) -> Any
  {Return the product of the elements of a list}
  res := empty;
  for x in list do
    res *:= x;
  end for;
  return res;
end intrinsic;

intrinsic Product(list::List: empty:=1) -> Any
  {Return the product of the elements of a list}
  res := empty;
  for x in list do
    res *:= x;
  end for;
  return res;
end intrinsic;

intrinsic Sum(list::List: empty:=0) -> Any
  {Return the sum of the elements of a list}
  res := empty;
  for x in list do
    res +:= x;
  end for;
  return res;
end intrinsic;

intrinsic Sum(list::List, empty::Any) -> Any
  {Return the sum of the elements of a list}
  return Sum(list: empty:=empty);
end intrinsic;

intrinsic 'eq'(a::Assoc, b::Assoc) -> BoolElt
  {Return if two associative arrays are equal}
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




intrinsic IsEvenAtoo(chi::GrpHeckeElt) -> BoolElt
{Return if the components of the Dirichlet restriction at the infinity places are all even}
  F := NumberField(Ring(Domain(Parent(chi))));
  return &and[IsEven(c[v]) : v in InfinitePlaces(F)] where c:=Components(chi);
end intrinsic;

intrinsic IsOddAtoo(chi::GrpHeckeElt) -> BoolElt
{Return if the components of the Dirichlet restriction at the infinity places are all odd}
  F := NumberField(Ring(Domain(Parent(chi))));
  return &and[IsOdd(c[v]) : v in InfinitePlaces(F)] where c:=Components(chi);
end intrinsic;

intrinsic ElementToSequence(F::FldNum) -> SeqEnum[RngIntElt]
  {Return the sequence associated to the defining polynomial}
    return ElementToSequence(DefiningPolynomial(F));
end intrinsic;

intrinsic ElementToSequence(I::RngOrdIdl) -> SeqEnum[RngIntElt]
  {Return the sequence associated to the defining polynomial}
    return [ElementToSequence(g) : g in Generators(I)];
end intrinsic;

intrinsic ElementToSequence(SI::SetIndx[RngOrdIdl]) -> SeqEnum[SeqEnum[RngIntElt]]
  {Return the sequence associated to the defining polynomial}
    return [ElementToSequence(elt) : elt in SI];
end intrinsic;

intrinsic ElementToSequence(SI::SetIndx[FldNumElt]) -> SeqEnum[SeqEnum[RngIntElt]]
  {Return the sequence associated to the defining polynomial}
    return [ElementToSequence(elt) : elt in SI];
end intrinsic;

intrinsic ChangeRing(I::RngOrdIdl, m::Map) -> RngOrdIdl
  {Return the ideal over the codomain}
  return ideal<Integers(Codomain(m)) | [m(g): g in Generators(I)]>;
end intrinsic;






// IO


intrinsic ReadRecords(filename::MonStgElt : Delimiter:=":") -> SeqEnum
{Read a delimited file, return list of lists of strings (one list per line). }
    return [Split(r,Delimiter):r in Split(Read(filename))];
end intrinsic;


intrinsic WriteRecords(filename::MonStgElt, S::SeqEnum[SeqEnum[MonStgElt]]) -> RngIntElt
{Given a list of lists of strings, create a colon delimited file with one list per line, return number of records written. }
    fp := Open(filename,"w");
    n := 0;
    for r in S do Puts(fp,Join(r,":")); n+:=1; end for;
    Flush(fp);
    return n;
end intrinsic;


intrinsic Strip(X::MonStgElt) -> MonStgElt
{ Strip spaces and carraige returns from string; much faster than StripWhiteSpace. }
    return Join(Split(Join(Split(X," "),""),"\n"),"");
end intrinsic;


intrinsic StringToArrayOfIntegers(s::MonStgElt) -> SeqEnum[RngIntElt]
{ Given string representing a sequence of integers, returns the sequence (faster and safer than eval). }
    t := Strip(s);
    if t eq "[]" then return [Integers()|]; end if;
    assert #t ge 2 and t[1] eq "[" and t[#t] eq "]";
    return [Integers()|StringToInteger(n):n in Split(t[2..#t-1],",")];
end intrinsic;


intrinsic StringToArrayOfArraysOfIntegers(s::MonStgElt) -> SeqEnum[RngIntElt]
{ Converts a string to a sequence of sequences of integers. }
    t := Strip(s);
    if t eq "[]" then return []; end if;
    if t eq "[[]]" then return [[Integers()|]]; end if;
    assert #t gt 4 and t[1..2] eq "[[" and t[#t-1..#t] eq "]]";
    r := Split(t[2..#t-1],"[");
    return [[Integers()|StringToInteger(n):n in Split(a[1] eq "]" select "" else Split(a,"]")[1],",")]:a in r];
end intrinsic;

intrinsic StringToArrayOfArraysOfRationals(s::MonStgElt) -> SeqEnum[RngIntElt]
{ Converts a string to a sequence of sequences of integers. }
    t := Strip(s);
    if t eq "[]" then return []; end if;
    if t eq "[[]]" then return [[Integers()|]]; end if;
    assert #t gt 4 and t[1..2] eq "[[" and t[#t-1..#t] eq "]]";
    r := Split(t[2..#t-1],"[");
    return [[Rationals()|StringToRational(n): n in Split(a[1] eq "]" select "" else Split(a,"]")[1],",")]:a in r];
end intrinsic;

intrinsic JoinString(list::SeqEnum[MonStgElt], sep::MonStgElt) -> MonStgElt
  {The concatenation of the strings of list with seperator sep.}
  if IsEmpty(list) then return ""; end if;
  s:=list[1]; list:=list[2..#list];
  for i in list do
    s *:=sep*i;
  end for;
  return s;
end intrinsic;
