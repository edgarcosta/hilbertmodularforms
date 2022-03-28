freeze;

//////////////////////////////////////////////////////////////////////////////
//
// Unit Groups for Quaternion Algebras
// February-March 2006, John Voight
//
//////////////////////////////////////////////////////////////////////////////

debug := false; 

please_tell_us := 
"\n\nPLEASE SEND THIS EXAMPLE TO magma-bugs@maths.usyd.edu.au\n" *
"Helpful hint: type %P to see all commands executed in this Magma session";

//-------------
//
// Algorithms for unit groups in quaternion algebras over number fields.
//
//-------------

// Compute the set of cyclotomic extensions over F which are quadratic

intrinsic CyclotomicQuadraticExtensions(F::FldRat) -> SeqEnum
  {Sequence containing all prime powers m = p^e such that [F(zeta_m):F] <= 2}

  return [4, 3];
end intrinsic;

intrinsic CyclotomicQuadraticExtensions(F::FldAlg) -> SeqEnum
  {"} // "

  d := Degree(F);
  Z_F := Integers(F);

  // By a field diagram, we must have phi(p^e) divide 2d
  P := [p : p in [2..2*d+1] | IsPrime(p) and 2*d mod (p-1) eq 0];
  S := [p^(Valuation(2*d,p)+1) : p in P];

  function IsCycExtQuad(m);
    // Test the first few primes to rule out impossible ones
    // TO DO: get primes outside
    for q in [q : q in [1..100] | IsPrime(q) and Gcd(q,m) eq 1 and
                                  Valuation(Norm(Discriminant(Z_F)),q) eq 0] do
      qfacts := Decomposition(Z_F,q);
      for qq in qfacts do
        if Integers(m) ! AbsoluteNorm(qq[1]) notin [Integers(m) | -1,1] then
          return false;
        end if;
      end for;
    end for;
    return forall{f : f in Factorization(CyclotomicPolynomial(m), F) | Degree(f[1]) eq 2};
  end function;

  for i := 1 to #S do
    m := S[i];
    while m gt 1 and not IsCycExtQuad(m) do
      m div:= P[i];
    end while;
    S[i] := m;
  end for;

  return [m : m in S | m ne 1];
end intrinsic;

/* intrinsic UnitGroup(O::AlgAssVOrd[RngOrd]) -> GrpPerm, Map
  {Returns the group G which is the quotient of O^* by the group of units 
   of the base ring; also returns the map G -> O^*.}

  if assigned O`UnitGroup then
    require assigned O`UnitMap : "Order has a UnitGroup stored, but not a UnitMap";
    require Domain(O`UnitMap) eq O`UnitGroup : "Stored UnitGroup and UnitMap don't match";
    return O`UnitGroup, O`UnitMap;
  end if;

  require Type(Algebra(O)) eq AlgQuat : 
    "O must be an order in a quaternion algebra";
  Z_F := BaseRing(O);
  F := NumberField(Z_F);
  require IsDefinite(Algebra(O)) : 
    "A must be a totally definite quaternion algebra";

  d := Degree(F);
  // If O is definite, then F is totally real and the group of units is
  // an extension of Z_F^* by a finite group.
  // Since the norm form is positive definite, we can just exhaustively
  // list all elements with bounded (reduced) norm.

  U_F, fUF := UnitGroup(F);
  U_Fmodsq, fsq := quo<U_F | [2*u : u in Generators(U_F)]>;
  U_Fmodsq1 := [fUF(u@@fsq) : u in U_Fmodsq];
  U_Fmodsq1 := [u : u in U_Fmodsq1 | IsTotallyPositive(u)];
  U := [];
  for usq in U_Fmodsq1 do
    S := [u : u in Enumerate(O, Trace(usq), Trace(usq)) | IsUnit(Z_F!Norm(u))];
    U cat:= S;
  end for;
  // U cat:= [-u: u in U];

//  print PseudoBasis(O);
  for i := 1 to #U do
    U[i] /:= fUF(U_F![e div 2 : e in Eltseq(Norm(U[i])@@fUF)]);
  end for;
  U := SetToSequence(SequenceToSet(U));

  i := 1;
  while i lt #U do
    j := i+1;
    while j le #U do
      if IsScalar(U[j]/U[i]) then
        Remove(~U, j);
      else
        j +:= 1;
      end if;
    end while;
    i +:= 1;
  end while;
//  print #U, U;
  
  if debug then
    assert #U_Fmodsq eq 2^#InfinitePlaces(F);
    // make sure these are really units in O
    for u in U do assert IsCoercible(O,1/u); end for;
    // double-check independence modulo scalars
    for i := 1 to #U do for j := i+1 to #U do 
      assert not IsCoercible(BaseRing(O),O!(U[i]/U[j])); end for; end for;
  end if;
    
  if d le 2 then 
    require #U in {1,2,3,4,6,8,12,24,60} : 
            "Error in unit computation" * please_tell_us; // SRD, 24-08-07
  end if;
  // TO DO: what's the correct list of possibilities for #U in general?

  G := Sym(#U);
  M := [];
  for u in U do
    perm := [];
    for v in U do
      Nuv := Norm(u*v);
//      if fsq((Nuv)@@fUF) eq U_Fmodsq!0 then
        Nuvsqrt := fUF(U_F![e div 2 : e in Eltseq(Nuv@@fUF)]);
//      end if;
      indu := Index(U, (u*v)/Nuvsqrt);
      if indu eq 0 then
        indu := Index(U, -(u*v)/Nuvsqrt);
      end if;
      assert indu ne 0;
      Append(~perm, indu);
      /*
      if indu eq 0 then
        Append(~perm, Index(U, -(u*v)/Nuvsqrt));
      else
        Append(~perm, Index(U, (u*v)/Nuvsqrt));
      end if;
      */ /*
    end for;
//    print perm;
    Append(~M, G!perm);
  end for;
  H := sub<G | M>;
  require #H eq #U : "Bad symmetric representation of units" * please_tell_us;
//  HPC, gpc := PCGroup(H);
//  phi := map<HPC -> O | h :-> U[Index(M,h@@gpc)], u :-> gpc(G!M[Index(U,u)])>;
  phi := map<H -> O | h :-> U[Index(M,h)], u :-> G!M[Index(U,u)]>;
//    return HPC, phi;
  
  O`UnitGroup := H;
  O`UnitMap := phi;
  return H, phi;
end intrinsic;	*/

intrinsic Units(O::AlgAssVOrd) -> SeqEnum
  {Returns the sequence of units of O.}

  U, phi := UnitGroup(O);
  return [phi(u) : u in U];
end intrinsic;

intrinsic NormOneSubgroup(f::Map) -> Grp, Map
  {Returns the norm one subgroup of the unit group O^*, represented by the 
   map G -> O^*.}

  require BaseRing(Codomain(f)) cmpeq Integers() : 
    "The argument should be a map returned by UnitGroup for a quaternion order over Z";

  G := Domain(f);
  G1 := [];
  for g in G do
    if Norm(f(g)) eq 1 then
      Append(~G1, g);
    end if;
  end for;
  G1, mG1 := sub<G | G1>;
  return G1, mG1*f;
end intrinsic;

intrinsic IsUnit(a::AlgAssVOrdElt) -> BoolElt
  {Returns true iff a is a unit (considered as an element of its parent order).}

  Na := Norm(a);
  Z_F := BaseRing(Parent(a));
  return IsUnit(Z_F!Na);
end intrinsic;
