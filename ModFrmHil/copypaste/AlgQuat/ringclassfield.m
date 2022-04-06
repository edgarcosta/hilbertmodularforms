freeze;

//////////////////////////////////////////////////////////////////////////////
//
// Ring Class Fields
// November 2005, John Voight
//
//////////////////////////////////////////////////////////////////////////////

//-------------
//
// Algorithm to compute the ring class field and group of a quadratic 
// extension.
// 
// Let F be a number field with ring of integers Z_F.  The quadratic extensions
// K of F are in bijection with elements D in F^*/F^{*2}.
// A quadratic order over Z_F is an order in a quadratic extension of F
// (or, equivalently, a Z_F-algebra which is a domain and a projective 
// Z_F-module of rank 2).  Quadratic orders over Z_F are in bijection 
// with the set of orbits of
//    {D in Z_F : D is not a square, D is a square modulo 4Z_F} 
// under the action of multiplication by Z_F^{*2}.  Each such order
// is contained in a unique maximal order with fundamental discriminant d, 
// with D = df^2, with f in Z_F, and to each such d,f we have the order
//    O_D = Z_F + fZ_K.
// Note that as D is only well-defined up to an element of Z_F^{*2}, 
// f is well-defined up to Z_F^*, hence the ideal (f) = f*Z_F is
// well-defined.
//
// Let K be a quadratic extension of discriminant d.  The ring
// class group of K of conductor (f) is the class group of O_D, the order of
// discriminant D = df^2.  
//
//-------------

forward RingClassGroupInternal;

intrinsic RingClassGroup(K::FldNum, f::RngIntElt) -> GrpAb, Map
  {For K/F quadratic, and f an integer, return the ring class
   group of K of conductor f.}

  F := BaseField(K);
  if F eq Rationals() then
    Z_K := MaximalOrder(K);
    return RingClassGroupInternal(Z_K, Integers(), Z_K, Integers(), f);
  else
    Z_F := MaximalOrder(F);
    return RingClassGroup(K, ideal<Z_F | f>);
  end if;
end intrinsic;

intrinsic RingClassGroup(K::FldNum, f::RngOrdElt) -> GrpAb, Map
  {For K/F quadratic, and f integral in F, return the ring class
   group of K of conductor f.}

  Z_F := MaximalOrder(BaseField(K));
  return RingClassGroup(K, ideal<Z_F | f>);
end intrinsic;

intrinsic RingClassGroup(K::FldNum, f::RngOrdIdl) -> GrpAb, Map
  {For K/F quadratic, and (f) a principal ideal of F, 
   return the ring class group of K of conductor (f).}
  require Degree(K) eq 2 :
    "K must be a quadratic extension of its base field";
  F := BaseField(K);
  require FieldOfFractions(Order(f)) eq F :
    "f must be an ideal of the base field of K";
  bl, ff := IsPrincipal(f);
  require bl : "(f) must be a principal ideal";

  Z_F := MaximalOrder(F);
  Z_K := MaximalOrder(K);

  Z_Fabs := AbsoluteOrder(Z_F);
  Z_Kabs := AbsoluteOrder(Z_K);

  return RingClassGroupInternal(Z_K, Z_F, Z_Kabs, Z_Fabs, ff);
end intrinsic;

// All of the work is done here
RingClassGroupInternal := function(Z_K, Z_F, Z_Kabs, Z_Fabs, f);
  Z_Fmodf, mFf := quo<Z_Fabs | ideal<Z_Fabs | f>>;

  ClK, mK := ClassGroup(Z_Kabs);
  Z_Kstar, mKstar := UnitGroup(Z_Kabs);
  Z_Kmodf, mKf := quo<Z_Kabs | ideal<Z_Kabs | f>>;

  Z_Fmodfstar, mFfstar := UnitGroup(Z_Fmodf);
  Z_Kmodfstar, mKfstar := UnitGroup(Z_Kmodf);

  // We have an exact sequence
  //   1 -> (Z_K/fZ_K)^* / ( Z_K^* (Z_F/fZ_F)^* ) -> Cl(O_D) -> Cl(Z_K) -> 1
  G := Z_Kmodfstar;
  mG := mKfstar * Inverse(mKf);
  G, mH := quo<G | [Inverse(mKfstar)(mKf(mKstar(g))) : g in Generators(Z_Kstar)] cat
                   [Inverse(mKfstar)(mKf(mFfstar(g)@@mFf)) : g in Generators(Z_Fmodfstar)]>;
  mG := Inverse(mH) * mG;

  // "Split" the exact sequence
  ClODcontainer := AbelianGroup(Invariants(G) cat [0 : s in [1..#Generators(ClK)]]);
  GtoClODcontainer := hom<G -> ClODcontainer | [ClODcontainer.i : i in [1..#Generators(G)]]>;
  relations := [];
  for i := 1 to #Generators(ClK) do
    c := ClK.i;
    aa := mK(c)^Order(c);
    _, alpha := IsPrincipal(aa);
    g := GtoClODcontainer(Inverse(mG)(alpha));
    Append(~relations, Order(c)*ClODcontainer.(#Invariants(G)+i)-g);
  end for;

  ClOD, mOD := quo<ClODcontainer | relations>;

  Z_Kf := sub<Z_K | [f*Z_K.1, f*Z_K.2]>;

  // This would be better to compute "once and for all"
  phiMap := function(c);
    if c eq ClOD ! 0 then
      return ideal<Z_Kf | 1>;
    end if;
    cin := Eltseq(c@@mOD);
    if #Invariants(G) eq 0 then
      alpha := 1;
    else
      alpha := mG(G ! cin[1..#Invariants(G)]);
    end if;
    aa := mK(ClK ! cin[#Invariants(G)+1..#cin]);
    return (alpha*ideal<Z_K | aa>) meet Z_Kf;
  end function;

  phi := hom<ClOD -> Parent(ideal<Z_Kf | 1>) | c :-> phiMap(c)>;
  return ClOD, phi;
end function;  

