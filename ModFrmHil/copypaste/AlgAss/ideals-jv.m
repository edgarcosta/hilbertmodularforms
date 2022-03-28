freeze;

//////////////////////////////////////////////////////////////////////////////
//
// Ideals of orders
// November 2005-April 2006, Claus Fieker, Nicole Sutherland, 
// and John Voight
//
// Substantially rewritten by Steve Donnelly
// 
// Last modified: October 2010
//
//////////////////////////////////////////////////////////////////////////////

declare attributes RngOrd : TotallyPositiveUnits;

// Data can be stored on AlgAssVOrdIdl's by attaching a record of this format
// as I`PackageAttributes (the type does not support package attributes directly)

AlgAssVOrdIdlData := recformat< 
   Jprimes:List               // list of tuples <JJ,b,n> containing output of Jprime
                              >;

debug := false;  

please_tell_us :=
"\n\n  PLEASE SEND THIS EXAMPLE TO magma-bugs@maths.usyd.edu.au \n" *
"  Hints: Type %P to see all commands executed in this Magma session \n" *
"         To write them to a file, first SetOutputFile(\"file_name\"); \n";

import "../AlgQuat/enumerate.m" : EnumerateInternal, EnumerativeSearchUntilSuccess,
                                  EnumerateInternalFromBasis, ReducedBasisInternal;
import "enum.m" : RightIdealClassesAndOrders, rids_record, TraceFormsOnQBasis;

forward ColonInternal;

/////////////////////////////////////////////////////////////////////////////////////////

// Analog of IsPrincipal for number fields:

intrinsic IsNarrowlyPrincipal(I::RngOrdFracIdl : real_places:=0, UnitRealValuations:=<>) -> BoolElt, FldOrdElt
{Given an ideal I in a totally real number field, returns true iff I is principal 
 with a totally positive generator (and also returns the generator in that case)}
  F := NumberField(Order(I));
  bool, g := IsPrincipal(I);
  if not bool then return false, _; end if;
  if real_places cmpeq 0 then real_places := RealPlaces(F); end if;
  sgns := RealSigns( F!g : real_places:=real_places);
  if &or [s lt 0 : s in sgns] then
    u := RealWeakApproximation(real_places, sgns : UnitOnly, UnitRealValuations:=UnitRealValuations);
    if u cmpeq false then return false, _; end if;
    g *:= u;
  end if;
  return true, g;
end intrinsic;

//-------------
//
// Basic algorithms for ideals.
//
//-------------

intrinsic IsTwoSidedIdeal(I::AlgAssVOrdIdl) -> BoolElt
  {Returns true iff I is equipped with the structure of a two-sided ideal.}

//return IsLeftIdeal(I) and IsRightIdeal(I) and (LeftOrder(I) eq RightOrder(I));
  return IsLeftIdeal(I) and IsRightIdeal(I); 
end intrinsic;

intrinsic Algebra(I::AlgAssVOrdIdl) -> AlgAssV
  {Returns the container algebra.}

  return Algebra(Order(I));
end intrinsic;

intrinsic Conjugate(I::AlgAssVOrdIdl[RngOrd]) -> AlgAssVOrdIdl
  {Returns the conjugate of I.}

  B := Basis(I);
  O := Order(I);
  A := Algebra(O);

  require Type(A) eq AlgQuat : "The ideal must come from a quaternion order.";

  P := PseudoMatrix(I);
  try
    Pconj := PseudoMatrix(CoefficientIdeals(P), Matrix([Eltseq(O!Conjugate(b)) : b in B]));
  catch err  // Conjugate(b) might not be coercible to O ... lazy fix, just get Z-basis:
    Pconj := [Conjugate(b) : b in ZBasis(I)];
  end try;
  if IsLeftIdeal(I) and IsRightIdeal(I) then
    Iconj := ideal<O | Pconj : Check:=debug>;
  elif IsLeftIdeal(I) then
    Iconj := rideal<O | Pconj : Check:=debug>;
  elif IsRightIdeal(I) then
    Iconj := lideal<O | Pconj : Check:=debug>;
  else
    error "Ideal is not a two-sided, left, or right ideal";
  end if;
  if assigned I`RightOrder then Iconj`LeftOrder := I`RightOrder; end if;
  if assigned I`LeftOrder then Iconj`RightOrder := I`LeftOrder; end if;
  if assigned I`Norm then Iconj`Norm := I`Norm; end if;
  return Iconj;
end intrinsic;

intrinsic LeftInverse(I::AlgAssVOrdIdl[RngOrd]) -> AlgAssVOrdIdl
  {Returns the inverse (fractional) ideal to I.}

  Ibar := Conjugate(I);
  ORN := ideal<RightOrder(I) | Generators(Norm(I)^(-1))>;
  L := ORN*Ibar;
  return L;
end intrinsic;

intrinsic RightInverse(I::AlgAssVOrdIdl[RngOrd]) -> AlgAssVOrdIdl
  {Returns the inverse (fractional) ideal to I.}

  Ibar := Conjugate(I);
  ORN := ideal<LeftOrder(I) | Generators(Norm(I)^(-1))>;
  _, R := Ibar*ORN;
  return R;
end intrinsic;

intrinsic PseudoBasis(I::AlgAssVOrdIdl[RngOrd]) -> SeqEnum
  {Returns a pseudobasis of I.}
 
  C := CoefficientIdeals(PseudoMatrix(I));
  B := [<C[i], Ba[i]> : i in [1..#C]] where Ba := Basis(I);
  return B;
end intrinsic;

intrinsic PseudoBasis(I::AlgAssVOrdIdl[RngOrd], R::Str) -> SeqEnum
  {Returns a pseudo basis for I over R.}

  B := Basis(I);
  ok, B := CanChangeUniverse(B, R);
  require ok : "Basis is not coercible over the structure";
  C := CoefficientIdeals(PseudoMatrix(I));
  return [<C[i], B[i]> : i in [1 .. #C]];
end intrinsic;

intrinsic PseudoMatrix(I::AlgAssVOrdIdl[RngOrd], R::Str) -> PMat
{Returns a pseudomatrix for I with respect to the basis of R}

  B := PseudoBasis(I);
  b := [B[i][2] : i in [1 .. #B]];
  ok, b := CanChangeUniverse(b, R);
  require ok : "Basis is not coercible over the structure";
  return PseudoMatrix([B[i][1] : i in [1 .. #B]], Matrix(b));
end intrinsic;

intrinsic Generators(I:: AlgAssVOrdIdl) -> SeqEnum
  {A sequence of generators for the ideal I as a module over its base ring}
  if Type(I) eq AlgQuatOrdIdl then return Basis(I); end if;
  return [p[2] * x: x in Generators(p[1]), p in PseudoBasis(I)];
end intrinsic;

function _LocalBasis(M, p, Type)
  if Type eq "" then
    pi:= UniformizingElement(p);
  end if;
  B:= [ ];
  P:= PseudoBasis(M);
  for i in [1..#P] do
    I:= P[i,1];
    g:= Generators(I);
    if #g eq 1 then x:= g[1];
    elif Type eq "" then x:= pi^Valuation(I, p);
    else
      Fact:= Factorization(I);
      Fact:= Type eq "Submodule" select [ f: f in Fact | f[1] eq p or f[2] gt 0 ]
                                   else [ f: f in Fact | f[1] eq p or f[2] lt 0 ];
      if forall{ f: f in Fact | f[1] ne p } then Append(~Fact, <p, 0>); end if;
      x:= WeakApproximation([ f[1] : f in Fact ], [ f[2] : f in Fact ]);
    end if;
    assert Valuation(x, p) eq Valuation(I, p);
    Append(~B, x*P[i,2]);
  end for;
  return B;
end function;

intrinsic LocalBasis(M::AlgAssVOrdIdl[RngOrd], p::RngOrdIdl : Type:= "") -> []
{A basis of a free module that coincides with M at the prime ideal p}
  require Order(p) cmpeq BaseRing(M) : "Incompatible arguments";
  require IsPrime(p) : "The ideal must be prime.";
  require Type in {"", "Submodule", "Supermodule"} : "Type must be \"Submodule\" or \"Supermodule\" when specified";
  return _LocalBasis(M, p, Type);
end intrinsic;

// TO DO: ridiculous

intrinsic Norm(I::AlgAssVOrdIdl[RngOrd]) -> RngOrdFracIdl
  {The norm of the ideal I.}

  if assigned I`Norm then return I`Norm; end if;

  O := Order(I);
  A := Algebra(O);
  n := Degree(O);
  B := PseudoBasis(I);

  M := Matrix(#B, [Trace(B[i,2]*B[j,2]) : i,j in [1..n]]);
  d := Determinant(M);
  Z_F := BaseRing(O);

  if Type(A) eq AlgQuat then
    N := SquareRoot(ideal<Z_F | d>)*( &*[ B[i][1] : i in [1..n]] )/
                                                Discriminant(LeftOrder(I));
    N := SquareRoot(N);
  else
    N := d*(&*[ B[i][1] : i in [1..n]])^2/Discriminant(Order(I));
  end if;
  I`Norm := N;
  return N;
end intrinsic;

// TO DO: in C
intrinsic IsIntegral(x::FldFunRatUElt) -> BoolElt
{Returns true iff x is integral}
  return Denominator(x) eq 1;
end intrinsic;

intrinsic 'in'(a::RngElt, I::AlgAssVOrdIdl) -> BoolElt
  {Return true iff a is in I. Here I must be an ideal (or fractional ideal) of an order 
   in an associative algebra.}

  A:= Algebra(I);
  bool, a := IsCoercible(A, a);
  require bool : "The given element must be coercible to the algebra of the ideal";
  matrix:= Matrix(Basis(I, A));
  ans, coords := IsConsistent(matrix, Vector(a));
  assert ans;
  if Type(I) eq AlgQuatOrdIdl then
    ans:= forall{ i: i in [1..4] | IsIntegral(coords[i]) };
  else
    ideals:= CoefficientIdeals( PseudoMatrix(I) );
    ans:= forall{ i: i in [1..#ideals] | coords[i] in ideals[i] };
  end if;

  if debug then 
    // some of this takes a LOT of time
    a_ideal := IsLeftIdeal(I) select lideal<Order(I) | a> 
                               else  rideal<Order(I) | a>;
    I_plus_a := I + a_ideal;
    CheckIdeal(I_plus_a : Use_in:=false); 
    assert ans eq IdealsAreEqual(I, I_plus_a : Use_in:=false);
  end if;
  return ans;
end intrinsic;

intrinsic 'subset'(I::AlgAssVOrdIdl, J::AlgAssVOrdIdl) -> BoolElt
  {Return true if I is a subset of J}

  require Algebra(I) eq Algebra(J) : "Ideals must come from the same order";

  if debug then 
    IinJ := &and[ Algebra(J)!ii in J : ii in ZBasis(I)];
    IplusJ := I + J;
    assert IinJ eq  IdealsAreEqual(J, IplusJ); 
  end if;

  return J eq I + J;
end intrinsic;

intrinsic RandomRightIdeal(O::AlgAssVOrd) -> AlgAssVOrdIdl
  {Returns a random (small coefficient) right ideal of O.}

  repeat mu := Random(O); until Norm(mu) ne 0;
  T := TrialDivision(Integers()!Norm(Norm(mu)));
  if #T ne 0 then
    return rideal<O | [T[1][1], mu]>;
  else
    return rideal<O | mu>;
  end if;
end intrinsic;

//-------------
//
// Multiplication for ideals.
//
//-------------

intrinsic '/'(I::AlgAssVOrdIdl[RngOrd], x::RngElt) -> AlgAssVOrdIdl
  {Returns the quotient I*(1/x).}

  return I*(1/x);
end intrinsic;

intrinsic '*'(I::AlgAssVOrdIdl[RngOrd], J::AlgAssVOrdIdl[RngOrd] : Check:=true, Sides:="Both") -> 
     AlgAssVOrdIdl, AlgAssVOrdIdl
  {Product of ideals I and J. Returns two objects by default: firstly I*J as a left ideal,
   and secondly I*J as a right ideal.  When "Sides" is set to "Left" or "Right", only one 
   of these is returned}

  // When I is officially a left ideal (of Order(I)), the left ideal I*J is created 
  // as a lideal of Order(I), and otherwise as a lideal of LeftOrder(I).  
  // Likewise for the right I*J.

  if Check then
    require RightOrder(I) cmpeq LeftOrder(J) : 
      "Right order of the first argument must be equal to the left order of the second";
  end if;
  require Algebra(Order(I)) cmpeq Algebra(Order(J)) : 
    "Arguments must be ideals of orders in the same algebra";
  require Sides in {"Left", "Right", "Both"} : 
    "The optional argument \"Sides\" should be \"Left\", \"Right\" or \"Both\"";

  // Compute P = pmatrix of I*J, expressed relative to the basis of A
  O := Order(I);
  A := Algebra(O);
  S := [x*y : x in Basis(I, A), y in Basis(J, A)];
  CI := CoefficientIdeals(PseudoMatrix(I));
  CJ := CoefficientIdeals(PseudoMatrix(J));
  C := [ci*cj : ci in CI, cj in CJ];
  P := PseudoMatrix(C, Matrix(S));
  P := HermiteForm(P);

  // If I and J are both officially 2-sided ideals of O, return the same object for left and right
  if Sides ne "Right" and IsTwoSidedIdeal(I) and IsTwoSidedIdeal(J) and O eq Order(J) then
    // Get P relative to the basis of O, since the ideal constructor expects this
    P := PseudoMatrix(CoefficientIdeals(P), Matrix(P) * Matrix(PseudoMatrix(O))^-1 );
    IJ := ideal<O | P : Check:=debug>;
    if assigned I`LeftOrder then IJ`LeftOrder := I`LeftOrder; end if;
    if assigned J`RightOrder then IJ`RightOrder := J`RightOrder; end if;
    if assigned I`Norm and assigned J`Norm then IJ`Norm := I`Norm*J`Norm; end if;
    return IJ, IJ;
  end if;

  // Set up left ideal I*J
  if Sides ne "Right" then
    OL := IsLeftIdeal(I) select Order(I) 
                          else  LeftOrder(I);
    PL := PseudoMatrix(CoefficientIdeals(P), Matrix(P) * Matrix(PseudoMatrix(OL))^-1 );
    IJleft := lideal< OL | PL : Check:=debug >;
    if assigned I`LeftOrder then IJleft`LeftOrder := I`LeftOrder; end if;
    if assigned J`RightOrder then IJleft`RightOrder := J`RightOrder; end if;
    if assigned I`Norm and assigned J`Norm then IJleft`Norm := I`Norm*J`Norm; end if;
  end if;

  // Set up right ideal I*J
  // TO DO: we could take PR:=PL when IsIdentical(OL,OR), or when they have the same basis
  if Sides ne "Left" then
    OR := IsRightIdeal(J) select Order(J) 
                           else  RightOrder(J);
    PR := PseudoMatrix(CoefficientIdeals(P), Matrix(P) * Matrix(PseudoMatrix(OR))^-1 );
    IJright := rideal< OR | PR : Check:=debug >;
    if assigned I`LeftOrder then IJright`LeftOrder := I`LeftOrder; end if;
    if assigned J`RightOrder then IJright`RightOrder := J`RightOrder; end if;
    if assigned I`Norm and assigned J`Norm then IJright`Norm := I`Norm*J`Norm; end if;
  end if;

  if Sides eq "Left" then 
    return IJleft;
  elif Sides eq "Right" then 
    return IJright;
  elif Sides eq "Both" then 
    return IJleft, IJright;
  end if;
end intrinsic;

intrinsic '*'(a::RngElt, I::AlgAssVOrdIdl[RngOrd]) -> AlgAssVOrdIdl
  {Product of (fractional) ideals of an order in an associative algebra}

  O := Order(I);
  A := Algebra(O);
  bl, aa := IsCoercible(A, a);
  require bl : "Argument must be coercible into the algebra of the ideal";

  scalar, s := IsCoercible(BaseRing(A), aa);
  central := scalar or IsCentral(aa);
  require IsRightIdeal(I) or central : 
         "a*I does not make sense for left ideal I and non-central element a";

  if scalar then 
    C := [ s*CI : CI in CoefficientIdeals(PseudoMatrix(I)) ];
    M := Matrix(PseudoMatrix(I));
    P := PseudoMatrix(C, M);
  else
    // need matrix relative to Basis(O) for ideal constructor, but elements are in A not O
    C := CoefficientIdeals(PseudoMatrix(I));
    M := Matrix([Eltseq(A!(aa*b)) : b in Basis(I)]) * Matrix(PseudoMatrix(O))^(-1);
    P := HermiteForm(PseudoMatrix(C, M));
  end if;
  if IsTwoSidedIdeal(I) and central then
    aI := ideal<O | P : Check:=debug>;
  elif IsLeftIdeal(I) and central then
    aI := lideal<O | P : Check:=debug>;
  else
    aI := rideal<O | P : Check:=debug>;
  end if;

  if assigned I`RightOrder then 
    aI`RightOrder := I`RightOrder; 
  end if;
  if assigned I`LeftOrder then 
    bool, ai := IsInvertible(aa);
    if bool then
      aI`LeftOrder := (I`LeftOrder)^ai;
    end if;
  end if;
  if assigned I`Norm then 
    aI`Norm := Norm(aa)*I`Norm; 
  end if;

  return aI;
end intrinsic;

intrinsic '*'(I::AlgAssVOrdIdl[RngOrd], a::RngElt) -> AlgAssVOrdIdl
  {"} // "

  O := Order(I);
  A := Algebra(O);
  bl, aa := IsCoercible(A, a);
  require bl : "Argument must be coercible into the algebra of the ideal";

  scalar, s := IsCoercible(BaseRing(A), aa);
  central := scalar or IsCentral(aa);
  require IsLeftIdeal(I) or central : 
         "I*a does not make sense for right ideal I and non-central element a";
  
  if scalar then 
    if false and IsZero(s) then
	P := PseudoMatrix([], RowSubmatrix(Matrix(PseudoMatrix(I)), 0));
    else
	C := [ s*CI : CI in CoefficientIdeals(PseudoMatrix(I)) ];
	M := Matrix(PseudoMatrix(I));
	P := PseudoMatrix(C, M);
    end if;
  else

    // need matrix relative to Basis(O) for ideal constructor, but elements are in A not O
    C := CoefficientIdeals(PseudoMatrix(I));
    M := Matrix([Eltseq(A!(b*aa)) : b in Basis(I)]) * Matrix(PseudoMatrix(O))^(-1);
    P := HermiteForm(PseudoMatrix(C, M));
  end if;
  if IsTwoSidedIdeal(I) and central then
    Ia := ideal<O | P : Check:=debug>;
  elif IsRightIdeal(I) and central then
    Ia := rideal<O | P : Check:=debug>;
  else
    Ia := lideal<O | P : Check:=debug>;
  end if;

  if assigned I`LeftOrder then 
    Ia`LeftOrder := I`LeftOrder; 
  end if;
  if assigned I`RightOrder then 
    bool := IsInvertible(a);
    if bool then
      Ia`RightOrder := (I`RightOrder)^aa; 
    end if;
  end if;
  if assigned I`Norm then 
    Ia`Norm := Norm(aa)*I`Norm; 
  end if;

  return Ia;
end intrinsic;

intrinsic IsCentral(a::AlgAssVElt) -> BoolElt
{True iff the element a of an associative algebra A belongs to the center of A}
  A := Parent(a);
  if ISA(Type(A),AlgQuat) then 
     return IsScalar(a);
  else
     return a in Center(A);
  end if;
end intrinsic;

intrinsic IsCentral(a::AlgAssVOrdElt) -> BoolElt
{True iff the element a of an associative order O belongs to the center of O}
  return IsCentral(Algebra(Parent(a))!a);
end intrinsic;

//-------------
//
// Algorithms for left and right orders, colon ideals.
//
//-------------

procedure DebugColon(I, J, IcolonJ, A, isLeft, isRight)
  CheckIdeal(I);  CheckIdeal(J);
  if isLeft then
    assert &and[ jj*xx in I : xx in ZBasis(IcolonJ,A), jj in ZBasis(J)];
    ROI := RightOrder(I);  ROJ := RightOrder(J);

    rcolon_ideal := rideal< ROI | ZBasis(IcolonJ,A) >;  CheckIdeal(rcolon_ideal);
    assert &and[ jj*xx in I : xx in ZBasis(rcolon_ideal), jj in ZBasis(J)];
    if IsMaximal(ROI) then assert RightOrder(rcolon_ideal) eq ROI; end if;
    if IsMaximal(ROJ) then assert LeftOrder(rcolon_ideal) eq ROJ; end if;
    
    lcolon_ideal := lideal< ROJ | ZBasis(IcolonJ,A) >;  CheckIdeal(lcolon_ideal);
    assert &and[ jj*xx in I : xx in ZBasis(lcolon_ideal), jj in ZBasis(J)];
    if IsMaximal(ROI) then assert RightOrder(lcolon_ideal) eq ROI; end if;
    if IsMaximal(ROJ) then assert LeftOrder(lcolon_ideal) eq ROJ; end if;
  elif isRight then
    assert &and[ xx*jj in I : xx in ZBasis(IcolonJ,A), jj in ZBasis(J)];
    LOI := LeftOrder(I);  LOJ := LeftOrder(J);

    lcolon_ideal := lideal< LOI | ZBasis(IcolonJ,A) >;  CheckIdeal(lcolon_ideal);
    assert &and[ xx*jj in I : xx in ZBasis(lcolon_ideal), jj in ZBasis(J)];
    if IsMaximal(LOI) then assert LeftOrder(lcolon_ideal) eq LOI; end if; 
    if IsMaximal(LOJ) then assert RightOrder(lcolon_ideal) eq LOJ; end if;
    
    rcolon_ideal := rideal< LOJ | ZBasis(IcolonJ,A) >;  CheckIdeal(rcolon_ideal);
    assert &and[ xx*jj in I : xx in ZBasis(rcolon_ideal), jj in ZBasis(J)];
    if IsMaximal(LOI) then assert LeftOrder(rcolon_ideal) eq LOI; end if; 
    if IsMaximal(LOJ) then assert RightOrder(rcolon_ideal) eq LOJ; end if;
  end if; 
end procedure;

// If PI, PJ are pseudomatrices with respect to the algebra A, 
// representing lattices I, J, compute the colon
//   (I:J) = {x in A : x*J in I} 
// (if isLeft, otherwise swap).  Returns a pseudomatrix.

function ColonInternal(PI, PJ, A, isLeft : Hermite:=true);
  CI := CoefficientIdeals(PI);
  CJ := CoefficientIdeals(PJ);
  Si := Matrix(PI)^(-1);

  n := Nrows(Si);

  F := BaseField(A);
  M := Matrix(F,0,n, []);
  C := [];
  BJ := Matrix(PJ);
  for i in [1..n] do
    b := A!BJ[i];
    if isLeft then
      m := Transpose(RepresentationMatrix(b : Side := "Right")*Si);
    else
      m := Transpose(RepresentationMatrix(b : Side := "Left")*Si);
    end if;
    M := VerticalJoin(M, m);
    C cat:= [CJ[i]/c : c in CI];
  end for;

  P := HermiteForm(PseudoMatrix(C, M));
  C := CoefficientIdeals(P);
  M := Transpose(Matrix(P))^(-1);

  P := PseudoMatrix([C[i]^(-1) : i in [1..n]], M);
  if Hermite then P := HermiteForm(P); end if;
  return P;
end function;

// TO DO: add ColonIdeal ... note that ideal<O | Colon(I,J)> would be WRONG
//                      (because the Colon is a PMat relative to Algebra(O))

// TO DO: Left/Right option in Colon, and fix description 

intrinsic Colon(I::AlgAssVOrdIdl[RngOrd], J::AlgAssVOrdIdl[RngOrd] : Verify := true) -> PMat
  {Returns the colon (I:J), defined as the set of x in A such that x*J is contained in I, 
   where I and J are both  left (or right) ideals of the same order O.  
   The output is a pseudomatrix with respect to the parent algebra A.}

  O := Order(I);
  A := Algebra(O);

  isLeft := IsLeftIdeal(I) and IsLeftIdeal(J);
  isRight := IsRightIdeal(I) and IsRightIdeal(J);
  
  // Don't need this (previously: if Veriry then check these conditions)
  // require Order(J) cmpeq O : "The given ideals must both be ideals of the same order";
  // require (isLeft or isRight) : "Ideals must both be left ideals or both right ideals";

  IcolonJ := ColonInternal(PseudoMatrix(I, A), PseudoMatrix(J, A), A, not isLeft);

  if debug then DebugColon(I, J, IcolonJ, A, isLeft, isRight); end if;
  return IcolonJ;
end intrinsic;

intrinsic LeftOrder(I::AlgAssVOrdIdl[RngOrd]) -> AlgAssVOrd
  {The left multiplicator order of I};

  if assigned I`LeftOrder then
    return I`LeftOrder;
  end if;

  OI := Order(I);

  if IsLeftIdeal(I) and assigned OI`IsMaximal and OI`IsMaximal then
    I`LeftOrder:= OI;
    return OI;
  end if;

  A := Algebra(OI);

  // Optional secondary algorithm for quaternion algebras
  // which seems to run slower in practice
  debug1 := false and debug;
  if debug1 then
    if Type(A) eq AlgQuat then
      n := Norm(I);
      B := Basis(I);
      CI := CoefficientIdeals(PseudoMatrix(I));
      O1 := Order([A!(B[i]*Conjugate(B[j])) : i,j in [1..4]], 
                  [CI[i]*CI[j]/n : i,j in [1..4]]);
    end if; 
  end if;

  PI := PseudoMatrix(I, A);
  PO := ColonInternal(PI, PI, A, true);
  O := Order(A, PO);
  
  if debug then
    CheckIdeal(I);
    CheckOrder(O);
  end if;
  if debug1 then assert O eq O1; end if;

  if assigned OI`ChangeRingMap then
    O`ChangeRingMap := OI`ChangeRingMap;
  end if;

  I`LeftOrder := O;
  return O;
end intrinsic;

intrinsic RightOrder(I::AlgAssVOrdIdl[RngOrd]) -> AlgAssVOrd
  {The right multiplicator order of I};
  
  if assigned I`RightOrder then
    return I`RightOrder;
  end if;
 
  OI := Order(I);

  if IsRightIdeal(I) and assigned OI`IsMaximal and OI`IsMaximal then
    I`RightOrder:= OI;
    return OI;
  end if;

  A := Algebra(OI);

  // Optional secondary algorithm for quaternion algebras
  // which seems to run slower in practice
  // if Type(A) eq AlgQuat then
  //   n := Norm(I);
  //   B := Basis(I);
  //   CI := CoefficientIdeals(PseudoMatrix(I));
  //   O := Order([A!(Conjugate(B[i])*B[j]) : i,j in [1..4]], 
  //              [CI[i]*CI[j]/n : i,j in [1..4]]);

  PI := PseudoMatrix(I, A);
  PO := ColonInternal(PI, PI, A, false);
  O := Order(A, PO);
  
  if debug then
    CheckIdeal(I);
    CheckOrder(O);
  end if;
  
  if assigned OI`ChangeRingMap then
    O`ChangeRingMap := OI`ChangeRingMap;
  end if;

  I`RightOrder := O;
  return O;
end intrinsic;
 
intrinsic MultiplicatorRing(I::AlgAssVOrdIdl : Side := "Left") -> AlgAssVOrd
  {Returns the Side-multiplicator ring of I.}

  if Side eq "Left" then
    return LeftOrder(I);
  elif Side eq "Right" then
    return RightOrder(I);
  else
    error "Improper value for Side";
  end if;
end intrinsic;

//-------------
//
// Isomorphism testing for ideals.
//
//-------------

intrinsic IsLeftIsomorphic(I::AlgAssVOrdIdl[RngOrd], J::AlgAssVOrdIdl[RngOrd]) -> 
     BoolElt, AlgQuatElt
  {Returns true iff I,J are isomorphic left ideals.}

  require IsLeftIdeal(I) and IsLeftIdeal(J) : "Ideals must be left ideals";
  return IsIsomorphic(I,J);
end intrinsic;

intrinsic IsRightIsomorphic(I::AlgAssVOrdIdl[RngOrd], J::AlgAssVOrdIdl[RngOrd]) -> 
     BoolElt, AlgQuatElt
  {Returns true iff I,J are isomorphic right ideals.}

  require IsRightIdeal(I) and IsRightIdeal(J) : "Ideals must be right ideals";
  return IsIsomorphic(I,J);
end intrinsic;

// This is a helper for ideal-isomorphism testing for definite orders.
// Given an invertible right O-ideal J, returns b in J and JJ s.t O*b = J*JJ (with b small) 
// and with JJ of prime power norm, coprime to the given integral ideal of BaseRing(O)

function Jprime(J : coprime_to:=1) 
  // Check cache
  if assigned J`PackageAttributes and assigned J`PackageAttributes`Jprimes then
    for tup in J`PackageAttributes`Jprimes do 
      JJ, b, normb := Explode(tup); 
      NJJ := Norm(JJ); 
      if coprime_to cmpeq 1 or AbsoluteNorm(NJJ + ideal< Order(NJJ) | coprime_to >) eq 1 then 
        return JJ, b, normb; 
      end if; 
    end for; 
  end if;

  O := Order(J);
  assert IsRightIdeal(J) and O eq RightOrder(J); 
  OJ := LeftOrder(J);
  A := Algebra(O);
  K := BaseField(A);
  // set up usual pos def Tr(N(.)) on J
  ZBJ := ZBasis(J);
  L := ReducedBasisInternal(ZBJ, A : return_new_basis:=false);
  
  // iterate small combinations of the reduced basis, until we find b with Nb/NJ okay
  m := Integers()! Norm(coprime_to);
  NJ := Norm(Norm(J));
  Lmat := BasisMatrix(L);
  SVPB := 1; SVP := ShortVectorsProcess(StandardLattice(Dimension(L)), SVPB); 
  repeat 
    sv, nsv := NextVector(SVP);
    if nsv eq -1 then
      SVPB *:= 2; SVP := ShortVectorsProcess(StandardLattice(Dimension(L)), SVPB);
      continue; end if;
    v := Vector( ChangeRing(sv, BaseRing(Lmat)) * Lmat );
    b := &+[A| v[i]*ZBJ[i] : i in [1..#ZBJ] ];
    nn := Integers()! (Norm(Norm(b))/NJ); 
  until GCD(nn,m) eq 1 and #PrimeDivisors(nn) eq 1;
  
  // get pseudomatrix for OJ*b with minimal work:
  CIs_OJ := CoefficientIdeals(PseudoMatrix(OJ));
  bas_OJ := Basis(OJ);  assert Universe(bas_OJ) eq A;
  POJb := PseudoMatrix( CIs_OJ, Matrix([Eltseq(x*b) : x in bas_OJ]) );
  JJ := ColonInternal(POJb, PseudoMatrix(J,A), A, false); // 'false' means right multipliers 
  Obasismat := Matrix([Eltseq(A!x) : x in Basis(O)]);
  JJmat,kn := Solution(Obasismat, ChangeRing(Matrix(JJ),K)); // change basis from A to O
  JJ := PseudoMatrix( CoefficientIdeals(JJ), JJmat );
  JJ := lideal< O | JJ : Check:=debug >;
  if debug then 
    assert OJ eq Order(bas_OJ, CIs_OJ);
    assert lideal< OJ | ZBasis(POJb,A) > eq OJ*b;
    assert RightOrder(JJ) eq OJ^b; // or is it b^-1 ??
    assert J*JJ eq OJ*b; 
  end if;

  normb := ideal<BaseRing(O)|Norm(b)>;
  JJ`Norm := normb/Norm(J);
  
  // Cache JJ
  if not assigned J`PackageAttributes then 
    J`PackageAttributes := rec< AlgAssVOrdIdlData | >; end if;
  if not assigned J`PackageAttributes`Jprimes then 
    J`PackageAttributes`Jprimes := [* *]; end if;
  Append(~J`PackageAttributes`Jprimes, <JJ, b, normb>);

  return JJ, b, normb;
end function;

function TotallyPositiveUnits(Z_F)
  if assigned Z_F`TotallyPositiveUnits then 
    return Z_F`TotallyPositiveUnits; 
  end if;

  UF, mUF := UnitGroup(Z_F);
  M := [[(1-t) div 2 : t in RealSigns(mUF(UF.i))] : i in [1..#Generators(UF)]];
  hk := hom<UF -> AbelianGroup([2 : ind in [1..Degree(Z_F)]]) | M>;
  UFplus := sub<UF | Kernel(hk)>;
  UFplusmodsq,msq := quo<UFplus | [2*UF.i : i in [1..#Generators(UF)]]>;
  Z_F`TotallyPositiveUnits := [mUF(u@@msq) : u in UFplusmodsq];
  return Z_F`TotallyPositiveUnits;
end function;

// Find some or all nu in the module generated by ZB (inside a quat alg) 
// such that Norm(nu) = Nnu

function has_element_of_norm(ZB, Nnu : all:=false, svp:=true, prune:=false)

  A := Universe(ZB);  
  F := BaseRing(A);  
  Z_F := Integers(F);
  Nnu:= F ! Nnu;

  // The trick here ensures we are looking for vectors of the twisted trace form
  //     Tr( 1/Nnu * trd(x*y^bar) )
  // having length 2*[F:Q]. These are shortest vectors if nu generates the norm.
  // Here the mat mults are a bit costly when field degree is 2

  M    := Matrix(4*Degree(F), &cat [Flat(x) : x in ZB]);
  R    := RepresentationMatrix(1/Nnu);
  Gram := M * DiagonalJoin([R : i in [1..4]]) * TraceFormsOnQBasis(A) * Transpose(M);
  Gram, d:= IntegralMatrix(Gram);
  c    := Content(Gram);
  if c ne 1 then Gram := Gram div c; end if;
  B    := 2 * AbsoluteDegree(F) * d/c;
  
  if not IsIntegral(B) then
    return false, _;
  end if;

  // Strongest available LLL!  
  // TO DO: BKZ when that's available for lattices defined by Gram matrices
  L := LatticeWithGram(Gram : CheckPositive:=debug);
  L := LLL(L : Delta:=0.9999, Eta:=0.5001, DeepInsertions:=(Dimension(L) le 80), Proof:=false);

  // Empirical observation: when the answer consists of 1 or 0 elements,
  // typically this is also the number of candidate short vectors.
  // When the answer contains many elements, the number of candidates 
  // is sometimes still the same, but usually considerably larger.

  // TO DO: When there are many short vectors, we'd like to use ShortVectorsProcess,
  // but it uses Allan's old enumeration; ShortVectors using Damien's enumeration 
  // saves some time, but obviously takes memory.

  if all or not svp or prune then 

    if prune then
      d := Dimension(L);
      linear := [RealField()| 1 - i/d : i in [0..d-1]];
      SV := ShortVectors(L, B, B : Prune:=linear);
    else
      SV := ShortVectors(L, B, B);
    end if;

    if all then 
      elts := Internal_has_element_of_norm(SV, ZB, Nnu, F!1);
    else
      for tup in SV do 
        s := tup[1];
        anu := AddMult(s, ZB);
        if Norm(anu) eq Nnu then   // J = product of (nu) and I
          return true, anu;
        end if;
      end for;
    end if; // all

    // #SV, "candidates"; #elts, "elements";

  else

    SVP := ShortVectorsProcess(L, B, B);
    s,l := NextVector(SVP);

    if all then // (not reachable, currently)
      elts := [A| ];
      while l ne -1 do
        anu := AddMult(s, ZB);
        if Norm(anu) eq Nnu then   // J = product of (nu) and I
          Append(~elts, anu);
        end if;
        s,l := NextVector(SVP);
      end while;
    else
      while l ne -1 do
        anu := AddMult(s, ZB);
        if Norm(anu) eq Nnu then   // J = product of (nu) and I
          return true, anu;
        end if;
        s,l := NextVector(SVP);
      end while;
    end if; // all

  end if;

  if all and #elts gt 0 then 
    return true, elts;
  else 
    return false, _; 
  end if;
end function;

function IsPrincipalZBasis(zbasis, Nnu) 
  // It suffices to look for nu with Norm(nu) = u*Nnu for some u in a finite list 
  // of representatives for the totally positive units modulo squares of units.
  for u in TotallyPositiveUnits( Integers(BaseRing(Universe(zbasis))) ) do
    vprintf Quaternion,3: "IsIsomorphic: enumerating with unit %o\n", u; 
    bool, nu := has_element_of_norm(zbasis, u*Nnu); 
    if bool then return true, nu; end if;
  end for;
  return false, _;
end function;

function IsIsomorphicInternal(I,J : real_places:=0, UnitRealValuations:=<>, JJ:=0 )        
  vprintf Quaternion,3: "Calling IsIsomorphic for ideals of norms %o,%o\n", Norm(Norm(I)), Norm(Norm(J));
  if debug then CheckIdeal(I); CheckIdeal(J); end if;

  O := Order(I);
  A := Algebra(O);
  F := BaseField(A); 
  Z_F := BaseRing(O);
  FeqQ := F cmpeq Rationals();

  // We need to determine whether there exists an element nu in JcolonI 
  // with Norm(nu) * Norm(I) = Norm(J).  Nnu stands for Norm(nu) below.
  N := Norm(J)/Norm(I);
  if IsDefinite(A) then 
    bl, Nnu := IsNarrowlyPrincipal(N : real_places:=real_places, UnitRealValuations:=UnitRealValuations);
  else  
    if FeqQ then
      bl := true;
      Nnu := N;
    else
      bl, Nnu := IsPrincipal(N); 
    end if;
  end if;
  if not bl then
    return false, _;  // necessary, but not sufficient condition
  end if;

  if IsDefinite(A) then
    // This is a way of avoiding the (somewhat painful) colon operation!
    // Suppose b generates J*JJ.  Then I*JJ = I*J^-1*b, 
    // so x generates I*JJ <==> x/b generates I*J^-1
    if JJ cmpne 0 then
      JJ, b := Explode(JJ);
      if debug then 
        assert LeftOrder(J)*b eq J*JJ; 
        assert Norm(JJ) + Norm(I) eq 1*Z_F; 
      end if; 
      // By coprimality, I*JJ = I meet JJ, which we compute as a Z-module
      IJJ_ZB := IntersectionZBasis(I, JJ);
      bool, x := IsPrincipalZBasis( IJJ_ZB, Norm(b)/Nnu ); 
      if bool then 
        if debug then assert J cmpeq (b/x)*I or J cmpeq I*(b/x); end if;
        return true, b/x;
      else 
        return false, _;
      end if;
    end if;        

    // [J:I] = J*I^-1 for right ideals, or I^-1*J for left ideals, as a pmatrix
    // The fourth argument means take left multipliers when true
    JcolonI := ColonInternal(PseudoMatrix(J, A), PseudoMatrix(I, A), A, IsRightIdeal(I) and IsRightIdeal(J)
                            : Hermite:=false); // empirically, saves time to skip the final Hermite
    JcolonI_ZB := ZBasis(JcolonI, A);
    bool, nu := IsPrincipalZBasis(JcolonI_ZB, Nnu);
    if bool then 
      if debug then assert J cmpeq nu*I or J cmpeq I*nu; end if; 
      return true, nu;
    else 
      return false, _;
    end if;
  else
    // The quaternion algebra A satisfies the Eichler condition, so 
    // there the norm map gives a bijection of sets from the set
    // of ideal classes to Cl^S(F), where S is the set of ramified 
    // infinite places of A.
    _, S := RamifiedPlaces(A);
    if not FeqQ then
      if real_places cmpeq 0 then real_places := RealPlaces(F); end if;
      sgnsNnu := RealSigns(Nnu : real_places:=real_places);
      sgns := [sgnsNnu[Index(real_places, v)] : v in S];
      u := RealWeakApproximation(S, sgns : UnitOnly, UnitRealValuations:=UnitRealValuations);
      if u cmpeq false then
        return false, _;
      end if;
    end if;
    // Otherwise, u*Nnu is now a generator for the ideal Norm(I)/Norm(J)
    // with the right signs, so by Eichler's theorem, I is isomorphic to J.
    JcolonI := Colon(J, I);
    Lbasis, L := ReducedBasisInternal(JcolonI, A);  

  //"Old way ..."; time
  //delta := EnumerativeSearchUntilSuccess(Lbasis, Abs(Norm(Nnu)));

    d := Degree(F);
    NNnu := Abs(Norm(Nnu));
    m := 0;
    SVP := ShortVectorsProcess(L, d);
    while true do
      v := NextVector(SVP);
      if IsZero(v) then
        m +:= 1;
        SVP := ShortVectorsProcess(L, m*d, (m+1)*d);
        continue;
      end if;
      // Coordinates often fails, due to even slight precision loss.
      // Don't want to break it now, so just putting potentially infinite loop
      // in already-broken cases
      // SRD, Dec 2011
      try
        coords := Coordinates(v);
        delta := &+[coords[i]*Lbasis[i] : i in [1..4*d]];
        okay := true;
      catch ERROR
        okay := false;
      end try;
      if not okay then
        continue; // even though likely to never by okay
      end if;
      // In the case where ReducedBasisInternal constructs a LatticeWithGram,
      // we could avoid Coordinates: if JcolonI_ZB is the same ZBasis(JcolonI) then
      // delta := &+[Round(v[i])*JcolonI_ZB[i] : i in [1..4*d]];
      if Abs(Norm(Norm(delta))) eq NNnu then
        return true, delta;
      end if;
    end while;
  end if;
end function;

intrinsic IsIsomorphic(I::AlgAssVOrdIdl[RngOrd], J::AlgAssVOrdIdl[RngOrd])
       -> BoolElt, AlgQuatElt
  {Returns true iff I,J are isomorphic (left or right) ideals (ie, whether 
   I and J are in the same left or right ideal class), and if so, also 
   returns an element x such that J = x*I (or I*x)}  

  require Order(I) cmpeq Order(J): "The arguments must be ideals with the same order";
  require IsLeftIdeal(I) and IsLeftIdeal(J) or IsRightIdeal(I) and IsRightIdeal(J) :
         "Ideals must both be left ideals or both be right ideals";
  require Type(Algebra(Order(I))) eq AlgQuat : "Only implemented for quaternion algebras";

  return IsIsomorphicInternal(I,J);
end intrinsic;

intrinsic IsPrincipal(I::AlgAssVOrdIdl) -> BoolElt, AlgQuatElt
  {Returns true iff I is a principal (left or right) ideal, and a generator.}

  O := Order(I);
  R:= BaseRing(O);
  T:= Type(R);
  if T eq RngUPol then 
    k:= BaseRing(R);
    require IsFinite(k) and IsField(k) and IsOdd(Characteristic(k)) : 
         "Order of the given ideal must be over Z or a number ring or F_q[x] with q odd";
  else
    require T eq RngInt or ISA(T, RngOrd) : 
         "Order of the given ideal must be over Z or a number ring or F_q[x] with q odd";
  end if;

  return IsIsomorphic(ideal<O | 1>, I);
end intrinsic;

// Given a sequence of right ideal class reps, compute a sequence
// of equivalent reps with norms supported in the given primes
// (which must be disjoint from the support of the rids1).
// Also return sequence of algebra elts such that rids[i] = elts[i]*rids1[i]

// TO DO: could convert other stuff too, eg the left orders and unit groups

function convert_rids(rids1, primes)

  assert not IsEmpty(rids1);
  if debug then
    assert not &and [t[1] in primes : t in Factorization(Norm(I)), I in rids1];
  end if;

  O := Order(rids1[1]);
  ZF := BaseRing(O);
  F := NumberField(ZF);
  PI := PowerIdeal(FieldOfFractions(ZF));
  tot_pos_units := TotallyPositiveUnits(ZF);

  NCl, cl := NarrowClassGroup(F);
  S := AbelianGroup([0 : p in primes]);
  StoNCl := hom< S -> NCl | [p @@ cl : p in primes] >;

  // Lattice of principal ideals within S
  K := Kernel(StoNCl);
  L := LatticeWithBasis(Matrix(Integers(), [Eltseq(S!K.i) : i in [1..Ngens(K)]] ));
  Lgens := [ZF| ];
  for v in Basis(L) do 
    I := &* [primes[i]^v[i] : i in [1..#primes]];
    bl, g := IsNarrowlyPrincipal(I); assert bl;
    Append(~Lgens, g);
  end for;

  procedure select_vecs(~vecs, v1)
    vecs := [v : v in vecs | forall{c : c in Eltseq(v+v1) | c ge 0}];
    vecs_norms := [Integers()| &*[Norm(primes[i])^vv[i] : i in [1..#primes]]
                                 where vv is v+v1 
                             : v in vecs ];
    ParallelSort(~vecs_norms, ~vecs);
  end procedure;

  U := Universe(rids1);
  rids := [U| ];
  elts := [Algebra(Ring(U))| ];
  vprintf Quaternion: "Converting right ideal class representatives to support \n%o\nwith norms %o\n", 
                      primes, [Norm(p) : p in primes];
  time0 := Cputime();
  IndentPush();
  for I1 in rids1 do 
    // Want I = x*I1 with Norm(I) = N, so find x in I1^-1 with Norm(x) = u*s 
    // where s runs over generators of principal ideals supported within primes,
    // and u runs over units
    I1inv := ZBasis(LeftInverse(I1));
    N1 := Norm(I1);
    bl, n := HasPreimage(N1 @@ cl, StoNCl);
    error if not bl, 
         "The given primes do not generate the narrow ideal classes of the norms";
    e := Eltseq(n); 
    N := &* [PI| primes[i]^e[i] : i in [1..#primes]];
    bl, s1 := IsNarrowlyPrincipal(N/N1); assert bl;
    v1 := Vector([Valuation(s1,p) : p in primes]);
    // Test candidates s in same coset as s1, integral at primes, with small Norm
    // TO DO: can we guess an s that works? or how large s is needed to find I1?
    // TO DO: run through candidates s strictly in order of Norm 
    // (currently, we get them in order of L2-norm of exponent vectors,
    // in batches and then reorder each batch by Norm)
    _, i := ClosestVectors(L, -v1);
    i +:= 4;
    vecs := [tup[1] : tup in CloseVectors(L, -v1, i)];
    select_vecs(~vecs, v1);
    vprintf Quaternion, 2: "%o : ", Norm(N1);
    vtime Quaternion, 2:
    while true do 
      for v in vecs do 
        c := Coordinates(v); // coords wrt basis of L
        s := s1 * &* [Lgens[i]^c[i] : i in [1..#primes]];
        vprintf Quaternion, 2: "%o ", Numerator(Abs(Norm(s)));
        for u in tot_pos_units do
          bl, x := has_element_of_norm(I1inv, u*s : prune:=false);
          if bl then
            I := x*I1;
            Append(~rids, I);
            Append(~elts, x);
            continue I1;
          end if;
        end for;
      end for; // v in vecs
      i +:= 1;
      vecs := [tup[1] : tup in CloseVectors(L, -v1, i, i)];
      select_vecs(~vecs, v1);
    end while;
  end for; // I1
  IndentPop();
  vprintf Quaternion: "Converting right ideal representatives took %os\n", Cputime(time0);

  assert #rids eq #rids1;

  // actual support of rids
  support := {PI| };
  for I in rids do 
    NI := Norm(I);
    support join:= {P : P in primes | Valuation(NI, P) ne 0};
    if #support eq #primes then 
      break;
    end if;
  end for;

  if debug then
    assert &and [t[1] in primes : t in Factorization(Norm(I)), I in rids];
    assert &and [rids[i] eq elts[i]*rids1[i] : i in [1..#rids]];
  end if;

  // Cache
  Append(~O`RightIdealClasses, 
     rec< rids_record | rids := rids, rids1 := rids1, rids_conversion := elts, 
                        support := Sort(Setseq(support)) > );

  return rids, elts;
end function;


//-------------
//
// List of ideal classes.
//
//-------------

intrinsic ClassGroupPrimeRepresentatives(Z_F::RngOrd, dd::RngOrdIdl) -> Map
  {Returns a map of sets from Cl(Z_F) to prime ideals of Z_F, prime to dd.}

  return ClassGroupPrimeRepresentatives(Z_F, dd, []);
end intrinsic;

intrinsic ClassGroupPrimeRepresentatives(Z_F::RngOrd, dd::RngOrdIdl, S::SeqEnum[PlcNumElt]) -> Map
  {Returns a map of sets from Cl^S(Z_F) to prime ideals of Z_F, prime to dd, 
   where S is a set of infinite places.}

  Foo := InfinitePlaces(NumberField(Z_F));
  Si := [Index(Foo, v) : v in S];

  ClZF, mCl := RayClassGroup(ideal<Z_F | 1>, Si);
  idealSet := Parent(ideal<Z_F | 1>);
  d := Discriminant(Z_F);
  X := CartesianProduct(ClZF, idealSet);
  G := [X | <ClZF!0, ideal<Z_F | 1>>];
  ClZFnotfound := [g : g in ClZF | g ne ClZF!0];

  Nd := Norm(d*dd);
  p := 2;
  while #ClZFnotfound gt 0 do
    p := NextPrime(p);
    if Gcd(p, Nd) eq 1 then
      pFacts := Decomposition(Z_F, p);
      for pp in [pp : pp in pFacts] do
        g := pp[1]@@mCl;
        i := Index(ClZFnotfound, g);
        if i ne 0 then
          Append(~G, <g, pp[1]>);
          Remove(~ClZFnotfound, i);
        end if;
      end for;
    end if;
  end while;
  return map<ClZF -> idealSet | G>;
end intrinsic;

intrinsic LeftIdealClasses(O::AlgAssVOrd[RngOrd[RngInt]] : Support := [], Al:= "AllOrders") -> SeqEnum[AlgAssVOrdIdl]
  {Returns a sequence of representatives of the left ideal classes of O.}

  A := Algebra(O);
  require Type(A) eq AlgQuat : "Order must be a quaternion order";
  return [Conjugate(I) : I in RightIdealClasses(O : Support := Support, Al:= Al)];
end intrinsic;

intrinsic RightIdealClasses(O::AlgAssVOrd[RngOrd[RngInt]] : Support:=[], Al:="AllOrders", avoid_IsIsometric:=false, Strict := false, AvoidPrimes := []) 
       -> SeqEnum[AlgAssVOrdIdl], SeqEnum[AlgAssVOrd]
  {Returns a sequence of representatives of the right ideal classes of O
   with support in the prime ideals in Support, if given.}

  // Note : results are cached/accessed by RightIdealClassesAndOrders in O`RightIdealClasses 
  //        (but for other cases nothing is cached)
  //        ... except in the indefinite case, where we do not use RICAO!  JV

  A := Algebra(O);
  F := BaseField(A);
  Z_F := BaseRing(O);
  d := Degree(F);
  require Type(A) eq AlgQuat : "Order must be a quaternion order";

  ZbasisO := ZBasis(O);

  require IsMaximalAtRamifiedPrimes(O) : "O must be maximal at ramified primes";
  
  ideals := [rideal<O | 1>];

  if IsDefinite(A) then
    
    if Al cmpne "AllOrders" then
      "WARNING: 'Al' option in RightIdealClasses is obselete and is now ignored!";
    end if;

    return RightIdealClassesAndOrders(O: Support:= Support, avoid_IsIsometric:=avoid_IsIsometric);

    /********************************************************************************************
     THIS OLD VERSION IS SUPERCEDED  ---  NO REASON TO MAINTAIN IT  

    require Al cmpeq "FixOrder" : "If specified, Al must be either \"AllOrders\" or \"FixOrder\" ";

    massformula := 1/#UnitGroup(O);
    masses := [massformula];  // record the contribution of each ideal class to the total mass

    masstotal := Mass(O);
    vprintf Quaternion: 
           "Starting with the trivial ideal class. \nMass %o out of total mass %o\n", massformula, masstotal;

    if massformula ne masstotal then
     // Conditional upper bound for the reduced norm of an ideal.
     bnd := 4^d*Norm(Discriminant(O))*Discriminant(Z_F);
     safety_check_counter := 0; // the number of extra iterations
     // run through prime ideals of Z_F ordered by norm
     for pe in [3..bnd by 2] do
      factpe := Factorization(pe);
      if #factpe gt 1 then continue; end if;  
      p,e := Explode(factpe[1]);  assert pe eq p^e;
      for ppseq in [tup: tup in Factorization(ideal<Z_F | p>) | Norm(tup[1]) eq p^e] do
        pp := ppseq[1];
        // TO DO: use conjugates in a clever way?
        
        if Norm(pp) lt bnd and Valuation(Discriminant(O), pp) eq 0 and
                    pp notin AvoidPrimes then
          M2F, phi := pMatrixRing(O, pp);

          // Magma's choice of generators for a matrix algebra, whatev!
          e11 := Inverse(phi)(M2F.1);
          e21 := Inverse(phi)(M2F.2*M2F.1);

          // Ideals mod pp are in 1-1 correspondence with elements
          // of P^1(F_pp) on the first row (with zeros on the second)
          k, mk := ResidueClassField(pp);

          // Reduce mod p otherwise 'rideal' will choke  (Steve added this)
          e11coords, e21coords := Explode(Coordinates( [A!e11,A!e21], ZbasisO ));
          assert Universe(e11coords) eq Integers() and Universe(e21coords) eq Integers();
          if debug then
             assert e11 eq &+[ e11coords[i] * ZbasisO[i] : i in [1..#ZbasisO]];
             assert e21 eq &+[ e21coords[i] * ZbasisO[i] : i in [1..#ZbasisO]];
          end if;
          e11 := O! &+[ (e11coords[i] mod p) * ZbasisO[i] : i in [1..#ZbasisO]];
          e21 := O! &+[ (e21coords[i] mod p) * ZbasisO[i] : i in [1..#ZbasisO]];

          for museq in [[0,1]] cat [[1,x@@mk] : x in [x : x in k]] do
            mu := O!(museq[1]*e11 + museq[2]*e21);
            I := rideal<O | [mu] cat Generators(pp)>;
            if debug then assert Norm(I) eq pp; end if;
            I`Norm := pp;  

            found := false;
            for jj := 1 to #ideals do 
              if IsIsomorphic(I, ideals[jj]) then
                found := true;
                break jj;
              end if;
            end for;
            if not found then
              vprintf Quaternion: "New ideal of norm %o, now found %o ideal classes\n", 
                                                                   Norm(Norm(I)), #ideals+1;
              Append(~ideals, I);
              mass := 1/#UnitGroup(LeftOrder(I));
              massformula +:= mass;
              Append(~masses, mass);
              vprintf Quaternion: "Masstotal now %o out of %o\n", massformula, masstotal;
              vprintf Quaternion: "Contributions: %o\n", masses;
              require massformula le masstotal: "Found too many ideal classes" * please_tell_us;
              if not debug and massformula eq masstotal then 
                break pe;
              end if;
            end if;
            if debug and massformula eq masstotal then 
              if safety_check_counter ge 200 then break pe; end if;
              safety_check_counter +:= 1; 
            end if;
          end for;
        end if;
      end for;
     end for; // pe
    end if;  // massformula ne masstotal

    *******************************************************************************************/

  else
    if assigned O`RightIdealClasses and O`RightIdealClasses[1][4] eq Strict then
      return O`RightIdealClasses[1][2];
    end if;

    if Strict then
      S := RealPlaces(F);
    else
      // The quaternion algebra A satisfies the Eichler condition, so
      // there is a one-to-one correspondence between the ideal classes
      // of O and of Z_F (relative to the infinite ramified places).
      _, S := RamifiedPlaces(A);
    end if;
    if #AvoidPrimes eq 0 then
      dd := 1*Z_F;
    else
      dd := &*AvoidPrimes;
    end if;
    phi := ClassGroupPrimeRepresentatives(Z_F, Discriminant(O)*dd, S);
    ClZF := Domain(phi);
    twoClZF, mtwo := 2*ClZF;
    ClZFmod2, mmod2 := quo<ClZF | twoClZF>;
    twoClZFreps := [phi(ClZF![c div 2 : c in Eltseq(ClZF!h)]) : h in twoClZF];
    ideals := [rideal<O | Generators(aa)> : aa in twoClZFreps];
    
    for g in [g : g in ClZFmod2 | g ne ClZFmod2!0] do
      pp := phi(g@@mmod2);
      M2F, phipp := pMatrixRing(O, pp);
      Jpp := rideal<O | [Inverse(phipp)(M2F.1)] cat Generators(pp)>;
      for aa in twoClZFreps do
        _, Jppaa := Jpp*ideal<O | Generators(aa)>;
        Append(~ideals, Jppaa);
      end for;
    end for;

    orders := [LeftOrder(I) : I in ideals];
    orders[1] := O;

    O`RightIdealClasses := [* [* [Norm(I) : I in ideals], ideals, orders, Strict *] *];
  end if;
  
  return ideals;
end intrinsic;


intrinsic Coordinates(S::SeqEnum[AlgAssVElt[FldNum]], basis::SeqEnum[AlgAssVElt[FldNum]]) -> SeqEnum
{The coordinates of the sequence S of elements in an associative algebra A, 
 relative to the given basis of A over the rationals}
  A := Universe(S);
  K := BaseField(A);
  require Universe(basis) eq A : "The arguments should be sequences of elements in the same algebra";
  require BaseField(K) eq Rationals() : "Base field of the algebra must be an absolute extension of Q";
  require #basis eq Dimension(A)*Degree(K) : "Second argument should be a basis of the algebra over Q";
  
  basis_matrix := Matrix(Rationals(), [&cat[ Eltseq(cc) : cc in Eltseq(bb)] : bb in basis]);
  elts_matrix := Matrix(Rationals(), [&cat[ Eltseq(cc) : cc in Eltseq(x)] : x in S]);
  coords_matrix := Solution( basis_matrix, elts_matrix);
  coords := [ Eltseq(coords_matrix[i]) : i in [1..Nrows(coords_matrix)] ];
  if &and[ IsIntegral(c) : c in Flat(coords) ] then
    coords := [ChangeUniverse(coords[i], Integers()) : i in [1..#coords]]; 
  end if;
  return coords;
end intrinsic;
