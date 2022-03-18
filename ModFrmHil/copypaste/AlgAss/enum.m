freeze;

/**********************************************************
* Enumeration of ideal classes and unit group computation * 
* in (definite) quaternion algebras                       *
*                                                         *
* October 2007 / March 2010, Markus Kirschmer             *
*                                                         *
* Also modified by Steve Donnelly                         *
*                                                         *
* Last modified May 2013                                  *
*                                                         *
**********************************************************/

debug := false;

declare attributes AlgQuat : GramMatrix, TraceFormsOnQBasis;

declare attributes AlgAssVOrd: RightIdealClasses, TwoSidedIdealClassMaps,
                               junk_for_IsIsomorphic, masstotal, 
                               graph; // only for curiosity, plays no role yet

import "ideals-jv.m" : TotallyPositiveUnits, IsIsomorphicInternal, Jprime,
                       has_element_of_norm;

import "../AlgQuat/ramified.m" : RealValuations;
import "../AlgQuat/twosided.m" : SetupNormalizerMap;

/////////////////////////////////////////////
// Silly functions

function mult_no_check(I1,I2 : Sides:="Both")
  return '*'(I1,I2 : Check:=false, Sides:=Sides);
end function;

function grpab_to_string(C)
  c := Invariants(C);
  if c eq [] then
    return "trivial";
  end if;
  s := "";
  for i := 1 to #c do
    s *:= "Z";
    if c[i] ne 0 then s *:= "/"*IntegerToString(c[i]); end if;
    if i lt #c then s *:= " + "; end if;
  end for;
  return s;
end function;


///////////////////////////////////////////////
// Helper functions to work with the norm form

function GramMatrixofAlgebra(A)
  if not assigned A`GramMatrix then
    B:= Basis(A);
    A`GramMatrix:= SymmetricMatrix( [ Trace( B[i]*Conjugate(B[j])) : i in [1..j], j in [1..4] ] );
  end if;
  
  return A`GramMatrix;
end function;  

function TraceFormsOnQBasis(A)
  if not assigned A`TraceFormsOnQBasis then 
    F := BaseRing(A);  
    M := GramMatrixofAlgebra(A);
    B := [ A | b*f : f in AbsoluteBasis(F), b in Basis(A) ];
    B := Matrix([ Eltseq(b) : b in B ]);
    T := B * M * Transpose(B);
    d:= Nrows(T);
    T1 := Matrix(Rationals(), d, d, [AbsoluteTrace(x) : x in Eltseq(T)] );
    AF:= AbsoluteField(F);
    a:= PrimitiveElement(AF);
    ok, den := IsIntegral(a);
    if not ok then a*:= den; end if;
    a:= F ! a; 
    T2 := Matrix(Rationals(), d, d, [AbsoluteTrace(a*x) : x in Eltseq(T)] );
    A`TraceFormsOnQBasis := [T1, T2];
  end if;

  return Explode(A`TraceFormsOnQBasis);
end function;

function GramMatrixofOrder(O)
  A:= Algebra(O);
  if BaseField(A) eq Rationals() then
    return GramMatrix(O), Basis(O);
  end if;
  B:= ZBasis(O);
  GramOverF:= M * GramMatrixofAlgebra(A) * Transpose(M) where M:= Matrix(B);
  return Matrix( Integers(), #B, [ AbsoluteTrace(x): x in Eltseq(GramOverF)]), B;
end function;

function GramMatrices(O: LLL:= false, a:= 0)
  A:= Algebra(O);
  K:= BaseField(A);

  if K eq Rationals() then
    Grams:= [GramMatrix(O)];
    B:= Basis(O);
  else
    B:= ZBasis(O);
    if a cmpeq 0 then a:= AbsoluteField(K).1; end if;
    if not IsIntegral(a) then a *:= Denominator(a); end if;
    
    GramOverF:= M * GramMatrixofAlgebra(A) * Transpose(M) where M:= Matrix(B);
    Grams:= [ Matrix( Integers(), #B, [ AbsoluteTrace(  x): x in Eltseq(GramOverF)]),
              Matrix( Integers(), #B, [ AbsoluteTrace(a*x): x in Eltseq(GramOverF)]) ];
  end if;

  if LLL then
    F, T:= LLLGram( Grams[1] : Delta:= 0.999, Proof:= false);
    Grams:= [ F ] cat [ T * g * Transpose(T) : g in Grams[2..#Grams] ];
    B:= [ &+[ T[i,j] * B[j] : j in [1..#B] | T[i,j] ne 0]: i in [1..#B] ];
  end if;
 
  return Grams, B;
end function;


////////////////////////////////////////////////////////////////////////
// Conjugacy of orders

intrinsic '^'( O:: AlgAssVOrd, x:: AlgElt ) -> AlgAssVOrd
  {Gives the conjugate of an order O by an element x, i.e. x^-1*O*x.}

  require Parent(x) cmpeq Algebra(O) : "Element must lie in the algebra of the order";
  ok, xinv:= IsInvertible(x);
  require ok : "Conjugating element must be invertible"; 

  if IsCentral(x) then
    return O;
  end if;

  if Type(BaseRing(O)) in {RngInt, RngUPol} then
    OO:= Order( BaseRing(O), [xinv * b * x: b in Basis(O)] );
  else
    M:= PseudoMatrix(O);
    OO:= Order( [xinv * b * x: b in Basis(O)], CoefficientIdeals(M) : Check:=false);
  end if;
 
  // copy some attributes;
  if assigned(O`IsMaximal) then OO`IsMaximal:= O`IsMaximal; end if;
  if assigned(O`Discriminant) then OO`Discriminant:= O`Discriminant; end if;
  if assigned(O`FactoredDiscriminant) then OO`FactoredDiscriminant:= O`FactoredDiscriminant; end if;

  return OO; 
end intrinsic;

// Set up the lattices to be used in IsIsomorphic for O = AlgAssVOrd[RngOrd]

function junk_for_IsIsomorphic(O)
    if not assigned O`junk_for_IsIsomorphic then
      // Conjugating and multiplying elements in A is rather slow. This is faster.
      A:= Algebra(O);
      B:= ZBasis(O);

      Bmat:= Matrix([ &cat [ Flat(x) : x in Eltseq(b)] : b in B ]);
      T1, T2:= TraceFormsOnQBasis(A);

      F1:= ChangeRing(Bmat * T1 * Transpose(Bmat), Integers());
      F1, T:= LLLGram(F1 : Delta:= 0.9999, Eta:=0.5001, 
                           DeepInsertions:=(Nrows(F1) le 80), Proof:= false);
      // TO DO: this is the strongest LLL, is it too much for present purposes?

      B:= [ &+[T[i,j] * B[j] : j in [1..#B]] : i in [1..#B]];

      Bmat:= Matrix(Rationals(), T) * Bmat;
      F2:= ChangeRing(Bmat * T2 * Transpose(Bmat), Integers());

      O`junk_for_IsIsomorphic:= [* B, F1, F2 *];
    end if;
    return O`junk_for_IsIsomorphic;
end function;


function theta_series(O : prec:=0)
  if assigned O`thetas and AbsolutePrecision(O`thetas[1]) gt prec then
    return O`thetas[1];
  end if;

  M := junk_for_IsIsomorphic(O)[2];
  L := LatticeWithGram(M);

  if prec eq 0 then
    // choose a number of terms that won't take too long
    dim := 4*Degree(BaseRing(O));
    Vol1 := Pi(RealField())^(dim/2) / Gamma(dim/2 + 1); // = volume of unit sphere of this dimension
    prec := Ceiling( (100 * Sqrt(Determinant(M)) / Vol1) ^ (2/dim) );
  end if;

  // TO DO: ThetaSeries should be smart enough to do this itself!
  g := GCD([M[i,i] : i in [1..Nrows(M)]] cat [2*m : m in Eltseq(M)]);
  prec1 := (prec div g) * g;
  theta := ThetaSeries(L, prec1);
  assert AbsolutePrecision(theta) ge prec1+1;
  ChangePrecision(~theta, prec+1);

  O`thetas := [theta];
  return theta;
end function;


function IsIsomorphic1(O1, O2 : FindElement:= false, ConnectingIdeal:= 0)

  A:= Algebra(O1);
  K:= BaseField(A);

  if Type(K) eq FldFunRat then return IsIsomorphic(O1, O2 : FindElement:= FindElement); end if;
  
  if IsDefinite(A) /* and AbsoluteDegree(K) le 5*/ then
    if Type(K) eq FldRat then 
      ok:= IsIsomorphic(O1, O2);
      if ok and FindElement then
        h, x:= Isomorphism(O1, O2); 
        return true, h, x;
      end if;
      return ok, _, _;
    end if;
    
    B1, FF1, FF2 := Explode(junk_for_IsIsomorphic(O1)); // stored on O1
    B2, GG1, GG2 := Explode(junk_for_IsIsomorphic(O2));

    ok, T:= IsIsometric( [FF1, FF2], [GG1, GG2] );

    if ok and FindElement then
      B:= Basis(A);
      C1:= Matrix(K, [ Eltseq(A ! b): b in B1]); 
      C2:= Matrix(K, Coordinates(B, B2));
      // H describes an isometry \phi of O2 to O1 wrt. B
      H:= C2 * Matrix(K, T) * C1;

      // \phi(1) is a unit in O1. Change this to \phi(1)=1.
      e:= A ! H[1];
      if not IsOne(e) then
        // print "correcting unit";
        e:= 1/e; 
        H:= H * Matrix(K, [ Eltseq(e*b): b in B ]);
      end if;

      // If H describes a K - antiautomorphism, take conjugates.
      // assuming that B[1] = 1.
      if (A ! (Vector(Eltseq(B[2] * B[3])) * H)) ne  A ! H[2] * A ! H[3] then 
        // print "taking conjugates";
        H:= H * Matrix(K, [ Eltseq(Conjugate(b)): b in B ]);
      end if;

      // now H describes a K-algebra-automorphism. I.e. it is given by conjugation.
      h:= hom< A -> A | [ A ! H[i]: i in [1..4] ] >;
      KK:= Kernel(  Matrix([ &cat [Eltseq(b * c - h(c) * b): c in B] : b in B]));
      // this should never happen
      error if Dimension(KK) eq 0, "could not find conjugating element";
      x:= A ! KK.1;

      assert O2 eq O1^x;

      return true, hom< O1 -> O2 | t:-> x^-1 * t * x, s:-> x*s*x^-1 >, x;
    end if;
    return ok, _, _;
  end if;	// IsDefinite

  if ConnectingIdeal cmpeq 0 then 
    error if not IsMaximal(O1), "In indefinite algebras, this is currently implemented for maximal orders only. Sorry.";
    ConnectingIdeal:= lideal< O1 | [x * y : x in Generators(O1), y in Generators(O2) ] >;
  else
    error if LeftOrder(ConnectingIdeal) ne O1 or RightOrder(ConnectingIdeal) ne O2,
	 "ConnectingIdeal must have left order O1 and right order O2";
    // This is funny..., why can't ideals be just lattices ???
    if Order(ConnectingIdeal) ne O1 or not IsLeftIdeal(ConnectingIdeal) then
      ConnectingIdeal:= lideal< O1 | Generators(ConnectingIdeal) >;
      ConnectingIdeal`LeftOrder := O1;
      ConnectingIdeal`RightOrder:= O2;
    end if;
  end if;
    
  if not FindElement then
    if K cmpeq Rationals() then return true, _, _; end if;
    _, inf:= RamifiedPlaces(A);
    if IsEmpty(inf) then
      RCl, h:= ClassGroup(K);
    else
      RCl, h:= RayClassGroup(&+inf);
    end if;
    TwoSided:= sub< RCl | 2*RCl, [ (f[1]) @@ h : f in FactoredDiscriminant(O1) | IsOdd(f[2]) ] >;
    return Norm(ConnectingIdeal) @@ h in TwoSided, _, _;
  end if;

  swap:= not assigned O1`TwoSidedIdealClassMaps and assigned O2`TwoSidedIdealClassMaps;
  if swap then
    temp:= O1; O1:= O2; O2:= temp;
    // as above: ConnectingIdeal:= Conjugate( ConnectingIdeal ); is WRONG, since the result
    // would be a right ideal where we need a left ideal ...
    ConnectingIdeal:= lideal < O1 | [ Conjugate(x): x in Generators(ConnectingIdeal) ] >;
    ConnectingIdeal`LeftOrder := O1;
    ConnectingIdeal`RightOrder:= O2;
  end if;

  for J in TwoSidedIdealClasses(O1) do
    if Type(O1) eq AlgQuatOrd then
      ok, _, x:= IsLeftIsomorphic(ConnectingIdeal, J);
    else
      ok, x:= IsLeftIsomorphic(ConnectingIdeal, J);
    end if;
    if ok then
      if not assigned(x) then return true, _, _; end if;
      if swap then
        return true, hom< O2 -> O1 | t:-> x * t * x^-1, s:-> x^-1*s*x>, x^-1;
      else
        return true, hom< O1 -> O2 | t:-> x^-1 * t * x, s:-> x*s*x^-1>, x;
       end if;
     end if;
  end for;
  return false, _, _;
end function;

intrinsic IsIsomorphic(O1:: AlgAssVOrd[RngOrd], O2:: AlgAssVOrd[RngOrd] 
                      : FindElement:= false, ConnectingIdeal:= 0) 
      -> Bool, Map, AlgAssElt
  { Checks whether two orders in a quaternion algebra are isomorphic, i.e. conjugate.
    If so, and if FindElement is set, an isomorphism O1-> O2 and an element x with O1^x = O2 are also computed}

  A:= Algebra(O1);
  require A cmpeq Algebra(O2): "Orders must be defined over the same algebra.";
  require Type(A) eq AlgQuat : "Currently only implemented for quaternion algebras.";
  if Discriminant(O1) ne Discriminant(O2) then return false, _, _; end if;
  return IsIsomorphic1(O1, O2 : FindElement:= FindElement, ConnectingIdeal:= ConnectingIdeal);
end intrinsic;

intrinsic IsConjugate(O1:: AlgAssVOrd, O2:: AlgAssVOrd: FindElement:= false, ConnectingIdeal:= 0) -> Bool, Map, AlgAssElt
  {Same as IsIsomorphic}

  A:= Algebra(O1);
  require A cmpeq Algebra(O2): "Orders must be defined over the same algebra.";
  require Type(A) eq AlgQuat : "Currently only implemented for quaternion algebras.";
  if Discriminant(O1) ne Discriminant(O2) then return false, _, _; end if;
  return IsIsomorphic1(O1, O2: FindElement:= FindElement, ConnectingIdeal:= ConnectingIdeal);
end intrinsic;


////////////////////////////////////////////////////////////////////////////
// Unit groups

intrinsic NormOneGroup(O :: AlgAssVOrd : ModScalars:= false) -> GrpPerm, Map 
  { Returns a group G isomorphic to the group of norm 1 elements in O, where O is an order 
    in a definite quaternion algebra. If ModScalars is set, we will mod out \{-1, 1\}.
    The second return value is a map from G to the set of norm 1 elements. }

  A:= Algebra(O);
  require Type(A) eq AlgQuat and IsDefinite(A) : "The algebra is not a definite quaternion algebra.";

  G, B:= GramMatrixofOrder(O);
  L:= LatticeWithGram(G);
  L`Minimum:= #B div 2;
  S:= ShortestVectors(L);
  N:= [ &+ [B[i] * s[i] : i in [1..#B] | s[i] ne 0]: s in S ];
  if ModScalars then
    G, h:= GenericGroup(N: Eq:= func< x,y | x eq y or x eq -y >); 
    // N might differ from Codomain(h) by \pm 1
    N:= Codomain(h);
    N cat:= [-n: n in N];
    // make sure 1@@h and (-1)@@h both succeed
    h:= map< G -> N | x:-> h(x), y:-> N[i] @@ h where i:= 1+((Index(N, y)-1) mod #G) >;
  else
    G, h:= GenericGroup(Append(N, -1)); 
  end if;
  hh:= (G`GenericGroup)`q;
  return Codomain(hh), hh^-1 * h;
end intrinsic;

function force_norm1(u)
  error if Norm(u) ne 1, "element must have norm 1.";
  return u;
end function;

intrinsic NormOneGroup(O::AlgQuatOrd[RngUPol] : ModScalars:= false) -> GrpAb, Map
{"} //"
  k:= BaseRing(BaseRing(O));
  require IsField(k) and IsFinite(k) and Characteristic(k) ne 2 :
    "Coefficient ring must be over a finite field of odd characteristic";
  require IsDefinite(Algebra(O)) : "The quaternion algebra must be definite";

  U, h:= UnitGroup(O);
  UU:= (ModScalars select 2*n else n) * U where n:= #k-1;
  if ModScalars then
    m1:= (#U div 2) * U.1;		// -1 in U
    return UU, map< UU -> O | x:-> x @ h, u:-> uu in UU select uu else uu+m1 where uu:= force_norm1(u) @@ h >;
  end if;
  return UU, map< UU -> O | x:-> x @ h, u:-> force_norm1(u) @@ h >;
end intrinsic;



force_unit:= function(x)
  error if not IsUnit(x), "element is not a unit";
  return x;
end function;

intrinsic UnitGroup(O::AlgQuatOrd[RngUPol] : ModScalars:= false) -> GrpAb, Map
{ An abelian group G isomorphic to the unitgroup of O (mod scalars if wanted) where O is an
  order in a definite quaternion algebra. The second return value is a map G -> O^*. }

  k:= BaseRing(BaseRing(O));
  require IsField(k) and IsFinite(k) and Characteristic(k) ne 2 :
    "Coefficient ring must be over a finite field of odd characteristic";
  require IsDefinite(Algebra(O)) : "The quaternion algebra must be definite";

  if assigned O`UnitMap then
    m:= O`UnitMap;
    G:= Domain(m);
  else
    B:= ReducedBasis(O);
    g2:= Norm(B[2]);
    if Degree(g2) ne 0 then
      G, h:= UnitGroup(k);
      m:= map< G -> O | g :-> g @ h, o :-> (k ! force_unit(o)) @@ h >;
    else
      kk:= ext< k | Polynomial([g2,0,1]) >;
      G, h:= UnitGroup(kk);
      b:= B[2]^-1;
      m:= map< G -> O | g :-> e[1] + B[2]*e[2] where e:= Eltseq(g @ h),
                        o :-> (kk ! [ k | t, ((o-t)*b)[1] ]) @@ h where t:= Trace(force_unit(o))/2 >;
    end if;
    O`UnitMap:= m;
  end if;

  if ModScalars then
    if #G eq #k-1 then
      G:= AbelianGroup([]);
      // avoid computing discrete logs
      return G, map< G -> O | g:-> 1, o:-> G ! 0 where dummy:= force_unit(o) >;
    end if;
    G, hh:= quo< G | (#k+1) * G.1 >;
    m:= hh^-1 * m;
  end if;
  return G, m;
end intrinsic;

// check UnitGroup (check that the group multiplication table works)
procedure check_unit_group(GG, umap)
  "Checking unit group multiplication table";
  for u in GG do assert IsUnit(u@umap) and Norm(Norm(u@umap)) in {1,-1}; end for;
  for u1, u2 in GG do
      assert IsScalar( (u1@umap) * (u2@umap) / (u1*u2)@umap );
  end for;
end procedure;
  
intrinsic UnitGroup(O :: AlgAssVOrd[RngOrd]) -> GrpPerm, Map
  { A permutation group G isomorphic to the unitgroup of O mod scalars where O is an
    order in a definite quaternion algebra. The second return value is a map G -> O^*. }

  if assigned O`UnitMap then
    return Domain(O`UnitMap), O`UnitMap;
  end if;

  A:= Algebra(O);
  require Type(A) eq AlgQuat and IsDefinite(A): "The order must be in a definite quaternion algebra.";

  // make sure the inverse of f goes from O^* to Domain(G)
  FixMap:= function(f)
    Rep:= function(List, x)
      error if not (x in O and IsUnit(O ! x)), "element is not a unit of the order";
      xinv:= (A ! x)^-1;	// faster
      for l in List do if IsScalar(l*xinv) then return l; end if; end for;
    end function;
    ff:= map< Domain(f) -> O |
           x:-> f(x), y:-> Rep(Codomain(f), y) @@ f >;
    return ff;
  end function;
  
  NewUnits:= [O | ];
  K:= BaseField(A);
  R:= BaseRing(O);
  G, B:= GramMatrixofOrder(O);
  L:= LatticeWithGram(G : CheckPositive:= debug);
  // let's help
  L`Minimum:= #B div 2;
  BMat:= Matrix(B);

  // construct the norm1 group mod {\pm 1}.
  S:= Matrix(K, ShortestVectorsMatrix(L)) * BMat;
  N:= ChangeUniverse(Rows(S), A);
  G, h:= GenericGroup(N : Eq:= func< x, y | IsScalar(x/y) >);
  hh:= (G`GenericGroup)`q;
  GG:= Codomain(hh);
  //hh, GG:= CosetAction(G, sub< G | >);
  GG`Order:= #N;
  GGtoN:= hh^-1 * h;

  U:= TotallyPositiveUnits(R);
  if #U eq 1 then 
    //vprint Quaternion, 2 : "UnitGroup: only one class of totally pos. units.";
    O`UnitMap:= FixMap(GGtoN);
    if debug then check_unit_group(GG, O`UnitMap); end if;
    return GG, O`UnitMap;
  end if; 

  // E_48 and E_120=SL(2,5) cannot be enlarged
  // maybe counting elements of certain traces is faster, see [Vigneras80]
  if #GG in {24, 60} and IdentifyGroup(GG) in {<24, 12>, <60, 5>} then
    vprint Quaternion, 1 : "UnitGroup: E_48 or E_120 = SL(2,5).";
    O`UnitMap:= FixMap(GGtoN);
    if debug then check_unit_group(GG, O`UnitMap); end if;
    return GG, O`UnitMap;
  end if;

  assert (R ! 1) in U;
  Exclude(~U, 1);
  // G uses another copy of N (elements might differ by -1)
  N:= Codomain(h);

  if IsCyclic(GG) then
    vprint Quaternion, 1 : "UnitGroup: cyclic group of order", 2*#GG;
    // in this case, we cannot do much, but using a brute force search
    // or using norm equations or unit groups of splitting fields.
    if #GG eq 1 then
      T:= KernelMatrix(Matrix(Integers(), [Eltseq(R ! Trace(b)): b in B]));
      B0:= ChangeUniverse(Rows(Matrix(K, T) * BMat), A);
      for i in [1..#U] do
        ok, x:= has_element_of_norm(B0, U[i]);
	if ok then 
          vprint Quaternion, 2 : "UnitGroup: Found unit in a sublattice.";
	  Append(~NewUnits, x);
	  if #NewUnits eq 2 or i eq #U then break; end if;
	  // There might be second generator. But this must anti-commute with x.
          T:= KernelMatrix( Matrix( Integers(), Coordinates([b*x + x*b : b in B], B) ) );
          B0:= ChangeUniverse(Rows(Matrix(K, T) * BMat), A);
	end if;
      end for;
    else
      ok:= exists(x){ GGtoN(g) : g in GG | Order(g) eq #GG };
      assert ok;

      // There are two possibilities. First we look for a unit in K(x) with nonsquare norm.
      NF:= NumberField(MinimalPolynomial(x));
      NFA:= AbsoluteField(NF);
      MNFA:= MaximalOrder(NFA);
      // we need K(x) meet O:
      C:= Coordinates([ e[2] * x + e[1] where e:= Eltseq(NF ! b) : b in Basis(MNFA) ], B);
      LmeetKx:= StandardLattice(#B) meet Lattice(Matrix(C));

      Bx:= [ &+[ b[i]*B[i]: i in [1..#B] | b[i] ne 0] : b in Basis(LmeetKx) ];
      for u in U do
        ok, y:= has_element_of_norm(Bx, u);
        if ok then
          Append(~NewUnits, y);
          Exclude(~U, u);
          vprint Quaternion, 2 :  "UnitGroup: Found unit in a commutative suborder.";
          break;
        end if;
      end for;

/*      M:= Matrix(K, [Eltseq(A!1), Eltseq(A!x)]);
      S:= Solution(M, [ Vector(K, Eltseq(&+[ b[i]*B[i]: i in [1..#B] | b[i] ne 0])) : b in Basis(LmeetKx)] );
      OmeetKx:= sub< MNFA | [NFA | NF ! Eltseq(s): s in S] >;

      UOKx, hOKx:= UnitGroup(OmeetKx);
      UOKxModSqr, hUOKxModSqr:= quo< UOKx | [2*g : g in Generators(UOKx)] >;
      for g in UOKxModSqr do
        if IsIdentity(g) then continue; end if;
        xx:= NF ! (g @@ hUOKxModSqr @ hOKx);
        nxx:= R ! Norm(xx);
        if IsSquare(nxx) then continue; end if;
        xx:= e[1] + e[2] * x where e:= Eltseq(xx);
        // found a new unit, so remove its normclass from the set U.
        ok:= exists(u){u: u in U | IsSquare(R ! (nxx / u))};
        assert (xx in O) and ok;
        Append(~NewUnits, xx);
        Exclude(~U, u);
        vprint Quaternion, 2 :  "UnitGroup: Found unit in a commutative suborder."; 
        break g;
      end for;*/

      // now we look for a unit e with e*x=x^-1*e with norm in U.
      if not IsEmpty(U) then
        T:= KernelMatrix( Matrix( Integers(), Coordinates([b*x - xinv*b : b in B], B) ) ) where xinv:= x^-1;
        if Nrows(T) ne 0 then
	  B0:= ChangeUniverse(Rows(Matrix(K, T) * BMat), A);
          for u in U do
	    ok, y:= has_element_of_norm(B0, u);
            if ok then 
              Append(~NewUnits, y);
              vprint Quaternion, 2 :  "UnitGroup: Found unit in a sublattice.";
	      break;
            end if;
          end for;
        end if;
      end if;
    end if;
  else
    if #GG eq 12 and IdentifyGroup(GG) eq <12, 3> then
      vprint Quaternion, 1 :  "UnitGroup: E_24 = SL_(2,3)";
      for t in N do
        // any element with trace 0 should do
        if Trace(t) eq 0 then cands:= [1+t]; break; end if;
      end for;
    else
      n:= #GG div 2;
      vprint Quaternion, 1 :  "UnitGroup: H_n4 with n=", n;
      if n eq 2 then
        // This is a nasty one. Only one of these three works.
        cands:= [1+n: n in N | not IsScalar(n)];
      else
        for g in GG do
          if Order(g) eq n then
            // we need an element of order 2*n in the Norm1Group, so...
            t:= GGtoN(g);
            if t^n ne 1 then break; end if;
            if IsOdd(n) then t:= -t; break; end if;
          end if;
        end for;
        // I am not sure if we need them all.
        // If not, we can greatly simplify the rest of this function...
        cands:= [1+t^i: i in [1..n by 2] | GCD(n, i) eq 1];
      end if;
    end if;

    norms:= [Norm(c): c in cands];
    // combine those that have the same norms
    uniquenorms:= Setseq(Seqset(norms));
    cands:= [ cands[ [i: i in [1..#norms] | norms[i] eq n] ] : n in uniquenorms ];

    for u in U do
      for i in [1..#uniquenorms] do
        ok, tt:= IsSquare(u/uniquenorms[i]);
        if ok then
          for c in cands[i] do
            if (c*tt) in O then
              Append(~NewUnits, c*tt);
              break u;
            end if;
          end for;
        end if;
      end for;
    end for;
  end if;

  if #NewUnits ne 0 then
    for u in NewUnits do ok, G, h:= AddGenerator(G, u); end for;
    assert ok;
    hh:= (G`GenericGroup)`q;
    GG:= Codomain(hh);
    //hh, GG:= CosetAction(G, sub< G | >);
  end if;
  O`UnitMap:= FixMap(hh^-1 * h);
  if debug then check_unit_group(GG, O`UnitMap); end if;
  return GG, O`UnitMap;
end intrinsic;


////////////////////////////////////////////////////////////////
// Order classes and ideal classes

ListPrimes:= function(R, Num, D)
  case Type(R):
    when RngInt:
      List:= [];
      p:= 1;
      repeat
        p:= NextPrime(p);
        if D mod p ne 0 then Append(~List, <p,p>); end if;
      until #List ge 5;
      return List, [];

    when RngUPol:
      List:= [];
      k:= BaseRing(R);
      i:= 1;
      repeat
        L:= AllIrreduciblePolynomials(k, i);
        for f in L do
          if Valuation(D, f) eq 0 then Append(~List, <f,f>); end if;
        end for;
        i +:= 1;
      until #List ge 5;
      return List, [];

  else
    NCl, h:= NarrowClassGroup(R);
    // we need prime ideals that generate this group, at least modulo the norms of the twosided ideals
    S:= sub< NCl | 2*NCl, [(f[1]) @@ h : f in Factorization(D) | IsOdd(f[2]) ] >;
    RayClassPrimes:= [];
    // now look for ideals with small norm
    p:= 1;
    while #S ne #NCl do
      p:= NextPrime(p);
      for f in Decomposition(R, p) do
        if (Valuation(D, f[1]) eq 0) and (f[1] @@ h) notin S then
          Append(~RayClassPrimes, <f[1], p>);
          S:= sub< NCl | S, f[1] @@ h >;
          if #S eq #NCl then break; end if;
        end if;
      end for;
    end while;

    // choose the smallest odd split primes not dividing D
    Primes:= [];
    p := 2;
    while #RayClassPrimes + #Primes lt Num do 
      p := NextPrime(p);
      for f in Decomposition(R, p) do
        P := f[1];
        if RamificationDegree(P) eq 1 and InertiaDegree(P) eq 1 and
           Valuation(D,P) eq 0 and (<P,p> notin RayClassPrimes) then 
          Append(~Primes, < Norm(f[1]), f[1], p >);
        end if;
        if #RayClassPrimes + #Primes ge Num then break; end if;
      end for;
    end while;

    // Sort by the number of maximal right ideals we will get
    Primes:= [ <P[2], P[3]>: P in Sort(Primes) ];

    return Primes, RayClassPrimes;
  end case;
end function;


MassInfinity:= function(F)
  if Type(F) eq FldRat then
    return 1/12;
  elif Type(F) eq FldFunRat then
    return 1/((#BaseRing(F))^2-1);
  else
    S := LCM(CyclotomicQuadraticExtensions(F));
    // Sort out all possible m such that [F(zeta_m):F] = 2.
    Sdiv := [m : m in Divisors(S) | m ne 1 and Valuation(m,2) ne 1]; // avoid repetition
    Sdiv := [m : m in Sdiv |
             &and[Degree(f[1]) eq 2 : f in Factorization(CyclotomicPolynomial(m), F)]];
    Lden := Lcm(Sdiv);

    // WARNING: in LSeries, the Precision vararg does NOT guarantee 
    // that L-values are correct to this much relative precision!!!
    // I'm adding 'extra' (just a random guess which I hope is enough).
    // --- SRD, October 12
    extra := 4;
    L := LSeries(NumberField(F) : Precision := 6 + extra);
    z := Real(Evaluate(L, -1));
    tz10 := Log(Lden*Abs(z))/Log(10);
    if tz10 ge 4 then
      LSetPrecision(L, Ceiling(tz10) + 3 + extra );
      z := Real(Evaluate(L, -1));
    end if;
    return 2^(1-Degree(F)) * Abs(Round(Lden*z)/Lden) * ClassNumber(F);
  end if;
end function;

intrinsic Mass(O::AlgAssVOrd) -> FldRatElt
  {Returns the mass of an order O in a definite quaternion algebra 
   over Q, F_q(X) or a totally real number field.}

  if not assigned O`masstotal then
    A := Algebra(O);
    T := Type(BaseField(A));
    require T in {FldRat, FldFunRat} or ISA(T, FldAlg) : "Base field not supported";
    require Type(A) eq AlgQuat and IsDefinite(A) :
      "The algebra is not a definite quaternion algebra";

    F:= BaseField(A);
    mass:= MassInfinity(F);
    for f in FactoredDiscriminant(O) do
      q:= T eq FldFunRat select (#BaseRing(F))^Degree(f[1]) else Norm(f[1]);
      mass *:= q^f[2] * (1-q^-2)/(1-EichlerInvariant(O, f[1])*q^-1);
    end for;
    O`masstotal:= mass;
  end if;
  return O`masstotal;
end intrinsic;


get_coords:= function(O, p)
  if Type(O) eq AlgQuatOrd then
    B:= Basis(O);
    pO:= ideal< O | p >; 
  else
    B:= LocalBasis(O, p : Type:= "Submodule");
    B:= ChangeUniverse(B, O);
    pO:= ideal< O | Generators(p) >;
  end if;
  A:= Algebra(O);
  BI:= Matrix([Eltseq(A ! b) : b in B] )^-1;
  k, h:= ResidueClassField(p);
  T:= Matrix(k, 1, [ Trace(B[i]) @ h : i in [1..4] ]);
  P:= PolynomialRing(k);
  v:= Valuation(Discriminant(O), p);

  found:= false;
  repeat
    e:= &+[ B[i] * (Random(k) @@ h) : i in [1..4] ];
    m:= P ! [ x @ h : x in Eltseq(MinimalPolynomial(e)) ];
    roots:= Roots(m);
    if #roots eq 2 then
      e:= (e - (roots[1,1] @@ h)) * (((roots[2,1] - roots[1,1])^-1) @@ h);
      S:= HorizontalJoin(T, Matrix( [ [ v[j] @ h : j in [1..4] ] where v:= Vector(Eltseq(A ! (B[i] * e))) * BI : i in [1..4] ] ));
      K:= Kernel(S);
      assert Dimension(K) eq 1;
      x:= &+ [e[i] @@ h *B[i] : i in [1..4] | e[i] ne 0] where e:= Eltseq(K.1);
      found := true;
    elif v eq 0 and #roots eq 1 and roots[1,2] eq 2 then
      x:= e - (roots[1,1] @@ h);
      if x notin pO then
        S:= HorizontalJoin(T, Matrix( [ [ v[j] @ h : j in [1..4] ] where v:= Vector(Eltseq(A ! (x * B[i]))) * BI : i in [1..4] ] ));
        s:= Solution(S, Vector(k, [1,0,0,0,0]));
        e:= &+ [ee[i] @@ h *B[i]  : i in [1..4] | ee[i] ne 0] where ee:= Eltseq(s);
        found:= true;
      end if;
    end if;
  until found;

  // now wlog. e and x map to the upper entries of M(2,k)
  f:= 1-e;
  S:= HorizontalJoin(T, Matrix( [ [ v[j] @ h : j in [1..4] ] where v:= Vector(Eltseq(A ! (B[i] * f))) * BI : i in [1..4] ] ));
  K:= Kernel(S);
  assert Dimension(K) eq 1;
  y:= &+ [e[i] @@ h *B[i]  : i in [1..4] | e[i] ne 0] where e:= Eltseq(K.1);

  if v eq 0 then
    // Let's get a ring isomorphism O/pO -> M(2,k). Wlog. only y is off by a scalar.
    y*:= ((Trace(x*y) @ h)^-1) @@ h;
  end if;

  assert not debug or ([e,x,y,f] subset O);

  return e, x, y, f;
end function;


// Caching: O`RightIdealClasses is a list of records with this format.
// (Also used to store data for the Hilbert modular forms precomputation)

rids_record := recformat< orders:SeqEnum,    // a list of conjugacy classes of Orders 
                          rids:SeqEnum,      // a list of RightIdealClasses
                          support:SeqEnum,   // primes dividing the norms of the rids

                          rids1:SeqEnum,     // rids were obtained by converting from rids1
                          rids_conversion:SeqEnum, 

                          tps:Assoc,         // array with values [[tps_ij:i]:j]
                          tps_rows:Assoc,    // array recording which rows of tps have been computed
                          rids_colonZBs:Assoc,      // used in precompute_tps
                          rids_narrow_class_junk:List // ""
                        >;


// This function is SUPPOSED to work over Q and F_q(X) as well 
// (i.e. it gets called from ConjugacyClasses)
// mkirschm -- Feb 2009

RightIdealClassesAndOrders:= function(O : Support:= [], strict_support:= true, 
                                          compute_order_classes:= true,
                                          avoid_IsIsometric:= false);
  A:= Algebra(O);
  F := BaseField(A);
  Z_F:= BaseRing(O);
  flat:= Type(F) in {FldRat, FldFunRat};
  error if not flat and not IsAbsoluteField(F), 
    "The base field of the algebra must be absolute.";
  if flat then
    _Support:= Type(F) eq FldRat select func< x | Set(PrimeDivisors(Integers() ! x)) >
                                   else func< x | { f[1] : f in Factorization(Z_F ! x) } >;
  else
    _,_Support := IsIntrinsic("Support");
  end if;

  // check if stored in O`RightIdealClasses, which is a list of entries [* Support, Ideals, Orders *]
  if assigned O`RightIdealClasses then
    for rec in O`RightIdealClasses do
      if (IsEmpty(Support) or rec`support subset Support) and 
         (not compute_order_classes or assigned rec`orders)
      then
        return rec`rids, rec`orders;
      end if;
    end for;
  end if;

  vprint Quaternion: "Computing RightIdealClassesAndOrders.";
  if debug then 
    vprint Quaternion: "IN DEBUG MODE";
  end if;

  if flat then
    mult:= function(I,J)
      IJ:= rideal< O | [ x*y : x in Basis(I), y in Basis(J) ] >;
      if assigned(I`Norm) and assigned(J`Norm) then IJ`Norm:= Norm(I) * Norm(J); end if;
      return IJ;
    end function;
    test_iso:= IsRightIsomorphic;
  else
    mult:= func< I, J | mult_no_check(I,J : Sides:= "Right") >;
    // initialise data to be passed to IsIsomorphicInternal 
    real_places := RealPlaces(F);
    U, Umap := pFundamentalUnits(Z_F, 2);
    Uvals := [RealValuations(real_places, Umap(U.i)) : i in [1..Ngens(U)]];
    units_vals := <U, Umap, Uvals>; 
    test_iso:= func<I, J : JJ:=0 | IsIsomorphicInternal(I, J : JJ:= JJ, real_places:= real_places, 
                                                               UnitRealValuations:= units_vals) >;
  end if;

  DA:= Discriminant(A);
  DO:= Discriminant(O);

  if IsEmpty(Support) then
    Primes, RayClassPrimes:= ListPrimes(Z_F, 1, DO); 
    Primes:= RayClassPrimes cat Primes;
    strict_support := false; // two-sided ideals will involve divisors of DO
  else
    vprint Quaternion, 2: "Support was specified to be", Support;
    if Type(Support) ne SeqEnum then
      Support := [P : P in Support];
    end if;
    if flat then
      ok, Support:= CanChangeUniverse(Support, Z_F);
      error if not ok or exists{p: p in Support | not IsPrime(p)},
           "Support must only contain prime ideals of the base ring of O.";
    else
      error if not forall{p: p in Support | IsPrime(p) and Order(p) cmpeq Z_F },
           "Support must only contain prime ideals of the base ring of O.";
    end if;
    // FIXME/TO DO: Use all primes coprime to Discriminant(A).
    // This requires, that we can handle EichlerOrders of Level p^n locally with pMatrixring ... 
    //  ... we can now handle level p, at least  --SRD
    Primes:= [<p, flat select p else Minimum(p)> : p in Support | Valuation(DA,p) eq 0 and Valuation(DO,p) le 1];
    if strict_support and _Support(DO) subset Support then
      strict_support := false; // it's okay to use all two-sided ideals
    end if;
  end if;
  // Current strict_support setting is final

  actual_support := Primes;  // only used for verbose
  if not strict_support then
    actual_support cat:= [<t[1], flat select t[1] else Minimum(t[1])> : t in FactoredDiscriminant(O)];
  end if;
  vprint Quaternion: "Support to be used is", [t[1] : t in actual_support];
  vprint Quaternion: "These primes lie above", [t[2] : t in actual_support];

  if not flat then 
    NCl, NClh:= NarrowClassGroup(Z_F);
    vprint Quaternion: "The narrow class group of the base field is", grpab_to_string(NCl); 
    if #NCl gt 1 and IsVerbose("Quaternion") then
      printf "Narrow classes of primes in the support are:"; 
      for t in actual_support do 
        printf " %o", Eltseq(t[1]@@NClh);
      end for;
      printf "\n";
    end if;

    if not IsEmpty(Support) then
      // Support was specified, so check 
      // (this is not a sufficient but a necessary condition)
      error if NCl ne sub< NCl | [p[1] @@ NClh : p in Primes] cat (strict_support select [] else  
                                 [(f[1]) @@ NClh : f in FactoredDiscriminant(O) | IsOdd(f[2])]) >,
           "The support does not generate the narrow class group";
    end if;

    // Use automorphisms of the field, if possible
    // IMPORTANT: for correctness, must ensure at all stages that the 
    // set of ideal classes found is closed under the action of Auts
    a := F!(A.1^2);
    b := F!(A.2^2);
    assert A.3 eq A.1*A.2;
    AutsF := [m : m in Automorphisms(F) | m(F.1) ne F.1 and m(a) eq a and m(b) eq b];
    Auts := [map< A->A | x:-> A![m(c) : c in Eltseq(A!x)] > : m in AutsF];
    // For now, only use the subgroup of Auts that fix the original order
    inds := [i : i in [1..#Auts] | [m(x) : x in ZBasis(O)] subset O where m is Auts[i]];
    Auts := [Auts[i] : i in inds];
    AutsF := [AutsF[i] : i in inds];
    // Auts must preserve the set of Primes 
    // TO DO: if Support not specified, enlarge Primes so they are stable
    Primes1 := {t[1] : t in Primes};
    inds := [i : i in [1..#Auts] | forall{P: P in Primes1 | 
                                   ideal<Z_F| {x@m : x in Generators(P)}> in Primes1}
                                   where m is AutsF[i]];
    Auts := [Auts[i] : i in inds];
    AutsF := [AutsF[i] : i in inds];
  end if;

  use_Auts := not flat and #Auts gt 0;

  if not flat or strict_support then
    avoid_IsIsometric := true;
  end if;
  // Current avoid_IsIsometric setting is final

  use_thetas := not flat;
  // use theta series of orders to quickly distinguish order classes
  // TO DO: use thetas also over Q, not only FldNum

  use_norm_classes := not flat and #NCl gt 1; // avoid testing IsNarrowlyPrincipal for every Norm(I)/Norm(J)

  use_Jprime := not flat and Degree(F) le 8; 
  // reason: between degree 8 and 10, the lattice stuff starts to dominates, and Jprime makes that worse
  // TO DO: Jprime is bad for memory, should maybe be careful of that?

  if use_Jprime then
    // make JJs coprime to small primes, so the same JJs can be used for small Hecke operators
    bad_primes_for_Jprime := &* Setseq(Seqset( [tup[1] : tup in Primes] cat Support cat PrimesUpTo(20,F) ));
  end if;

  masstotal := Mass(O);

  vprint Quaternion: "Now starting search for ideal classes";
  vprint Quaternion: " -- search will terminate when masstotal =", masstotal;
  if use_Auts then
    vprintf Quaternion: " -- using %o nontrivial field automorphisms\n", #Auts;
  end if;
  if use_Jprime then
    vprint Quaternion: " -- using the J' trick";
  end if;
  if use_thetas then
    vprint Quaternion: " -- using theta series";
  end if;

  // The Unitgroup does not mod out Z_F^* in the "flat" cases. We take care of this here.
  case Type(F):
    when FldRat: correction := 2;
    when FldFunRat: correction := #BaseRing(F)-1;
    else correction := 1;
  end case;

  s:= #FactoredDiscriminant(O);
  Orders:= [O];
  ZBases:= [ZBasis(O)];
  generations:= [0];                 // the number of p-neighbour steps from the original order
  O`graph:= [[Integers()| ]];        // O`graph[i] contains j if the jth order was a neighbour of the ith
  orders_from_Auts := [Integers()| ]; // indices of orders obtained from other orders via Auts

  vprintf Quaternion, 2: "Determining two-sided ideal class group: "; 
  vtime Quaternion, 2: 
  List:= TwoSidedIdealClasses(O : Support:= Support);
  if strict_support then 
    List:= [ I : I in List | _Support(Norm(I)) subset Support ];
  end if;
  assert forall{I : I in List | IsIdentical(LeftOrder(I), O)}; // this assigns I`LeftOrder 
  NumberOfTwoSided:= [#List];
  if use_norm_classes then
    norm_classes:= [Norm(I) @@ NClh : I in List];
    // TO DO: could be much more elaborate 
    //      + the classes of the neighbours could mostly be obtained from eachother
    //      + avoid computing Nnu for each quotient in IsIsomorphicInternal (as in get_tps)
  end if;
  if use_Jprime then
    JJs := [<JJ,b,P> where JJ,b,P is Jprime(I : coprime_to:= bad_primes_for_Jprime) : I in List];
  end if;
  vprint Quaternion, 1: "Determining unit group:"; 
  vtime Quaternion, 1: 
  u:= correction / #UnitGroup(O);
  masses := [<u,#List>];
  massfound:= #List * u;
  assert masstotal ge massfound;
if false and debug and not strict_support and Type(F) ne FldFunRat then 
    cl := flat select 1 else ClassNumber(Z_F);
    forms := flat select GramMatrix(O) else GramMatrices(O: LLL:=true);
    aut := AutomorphismGroup(forms);
    assert massfound eq cl * #NormOneGroup(O) * 2^(1+s) / #aut;
  end if;

  pValuations:= [Valuation(DO, p[1]): p in Primes];

  vprintf Quaternion, 1: "Starting with %o class%o, mass = %o out of %o\n", 
                         #List, #List ne 1 select "es" else "", massfound, masstotal;
  time0 := Cputime();

  num_iso_tests := 0; // only for verbose info
  time_iso_tests := Cputime();

  check_all_subideals := flat or IsOdd(#NCl);

get_full_graph := false;
if get_full_graph then
 check_all_subideals := true;
 use_Auts := false;
end if;

  PrimesChecked:= [ {Integers() | } ];
  i:= 1; // index of current order
  j:= 0; // index of current prime
while (massfound ne masstotal) or 
get_full_graph and exists{s: s in O`graph | #s lt 1+Norm(Primes[1][1])} do
        
      // TO DO: better to take random edges for random [order,prime] pairs.
      // Currently we try all (or many) edges for each [order,prime] pair.
      // (Actually this isn't clear; it would be better in the case where 
      // there are lots of multiple edges between the same two order classes.)

      // run through pairs [order,prime] systematically
      j +:= 1;
      if j gt #Primes then
        j := 1;
        // Choose another order: 
        // explore those with large unit group first, since they will tend to have
        // neighbours with large unit group (these are the hardest classes to find);
        // if these are similar, we prefer orders closer to the original order, 
        // (to keep the powers of primes small).
        // TO DO: keep track of which [neighbour,prime] pairs have been checked for each order
        priorities := [ExtendedReals()| i in orders_from_Auts or #PrimesChecked[i] eq #Primes
                                        select -Infinity() else 1/masses[i][1] - generations[i] 
                                      : i in [1..#Orders]];
        max, i := Max(priorities);
        if max eq -Infinity() then
          if not check_all_subideals then
            vprint Quaternion: "WARNING: heuristic strategy failed in RightIdealClassesAndOrders";
            // Start again and check all subideals for each order and prime
            // (TO DO: this does happen in the following kind of scenario:
            // there are two orders not yet found, one is not a neighbour the current order
            // while the other has very small mass and its only neighbour is the current order.)
            check_all_subideals := true;
            PrimesChecked:= [ {Integers() | }^^#Orders ];
            i := 1;
            j := 0;
            continue;
          else
            error "Something is seriously wrong in RightIdealClassesAndOrders";
          end if;
        end if;
      end if;
      Include(~PrimesChecked[i], j);

      pp:= Primes[j,1];
      p := Primes[j,2];
      vprintf Quaternion, 1: "Trying p-neighbour ideals for prime #%o (over %o) and order #%o\n", j, p, i;
      k, mk := ResidueClassField(pp);
      index:= 1+ &+NumberOfTwoSided[1..i-1];
      OO:= Orders[i];
      ZbasisOO:= ZBases[i];
      genpp:= flat select [ OO ! pp ] else ChangeUniverse(Generators(pp), OO);

      x11, x12, x21, x22:= get_coords(OO, pp);
      BOp:= [OO | x11, x12, x21, x22 ];

      used := []; // points in P^1(k) used so far
      tries := 0; // number of subideals tried since a new class was found
      num_total:= pValuations[j] eq 0 select #k+1 else 2*#k;
      flip:= false; // toggle, used in 2*#k case
      museq:= []; // initialize to avoid error

      for counter := 1 to num_total do  

        if not check_all_subideals then
          // Switch to the next pair (i,j) if it seems likely there won't be more new classes from this pair
          // TO DO: refined mass formula! or else should make sure to jump to a different genus when we switch
          expected := masstotal/(masstotal-massfound); // = expected # of tries to get a new class (assuming Poisson)
          C := 2^Max(1, 4 - (#Orders-i) ); // be careful about switching when there are not many orders left
          if tries gt C*expected then
            vprintf Quaternion: "Switching after trying %o neighbours of order #%o\n", tries, i;
            break counter; 
          end if; 
        end if; 

        tries +:= 1;
        vprintf Quaternion, 2: ".";
        if counter eq num_total then 
          vprintf Quaternion, 2: "\n";
        end if;

        if flip then
          flip:= false;
          mu:= OO!(BOp[3] + museq[1]*BOp[4] + museq[2]*BOp[2]);
        else
          if (#used eq 0) and (pValuations[j] eq 0) then 
            // if pp | DO the current setup below produces the unique integral twosided ideal of norm pp. So skip this.
            used := [[k|0,1]];
            museq := [0,1];
          else 
            repeat x := Random(k); until [1,x] notin used; 
            Append(~used, [1,x]);
            museq := [1,x@@mk];
          end if;
          mu := OO!(museq[1]*BOp[1] + museq[2]*BOp[3]);
          flip:= pValuations[j] ne 0;
        end if;

        I := rideal<OO | Append(genpp, mu) >;
        assert IsMaximal(O) or RightOrder(I) eq OO;		// If this fails, we managed to pick a noninvertible ideal!
        I`RightOrder := OO;					// use same copy of the order for all the I's
        if debug then
          assert Norm(I) eq pp;
        else
          I`Norm := pp;
        end if;
 
        // Check whether the class of I is new i.e. whether its left order is already there
        // This bit has become simpler: always avoid_IsIsometric in the non-flat case
        // (the ideal testing is now highly optimized).
        // TO DO: when (and if) the new IsIsometric is there, see if it's faster.

        if not avoid_IsIsometric then
          LO:= LeftOrder(I);
          for k:= 1 to #Orders do
            try
              LO_is_old:= IsIsomorphic1(Orders[k], LO: FindElement:= false); 
            catch ERR
              error "Isomorphism testing of orders failed. PLEASE, report this example!";
            end try;
            if LO_is_old then 
              Append(~O`graph[i], k);
              continue counter; 
            end if;
          end for;
          vprintf Quaternion, 2: "\n";
          vprintf Quaternion: "New class found after %os\n", Cputime(time_iso_tests);
        end if;

        // now either we are in "avoid_IsIsometric" mode or we found a new order.
        // Anyway, replace I by I*J where J connects O[i] with O.
        assert IsIdentical(I`RightOrder, List[index]`LeftOrder); 
        I:= mult(I, List[index]);

        if avoid_IsIsometric then 
          if use_norm_classes then
            NClI := Norm(I) @@ NClh;
          end if;
          if use_thetas then
            theta := theta_series(LeftOrder(I));
          end if;

          sum:= 1;
          for k in [1..#Orders] do
            range:= [sum..sum+NumberOfTwoSided[k]-1];
            sum +:= NumberOfTwoSided[k];
            if use_thetas and not IsWeaklyZero(theta - theta_series(Orders[k])) then
              continue; // LeftOrder(I) is not in the kth order class
            end if;
            for jj in range do
              if use_norm_classes and NClI ne norm_classes[jj] then
                continue; // I is not in the jj'th ideal class
              end if;
              num_iso_tests +:= 1;
              if use_Jprime then
                // avoid_IsIsometric, not flat
                // Note: the Jprime trick assumes I is a proper ideal of its order
                I_is_old := test_iso(I, List[jj] : JJ:=JJs[jj]);
                if debug then 
                  assert I_is_old eq test_iso(I, List[jj] : JJ:=0);
                end if;
              else
                I_is_old := test_iso(I, List[jj]);
              end if;
              if I_is_old then
                Append(~O`graph[i], k);
                continue counter;
              end if;
            end for; // jj
          end for; // k

          vprintf Quaternion, 2: "\n";
          vprintf Quaternion: "New class found after %os (%o ideal-isomorphism tests)\n", 
                               Cputime(time_iso_tests), num_iso_tests;
          num_iso_tests := 0;
          time_iso_tests := Cputime();
        end if;

        tries := 0; // reset

        // I is a new ideal class, and its left order LO is a new order class.
        // Next get the other LO-O-ideals as T*I where T are 2-sided LO-ideals

        // The Galois conjugates of I are also classes not seen so far,
        // since the set of ideal classes found so far is Galois stable
        // (So it suffices to test them against eachother)
        GalI := [I];
        if use_Auts then
          for tau in Auts do 
            Itau := rideal< O | [x@tau: x in ZBasis(I)] >;
            Itau`RightOrder := O;
            Itau`Norm := ideal< Z_F | {Z_F| x@tau : x in Generators(Norm(I))} >;
            Append(~GalI, Itau);
            if debug then 
              LO:= LeftOrder(I);
              LOtau := Order([A| x@tau : x in ZBasis(LO)]);
              CheckOrder(LOtau);
              assert LOtau eq LeftOrder(Itau);
              CheckIdeal(Itau);
            end if;
          end for;
        end if;

        // TO DO: assign more stuff to the conjugates?

        // If 'flat or not use_Auts', GalI = [I] and no iso-testing occurs here
        num_old := #List;
        for g := 1 to #GalI do 
          I := GalI[g];
          // Compare I with the new ideals already listed
          for jj := 1 + num_old to #List do 
            if test_iso(I, List[jj] : JJ:= use_Jprime select JJs[jj] else 0) then
              continue g; // the ideal class of I was already listed
            end if;
          end for;
          if g gt 1 then
            vprint Quaternion: "Obtained a new class from Galois action";
          end if;
          LO := LeftOrder(I); // could compute LO using Galois action

          vprint Quaternion, 2: "Determining two-sided ideal class group:"; 
          vtime Quaternion, 2: 
          T:= TwoSidedIdealClasses(LO : Support:= Support);
          if strict_support then
            T:= [ t : t in T | _Support(Norm(t)) subset Support ];
          end if;
          vprint Quaternion, 1: "Determining unit group:"; 
          vtime Quaternion, 1: 
          u:= correction / #UnitGroup(LO);
if false and debug and not strict_support and Type(F) ne FldFunRat then 
            cl := flat select 1 else ClassNumber(Z_F);
            forms := flat select GramMatrix(O) else GramMatrices(O: LLL:=true);
            aut := AutomorphismGroup(forms);
            assert #T*u eq cl * #NormOneGroup(O) * 2^(1+s) / #aut;
          end if;
          massfound +:= #T*u;
          Append(~masses, <u,#T>);
          Append(~ZBases, ZBasis(LO));
          Append(~NumberOfTwoSided, #T);
          Append(~Orders, LO);
          Append(~generations, 1+generations[i]);
          Append(~PrimesChecked, {Integers()| });
          if g gt 1 then
            Append(~orders_from_Auts, #Orders);
          end if;
          Append(~O`graph[i], #Orders);
          Append(~O`graph, [Integers()| ]);

          for t in T do
            tI:= mult(t, I);
            tI`RightOrder:= O;
            tI`LeftOrder:= LO;
            if debug then assert forall{l : l in List | not test_iso(l, tI) }; end if;
            Append(~List, tI);
            if use_norm_classes then
              Append(~norm_classes, Norm(tI) @@ NClh);
            end if;
            if use_Jprime then
              Append(~JJs, <JJ,b,P> where JJ,b,P is Jprime(tI : coprime_to:= bad_primes_for_Jprime));
            end if;
          end for;

        end for; // g

        vprintf Quaternion, 1: "Now found %o ideal classes, with mass %o out of %o (%o%%)\n", 
                               #List, massfound, masstotal, 
                               RealField(Floor(Log(10,1+pc))+2)!pc where pc is 100*massfound/masstotal;
        vprintf Quaternion, 2: "Mass contributions for orders so far are \n%o\n", 
                               #masses gt 1000 select Multiset(masses) else  
                               [* t[2] eq 1 select t[1] else t : t in masses *];
        if masstotal eq massfound then 
          vprintf Quaternion, 1: "Finished!  Search for ideal classes took %os\n", Cputime(time0);
if not get_full_graph then
          break; 
end if;
        end if;
        error if (masstotal lt massfound), "Found too many RightIdealClasses!";
        if debug and not flat then
          // The ModFrmHil code assumes that the left orders are identical iff they are equal 
          assert &and[ exists{Ord: Ord in Orders | IsIdentical(JJ`LeftOrder, Ord)} : JJ in List ]; 
        end if;
      end for; // counter

  end while; // massfound ne masstotal

  if use_thetas then
    vprint Quaternion, 2: "Theta series of the left orders (sorted):", 
                              Sort([theta_series(OO) : OO in Orders]);
  end if;

  if (masstotal ne massfound) then
    assert not IsEmpty(Support);
    // really, this should never ever happen
    error "The given support was not large enough to enumerate all classes!";
  end if;

  if compute_order_classes and strict_support then
    vprint Quaternion, 1: "Support did not contain the divisors of the discriminant!",
                          "\nNow determining conjugacy classes of orders";
    cc_time0 := Cputime();
    sum:= 1;
    Conn:= [];
    for i:= 1 to #Orders do
      Append(~Conn, List[sum]);
      sum +:= NumberOfTwoSided[i];
    end for;
    i:= 1;
    while i le #Orders do
      T:= TwoSidedIdealClasses(Orders[i]);	// is cached anyway
      I:= Conjugate(Conn[i]);
      for j in [#Orders..i+1 by -1] do
        _, IJ:= Conn[j] * I;			// do not call mult here! 
        if exists{t : t in T | test_iso(IJ, t) } then
          NumberOfTwoSided[i]+:= NumberOfTwoSided[j];
          Remove(~Orders, j);
          Remove(~NumberOfTwoSided, j);
          Remove(~Conn, j);
          if NumberOfTwoSided[i] eq #T then break; end if;
        end if;
      end for;
      assert(NumberOfTwoSided[i] eq #T);
      i+:= 1;
    end while; 
    vprint Quaternion, 1: "Time for conjugacy classes of orders:", Cputime(cc_time0);

  elif not compute_order_classes and strict_support then
    // we have not computed the conjugacy classes, so don't cache the Orders
    Orders:= [Universe(Orders)| ];
  end if;

  if not flat and #NCl gt 1 then
    // Sort ideals according to the narrow ideal class of their norms
    // DO NOT CHANGE this -- Hilbert modular forms rely on it
    norm_classes := [Eltseq(Norm(I) @@ NClh) : I in List];
    ParallelSort(~norm_classes, ~List);
  end if;

  // Cache results, using minimal Support
  Support := Setseq(&join[ _Support(Norm(I)) : I in List ]);
  if not assigned O`RightIdealClasses then 
    O`RightIdealClasses := [* *]; 
  end if;
  rec := rec< rids_record | rids := List, support := Support >;
  if not IsEmpty(Orders) then 
    rec`orders := Orders;
  end if;
  Append(~O`RightIdealClasses, rec);

  return List, Orders; 
end function;


RayClassGroupPrimeReps:= function(O : ModTwoSided:= false)
  R:= BaseRing(O);
  if Type(R) in {RngInt, RngUPol} then return []; end if;

  _, inf:= RamifiedPlaces(Algebra(O));
  if IsEmpty(inf) then
    G, h:= ClassGroup(R);
  else 
    G, h:= RayClassGroup( &+ inf );
  end if;
  if ModTwoSided then
    G, hh:= quo< G | 2*G, [ (p[1]) @@ h : p in FactoredDiscriminant(O) | IsOdd(p[2]) ] >;
    h:= hh^-1 * h;
  end if;
  
  Found:= {G | Id(G)};
  List:= [];
  p:= 2;
  DA:= Discriminant(Algebra(O));
  DO:= Discriminant(O);
  while #Found ne #G do
    for P in Decomposition(R, p) do
      // FIXME/TO DO :: should only be Discr(A), if pMatrixRing can handle primes dividing the level 
      if Valuation(DA, P[1]) eq 0 and Valuation(DO, P[1]) le 1 then
        g:= (P[1]) @@ h;
        if g notin Found then
          Include(~Found, g);
          Append(~List, P[1]);
          if #Found eq #G then break; end if;
        end if;
      end if;
    end for;
    p:= NextPrime(p);
  end while;
  return List;
end function;

//intrinsic CanonicalSuborders(O::AlgAssVOrd, p::. : TypeRep:= 0) -> []
//{}
function CanonicalSuborders(O, p : TypeRep:= 0)
  A:= Algebra(O);
  if Type(O) eq AlgQuatOrd then
    B:= Basis(O);
    B:= ChangeUniverse(B, A);
    pO:= [p*b : b in B];
    OrderInt:= QuaternionOrder;
    pi:= p;
    even:= Abs(p) eq 2;
  else
    B:= LocalBasis(O, p : Type:= "Submodule");
    pO:= [g*b : b in Generators(O), g in Generators(p)];
    OrderInt:= Order;
    pi:= UniformizingElement(p);
    even:= Minimum(p) eq 2;
  end if;

  if TypeRep cmpne 0 then
    dim:= 3 - Valuation(Discriminant(TypeRep), p) + Valuation(Discriminant(O), p);
    assert dim in {1,2};
    T:= TernaryForm(TypeRep);
    if Type(O) eq AlgQuatOrd then
      QNF:= RationalsAsNumberField();
      pp:= p*Integers(QNF);
      T:= NumberFieldLatticeWithGram(Matrix(QNF, T));
    else
      pp:= p;
    end if;
    TypeRep:= < IsEichler(TypeRep), T >;
  end if;

  k, h := ResidueClassField(p); hi:= h^-1;
  BM:= Matrix(B);
  BMI:= BM^-1;
  M:= RModule(k, 4);
  Q, hh:= quo< M | [ x @ h: x in Eltseq(BMI[1]) ] >;

  if TypeRep cmpne 0 then
    S:= Submodules(Q : CodimensionLimit:= 3-dim);
  else
    S:= Submodules(Q);
  end if;

  G:= BM * GramMatrix(NormSpace(A)) * Transpose(BM);
  discO:= Valuation(Discriminant(O), p);
  assert discO eq Valuation(Determinant(G), p) div 2;

  L:= [];
  for s in S do
    if (Rank(s) in {0,3}) or (TypeRep cmpne 0 and Rank(s) ne dim) then continue; end if;

    t:= s @@ hh;
    N:= ChangeUniverse(Basis(t), M);

    // Use Peter's criterion to decide if s constitutes a local Gorenstein order.
    C:= Complement(M, t);
    BN:= VerticalJoin( ChangeRing( Matrix(N), hi ) , pi * ChangeRing( Matrix(ChangeUniverse(Basis(C), M)), hi ) );
    GN:= BN * G * Transpose(BN);
    DN:= GN^-1;
    if even then for i in [1..4] do DN[i,i] /:= 2; end for; end if;
    l:= -Minimum( [ Valuation(DN[i,j], p) : i in [1..j], j in [1..4] ] );
    d:= discO + 3-Dimension(s);
    assert not debug or d eq Valuation(Determinant(GN), p) div 2;
    // The criterion is now: (l eq d)
    if (l ne d) then continue; end if;

    BN:= [ &+[B[j] * (n[j] @@ h) : j in [1..4] | n[j] ne 0] : n in N ];
    if debug then
      X:= Matrix([ Eltseq(x*y): x,y in BN ]) * BMI;
      if sub< M | [ [ e @ h : e in Eltseq(x) ] : x in Rows(X) ] > ne t then assert l ne d; continue; end if;
    end if;
    OO:= OrderInt([1] cat BN cat pO);
    assert Discriminant(OO) eq Discriminant(O) * p^(3-Dimension(s));
    if debug then assert IsGorenstein(OO); end if;

    if RadicalIdealizer(OO, p) ne O then continue; end if;

    if TypeRep cmpne 0 then
      if TypeRep[1] then 
        if not IsEichler(OO) then continue; end if;
      else
        T:= TernaryForm(OO);
        if Type(O) eq AlgQuatOrd then
          T:= NumberFieldLatticeWithGram(Matrix(QNF, T));
        end if;
        if not IsLocallyIsometric( TypeRep[2], T, pp ) then continue; end if;
      end if;
    end if;

    Append(~L, OO);
  end for;
  return L;
end function;
//end intrinsic;

function MyOrbitStab(G, h, X)
  n:= Ngens(G);
  A:= [ h(G.i) : i in [1..n] ];
  Orbit:= {@ X @};
  Path:= [ Id(G) ];
  Stab:= sub< G | >;

  i:= 1;
  while (i le #Orbit) and (#Stab * #Orbit lt #G) do
    for j in [1..n] do
      x:= Path[i] * G.j;
      Y:= Orbit[i]^A[j];
      idx:= Index(Orbit, Y);
      if idx eq 0 then
        Include(~Orbit, Y);
        Append(~Path, x);
      else
        x:= x * Path[idx]^-1;
        if x notin Stab then Stab:= sub< G | Stab, x >; end if;
      end if; 
    end for;
    i:= i+1;
  end while;

  assert #Stab * #Orbit eq #G;
  return Orbit, Stab;
end function;

procedure SetNormalizerFromStab(O, OO, Stab, h)
  Gens:= [ Algebra(O) | h(Stab.i) : i in [1..Ngens(Stab)] ];
  if Type(O) eq AlgQuatOrd then
    T:= (BasisMatrix(O) * BasisMatrix(OO)^-1);
    Stab:= ChangeRing(Stab, Rationals())^( GL(4, Rationals()) ! T);
    Stab:= ChangeRing(Stab, Integers());
  else ;
//    Stab:= Stab^( Generic(Stab) !  T );
  end if;
  OO`Normalizer:= SetupNormalizerMap(Stab, Gens, OO, 0);
// test
//  NN, hh:= Normalizer(OO);
//  assert forall{ n : n in NN | n eq (n @ hh) @@ hh };
//  assert forall{ n : n in Generators(NN) | OO^hh(n) eq OO };
end procedure;

// ConjugacyClasses would work for every order, provided we implement:
// * local isometry tests over Fq[X]. That is very easy.
// * normalizers for indefinite orders. 
intrinsic ConjugacyClasses( O :: AlgAssVOrd : Al:= "AllOrders") -> SeqEnum
  {Returns a sequence of representatives of the conjugacy classes of Eichler orders that have the same level as O.}
  A:= Algebra(O);
  F:= BaseField(A);
  require Type(A) eq AlgQuat : "Only implemented for quaternion orders.";
  require (Type(F) in {FldRat, FldFunRat} and Characteristic(F) ne 2) or ISA(Type(F), FldNum) : 
    "The base ring is not supported.";

  if IsDefinite(A) then
    if Al cmpne "AllOrders" then
      "WARNING: 'Al' option in ConjugacyClasses is obselete and is now ignored!";
    end if;
    if IsEichler(O)  then
      _, Orders:= RightIdealClassesAndOrders(O);
    else
      require Type(F) ne FldFunRat: "Non-Eichler orders over function fields are currently not supported";

      // Repeated application of GorensteinClosure and RadicalIdealizer 
      // yields an ascending chain of orders whose normalizers grow and the last element is hereditary.
      OO:= O;
      Chain:= [];
      Primes:= [ p[1]: p in FactoredDiscriminant(O) | p[2] ne 1 ];
      Norms:= [ Norm(p): p in Primes ];
      ParallelSort(~Norms, ~Primes);
      for p in Reverse(Primes) do
        while not IsHereditary(OO, p) do
          G, b:= GorensteinClosure(OO);
          if IsOne(b) then
            Append(~Chain, < OO, p, true > );
            OO:= RadicalIdealizer(OO, p);
          else
            Append(~Chain, < OO, b, false > );
            OO:= G;
          end if;
        end while;
      end for;

      assert IsHereditary(OO);
      _, Orders:= RightIdealClassesAndOrders(OO);

      // Now we construct the conjugacy classes of all orders in the chain, by inverting
      // the previous operations in reverse order.
      // If G is the Gorenstein closue of O with Brandt invariant b, then O = <1, b*G >.
      // If the radical idealizer of X is O, then X can be computed by "CanonicalSuborders".
      // Two such orders are conjugate in the algebra iff they are conjugate in the normalizer of O.

      for i in [#Chain..1 by -1] do
        Orders2:= [];
        if not Chain[i,3] then
          b:= Chain[i,2];
          for OO in Orders do
            if Type(O) eq AlgQuatOrd then
              X:= QuaternionOrder( [1] cat [b*x: x in Basis(OO)] );
            else
              X:= Order( [1] cat [g*x: g in Generators(b), x in Generators(OO)] );
            end if;
            if assigned(OO`Normalizer) then
              N, h:= Normalizer(OO);
              SetNormalizerFromStab(OO, X, N, h);
            end if;
            Append(~Orders2, X); 
          end for;  
        else
          p:= Chain[i, 2];
          for OO in Orders do
            C:= CanonicalSuborders(OO, p : TypeRep := Chain[i,1]);
            C:= Set(C);
            N, h:= Normalizer(OO);
            while not IsEmpty(C) do
              X:= Chain[i,1] in C select Chain[i,1] else Rep(C);
              Orbit, Stab:= MyOrbitStab(N, h, X);
              size:= #C;
              C:= C diff Set(Orbit);
              assert size eq #C + #Orbit;
              SetNormalizerFromStab(OO, X, Stab, h);
              Append(~Orders2, X);
            end while;
          end for;
        end if;
        Orders:= Orders2;
      end for;

      idx:= Index(Orders, O);
      assert idx ne 0;
      Orders[idx]:= Orders[1];
      Orders[1]:= O;
    end if;
  else
    require IsEichler(O): "Indefinite non-Eichler orders are not supported";
    Orders:= [O];
    Primes:= RayClassGroupPrimeReps(O : ModTwoSided:= true);
    for p in Primes do
      a:= get_coords(O, p);
      Append(~Orders, LeftOrder(rideal<O | [a] cat Generators(p)>));
    end for; 
  end if;
  return Orders;
end intrinsic;


