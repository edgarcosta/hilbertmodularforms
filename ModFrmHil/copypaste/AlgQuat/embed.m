freeze;

//////////////////////////////////////////////////////////////////////////////
//
// Quadratic Embeddings into Quaternion Algebras
// February-March 2006, John Voight
//
// Last modified March 2010, Steve Donnelly
//
//////////////////////////////////////////////////////////////////////////////

debug := false;

/****************************************************************************

  CHANGE LOG:

  !!!! PLEASE record all changes here          Thanks!   -- Steve

  November 2011 -- Markus
    pMatrixRing now works for orders of type AlgQuatOrd directly.

  March 2010 -- Markus
    Add missing case in Embed and allow more base fields

  March 2010 -- Steve
    In pMatrixRing, also increase precision if conjugating matrix T 
    or its inverse don't have enough precision.

    Now not using the old pMatrixRing in any cases -- not sensible to 
    maintain two implementations of the same thing.  (The only reason 
    for keeping the old one until now was that it's sometimes slightly 
    faster, but only because it used too low precision).

  January 2009 -- JV
    It is more convenient to compute a splitting "once and for all"
    for a given prime (since this is probabilistic): so now we store it.

  July 2008 -- Steve
    Fixed pMatrixRing (Precision should now be nearly okay)
    now lifting by hand instead of using LiftPoint

  July 2008 -- Matt 
    Added new case in pMatrixRing(AlgQuatOrd, p) for Eichler orders 
    where p appears only once in the level (identifies order with the
    standard Eichler order in the matrix ring)
    
  September 2007  -- Steve
    Added new alternative version of pMatrixRing, called pMatrixRing1,
    which is called when all else fails, namely whenever the (new) 
    'Precision' vararg is specified, and in cases which would otherwise 
    hit the "not implemented" error or the good old "Too many tries" error.

    Catch errors in the call to MatrixRing in pMatrixRing, and try again.

  July 2007  --  Steve
    Fixed two bugs in Embed(FldAlg, AlgQuat):
    1) The code incorrectly assumed the AlgQuat was in standard form
    2) The case where A.l^2 = K.1^2 slipped through a crack in the logic
    (See comments in the code.)
    Also added a check at the end of Embed.

****************************************************************************/

declare attributes AlgAssVOrd : pMatrixRings;

import "interface.m" : MatrixRingInternal;
import "enumerate.m" : EnumerativeSearchInternal;

//-------------
//
// These intrinsics could use further development; in particular, they lack
// functionality to compute optimal embeddings, or to enumerate such.
// These seem to be computationally quite hard problems, at least when
// the quaternion algebra (or the base field) become complicated enough.
// 
//-------------

intrinsic '!!'(Z_K::RngOrd, p::RngInt) -> RngOrdIdl
  {}

  return ideal<Z_K | Generator(p)>;
end intrinsic;

//-------------
//
// Algorithms to find an embedding of a quadratic field in a quaternion algebra.
//
//-------------

intrinsic InternalConjugatingElement(alpha::AlgQuatElt, beta::AlgQuatElt) -> AlgQuatElt
  {Finds a basis of elements nu such that nu^(-1)*alpha*nu = beta.}

  require MinimalPolynomial(alpha) eq MinimalPolynomial(beta) :
    "Arguments must have the same minimal polynomial";

  M := RepresentationMatrix(alpha : Side := "Left");
  M -:= RepresentationMatrix(beta : Side := "Right");
  return [Parent(alpha) ! nu : nu in Basis(Kernel(M))];
end intrinsic;

intrinsic HasEmbedding(K::Fld, A::AlgQuat : ComputeEmbedding := false) -> BoolElt, ., .
  {Determine if there exists an embedding of the quadratic extension K into A;
   and if so and ComputeEmbedding is true, return an embedding;
   if not, return a witness place.}

  F:= BaseField(K);
  require F cmpeq BaseField(A) and Degree(K) eq 2 :
    "The first argument should be a quadratic extension of the base field of the algebra";

  T:= Type(F);
  if T in {FldRat, FldFunRat} then
    if T eq FldRat then
      if IsTotallyReal(K) and IsDefinite(A) then return false, Infinity(), _; end if;
      Z_K:= MaximalOrder(K);
    else
      require IsFinite(BaseRing(F)) and Characteristic(F) ne 2 : "The field is not supported.";
      if IsDefinite(A) and #InfinitePlaces(K) eq 2 then return false, Infinity(), _; end if;
      Z_K:= MaximalOrderFinite(K);
    end if;
    if exists(p){ p : p in RamifiedPrimes(A) | IsSplit(p, Z_K) } then return false, p, _; end if;
  else
    require ISA(T, FldAlg) : "The field is not supported.";

    Z_K := MaximalOrder(K);
    S, Soo := RamifiedPlaces(A);
    // if exists(p){ p : p in S |  #Factorization(Z_K!!p) eq 2 } then return false, p; end if;
    if exists(p){ p : p in S | IsSplit(p, Z_K) } then return false, p, _; end if;

    d := Discriminant(MinimalPolynomial(K.1));
    if exists(v){v: v in Soo | Evaluate(d,v) gt 0} then return false, v, _; end if;
  end if;

  if ComputeEmbedding then
    mu, h := Embed(K,A);
    return true, mu, h;
  end if;
  return true, _, _;
end intrinsic;

intrinsic IsSplittingField(K::Fld, A::AlgQuat : ComputeEmbedding := false) -> BoolElt, ., .
  {"} // "
  return HasEmbedding(K, A : ComputeEmbedding:= ComputeEmbedding);
end intrinsic;

intrinsic Embed(K::Fld, A::AlgQuat : Al := "NormEquation", 
                                        Basis := []) -> AlgQuatElt, Map
  {Find an embedding of the quadratic extension K into A.  The default
   algorithm "NormEquation" works by solving a conic (the algorithm for
   this does not involve solving a norm equation, in most cases) the other 
   option Al:="Search" performs a brute-force search.  The optional parameter 
   Basis may be used to specify a Z-basis to be used for the search; otherwise, 
   an LLL basis for a maximal order is used.}

  F := BaseField(K);
  if Type(F) eq FldOrd then
    F := NumberField(F);
  end if;
  require F eq BaseField(A) : "Arguments must have the same base field";
  require Degree(K) eq 2 : "First argument must be a quadratic extension";

  if Type(K) eq FldOrd then
    K := NumberField(K);
  end if;

  T:= Type(F);
  if T ne FldRat and not ISA(T, FldAlg) then
    require ISA(T, FldFunG) : "Base field is not supported";
    require Characteristic(F) ne 2 : "Not implemented for characteristic 2";
    Al:= "NormEquation";
  end if;

  // Compute a representative squareroot which generates K.
  alpha := K.1;
  da := Discriminant(MinimalPolynomial(alpha));
  PF := PolynomialRing(F);
  xF := PF.1;
  KK := ext<F | xF^2-da/4>;
  hKK := hom<KK -> K | alpha-Trace(alpha)/2>;
  invhKK := hom<K -> KK | KK.1+Trace(alpha)/2>;

  if Al eq "NormEquation" then
    // a, b := StandardForm(A); 
    // we need the map as well (the code below incorrectly assumes that A.1^2 = a and A.2^2 = b)
    // The following is exactly the same as what StandardForm does. (Steve added this)
    A_orig := A;
    a, b, A, A_orig_to_A := StandardForm(A_orig); 
    assert A.1^2 eq A!a and A.2^2 eq A!b;

    bl, sqrta := IsSquare(a);
    if bl then
      M2F, phi := MatrixRing(A, (A.1-sqrta)*A.2);
      mu := Inverse(phi)(M2F![0,1,da/4,0]);
    else 
      bl1, sqrta := IsSquare(KK!a); 
      if bl1 then 
        // missing case, added by Steve
        // Use the solution [sqrta,1,0] to x^2-ay^2 = bz^2 over KK,
        // and copy the "hard-coded" thing from below...
        s1,s2 := Explode(Eltseq(sqrta));  // in fact sqrta = s2*KK.1
        mu := A![s1,1,0,0] / A![s2,0,0,0];
      else
        // Solve the equation x^2-ay^2 = b with x,y in KK
        // (solving conic uses better algorithm than NormEquation)
        C := Conic([KK| 1, -a, -b]);
        bl, sol := HasRationalPoint(C);
        error if not bl, "The given field K does not embed in the algebra A";
        assert sol[3] ne 0; // otherwise in case above
        gg := [KK| sol[1]/sol[3], sol[2]/sol[3] ];
        g := [Eltseq(gg[1]), Eltseq(gg[2])];
        if g[1][2] eq 0 and g[2][2] eq 0 then
          M2F, phi := MatrixRing(A, A ! [g[1,1] , g[2,1], -1, 0]);
          mu := Inverse(phi)(M2F![0,1,da/4,0]);
        else
          // Hardcoded formula giving the embedding KK -> A by mu.
          mu := A![g[1][1],g[2][1],1,0] / A![g[1][2],g[2][2],0,0];
        end if;
      end if;
    end if;

    // convert back to A_orig  (Steve)
    mu := mu @@ A_orig_to_A;
    A := A_orig;

  elif Al eq "Search" then
    if Basis eq [] then
      O := MaximalOrder(A);
      if Type(BaseRing(O)) eq RngInt or not IsTotallyReal(F) then
        B := ZBasis(O);
      else
        B := ReducedBasis(O);
      end if;
    else
      B := Basis;
    end if;
    d := #B;

    lim := 1;

    L := StandardLattice(d);
    P := ShortVectorsProcess(L, lim);
    found := false;

    // Loop over small linear combinations of the basis vectors.
    while not found do
      v := NextVector(P);
      if v eq L!0 then
        lim +:= 1;
        P := ShortVectorsProcess(L, lim);
      end if;

      mu := &+[Eltseq(v)[i]*B[i] : i in [1..d]];
      dmu := Discriminant(MinimalPolynomial(mu));

      // We have an embedding if and only if the ratio of discriminants
      // is a square.
      rts := Roots(xF^2-dmu/da, F);  
      if #rts gt 0 then
        u := rts[1][1];

        mu /:= u;
        mu -:= -Trace(mu)/2;
      end if;
    end while;
  else
    error "Unknown algorithm in Al";
  end if;
  
  emb := invhKK * hom< KK -> A | mu>;

  if debug then
    assert mu^2 eq A! F! (KK.1^2);
    assert emb(K.1) eq mu+A!(Trace(alpha)/2);
  end if;

  return mu+A!(Trace(alpha)/2), emb;
end intrinsic;

//-------------
//
// Algorithms to find an embedding of a quadratic order in a quaternion order.
//
//-------------

intrinsic Embed(Oc::RngOrd, O::AlgAssVOrd : Al := "Conjugation", Basis := []) 
                                            -> AlgAssVOrdElt, Map
  {Find an embedding of the quadratic order Oc into the quaternion order O.  
   First, it finds an embedding of algebras K -> A, then conjugates into O;
   the optional parameters are passed to Embed(K, A).}

  Z_F := BaseRing(Oc);

  K := FieldOfFractions(Oc);
  A := Algebra(O);
  mu, h := Embed(K, A);
    
  // Conjugate gamma so that it is in O.
  mu := h(Oc.2);
  bl, nu := InternalConjugatingElement(O, mu);
  if not bl then
    error "Failure in principalization--we need a new algorithm for definite quaternion algebras";
  end if;
  return O!(nu*mu*nu^(-1)), map<Oc -> O | x :-> nu*h(K!x)*nu^(-1)>;
end intrinsic;

//-------------
//
// Algorithms to find local embeddings.
//
//-------------

intrinsic QuadraticNormForm(B::SeqEnum[AlgQuatElt] : Prime := false) -> RngMPolElt
  {Returns the norm form as a quadratic form on the elements in B, with
   coefficients modulo the prime p if specified.}

  if Type(Prime) eq RngOrdIdl then 
    k, mk := ResidueClassField(Prime);
    P := PolynomialRing(k, #B);
  else
    R := BaseRing(Parent(B[1]));
    mk := map<R -> R | x :-> x>;
    P := PolynomialRing(R, #B);
  end if;
  Q := [ &+[P.i*P.j*mk(Norm(B[i]+B[j])-Norm(B[i])-Norm(B[j]))/2 :
           j in [i..#B]] : i in [1..#B]];
  return &+Q;
end intrinsic;

intrinsic InternalCriticalPrimes(O::AlgAssVOrd, mu::AlgQuatElt) -> SeqEnum
  {Return the sequence of primes p such that mu is not in O_p.}

  if BaseRing(O) cmpeq Integers() then
    M := Matrix(Basis(O))^-1;
    // Coefficients of mu in the basis of O.
    muO := (Matrix(BaseRing(M),1,4,Eltseq(mu))*M)[1];
    P := {};
    for i := 1 to 4 do
      if muO[i] ne 0 then 
        P join:= {p[1] : p in Factorization(Numerator(1/muO[i]))};
      end if;
    end for;
  else
    M := Matrix(PseudoMatrix(O))^-1;
    C := CoefficientIdeals(PseudoMatrix(O));
    // Coefficients of mu in the basis of O.
    muO := (Matrix(BaseRing(M),1,4,Eltseq(mu))*M)[1];
    P := {};
    for i := 1 to 4 do
      if muO[i] ne 0 then 
        P join:= {p[1] : p in Factorization(C[i]/muO[i]) | p[2] gt 0};
      end if;
    end for;
  end if;

  return P;
end intrinsic;

intrinsic PseudoMatrix(O::AlgQuatOrd) -> PMat
  {Returns an artificially constructed pseudobasis of O.}

  return PseudoMatrix(Matrix(Basis(O)));
end intrinsic;

intrinsic InternalCriticalValuation(O::AlgAssVOrd, mu::AlgQuatElt, 
                                    p::RngOrdIdl) -> RngIntElt
  {Returns the valuation e needed to conjugate mu into O at p.}

  M := Matrix(PseudoMatrix(O))^-1;
  C := CoefficientIdeals(PseudoMatrix(O));
  muO := (Matrix(BaseRing(M),1,4,Eltseq(mu))*M)[1];
  e := 0;
  for i := 1 to 4 do
    if muO[i] ne 0 then 
      e := Max(e, Valuation(C[i]/muO[i], p));
    end if;
  end for;

  return e;
end intrinsic;

intrinsic InternalCriticalValuation(O::AlgQuatOrd, mu::AlgQuatElt, 
                                    p::RngIntElt) -> RngIntElt
  {Returns the valuation e needed to conjugate mu into O at p.}

  M := Matrix(Basis(O))^-1;
  muO := (Matrix(BaseRing(M),1,4,Eltseq(mu))*M)[1];
  e := 0;
  for i := 1 to 4 do
    if muO[i] ne 0 then 
      e := Max(e, Valuation(1/muO[i], p));
    end if;
  end for;

  return e;
end intrinsic;

function pConjugatingElementInternal(O, mu, p, e);
  A := Algebra(O);
  F := BaseField(A);

  // With a call to pMatrixRing, which will be stable for O, it suffices
  // to conjugate mu into normal form, which will then be p-integral as
  // mu is integral.
  M2F, phi, mFp := pMatrixRing(O, p);
  C, T := RationalForm(Matrix(F,2,2,[m@@mFp : m in Eltseq(phi(mu))]));
  T := Eltseq(T);
  nu := Inverse(phi)(M2F![mFp(t) : t in T]);

  // We actually only need nu up to precision e (larger for characteristic 2). 
  if Valuation(F!2,p) gt 0 then
    if Type(p) eq RngIntElt then
      Fp, mFp := Completion(F, p : Precision := (2*1+1)+2);
    else
      Fp, mFp := Completion(F, p : Precision := (2*RamificationDegree(p)+1)+2);
    end if;
  else
    Fp, mFp := Completion(F, p : Precision := e+2);
  end if;
  nu := A![mFp(Eltseq(nu)[i])@@mFp : i in [1..4]];
  if Valuation(Norm(nu),p) lt 0 then
    nuExp := -1;
    nu := nu^(-1);
    nu := A![mFp(Eltseq(nu)[i])@@mFp : i in [1..4]];
  else
    nuExp := 1;
  end if;

  // Any element in p^e*O + nu*O will be a conjugating element modulo p^e;
  // we must search for one which is supported only at p
  pp := rideal<O | Generators(p^e) cat [nu]>;

  // Get a "Minkowski-reduced" basis
  bl, nu := IsPrincipal(pp);
  if not bl then
    return false, _;
  else
    return true, nu^nuExp;
  end if;
end function;

intrinsic InternalConjugatingElement(O::AlgAssVOrd, mu::AlgQuatElt) -> BoolElt, AlgQuatElt
  {Returns an element nu such that nu*mu*nu^(-1) is in O.}

  P := InternalCriticalPrimes(O, mu);
  nu := 1;
  while not IsCoercible(O, mu) do
    for p in P do
      bl, nu0 := InternalpConjugatingElement(O, mu, p);
      if not bl then
        return false, _;
      end if;
      nu := nu0*nu;
      mu := nu0*mu*nu0^(-1);
    end for;
  end while;

  return true, nu;
end intrinsic;

intrinsic InternalpConjugatingElement(O::AlgAssVOrd, mu::AlgQuatElt, 
                                      p::RngOrdIdl) -> BoolElt, AlgQuatElt
  {Returns an element nu such that nu*mu*nu^(-1) is in O_p.}

  // Compute the valuation e needed to conjugate into O.
  e := InternalCriticalValuation(O, mu, p);

  if e gt 0 then
    bl, nu := pConjugatingElementInternal(O, mu, p, e);
    return bl, nu;
  else
    return true, Algebra(O)!1;
  end if;
end intrinsic;

intrinsic InternalpConjugatingElement(O::AlgQuatOrd, mu::AlgQuatElt, 
                                      p::RngIntElt) -> BoolElt, AlgQuatElt
  {Returns an element nu such that nu*mu*nu^(-1) is in O_p.}

  // Compute the valuation e needed to conjugate into O.
  e := InternalCriticalValuation(O, mu, p);

  if e gt 0 then
    bl, nu := pConjugatingElementInternal(O, mu, p, e);
    return bl, nu;
  else
    return true, Algebra(O)!1;
  end if;
end intrinsic;

//-------------
//
// New alternative pMatrixRing routine (by Steve)
//
//-------------

// Given a 2x2 matrix algebra M2F over a field F containing a maximal order OF,
// and a (maximal) order R in M2F specified by an OF basis, find some T in M2F 
// such that R = T^-1 * M_2(OF) * T.  If successful, return 'true' and T.
// If this turns out not to be possible, then R was not maximal, so return 'false'
// Currently OF is required to be Euclidean, so that matrix operations such as
// EchelonForm can be used on M_2(OF).
// TO DO: Always return false when it doesn't give an isomorphism
/*
intrinsic ConjugatingMatrix(M2F::AlgMat, basis::SeqEnum[AlgMatElt], OF::Rng) 
                         -> BoolElt, AlgMatElt
{Find T such that T*R*T^-1 = M_2(OF), where R is the order in M2F 
 generated as a free OF-module by the given basis (which should 
 consist of 4 elements of M2F)}
*/
function ConjugatingMatrix(M2F, basis, OF)
  assert Universe(basis) eq M2F and #basis eq 4;
  error if not HasEchelonForm(OF), "OF must have an Echelon form algorithm";
  F := BaseRing(M2F);  
  error if not IsField(F), "The first argument should be a matrix algebra over a field";
  F2 := VectorSpace(F,2);
  OF2 := RModule(OF,2);
  M2OF := MatrixAlgebra(OF,2);

  // Get the 2-dimensional lattice L := (1,0)*R, so that 
  // R is the right multiplicator ring of L
  
  Lgens := [F2.1 * basis[i] : i in [1..#basis]];
  // Scale L, so that it's integral (ie contained in OF2)
  // TO DO: How to get denoms in more generality?
  if Type(OF) eq RngInt or ISA( Type(OF), RngOrd) then 
     denom := LCM(Flat([[ Denominator(a) : a in Eltseq(v)] : v in Lgens]));
  elif ISA( Type(OF), RngPad) or Type(OF) eq RngSerPow then
     pi := UniformizingElement(OF);
     minval := Min([0] cat &cat[[ Valuation(a) : a in Eltseq(v)] : v in Lgens]);
     denom := pi ^ -minval;
  end if;
  Lgens := [OF2| Eltseq(denom*vec) : vec in Lgens];

  E := EchelonForm(Matrix(Lgens));
  Lbas := E[1..2];
  T := M2F! Matrix(Lbas); // change of basis from standard basis to Lbas (acting on rows, from right)
  bool, Tinv := IsInvertible(T);  
  if not bool then 
     return false, _; 
  elif not &and[ IsCoercible(M2OF, T*m*Tinv) : m in basis] then
     return false, _; 
  end if;
  return true, T;
end function;

// Given a maximal order O_B in B and a prime pr, this routine returns a splitting homomorphism 
// O_B --> M_2(O_pr), where O_pr is the completion of O_F at pr. The output is in the format 
// F_pr, O_pr, and the maps F --> F_pr, O_F --> O_pr and O_B --> M_2(O_pr).

function split_max_order(OH, pr, prec : extra_prec:=10, hp:=0 ); 
     H := Algebra(OH);
     F := BaseRing(H); 
     OF := BaseRing(OH);  
     TZBasis:=TraceZeroSubspace(OH);
     flat:= Type(BaseRing(OH)) in {RngInt, RngUPol};

// temp, compensate bug in (partially) ramified completions
safe_prec := 2*(prec+extra_prec);
     // need extra prec in hp (because then toHp will give this for each coord,
     // but when the coords have different valuations we lose precision in the sum)
     if hp cmpeq 0 then
       Fp, hp:=Completion(F, pr: Precision:=safe_prec);
     else
       Fp := Codomain(hp);
       if Fp`DefaultPrecision lt safe_prec then
         Fp`DefaultPrecision := safe_prec;
       end if;
     end if;
     Op:=Integers(Fp);
     gp:=hom<OF->Op| s :-> Op!hp(F!s)>;
     pi:=UniformizingElement(Fp);
     hp`IsHomomorphism:= true;
     Hp, toHp:=ChangeRing(H, Fp, hp); // the completion of the quaternion algebra H at p.

     // find a basis for the trace zero subspace locally (ie over the completion of OF)
     if flat then
       TZBasis_red:= TZBasis;
     else
       TZBasis_red:=[];
       for l:=1 to 3 do
         gens:=Basis(TZBasis[l][1]);
         _,idx:=Min([Valuation(gen,pr) : gen in gens]);  
         Append(~TZBasis_red, gens[idx]*TZBasis[l][2]);
       end for;
     end if;

     // basis for OH tensor the completion
     OHBasis := Basis(OH);
     if flat then 
       OHBasislocal:= [ OH ! b: b in OHBasis ];	// important for some Eltseq operations later.
     else
       OHPseudoBasis:=PseudoBasis(OH);
       OHBasislocal:=[OH| ];
       for l:=1 to 4 do
         gens:=Basis(OHPseudoBasis[l][1]);
         _,idx:=Min([Valuation(gen,pr) : gen in gens]);  
         Append(~OHBasislocal, OH!(gens[idx]*OHBasis[l]) );
       end for;
     end if;

     /* Here find an orthogonal basis of the reduction of maximal order modulo p with respect to the 
        trace form. If the reduction of the maximal order is not a division ring, we will find a zero-
        divisor in this process. */

     // Define the Trace form on the trace zero subspace
     tznorms:=[OF| Norm(tz) : tz in TZBasis_red];
     crossterms:=[OF| Norm(TZBasis_red[1]+TZBasis_red[2]) - tznorms[1] - tznorms[2],
                      Norm(TZBasis_red[1]+TZBasis_red[3]) - tznorms[1] - tznorms[3],
                      Norm(TZBasis_red[2]+TZBasis_red[3]) - tznorms[2] - tznorms[3] ];
     PRF<X, Y, Z>:=PolynomialRing(F, 3);
     Q0 := tznorms[1]*X^2 + tznorms[2]*Y^2 + tznorms[3]*Z^2 + 
           crossterms[1]*X*Y + crossterms[2]*X*Z + crossterms[3]*Y*Z;
     assert 0 eq Min([Valuation(s,pr) : s in Coefficients(Q0)]); // no common factor

     // the conic must have smooth reduction, so solve it over the finite field and lift 
     C:=Conic(ProjectiveSpace(PRF), Q0);
     GFP, modP:=ResidueClassField(Op);
     mymodP:=map<BaseRing(C)->GFP | aa:->aa@hp@modP>;
     C_red:=BaseChange(C,mymodP);  
     error if IsSingular(C_red), "Something is wrong in pMatrixRing. Is the order really maximal?";
     bool, P1:=HasPoint(C_red);  assert bool;
     // lift P1 (it's a smooth point on the reduction, so we can lift with two coords fixed)
     Fpxx := PolynomialRing(Fp); xx := Fpxx.1;
     PolFp<XX,YY,ZZ> := PolynomialRing(Fp,3);
     pol_map := hom< Parent(DefiningPolynomial(C)) -> PolFp | hp, [XX,YY,ZZ] >;
     C_loc_eqn := DefiningPolynomial(C) @ pol_map;
     lifts := [Fp| P1[i] @@modP : i in [1..3] ];
     for l := 1 to 3 do
       subst := ChangeUniverse(lifts, Fpxx);  subst[l] := xx;
       ok, rt := HasRoot(Evaluate(C_loc_eqn, subst));
       if ok then 
         P2 := [Fp| (i eq l) select rt else lifts[i] : i in [1..3] ];
         // assert Valuation(Evaluate( C_loc_eqn, P2 )) ge prec; // if not, should be caught below anyway
         break; 
       end if;
     end for;  assert ok;
     zerodiv:=&+[ P2[i]*toHp(TZBasis_red[i]) : i in [1..3]];

     if Valuation(Norm(zerodiv)) lt prec then 
       error if extra_prec ge 100, "Error in pMatrixRing: losing too much precision";
       return split_max_order(OH, pr, prec : extra_prec:=extra_prec+10, hp:=hp ); 
     end if;

     // Find the isomorphism to the maximal order M_2(O_p). 
     try 
       M2Fp, toM2Fp:=MatrixRing(Hp, zerodiv);
     catch err
       vprintf Quaternion, 3: "Increasing precision to %o in pMatrixRing...\n", prec+20;
       return split_max_order(OH, pr, prec+20 : extra_prec:=extra_prec, hp:=hp );
     end try;
     BsImag:=[((OHBasislocal[l]@toHp)@toM2Fp): l in [1..4]];
     bool, T:=ConjugatingMatrix(M2Fp, BsImag, Op);  
     if not bool then 
       vprintf Quaternion, 3: "Increasing precision to %o in pMatrixRing...\n", prec+20;
       return split_max_order(OH, pr, prec+20 : extra_prec:=extra_prec, hp:=hp );
     end if;
     M2Opr := MatrixRing(Op, 2);
     _, Ti := IsInvertible(T); 
     Tprec := Min([ AbsolutePrecision(x) : x in Eltseq(T) cat Eltseq(Ti) ]);
     Tden := Max([0] cat [ -Valuation(x) : x in Eltseq(T) cat Eltseq(Ti) ]);
     if Tprec lt prec + Tden then // we're doomed
       extra_prec +:= prec + Tden - Tprec + 10;
       vprintf Quaternion, 3: "Increasing extra precision to %o in pMatrixRing...\n", extra_prec;
       return split_max_order(OH, pr, prec : extra_prec:=extra_prec, hp:=hp );
     end if;

     OHpBasis := [toHp(H!b) : b in OHBasis];  // recall these b's are not in OH 
     basis_images := [M2Fp| T*(b@toM2Fp)*Ti : b in OHpBasis]; 
     OHp_to_M2Fp := Matrix([Eltseq(bim) : bim in basis_images]);
     // OHp_to_M2Fp map Hp ~~> M2Fp, relative to the standard bases of OH and M2Fp
     // we assume this in the inverse map below (otherwise mcoords might not be integral)
     bool, M2Fp_to_OHp := IsInvertible(OHp_to_M2Fp);  
     if not bool then 
       vprintf Quaternion, 3: "Increasing precision to %o in pMatrixRing...\n", prec+20;
       return split_max_order(OH, pr, prec+20 : extra_prec:=extra_prec, hp:=hp ); 
     end if;
     // Conversion between OHBasis and OHBasislocal ... we need to use OHBasislocal 
     // in the inverse map so that the coordinates are locally integral 
     OHBasislocal_to_OHBasis := Matrix(4, [F| e : e in Eltseq(b), b in OHBasislocal]);
     OHBasis_to_OHBasislocal := OHBasislocal_to_OHBasis^-1;
     OHBasis_to_OHBasislocal := Matrix(4, [Fp| hp(F!e) : e in Eltseq(OHBasis_to_OHBasislocal)]);
     basis_inverse_images := [OH! &+[coords_in_OHBasislocal[j]@@hp * OHBasislocal[j] : j in [1..4]]
                                     where coords_in_OHBasislocal is 
                                           Eltseq(M2Fp_to_OHp[i]*OHBasis_to_OHBasislocal)
                             : i in [1..4]];
     toM2Opr:=map<OH->M2Opr| q :-> M2Opr! &+[qcoords[j]*basis_images[j] : j in [1..4]]
                                      where qcoords is [hp(F!qq) : qq in Eltseq(q)],
                             m :-> &+[mcoords[j]*basis_inverse_images[j] : j in [1..4]] 
                                      where mcoords is [OF!((Op!mm)@@hp) : mm in Eltseq(M2Fp!m)] >;
     if debug then
       assert Basis(M2Fp) eq ChangeUniverse(Basis(M2Opr),M2Fp); 
       for zb in ZBasis(OH) do  // check that Eltseq is w.r.t. Basis(OH)
         assert zb eq OH! &+[Eltseq(OH!zb)[j]*OHBasis[j] : j in [1..4]]; end for;
       for b in Basis(M2Opr) cat [(OH!zb)@toM2Opr : zb in ZBasis(OH)] do m:=b;
         assert &and[Valuation(cc) gt prec-10 : cc in Eltseq(m-(m@@toM2Opr@toM2Opr))]; end for;
     end if;

     HBasis_to_OHBasis := Matrix(4, [F| e : e in Eltseq(b), b in OHBasis])^-1;
     scaling := flat select 1 else LCM([ Numerator(Norm( tup[1]*Denominator(tup[1]) )) : tup in OHPseudoBasis ]); // scales OHbasis into OH
     HtoM2Fp := map<H->M2Fp| q :-> M2Fp!(toM2Opr(OH!(q*s)))/hp(s) 
                                     where s is scaling*LCM([Denominator(qc) : qc in Eltseq(qvec)])
                                     where qvec is Vector(Eltseq(q))*HBasis_to_OHBasis,
                             m :-> ((m*s)@@toM2Opr)/(s@@hp) 
                                     where s is pi^-Min([0] cat [Valuation(mc) : mc in Eltseq(m)]) >; 
     return Fp, Op, hp, gp, HtoM2Fp;
end function;

//-------------
//
// pMatrixRing 
//
//-------------

// Precision refers to the absolute precision of the images of ZBasis(O),
// however it may sometimes fall short as this is not checked explicitly
// (although something related is checked).

intrinsic pMatrixRing(A::AlgQuat[FldNum[FldRat]], p::RngOrdIdl : Precision:=20) -> AlgMat, Map, Map
  {If p splits A, returns M_2(F_p), a map A -> M_2(F_p), and the embedding F -> F_p.}

  require IsPrime(p) : "Argument 2 must be prime";
  require CoefficientField(CoefficientField(A)) cmpeq Rationals() : "Argument 1 must be defined over an extension of Q";

  O := pMaximalOrder(TameOrder(A),p);
  return pMatrixRing(O, p : Precision:=Precision);
end intrinsic;

intrinsic pMatrixRing(A::AlgQuat, p::RngElt : Precision:=20) -> AlgMat, Map, Map
  {If p splits A, returns M_2(F_p), a map A -> M_2(F_p), and the embedding F -> F_p.}

  ok, p:= IsCoercible(Integers(BaseField(A)), p);
  require ok and IsPrime(p) and GCD(p, Discriminant(A)) eq 1:
    "p must be prime in the ring of integers of the base field coprime to the discriminant";

  return pMatrixRing(MaximalOrder(A), p : Precision:=Precision);
end intrinsic;

intrinsic pMatrixRing(O::AlgAssVOrd[RngOrd[RngInt]], p::RngOrdIdl : Precision:=20) -> AlgMat, Map, Map
  {If p splits O, returns M_2(F_p), a map A -> M_2(F_p) such that O |-> M_2(Z_F,p),
   and the embedding F -> F_p.}

   require IsPrime(p) : "Argument 2 must be prime";

   require IsCoercible(PowerIdeal(CoefficientRing(O)), p) : "Argument 2 must be an ideal of the coefficient ring of argument 1";

  require Valuation(Discriminant(Algebra(O)),p) eq 0 : 
         "Argument 2 must be an unramified prime for the algebra";

  require Valuation(Discriminant(O), p) le 1 :
         "Argument 2 can divide the level to order at most one!";

  dbro1 := Degree(BaseRing(O)) eq 1;

/*
  vprintf Shimura, 3 : "Computing pMatrixRing for prime of norm %o...", Norm(p);
*/

  if assigned O`pMatrixRings then
    for c in O`pMatrixRings do
      if (c[1] cmpeq p or (dbro1 and Norm(c[1]) eq Norm(p))) then
        return c[2], c[3], c[4];
      end if;
    end for;
  end if;
    
  if Valuation(Discriminant(O), p) eq 1 then
    Omax := MaximalOrder(O);
    M,m,t := pMatrixRing(Omax, p : Precision:=Precision);

    GFp, r := ResidueClassField(RingOfIntegers(BaseRing(M)));
  
    Mp := MatrixAlgebra(GFp,2);
    Np := sub<Mp | [Mp![r(x) : x in Eltseq(m(y))] : y in ZBasis(O)]>;
    bl, ap := IsTriangulable(Np);
    a := M![x@@r : x in Eltseq(ap)];

    n := map<M -> M | x :-> a*x*a^-1, y:-> a^-1*y*a>;

    if assigned O`pMatrixRings then
      Append(~O`pMatrixRings, <p, M, m*n, t>);
    else
      O`pMatrixRings := <<p, M, m*n, t>>;
    end if;
    return M, m*n, t;
  end if; // MG

  A := Algebra(O);
  F := BaseField(A);
  Z_F := MaximalOrder(F);

  _, _, hp, _, toM2Opr := split_max_order(O, p, Precision); 
  M2 := Codomain(toM2Opr); 
  m := toM2Opr; 
  f := hp;

  if assigned O`pMatrixRings then
    Append(~O`pMatrixRings, <p, M2, m, f>);
  else
    O`pMatrixRings := <<p, M2, m, f>>;
  end if;

  return M2, m, f; 
end intrinsic;

intrinsic pMatrixRing(O::AlgQuatOrd, p::RngElt : Precision:=0) -> AlgMat, Map, Map
{Given a R-order in a quaternion algebra B over F, returns an embedding
of B into M_2(F_p) which induces an isomorphism of O_p with M_2(R_p) 
or a suitable subring}
  R:= BaseRing(O);
  ok, p:= IsCoercible(R, p);
  require ok : "The second argument must lie in the base ring of the order";
  case Type(R):
    when RngInt:
      p:= Abs(p); ok:= true; okp:= IsPrime(p: Proof:= false);
    when RngUPol:
      p:= Normalize(p);
      ok:= IsField(F) and IsFinite(F) and Characteristic(F) ge 3 where F:= BaseRing(R);
      okp:= ok and IsPrime(p);
  else ok:= false;
  end case;
  require ok : "Base Ring is not supported";
  require okp and p notin RamifiedPrimes(Algebra(O)):
    "The second argument must be a nonramified prime";
  v:= Valuation(Discriminant(O), p);
  require v le 1: "The second argument must divide the discriminant of the order at most once.";

  if assigned O`pMatrixRings then
    ok:= exists(c){ c : c in O`pMatrixRings | c[1] eq p };
    if ok then return c[2], c[3], c[4]; end if;
  end if;

  if v eq 0 then
    _, _, f, _, m := split_max_order(O, p, Precision); 
    M := Codomain(m);
  else // v == 1
    Omax:= pMaximalOrder(O, p);
    M,m,f := pMatrixRing(Omax, p : Precision:=Precision);

    GFp, r := ResidueClassField(RingOfIntegers(BaseRing(M)));

    Mp := MatrixAlgebra(GFp,2);
    Np := sub<Mp | [Mp![r(x) : x in Eltseq(m(y))] : y in Basis(O)]>;
    bl, ap := IsTriangulable(Np);
    assert bl;
    a := M![x@@r : x in Eltseq(ap)];

    n := map<M -> M | x :-> a*x*a^-1, y:-> a^-1*y*a>;
    m:= m*n;
  end if;

  if assigned O`pMatrixRings then
    Append(~O`pMatrixRings, <p, M, m, f>);
  else
    O`pMatrixRings := <<p, M, m, f>>;
  end if;

  return M, m , f;
end intrinsic;
/*
intrinsic pMatrixRing(O::AlgQuatOrd, p::RngIntElt : Precision:=0) -> Rng, Map
{Computes an embedding of B into M_2(Q_p) which induces an isomorphism of O_p with M_2(Z_p) 
 or a suitable subring}
  require IsPrime(p) : "p must be prime!";
  require GCD(p, Integers()!Discriminant(Algebra(O))) eq 1 : 
         "The algebra containing O must split at p!";

  if assigned O`pMatrixRings then
    for c in O`pMatrixRings do
      if Norm(c[1]) eq Norm(p) then
        return c[2], c[3], c[4];
      end if;
    end for;
  end if;
 
    B := Algebra(O);
    QQ := NumberField(Polynomial([0,1]) : DoLinearExtension := true);
    ZZ := MaximalOrder(QQ);
    pp := p*ZZ;
  
    a, b, Bstd, B_to_Bstd := StandardForm(Algebra(O));    

    BB := QuaternionAlgebra<QQ | a,b>;

    B_to_BB := map<B -> BB | x :-> BB!Eltseq(B_to_Bstd(x)), 
                             y :-> (Bstd!Eltseq(y))@@B_to_Bstd >;

    OO := Order([B_to_BB(x) : x in ZBasis(O)]);

    if assigned O`pMatrixRings then
      OO`pMatrixRings := O`pMatrixRings;
    end if;
    
    M, mm,f := pMatrixRing(OO,pp : Precision:=Precision); 
    m := B_to_BB*mm;

    mmb := [mm(Basis(BB)[i]) : i in [1..4]];
    mmbinv := [Basis(M)[i]@@mm : i in [1..4]];
    mrecover := map<B -> M | x :-> &+[Eltseq(x)[i]*mmb[i] : i in [1..4]],
                             y :-> (&+[(Rationals()!(Eltseq(y)[i])@@f)*mmbinv[i] : i in [1..4]])@@B_to_BB>;

    if assigned O`pMatrixRings then
      Append(~O`pMatrixRings, <p, M, mrecover, f>);
    else
      O`pMatrixRings := <<p,M,mrecover,f>>;
    end if;
    return M, mrecover, f;
end intrinsic;
*/
intrinsic pMatrixRing(O::AlgQuatOrd[RngInt], p::RngInt : Precision := 0) -> AlgMat, Map, Map
{Computes an embedding of B into M_2(Q_p) which induces an isomorphism of O_p with M_2(Z_p) 
 or a suitable subring}
  M, m, f := pMatrixRing(O, Norm(p) : Precision:=Precision);
  return M, m, f;
end intrinsic;

intrinsic IsTriangulable(MM::AlgMat[Fld]) -> BoolElt, AlgMatElt
{Returns a matrix m such that m*MM*m^-1 is contained in the algebra of upper triangluar 
matrices.  All matrices must be 2x2 and defined over a field.}
  require Degree(MM) eq 2 : "2 by 2 matrices only!";
  X := Basis(MM);
  M := MatrixAlgebra(BaseRing(MM),2);
  w := M![0,-1,1,0];
  T := PolynomialRing(BaseRing(M)).1;
  fs := [x[1,2]*T^2 + (x[1,1]-x[2,2])*T - x[2,1] : x in X];
  fs := [f : f in fs | f ne 0];
  a := &meet[{x[1] : x in Roots(f)} : f in fs];
  if #a eq 1 then
    return true, M![1,0,-Random(a),1];
  elif { (w*x*w^-1)[2,1] : x in X } eq {0} then
    return true, w;
  else
    return false;
  end if;
end intrinsic;

