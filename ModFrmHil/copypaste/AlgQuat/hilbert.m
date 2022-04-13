freeze;

//////////////////////////////////////////////////////////////////////////////
//
// Hilbert symbols for Quaternion Algebras
// September-November 2005, John Voight
//
// Modified by Steve Donnelly
//
//////////////////////////////////////////////////////////////////////////////

//-------------
//
// Algorithms to compute ramification of quaternion algebras, in particular 
// check if a quaternion algebra is unramified and isomorphic to a matrix ring.
//
// These algorithms overlap with two existing architectures.  One is CrvCon, 
// which has in it functionality for NormResidueSymbol() over the rationals; 
// these are hardcoded by matrices, so we call them directly.  Second one is 
// FldAb, which has IsLocalNorm(); a call to this system will be more 
// expensive than computing directly with quadratic extensions as below, so 
// we make no use of it.
//
//-------------

forward EvenHilbertSymbol, EvenHilbertSymbolab, EvenDiagonalNormForm;

// true iff Discriminant(A) (or FactoredDiscriminant(A)) 
// will make use of a stored result.

function StoredDiscriminant(A)
  return Type(BaseRing(A)) eq FldRat 
      or assigned A`FactoredDiscriminant 
      or assigned A`MaximalOrder;
end function;

//-------------
//
// FldFunRat case
//
//-------------

function HilbertSymbolInternal(a, b, pi)

  if Type(pi) ne RngUPolElt then
    pi := Integers(Parent(pi)) ! pi;
  end if;

  vala := Valuation(a,pi);
  valb := Valuation(b,pi);

  if IsEven(vala) and IsEven(valb) then
    return 1;
  end if;
 
  // which two terms in x^2-a*y^2-b*z^2 have the same valuation mod 2 ?
  if IsEven(vala) then
    s := a; v:= vala;
  elif IsEven(valb) then
    s := b; v:= valb;
  else // both odd
    s := -a*b; v:= vala+valb;
  end if;
  s:= v ge 0 select s/pi^v else s*pi^-v;	// pi^-1 is not working

  return JacobiSymbol(Numerator(s)*Denominator(s), pi);

end function;

intrinsic HilbertSymbol(a::FldFunRatElt, b::FldFunRatElt, p::RngElt) -> RngIntElt
{The Hilbert symbol (a,b/p) for elements of a univariate rational function field F(t) of odd characteristic.
 By definition the symbol equals 1 if x^2-a*y^2-b*z^2=0 is soluble in the completion of F at the prime p,
 and otherwise -1.  The prime may be given as an element, or a prime ideal, of the polynomial ring F[t]}

  F := Parent(a);
  ok, p:= IsCoercible(F, p);
  require Parent(b) eq F and ok :
         "The arguments must be contained in the same rational function field";
  require IsFinite(BaseField(F)) and IsOdd(Characteristic(F)) : "The arguments must be contained in a "
                                   *"rational function field over a finite field of odd characteristic";
  require IsPrime(ideal<Integers(F)|p>) : "The third argument should be a prime element";
  require not IsZero(a) and not IsZero(b) : "The arguments should be nonzero";

  return HilbertSymbolInternal(a, b, p);
end intrinsic;

intrinsic HilbertSymbol(a::FldFunRatElt, b::FldFunRatElt, p::RngUPol) -> RngIntElt
{"} // "
  F := Parent(a);
  Pol := Integers(F);

  require IsFinite(BaseField(F)) and IsOdd(Characteristic(F)) : "The arguments must be contained in a "
                                   *"rational function field over a finite field of odd characteristic";
  require Parent(b) eq F : "The arguments must be contained in the same rational function field";
  require Generic(p) eq Pol : "The arguments are not compatible";
  require IsPrime(p) : "The third argument should be a prime ideal";
  require not IsZero(a) and not IsZero(b) : "The arguments should be nonzero";

  return HilbertSymbolInternal(a, b, Generator(p));
end intrinsic;

//-------------
//
// Interface and easy routines
//
//-------------

intrinsic HilbertSymbol(a::FldRatElt, b::FldRatElt, p::RngIntElt :
                        Al := "NormResidueSymbol") -> RngIntElt
  {Given rational numbers a,b and a prime p, returns the Hilbert 
   symbol (A/p) for the quaternion algebra A = (a,b / Q).  
   By default, uses the hard-coded function NormResidueSymbol(),
   but to override use Al := "Evaluate".}

  require a ne 0 and b ne 0: "a and b must be nonzero";
  if p eq -1 then 
    if a lt 0 and b lt 0 then return -1; end if; 
    return 1; 
  end if;

  if Al eq "Evaluate" then
    require IsPrime(p : Proof:=false): "Argument 3 must be prime";
    P := PolynomialRing(Rationals()); x := P.1;
    QQ := NumberField(x : DoLinearExtension := true);
    ZZ := MaximalOrder(QQ);
    p := ideal<ZZ | p>;
    return HilbertSymbol(QQ ! a, QQ ! b, p);
  else
    return NormResidueSymbol(a,b,p); // this checks p is prime
  end if;
end intrinsic;

intrinsic HilbertSymbol(a::RngIntElt, b::RngIntElt, p::RngIntElt :
                        Al := "NormResidueSymbol") -> RngIntElt
{"} // "
  require a ne 0 and b ne 0: "a and b must be nonzero";
  if p eq -1 then 
    if a lt 0 and b lt 0 then return -1; end if; 
    return 1; 
  end if;

  if Al eq "Evaluate" then
    require IsPrime(p : Proof:=false): "Argument 3 must be prime";
    P := PolynomialRing(Rationals()); x := P.1;
    QQ := NumberField(x : DoLinearExtension := true);
    ZZ := MaximalOrder(QQ);
    p := ideal<ZZ | p>;
    return HilbertSymbol(QQ ! a, QQ ! b, p);
  else
    return NormResidueSymbol(a,b,p); // this checks p is prime
  end if;
end intrinsic;


intrinsic HilbertSymbol(A::AlgQuat[FldRat], p::RngIntElt) -> RngIntElt
  {For a quaternion algebra A defined over the rationals or F_q[X] and
   an irreducible element p, computes the Hilbert symbol (A/p), which is 
   -1 if p is ramified in A and 1 otherwise.}

  require IsPrime(p : Proof:=false): "Argument 2 must be prime";

  // The ramified primes are already computed.
  return p in RamifiedPrimes(A) select -1 else 1;
  
  a := Trace(A.1)^2/4-Norm(A.1);
  b := Trace(A.2)^2/4-Norm(A.2);
  
  return NormResidueSymbol(a,b,p);
end intrinsic;

intrinsic HilbertSymbol(A::AlgQuat[FldFunRat], p::RngElt) -> RngIntElt
{"} // "
  F:= BaseField(A);
  require IsFinite(BaseField(F)) and IsOdd(Characteristic(F)): 
         "Argument 1 must be over F_q(X) for odd q"; 
  ok, p:= IsCoercible(Integers(F), p);
  require ok and IsPrime(p) : "p must generate a prime ideal";

  if StoredDiscriminant(A) then
    return Normalize(p) in RamifiedPrimes(A) select -1 else 1;
  end if;

  x:= A.1 - Trace(A.1)/2;
  y:= QuaternionicComplement(x);
  return HilbertSymbolInternal(-Norm(x), -Norm(y), p);
end intrinsic;

intrinsic HilbertSymbol(A::AlgQuat[FldFunRat], p::RngUPol) -> RngIntElt
{"} // "
  return HilbertSymbol(A, Generator(p));
end intrinsic;

intrinsic HilbertSymbol(a::FldAlgElt, b::FldAlgElt, p::RngOrdIdl) -> RngIntElt
  {Given a,b in K a number field and a prime p of K, returns the Hilbert 
   symbol (A/p) for the quaternion algebra A = (a,b / K).}
   
  require Parent(a) eq Parent(b) : 
    "Arguments must belong to the same number field";
  K := NumberField(Order(p));
  require Parent(a) eq K : 
    "p must be a prime of the number field containing a,b";
  require not IsZero(a) and not IsZero(b):
    "Arguments must be non zero";

  // Obviously, we don't want to construct quaternions, completions, 
  // and go through multiple function calls, on every call to this!!
  // On small input, this is something like 100 times faster.
  // (TO DO: when the field is nasty and the valuations are large, 
  // it could possibly be better to work in a completion).
  // SRD, July 2011

  if IsOdd(Minimum(p)) then
    va := Valuation(a, p);
    vb := Valuation(b, p);
    if IsEven(va) and IsEven(vb) then // [even, even]
      return 1;
    end if;
    // reduce to testing whether r mod p is a square
    if va eq 0 then                   // [0, odd]
      r := a;
    elif IsEven(va) then              // [even, odd]
      u := UniformizingElement(p);
      r := a * u^-va;
    elif vb eq 0 then                 // [odd, 0]
      r := b;
    elif IsEven(vb) then              // [odd, even]
      u := UniformizingElement(p);
      r := b * u^-vb;
    elif va eq vb then                // [odd = odd]
      r := - a / b;
    else                              // [odd, odd]
      u := UniformizingElement(p);
      r := - a * b * u^(-va-vb);
    end if;
    // assert Valuation(r, p) eq 0;
    k, mk := ResidueClassField(p);
    return IsSquare(r@mk) select 1 else -1;
  end if;
    
  // p is even
  return EvenHilbertSymbolab(a, b, p);
end intrinsic;

intrinsic IsRamified(p::RngElt, A::AlgQuat) -> BoolElt
  {Returns true iff p is ramified in A.}

  F:= BaseField(A);
  require Type(F) in {FldRat, FldFunRat} and IsCoercible(F, p) : "A and p must be over Q or F_q(X)";

  return HilbertSymbol(A,p) eq -1;
end intrinsic;

intrinsic IsRamified(p::RngUPol, A::AlgQuat[FldFunRat]) -> BoolElt
  {"} // "

  return HilbertSymbol(A,p) eq -1;
end intrinsic;

intrinsic IsRamified(p::RngOrdIdl, A::AlgQuat[FldAlg]) -> BoolElt
  {"} // "

  return HilbertSymbol(A,p) eq -1;
end intrinsic;

intrinsic IsUnramified(p::RngElt, A::AlgQuat) -> BoolElt
  {Returns true iff p is unramified in A.}

  F:= BaseField(A);
  require Type(F) in {FldRat, FldFunRat} and IsCoercible(F, p) : "A and p must be over Q or F_q(X)";

  return HilbertSymbol(A,p) eq 1;
end intrinsic;

intrinsic IsUnramified(p::RngUPol, A::AlgQuat[FldFunRat]) -> BoolElt
  {"} // "

  return HilbertSymbol(A,p) eq 1;
end intrinsic;

intrinsic IsUnramified(p::RngOrdIdl, A::AlgQuat[FldAlg]) -> BoolElt
  {"} // "

  return HilbertSymbol(A,p) eq 1;
end intrinsic;

//-------------
//
// Hilbert symbols for odd primes, and associated routines
//
//-------------

intrinsic HilbertSymbol(A::AlgQuat, p::RngOrdIdl) -> RngIntElt
  {For a quaternion algebra A and a prime p of its base field,
   computes the Hilbert symbol (A/p), which is -1 if p is ramified in A 
   and 1 otherwise.}

  O := Order(p);
  F := BaseField(A);
  
  require O eq Integers(F) : "p must be contained in the base field";  
  require IsPrime(p) :  "p must be a prime ideal";

  if StoredDiscriminant(A) then
    return p in FactoredDiscriminant(A) select -1 else 1;
  end if;

  a := Trace(A.1)^2/4-Norm(A.1);
  b := Trace(A.2)^2/4-Norm(A.2);
  return HilbertSymbol(a, b, p);
end intrinsic;

intrinsic UnramifiedSquareSymbol(x::FldAlgElt, p::RngOrdIdl) -> RngIntElt
  {For x a nonzero element of a number field K, and a prime of K, 
   returns 1 if a is a square in the completion K_p of K at p, 
   -1 if a is not a square and K_p(a^(1/2))/K_p is unramified, 
   and 0 otherwise.}

  require IsPrime(p) : "p must be a prime ideal";
  
  F := NumberField(Order(p));
  Fp, mFp := Completion(F,p : Precision := 20+2*Valuation(x,p));
  return UnramifiedSquareSymbol(mFp(x));
end intrinsic;

intrinsic UnramifiedSquareSymbol(a::FldPadElt) -> RngIntElt
  {For a a nonzero element of a p-adic field K, returns 1 if a is a square 
   in K (to the precision in K), -1 if a is not a square and K(a^(1/2))/K 
   is unramified, and 0 otherwise.}
  
  if IsSquare(a) then
    return 1;
  else 
    K := Parent(a);
    if Prime(K) ne 2 then
      // A quadratic extension with odd residue field is ramified if and only
      // if v(a) is odd
      if Valuation(a) mod 2 eq 0 then
        return -1;
      else
        return 0;
      end if;
    else
      PK := PolynomialRing(K);
      if #Roots(PK.1^2-a, ext<K | 2>) gt 0 then
        return -1;
      else
        return 0;
      end if;
    end if;
  end if;  
end intrinsic;

//-------------
//
// Hilbert symbols for even primes, and associated routines
//
//-------------

// This algorithm implements [Voight, Algorithm 4.3.7], corrected: 
// It finds a solution to the equation 
//   x^2 - ay^2 - bz^2 + abw^2 = 0 (mod 4)
// with x = 1 (mod 4) if Valuation(a) = 0 and Valuation(b) = 1.
function EvenDiagonalNormForm(a,b)
  K := Parent(a);
  O := Integers(K);
  p := Prime(K);

  e := RamificationIndex(K);
  
  pi := UniformizingElement(O);
  k, fk := ResidueClassField(O);
  f := Degree(k);

  assert Valuation(a) eq 0 and Valuation(b) eq 1;

  // Eltseq gives coefficients in terms of O.1, which may or may not be a
  // uniformizer!
  function EltseqUniformizerFull(x, l)
    x0 := x;
    xseq := [];
    for i := 1 to l do
      x0k := fk(x0);
      xseq cat:= Eltseq(x0k);
      x0 := (x0-(x0k@@fk))/pi;
    end for;
    return xseq;
  end function;

/*
  // Master vector upon which we record coefficients.
  V := [((k.1^i)@@fk)*pi^j : i in [0..f-1], j in [0..e-1]];

  // Compute the kernel of the augmented norm map.
  M := Matrix(k, [ EltseqUniformizerFull(c*v^2,e) : v in V, c in [1,-a,-b,a*b]]);
  Mker := Kernel(M);
  // Basis will be echelonized, so the first row vector will have the earliest
  // nonzero term
  v0 := [ &+[V[i]*((Mker.1)[i+f*e*(j-1)]@@fk) : i in [1..#V]] : j in [1..4]];
  if fk(v0[1]) eq 0 then
    // Fatal error has occurred; could be due to improper input, we need 
    // a to be not divisible by p.
    error "Fatal error in 'EvenDiagonalNormForm': "
         *"Failed to find proper element in kernel (1)";
  end if;
*/

  v0 := [1, (1/Sqrt(fk(a)))@@fk, 0, 0];
  Nv0 := v0[1]^2-a*v0[2]^2-b*v0[3]^2+a*b*v0[4]^2;

  procedure PseudoHenselLift(~v0,~Nv0)
    valNv0 := Valuation(Nv0);
    if valNv0 mod 2 eq 0 then
      v0[1] +:= (Sqrt(fk(-Nv0/pi^valNv0))@@fk)*pi^(valNv0 div 2);
    else
      v0[3] +:= (Sqrt(fk(Nv0/(b*pi^(valNv0-1))))@@fk)*pi^(valNv0 div 2);
    end if;
    Nv0 := v0[1]^2-a*v0[2]^2-b*v0[3]^2+a*b*v0[4]^2;
  end procedure;

  while Valuation(Nv0) lt 2*e do
    PseudoHenselLift(~v0,~Nv0);
  end while;

  return [1,v0[2]/v0[1],v0[3]/v0[1],0];
end function;

// Evaluates the Hilbert symbol for p an even prime
function EvenHilbertSymbol(A,p)
  // Remember for return alpha, beta
  _, _, Astan, phi := StandardForm(A);
  alpha := Astan.1@@phi;
  beta := Astan.2@@phi;
  a := Norm(alpha);
  b := Norm(beta);

  F := BaseField(A);
  Z_F := MaximalOrder(F);
  prec_extra := Max(Abs(Valuation(a, p)), Abs(Valuation(b, p)));
  Fp, mFp := Completion(F,p : Precision := 20+prec_extra);
  Op := Integers(Fp);
  k, fk := ResidueClassField(Op);

  ap := -mFp(a);
  bp := -mFp(b);
  e := RamificationIndex(Fp);

  // Normalize valuations of elements: a has valuation 0, 
  // b has valuation 1
  piFp := SafeUniformiser(p);
  pi := mFp(piFp);

  facts := Decomposition(Z_F,2);
  I := [q[1] : q in facts | q[1] ne p];
  V := [0 : i in I];
  piinvFp := WeakApproximation([p] cat I, [-1] cat V);

  // Step one: Ensure a,b have valuations in {0,1}  
  vala := Valuation(ap) div 2;
  valb := Valuation(bp) div 2;
  ap /:= pi^(2*vala);
  alpha /:= piFp^vala;
  bp /:= pi^(2*valb);
  beta /:= piFp^valb;

  if Valuation(ap) eq 1 then
    if Valuation(bp) eq 1 then
      ap := -ap*bp/pi^2;
      alpha := alpha*beta/piFp;
    else
      cp := ap;
      ap := bp;
      bp := cp;
      gamma := alpha;
      alpha := beta;
      beta := gamma;
    end if;
  end if;

  if Valuation(bp) eq 1 then
    xiseq := EvenDiagonalNormForm(ap,bp);
  else
    // Eltseq gives coefficients in terms of O.1, which may or may not be a 
    // uniformizer!
    function EltseqUniformizer(x, l)
      x0 := x;
      xseq := [];
      for i := 1 to l do
        Append(~xseq, fk(x0));
        x0 := (x0-(xseq[#xseq]@@fk))/pi;
      end for;
      return xseq;
    end function;

    apseq := EltseqUniformizer(ap,e);
    bpseq := EltseqUniformizer(bp,e);
    M := Matrix([apseq, bpseq]);
    M0 := ColumnSubmatrix(M, [i : i in [1..e] | i mod 2 eq 0]);

    if Rank(M0) eq 0 then
      a0 := &+[Sqrt(apseq[i])@@fk*pi^(i div 2) : i in [i: i in [1..e] | i mod 2 eq 1]];
      b0 := &+[Sqrt(bpseq[i])@@fk*pi^(i div 2) : i in [i: i in [1..e] | i mod 2 eq 1]];
      xiseq := [1,1/a0,1/b0,1/(a0*b0)];
    else
      if IsZero(M0[1]) then
        alpha0 := beta;
        beta0 := alpha;
        alpha := alpha0;
        beta := beta0;
        ap := -mFp(Norm(alpha));
        bp := -mFp(Norm(beta));
        apseq := EltseqUniformizer(ap,e);
        bpseq := EltseqUniformizer(bp,e);
        SwapRows(~M0, 1, 2);
      end if;

      tf2 := 1;
      while M0[1][tf2] eq 0 do
        tf2 +:= 1;
      end while;
      tf2 -:= 1;

      a0 := &+[Sqrt(apseq[i])@@fk*pi^(i div 2) : i in [i: i in [1..2*(tf2+1)] | i mod 2 eq 1]];
      at := (ap - a0^2)/pi^(2*tf2+1);

      xiseq_re := EvenDiagonalNormForm(ap,-pi*at/bp);
      y := xiseq_re[2];
      z := xiseq_re[3];
      xiseq := [1, 1/a0, pi^tf2/(a0*z), pi^tf2*y/(a0*z)];
    end if;

    xiseqlift := [c@@mFp : c in xiseq];
    xi := xiseqlift[1] + xiseqlift[2]*alpha + xiseqlift[3]*beta + xiseqlift[4]*alpha*beta;
    assert Valuation(mFp(Norm(xi))) ge Valuation(mFp(4));
  end if;

  xiseqlift := [xiseq[i]@@mFp : i in [1..4]];
  ZFmod8, m8 := quo<Z_F | 8>;

  // Coefficients only matter modulo 8, so reduce them to this size.
  OddDenominator := function(a);
    den := Denominator(a);
    while den mod 2 eq 0 do
      den div:= 2;
    end while;
    return den;
  end function;

  alpha *:= OddDenominator(Norm(alpha));
  beta *:= OddDenominator(Norm(beta));

  xiseqlift := [m8(xiseq[i]@@mFp)@@m8 : i in [1..4]];

  for i := 1 to 4 do
    // Small hack to reduce the sizes of the coefficients of xi,
    // not necessary, but nice anyway.
    if Max([Numerator(x) : x in Eltseq((-xiseq[i])@@mFp)]) lt 
       Max([Numerator(x) : x in Eltseq(xiseqlift[i])]) then
      xiseqlift[i] := -((-xiseq[i])@@mFp);
    end if;
  end for;

  xiseq := xiseqlift;
  xi := xiseq[1] + xiseq[2]*alpha + xiseq[3]*beta + xiseq[4]*alpha*beta;
  xi *:= piinvFp^e;

  // By Hensel's lemma, the characteristic polynomial of alpha
  //   x^2 - x + nrd(alpha)
  // has a root in K if and only if it has a root modulo p.

  Nxi := Norm(xi);
  trxi := Trace(xi);
  zeta := QuaternionicComplement(xi);
  z := Norm(zeta);
  valz := Valuation(mFp(z)) div 2;
  zeta *:= piinvFp^valz;

  if #Roots(PolynomialRing(k) ! [fk(mFp(Nxi)),-fk(mFp(trxi)),1]) ge 1 then
    return 1, xi, zeta;
  else
    // K(alpha) is an unramified extension of K, so by [Vigneras, Theoreme
    // II.1.3], it is a division ring if and only if the complementary element 
    // is a uniformizer.

    if Valuation(mFp(Norm(zeta))) eq 0 then
      return 1, xi, zeta;
    else
      return -1, xi, zeta;
    end if;
  end if;
end function;


// The HilbertSymbol code for (a,b)_p at even p.

// We start with an implementation of Alg. 6.2 -- 6.5 of [Voight2]
function SolveCongruence(a,b,p)
  //assert Valuation(a,p) eq 0;
  //assert Valuation(b,p) eq 1;
  pi:= PrimitiveElement(p);
  k, h:= ResidueClassField(p);
  y:= 1/(SquareRoot(a @ h) @@ h); z:= 0;
  ee:= 2*RamificationIndex(p);
  told:= -1;
  while true do
    N:= 1 - a*y^2 - b*z^2;
    t:= Valuation(N, p); assert t gt told; told:= t;
    if t ge ee then return y,z; end if;
    w:= pi^(t div 2);
    if IsEven(t) then
      y +:= SquareRoot((N/(a*w^2)) @ h) @@ h * w;
    else
      z +:= SquareRoot((N/(b*w^2)) @ h) @@ h * w;
    end if;
  end while;
end function;

// Decide if a*x^2=1 mod p^e has a solution.
// This is a variant of O'Meara 63.5. The code assumes that 0 <= e <= 2*RamIdx(p)
function CanLiftSquare(a,p,e)
  assert Valuation(a,p) eq 0;
  if Valuation(a-1, p) ge e then return true, Order(p) ! 1, e; end if;
  aold:= a;
  pi:= PrimitiveElement(p);
  k, h:= ResidueClassField(p);
  x:= SquareRoot( (a @ h)^-1 ) @@ h;
  a *:= x^2;
  t:= Valuation(a-1, p);
  while t lt e and IsEven(t) do
    s:= SquareRoot(h((a-1)/pi^t));
    s:= 1+(s@@h)*pi^(t div 2);
    a /:= s^2;
    x := x/s;
    tt:= Valuation(a-1, p);
    assert tt gt t;
    t:= tt;
  end while;
  t:= Min(t,e);
  assert Valuation(aold*x^2-1, p) ge t;
  return t eq e, x, t;
end function;

function SolveCongruence2(a,b,p)
  if Valuation(b, p) eq 1 then
    y,z:= SolveCongruence(a,b,p);
    return y,z,0;
  end if;

  e:= RamificationIndex(p);
  pi:= PrimitiveElement(p);
  oka, a0, t:= CanLiftSquare(a, p, e);
  if oka then
    okb, b0, t:= CanLiftSquare(b, p, e);
    if okb then return a0, b0, a0*b0; end if;
    bt:= (b-(1/b0)^2) /pi^t;
    y, z:= SolveCongruence(b, -pi*bt/a, p);
    w:= pi^(t div 2);
    return w*b0/z, b0, y*w*b0/z;
  else
    at:= (a-(1/a0)^2) /pi^t;
    y, z:= SolveCongruence(a, -pi*at/b, p);
    w:= pi^(t div 2);
    return a0, w*a0/z, y*w*a0/z;
  end if;
end function;

normalize:= function(a, p)
  vala:= Valuation(a, p);
  n:= vala div 2;
  if n ne 0 then a /:= PrimitiveElement(p)^(2*n); vala -:= 2*n; end if;
  assert Valuation(a, p) eq vala and vala in {0,1};
  return a, vala;
end function;

function EvenHilbertSymbolab(a,b,p)
  a, vala:= normalize(a, p);
  b, valb:= normalize(b, p);
  if vala eq 1 then
    if valb eq 1 then
      a:= (-a*b) / PrimitiveElement(p)^2;
    else
      x:= a; a:= b; b:= x;
    end if;
  end if;

  y,z,w:= SolveCongruence2(a,b,p);
  nrm:= 1-a*y^2-b*z^2+a*b*w^2;
  assert Valuation(nrm, p) ge 2*RamificationIndex(p);
  tmp:= (b*z)^2*a + (a*y)^2*b;

  if tmp eq 0 or IsEven(Valuation(tmp, p)) then
    res:= 1;
  else
    k,h:= ResidueClassField(p);
    res:= IsIrreducible(Polynomial([k| (nrm/4)@h,-1,1])) select -1 else 1;
  end if;

  // The maximal order computation uses some element xi from EvenHilbertSymbol.
  // I guess that xi:= (1+yi+zj+wij)/2 also would do the trick.
  // Then EvenHilbertSymbol would not be needed anymore.
  return res;
end function;



//-------------
//
// Bibliography
//
//-------------

/*

[Vigneras] 
Marie-France Vigneras, Arithmetique des algebres de quaternions, Lecture notes in mathematics, vol. 800, Springer, Berlin, 1980.

[Voight] 
John Voight, Quadratic forms and quaternion algebras: Algorithms and 
arithmetic, Ph.D. thesis, University of California, Berkeley, 2005.

[Voight2]
John Voight, Identifying the matrix ring: algorithms for quaternion algebras and quadratic forms,
in Quadratic and higher degree forms, Developments in Math., vol. 31, Springer, New York, 2013, 255--298.
*/
