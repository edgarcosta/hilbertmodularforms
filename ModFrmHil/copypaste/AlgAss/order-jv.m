freeze;

//////////////////////////////////////////////////////////////////////////////
//
// Orders
// November-December 2005, John Voight, Nicole Sutherland, and Claus Fieker
//
// Modified by Steve Donnelly and Markus Kirschmer
// Last modified November 2013
//
//////////////////////////////////////////////////////////////////////////////

declare attributes AlgAssVOrd : 
        IsMaximal, Discriminant, FactoredDiscriminant, TraceZeroInternalData;

declare attributes AlgQuat :
        FactoredDiscriminant;

import "../AlgQuat/hilbert.m" : HilbertSymbolInternal;
import "ideals-jv.m" : _LocalBasis;

//-------------
//
// Basic algorithms for orders over number fields.
//
//-------------

intrinsic '/'(x::AlgAssVOrdElt, y::AlgAssVOrdElt) -> AlgAssVElt
  {The quotient of x by y in their ambient algebra}

  A := Algebra(Parent(x));
  return (A!x)/(A!y);
end intrinsic;

intrinsic 'div'(x::AlgAssVOrdElt, y::AlgAssVOrdElt) -> AlgAssVOrdElt
  {The quotient of x by y; y must divide x exactly}

  q := x/y;
  bl, q := IsCoercible(Parent(x), q);
  require bl : "Division of elements of this order must be exact";
  return q;
end intrinsic;

intrinsic IsScalar(a::AlgAssVOrdElt) -> BoolElt, RngElt
  {Returns true (and R ! a) iff a belongs to the base ring R}

  return IsScalar(Algebra(Parent(a))!a);
end intrinsic;

intrinsic IsIntegral(a::AlgQuatElt) -> BoolElt
  {Returns true iff a is integral.}

  return IsIntegral(Trace(a)) and IsIntegral(Norm(a));
end intrinsic;

intrinsic TraceZeroSubspace(O::AlgQuatOrd) -> SeqEnum
  {A basis over Z or F_q[X] for the trace zero submodule of O,
   where O is an order in a quaternion algebra,
   returned as a sequence of elements of O.}
  
  basisO := Basis(O);
  traces := [Trace(b) : b in basisO];
  K := KernelMatrix(Matrix(BaseRing(O),4,1, traces));
  assert Nrows(K) eq 3;
  basis := [ &+[k[j]*basisO[j] : j in [1..4]] where k is Eltseq(K[i]) 
           : i in [1..3]];
  return basis;
end intrinsic;

intrinsic TraceZeroSubspace(O::AlgAssVOrd[RngOrd]) -> SeqEnum
  {Returns the trace zero subspace of O as a pseudobasis.}

  n := Degree(O);
  A := Algebra(O);
  M := Matrix(PseudoMatrix(O));
  N := [];

  for i := 1 to n do
    alpha := A ! M[i];
    Append(~N, Eltseq(M[i]) cat [Trace(alpha)]);
  end for;
  N := Matrix(N);
  P := PseudoMatrix(CoefficientIdeals(PseudoMatrix(O)), N);

  P := HermiteForm(P);
  N := Matrix(P);
  M := [];
  C := CoefficientIdeals(P);

  for i := 1 to n do
    if N[i][n+1] eq 0 then
      Append(~M, <C[i],A ! Eltseq(N[i])[1..n]>);
    end if;
  end for;

  return M;
end intrinsic;

intrinsic Random(O::AlgAssVOrd) -> AlgAssVOrdElt
  {Returns a random (small coefficient) element of O.}

  B := ZBasis(O);
  return &+[ Random([-3..3])*b : b in B];
end intrinsic;

intrinsic Generators(O:: AlgAssVOrd) -> SeqEnum
  {A sequence of generators for the order O as a module over its base ring}
  if Type(O) eq AlgQuatOrd then return Basis(O); end if;
  return [p[2] * x: x in Generators(p[1]), p in PseudoBasis(O)];
end intrinsic;

intrinsic LocalBasis(M::AlgAssVOrd[RngOrd], p::RngOrdIdl : Type:= "") -> []
{A basis of a free module that coincides with M at the prime ideal p}
  require Order(p) cmpeq BaseRing(M) : "Incompatible arguments";
  require IsPrime(p) : "The ideal must be prime.";
  require Type in {"", "Submodule", "Supermodule"} : "Type must be \"Submodule\" or \"Supermodule\" when specified";
  return _LocalBasis(M, p, Type);
end intrinsic;

//-------------
//
// Order constructors.
//
//-------------

function IsOrder(O);
  S := Basis(O);
  I := CoefficientIdeals(PseudoMatrix(O));

  // Check that (S,I) generates a ring
  isRing := true;
  for i,j in [1..Degree(O)] do
    for gi in Generators(I[i]) do
      for gj in Generators(I[j]) do
        s := gi*S[i];
        t := gj*S[j];
        if not IsCoercible(O, s*t) then
          printf "i = %o\nj = %o\ngi = %o\ngj = %o\nS[i] = %o\nS[j] = %o\nst = %o\n", 
                 i, j, gi, gj, S[i], S[j], s*t;
          isRing := false;
          break i;
        end if;
      end for;
    end for;
  end for;

  return isRing;
end function;


intrinsic Order(alpha::AlgQuatElt[FldAlg]) -> AlgAssVOrd
  {Returns some order containing alpha.}

  require IsIntegral(alpha) : "Argument must be integral";
  A := Parent(alpha);

  alphastar := alpha - Trace(alpha)/2;
  require alphastar ne 0 : "Argument is a scalar";

  t := Trace(alphastar^2);
  require t ne 0 : "Not implemented: Algebra contains zero-divisors";

  for i := 1 to 2 do 
    b := A.i;
    tb := Trace(b);
    if tb ne 0 then
      b := b - tb/2;
    end if;
    beta := b - Trace(alphastar*b)/t*alphastar;
    flag := beta ne 0;
    if flag then
      break;
    end if;
  end for;
  assert flag;

  d := Denominator(Norm(beta)); // beta has trace zero

  return Order([alpha, d*beta]); // TO DO: construct with explicit basis
end intrinsic;


intrinsic Order(S::SeqEnum[AlgAssVElt[FldAlg]] : Check := true) -> AlgAssVOrd
  {Given a sequence S of elements of A, returns the order generated by S
   as a module (over the maximal order of the underlying number field)}

  return Order(S, [] : Check := Check);
end intrinsic;

intrinsic Order(R::RngFunOrd, S::SeqEnum[AlgAssVElt[FldFunG]] : Check := true) -> AlgAssVOrd
  {Given a sequence S of elements of A, returns the order generated by S
   as a module (over the maximal order of the underlying function field)}

  require IsMaximal(R) : "Argument 1 must be a maximal order";
  return Order(S, [ideal<R | 1> : i in [1..#S]] : Check := Check);
end intrinsic;

forward order_over;

intrinsic Order(S::SeqEnum[AlgAssVElt[FldFunG]], I::SeqEnum[RngFunOrdIdl] : 
                Check := true) -> AlgAssVOrd
  {Returns the order which has pseudobasis given by the basis elements S 
   and the coefficient ideals I}  

  A := Universe(S);
  F := BaseRing(A);
  n := Dimension(A);

  require #I eq #S : "Length of arguments must be the same";

  require IsMaximal(R) and FunctionField(R) cmpeq F where R is Ring(Universe(I)) : 
        "Ideals in argument 2 must be of a ring of integers of the base ring of argument 1";

  require not ISA(Type(A), AlgMatV) : "Argument 1 must not contain elements of a matrix algebra";

  return order_over(Ring(Universe(I)), S, I : Check := Check);
end intrinsic;

intrinsic Order(S::SeqEnum[AlgAssVElt[FldAlg]], I::SeqEnum[RngOrdFracIdl] : 
                Check := true) -> AlgAssVOrd
  {Returns the order which has pseudobasis given by the basis elements S 
   and the coefficient ideals I}  

  A := Universe(S);
  F := BaseRing(A);
  Z_F := MaximalOrder(F);
  n := Dimension(A);

  if I eq [] then
    I := [ideal<Z_F | 1> : i in [1..#S]];
  end if;

  require R cmpeq Z_F or R cmpeq FieldOfFractions(Z_F) where R is Ring(Universe(I)) : 
        "Ideals in argument 2 must be of the ring of integers of the base ring of argument 1";

  require not ISA(Type(A), AlgMatV) : "Argument 1 must not contain elements of a matrix algebra";

  return order_over(Z_F, S, I : Check := Check);
end intrinsic;

function order_over(Z_F, S, I : Check := true)
  A := Universe(S);
  F := BaseRing(A);
  n := Dimension(A);

  if Check and (A!1 notin S) then 
    // Always add 1 to the order
    Append(~S, 1);
    Append(~I, 1*Z_F);
  end if;

  if not Check then
    error if #S ne n, "Argument 1 must have length ", n, " to be a basis";
    M := MatrixRing(F,n) ! &cat[Eltseq(s) : s in S];
    return Order(A, M, I);
  end if;

  // Find an initial pseudobasis
  M := Matrix(F,#S,n, &cat[Eltseq(s) : s in S]);
  P := PseudoMatrix(I,M);
  P := HermiteForm(P);
  I := CoefficientIdeals(P);

  M := ChangeRing(Matrix(P),F);
  S := [A ! Eltseq(M[i]) : i in [1..Nrows(M)]];

/*
  // Add 1 if not in the order
  M1 := VerticalJoin(Vector(A ! 1), M);
  if Rank(M1) gt NumberOfRows(M) then
    S := [A ! 1] cat S;
    I := [ideal<Z_F | 1>] cat I;
    M := M1;
  end if;
*/

  // Check that the module S tensor with the rationals is
  // multiplicatively closed
  if #S lt n then
    for i := 1 to #S do
      s := S[i];
      j := 1;
      while j le #S do
        t := S[j];
        Mst := VerticalJoin(M, Vector(s*t));
        if Rank(Mst) gt NumberOfRows(M) then
          Append(~S, s*t);
          Append(~I, I[i]*I[j]);
          M := Mst;
          if #S eq n then
            // We already have a full lattice
            break i;
          end if;
        end if;

        Mts := VerticalJoin(M, Vector(t*s));
        if Rank(Mts) gt NumberOfRows(M) then
          Append(~S, t*s);
          Append(~I, I[j]*I[i]);
          M := Mts;
          if #S eq n then
            // We already have a full lattice
            break i;
          end if;
        end if;

        j +:= 1;
      end while;  
    end for;
  end if;

  error if Rank(M) ne n, 
         "The given elements don't generate an order of full rank";
  M := MatrixRing(F,n) ! M;
  O := Order(A, M, I);

  // Check that (S,I) generates a ring
  if not IsOrder(O) then
    error "These generators do not generate a ring";
  end if;

  return O;
end function;

intrinsic Adjoin(O::AlgAssVOrd[RngOrd], a::AlgAssVElt) -> AlgAssVOrd
  {Returns the order generated by a and O.}
  return Adjoin(O,a, ideal<BaseRing(O) | 1>);
end intrinsic;

intrinsic Adjoin(O::AlgAssVOrd[RngOrd], a::AlgAssVElt, I::RngOrdFracIdl) -> AlgAssVOrd
  {Returns the order obtained by adjoining the set a*I to O}
  S := &cat[[a*x, x*a] : x in Basis(O)];
  I := &cat[[c*I, c*I] : c in CoefficientIdeals(PseudoMatrix(O))]; 
  P := PseudoMatrix(I, Matrix(S));
  P := VerticalJoin(PseudoMatrix(O), P);
  P := HermiteForm(P);
  Onew := Order(Algebra(O), P);

  if assigned O`ChangeRingMap then
    Onew`ChangeRingMap := O`ChangeRingMap;
  end if;

  isRing := IsOrder(Onew);
  if not isRing then
    error "The sum does not generate a ring";
  else
    return Onew;
  end if;
end intrinsic;

intrinsic '+'(O1::AlgAssVOrd[RngOrd], O2::AlgAssVOrd[RngOrd]) -> AlgAssVOrd
  {Computes the sum O1+O2, the smallest order containing both O1 and O2.}

  require Algebra(O1) cmpeq Algebra(O2) : 
    "Orders must be contained in the same algebra";

  P := VerticalJoin(PseudoMatrix(O1), PseudoMatrix(O2));
  P := HermiteForm(P);
  O := Order(Algebra(O1), P);

  if assigned O1`ChangeRingMap then
    O`ChangeRingMap := O1`ChangeRingMap;
  end if;

  isRing := IsOrder(O);
  if not isRing then
    error "The sum does not generate a ring";
  else
    return O;
  end if;
end intrinsic;

intrinsic 'meet'(O1 :: AlgAssVOrd[RngOrd], O2 :: AlgAssVOrd[RngOrd]) -> AlgAssVOrd
  {Computes the intersection of two orders.}

  A:= Algebra(O1);
  require A cmpeq Algebra(O2) : "The orders must be in the same algebras.";
  return Order(A, PseudoMatrix(Module(PseudoMatrix(O1)) meet Module(PseudoMatrix(O2))));
end intrinsic;

//The arithmetic radical of O. That is the twosided ideal J between O and pO
//that corresponds to the radical of O/pO.
function _Radical(O, p)
  R:= BaseRing(O);
  hasBasis:= Type(R) in {RngInt,RngUPol};
  if hasBasis then
    if Type(R) eq Type(p) then p:= Generator(p); end if;
    ok, p:= IsCoercible(R, p);
  else
    ok:= ISA(Type(p), RngOrdIdl) and R cmpeq Order(p);
  end if;
  ok:= ok and IsPrime(p);
  if not ok then return ok, "The second argument must be a prime (ideal) of the base ring of the order"; end if;

  A:= Algebra(O);
  if hasBasis then
    B:= Basis(O);
    Gens:= [ A ! p ];
  else
    B:= LocalBasis(O, p : Type:= "Submodule");
    Gens:= [ A ! g : g in Generators(p) ];
  end if;

  k, hk:= ResidueClassField(p);
  BM:= Matrix([ Eltseq(A ! x) : x in B ])^-1;
  RR:= [ Matrix([ Eltseq(A ! (b * c)) : c in B ])*BM : b in B ];
  RR:= [ [ hk(x) : x in Eltseq(m)] : m in RR ];
  AA:= sub< MatrixAlgebra(k, 4) | [ Matrix(4, x) :x in RR ] >;
  J:= JacobsonRadical(AA);
  if Dimension(J) eq 0 then return true, ideal< O | Gens >; end if;
  S:= Solution( Matrix(RR), Matrix([ Eltseq(AA ! j) : j in Basis(J) ]) );

  return true, ideal< O | Gens cat [ &+[(S[k,i] @@ hk) * B[i] : i in [1..4] | S[k,i] ne 0]: k in [1..Nrows(S)] ] >;
end function;

intrinsic ArithmeticRadical(O::AlgAssVOrd[RngOrd], p::RngOrdIdl) -> AlgAssVOrdIdl
{The arithmetic radical of O at the prime (ideal) p}
  ok, I:= _Radical(O, p); 
  require ok: I;
  return I;
end intrinsic;

intrinsic ArithmeticRadical(O::AlgQuatOrd, p::RngElt) -> AlgQuatOrdIdl
{"} //"
  ok, I:= _Radical(O, p); 
  require ok: I;
  return I;
end intrinsic;


intrinsic RadicalIdealizer(O::AlgAssVOrd[RngOrd], p::RngOrdIdl : Side:= "Intersection") -> AlgAssVOrd
{The radical idealizer of O at the prime (ideal) p}
  ok, I:= _Radical(O, p);
  require ok: I;
  if Side cmpeq "Right" or Type(Algebra(O)) eq AlgQuat then return RightOrder(I);
  elif Side cmpeq "Left" then return LeftOrder(I);
  elif Side cmpeq "Intersection" then return LeftOrder(I) meet RightOrder(I);
  end if;
  require false: "Side must be one of \"Left\", \"Right\" or \"Intersection\"";
end intrinsic;

intrinsic RadicalIdealizer(O::AlgQuatOrd, p::RngElt : Side:= "") -> AlgQuat
{"} //"
  ok, I:= _Radical(O, p);
  require ok: I;
  return RightOrder(I);
end intrinsic;

//-------------
//
// Discriminants.
//
//-------------


function algebraic_discriminant(O, Recompute)
  if assigned O`Discriminant and not Recompute then
    return O`Discriminant;
  else
    n := Degree(O);
    B := PseudoBasis(O);

    M := Matrix([[Trace(O.i*O.j) : i in [1..n]] : j in [1..n]]);
    d := Determinant(M);
    if Type(Algebra(O)) eq AlgQuat then
      d := SquareRoot(ideal<BaseRing(O) | d>);
      d *:= &*[ B[i][1] : i in [1..n]];
    else
      d *:= (&*[ B[i][1] : i in [1..n]])^2;
      // Trace normalisation different for AlgGrp
      if ISA(Type(Algebra(O)), AlgGrp)  and n mod Characteristic(O) ne 0 then 
        d *:= n^n;
      end if;
    end if;
    d, den := IntegralSplit(d);
    assert den eq 1;
    O`Discriminant := d;
    return d;
  end if;
end function;

intrinsic Discriminant(O::AlgAssVOrd[RngOrd] : Recompute := false) -> RngOrdIdl
{The discriminant of the order O.
For quaternion algebras, this returns the reduced discriminant.
For all other types of algebras, it returns the generic discriminant,
i.e. the determinant of the trace form (with generic trace).}
    return algebraic_discriminant(O, Recompute);
end intrinsic;

intrinsic Discriminant(O::AlgAssVOrd[RngFunOrd] : Recompute := false) -> RngOrdIdl
{The discriminant of the order O.
For quaternion algebras, this returns the reduced discriminant.
For all other types of algebras, it returns the generic discriminant,
i.e. the determinant of the trace form (with generic trace).}
    return algebraic_discriminant(O, Recompute);
end intrinsic;

// Cannot put extended type for over integers: ambiguous signature match 
// (AlgQuatOrd)
intrinsic Discriminant(O::AlgAssVOrd) -> RngIntElt
{"} // "
    if assigned O`Discriminant then
      return O`Discriminant;
    end if;

    // Other base rings could be allowed, but in view of 
    // the complicated conventions for what is returned, 
    // defer this until they are needed
    require Type(BaseRing(O)) in {RngInt, RngUPol, RngVal} :
      "Base ring must be Z, a polynomial ring, a valuation ring of a rational function field or an order in a number or function field";

    assert not ISA(Type(O), AlgQuatOrd); 
    // if so, return reduced discriminant (as above)

    n := Degree(O);
    M := Matrix(n, [Trace(b1 * b2) : b1, b2 in Basis(O)]);
    d := Determinant(M);

    // Trace normalisation different for AlgGrp
    if ISA(Type(Algebra(O)), AlgGrp) and n mod Characteristic(O) ne 0 then 
      d *:= n^n;
    end if;

    d := BaseRing(O) ! d;

    O`Discriminant := d;
    O`FactoredDiscriminant := Factorization(d);
    return d;
end intrinsic;

intrinsic FactoredDiscriminant(O::AlgAssVOrd) -> SeqEnum
  {The factorization of Discriminant(O)}

  if assigned O`FactoredDiscriminant then
    return O`FactoredDiscriminant;
  end if;

  if Type(O) ne AlgQuatOrd then
    t := Type(BaseRing(O));
    require t eq RngInt or ISA(t, RngOrd) :
      "Not implemented for orders over rings of type", t;
  end if;

  O`FactoredDiscriminant := Factorization(Discriminant(O));
  return O`FactoredDiscriminant;
end intrinsic;

intrinsic Discriminant(A::AlgQuat[FldAlg]) -> RngOrdIdl, SeqEnum
  {Returns the ideal of finite places and the sequence of real places 
   where A is ramified.}

  ps, S := FactoredDiscriminant(A);
  if #ps eq 0 then
    return ideal<MaximalOrder(BaseField(A)) | 1>, S;
  else
    return &*ps, S;
  end if;
end intrinsic;

intrinsic Discriminant(A::AlgQuat[FldFunRat]) -> RngUPolElt
  {The reduced discriminant}

  ps:= RamifiedPrimes(A);
  return IsEmpty(ps) select Integers(BaseField(A)) ! 1 else &* ps;
end intrinsic;

intrinsic RamifiedPrimes(A::AlgQuat[FldFunRat]) -> SeqEnum
  {The ramified (normalized) irreducible polynomials of the quaternion algebra A.}
  F:= BaseRing(BaseField(A));
  require Characteristic(F) ne 2 and IsFinite(F): "Base field is not supported";
  if not assigned A`FactoredDiscriminant then
    if assigned A`MaximalOrder then 
      return [ f[1] : f in FactoredDiscriminant(A`MaximalOrder) ];
    end if;
    x:= A.1 - Trace(A.1)/2;
    y:= QuaternionicComplement(x);
    a:= -Norm(x);
    b:= -Norm(y);
    x:= Numerator(a) * Denominator(a) * Numerator(b) * Denominator(b);
    // todo: use Squarefree
    A`FactoredDiscriminant:= [ f[1]: f in Factorization(x) | HilbertSymbolInternal(a,b,f[1]) eq -1 ];
  end if;
  return A`FactoredDiscriminant;
end intrinsic;

intrinsic FactoredDiscriminant(A::AlgQuat) -> SeqEnum, SeqEnum
  {Returns the sequence of finite and real places where A is ramified.}
  F:= BaseField(A);
  T:= Type(F);
  require T eq FldRat or ISA(T, FldAlg) or 
     (T eq FldFunRat and IsFinite(BaseRing(F)) and Characteristic(F) ne 2) :
        "The base field must be Q, F_q(X) or a number field";

  if T in {FldRat, FldFunRat} then
    R:= Integers(F);
    D:= [ideal<R | p> : p in RamifiedPrimes(A)];
    S:= IsOdd(#D) select [Infinity()] else [];
  else
    if assigned A`FactoredDiscriminant then
      D, S:= Explode(A`FactoredDiscriminant);
    else
      x:= A.1 - Trace(A.1)/2;
      y:= QuaternionicComplement(x);
      a:= Norm(x);
      b:= Norm(y);
      S := [ Places(F) | v : v in RealPlaces(F) | Real(Evaluate(a,v)) gt 0 and
                                                  Real(Evaluate(b,v)) gt 0];
      if assigned A`MaximalOrder then
        D:= [ f[1] : f in FactoredDiscriminant(A`MaximalOrder) ];
      else
        pps := &join{{f[1] : f in Factorization(c*Integers(F))} : 
                            c in [2, Numerator(a), Denominator(a), Numerator(b), Denominator(b)]};
        D:= [ pp : pp in pps | HilbertSymbol(A, pp) eq -1 ];
      end if;
      assert IsEven(#S+#D);
      A`FactoredDiscriminant:= < D, S >;
    end if;
  end if;
  return D, S;
end intrinsic;

intrinsic RamifiedPlaces(A::AlgQuat) -> SeqEnum, SeqEnum
  {Same as FactoredDiscriminant.}
  return FactoredDiscriminant(A);
end intrinsic;

intrinsic IsMatrixRing(A::AlgQuat : Isomorphism:= false) -> BoolElt, AlgMat, Map
  {Returns true iff A is isomorphic to a matrix ring.}

  F:= BaseField(A); T:= Type(F);
  require T eq FldRat or ISA(T, FldAlg) or 
     (T eq FldFunRat and IsFinite(BaseRing(F)) and Characteristic(F) ne 2) :
        "The base field must be Q, F_q(X) or a number field";

  P, S := FactoredDiscriminant(A);
  val:= IsEmpty(P) and IsEmpty(S);
  if not val or not Isomorphism then
    return val, _, _;
  end if;

  i:= A.1 - Trace(A.1)/2;
  a:= -Norm(i);
  bl, s:= IsSquare(a);
  if bl then
    eps:= i - s;
  else
    j:= QuaternionicComplement(i);
    K:= ext< F | Polynomial([-a, 0, 1]) >;
    bl, x:= NormEquation(K, -Norm(j));
    assert bl;
    eps:= e[1] + e[2]*i + j where e:= Eltseq(x[1]);
    assert IsZero(Norm(eps)); 
  end if;
  M2F, phi:= MatrixRing(A, eps);
  return true, M2F, phi;
end intrinsic;

//-------------
//
// Headers for calls to the base algebra.
//
//-------------

intrinsic Norm(a::AlgAssVOrdElt) -> RngElt
  {Norm of the element a.}

  return Norm(Algebra(Parent(a)) ! a);
end intrinsic;

intrinsic Trace(a::AlgAssVOrdElt) -> RngElt
  {Trace of the element a.}

  return Trace(Algebra(Parent(a)) ! a);
end intrinsic;

intrinsic Conjugate(a::AlgAssVOrdElt) -> AlgAssVOrdElt
  {Conjugate of the element a.}

  require Type(Algebra(Parent(a))) eq AlgQuat : 
    "Argument must come from a quaternion order";
  return Parent(a)!(Trace(a)-a);
end intrinsic;

intrinsic CharacteristicPolynomial(a::AlgAssVOrdElt) -> RngUPolElt
  {The characteristic polynomial of a.}

  return CharacteristicPolynomial(Algebra(Parent(a)) ! a);
end intrinsic;

intrinsic IsMaximalAtRamifiedPrimes(O::AlgAssVOrd) -> BoolElt
  {Returns true if and only if O is maximal at all ramified primes.}

  A := Algebra(O);
  FO := FactoredDiscriminant(O);
  return forall{f : f in FO | f[2] eq 1 or HilbertSymbol(A,f[1]) eq 1};
end intrinsic;

//-------------
//
// Module structure of orders
//
//-------------

intrinsic RModule(O::AlgAssVOrd, R::RngOrd) -> .
  {Returns the quaternion order O as a module over the quadratic order R.}

  A := Algebra(O);
  K := NumberField(R);
  F := BaseField(A);
  d := Degree(F);

  mu, iota := Embed(R, O);
  iotaK := hom<K -> A | x :-> iota(Denominator(x)*x)/Denominator(x)>;

  nu := QuaternionicComplement(A!mu);
  M := Matrix([Eltseq(c) : c in [1,mu,nu,mu*nu]])^(-1);
  T := Matrix([Matrix([Eltseq(v)])*M : v in ZBasis(O)]);
  TK := [[K!(t[1]+t[2]*R.2), K!(t[3]+t[4]*R.2)] : t in T[1..4*d]];
  PM := PseudoMatrix([1*R : i in [1..4*d]], Matrix(TK));
  PM := HermiteForm(PM);
  I := CoefficientIdeals(PM)[2];
  e := iotaK(Matrix(PM)[2][1]) + iotaK(Matrix(PM)[2][2])*nu;

  BI := Basis(I);
  g1 := iotaK(BI[1]);
  g2 := iotaK(BI[2]);

  if Trace(e) ne 0 then
    t1 := Trace(g1*e);
    t2 := Trace(g2*e);
    x := t2*BI[1] - t1*BI[2];
    I /:= x;
    e := iotaK(x)*e;
  end if;

  ZBIe := [iotaK(g*Basis(R)[1]) : g in Generators(CoefficientIdeals(R)[1])] cat 
          [iotaK(g*Basis(R)[2]) : g in Generators(CoefficientIdeals(R)[2])] cat
          [iotaK(g*Basis(I)[1])*e : g in Generators(CoefficientIdeals(I)[1])] cat 
          [iotaK(g*Basis(I)[2])*e : g in Generators(CoefficientIdeals(I)[2])];
  assert Order(ZBIe) eq O;

  P := PseudoMatrix([1*R, I], ChangeRing(Matrix([1,e]),K));
  return P, I, e, iotaK;
end intrinsic;

intrinsic RModule(O::AlgQuatOrd, R::RngOrd) -> .
  {Returns the quaternion order O as a module over the quadratic order R.}

  B := Algebra(O);
  QQ := NumberField(Polynomial([0,1]) : DoLinearExtension := true);
  ZZ := MaximalOrder(QQ);
  
  a, b, Bstd, B_to_Bstd := StandardForm(Algebra(O));    

  BB := QuaternionAlgebra<QQ | a,b>;

  B_to_BB := map<B -> BB | x :-> BB!Eltseq(B_to_Bstd(x)), 
                             y :-> (Bstd!Eltseq(y))@@B_to_Bstd >;

  OO := Order([B_to_BB(x) : x in ZBasis(O)]);

  RR := ext<ZZ | MinimalPolynomial(R.2)>;
//  assert RR cmpeq MaximalOrder(RR);

  _, II, e, iotaK := RModule(OO, RR);

  K := NumberField(R);
  KK := NumberField(RR);
  R_to_RR := map<K -> KK | x :-> KK!Eltseq(x), y :-> K!Eltseq(y)>;

  I := ideal<R | [x@@R_to_RR : x in Basis(II)]>;
  P := PseudoMatrix([1*R, I], ChangeRing(Matrix([1,e]),K));

  return P, I, e, R_to_RR*iotaK*B_to_BB^(-1);
end intrinsic;
