freeze;

/////////////////////////////////////////////
// Function to check if the input is sane

import "../AlgAss/enum.m": get_coords;

WrongBR:= "The base ring is not supported";
NotPrime:= "The second argument must be a prime in the base ring of the order";

function IsSupported(O: Prime:= false)
  if Type(Algebra(O)) ne AlgQuat then return false, "Only orders in quaternion algebras are supported", _; end if;
  R:= BaseRing(O); T:= Type(R); 

  if T eq RngInt then
    if Prime cmpne false then
      ok, Prime:= IsCoercible(R, Prime);
      if not ok or not IsPrime(Prime: Proof:= false) then return false, NotPrime, _; end if;
      Prime:= Abs(Prime);
    end if;
  elif T eq RngUPol then
    k:= BaseRing(R);
    if not IsField(k) or not IsFinite(k) or IsEven(Characteristic(k)) then 
      return false, WrongBR, _;
    end if;
    if Prime cmpne false then
      ok, Prime:= IsCoercible(R, Prime);
      if not ok or not IsPrime(Prime) then return false, NotPrime, _; end if;
      Prime:= Normalize(Prime);
    end if;
  elif ISA(T, RngOrd) then
    if Prime cmpne false and (Order(Prime) cmpne R or not IsPrime(Prime)) then return false, NotPrime, _; end if;
    if CoefficientRing(R) cmpne Integers() then
	return false, "Argument 1 must be over an extension of Z", _;
    end if;
  else
    return false, WrongBR, _;
  end if;

  return true, _, Prime;
end function;


/////////////////////////////////////////////
// The Eichler test and invariants

function EichlerFast(O, p)
  R:= BaseRing(O);
  k, h:= ResidueClassField(p);
  case Type(R):
    when RngInt : f:= func< x | KroneckerSymbol(x, p) >;
    when RngUPol: f:= func< x |    JacobiSymbol(x, p) >;
  else
    if Minimum(p) eq 2 then
      f:= func< x | h(x) eq 0 select 0 else (IsLocalSquare(x, p) select 1 else -1) >;
    else
      f:= func< x | y eq 0 select 0 else (IsSquare(y) select 1 else -1) where y:= h(x) >;
    end if;
  end case; 

  B:= LocalBasis(O, p);
  for i in [1..20] do
    x:= &+[ b * (Random(k) @@ h) : b in B ];
    e:= f(R ! (Trace(x)^2-4*Norm(x)));
    if e ne 0 then return e; end if;
  end for;

  return 0;
end function;

function EichlerInternal(O, p)
  // Let's try some discriminants first
  e:= EichlerFast(O, p);
  if e ne 0 then return e; end if;

  // So the result is most likely 0. Let's check to be sure.
  A:= Algebra(O);
  B:= LocalBasis(O, p);
  M:= Matrix([ Eltseq(A ! x) : x in B ])^-1;
  k, h:= ResidueClassField(p);

  RR:= [ Matrix([ Eltseq(A ! (b * c)) : c in B ])*M : b in B ];
  RR:= [ Matrix(4, [ h(x) : x in Eltseq(m)]) : m in RR ];
  B:= sub< MatrixAlgebra(k, 4) | RR >;
  J:= JacobsonRadical(B);
  if Dimension(J) eq 3 then return 0; end if;
  BQ:= Basis(quo< B | J >);
  assert #BQ eq 2;
  ok:= exists(m){ m : b in BQ | Degree(m) eq 2 where m:= MinimalPolynomial(b) };
  return ok and IsIrreducible(m) select -1 else 1;
end function;

intrinsic EichlerInvariant(O::AlgQuatOrd, p::RngElt) -> RngIntElt
{Returns the local Eichler invariant of the quaternion order O at the prime p}
  ok, str, p:= IsSupported(O: Prime:= p);
  require ok : str;
  require Valuation(Discriminant(O), p) ne 0 : "The prime must divide the discriminant of the order";
  return EichlerInternal(O,p);
end intrinsic;

intrinsic EichlerInvariant(O::AlgAssVOrd[RngOrd[RngInt]], p::RngOrdIdl) -> RngIntElt
{"} //"
  ok, str, p:= IsSupported(O: Prime:= p);
  require ok : str;
  require Valuation(Discriminant(O), p) ne 0 : "The prime must divide the discriminant of the order";
  return EichlerInternal(O,p);
end intrinsic;

forward ComputeMaximalOrders;

intrinsic IsEichler(O::AlgAssVOrd : MaximalOrders:= false) -> BoolElt, AlgAssVOrd, AlgAssVOrd
{Test if O is an Eichler order, i.e. the intersection of two maximal orders}
  ok, str:= IsSupported(O);
  require ok : str;
  D:= Discriminant(Algebra(O));
  val:= forall{ f: f in FactoredDiscriminant(O) |
    f[2] eq 1 or (Valuation(D, f[1]) eq 0 and EichlerInvariant(O, f[1]) eq 1) };
  if val and MaximalOrders then
    M1, M2:= ComputeMaximalOrders(O);
    return true, M1, M2;
  end if;
  return val, _, _;
end intrinsic;

intrinsic IsEichler(O::AlgQuatOrd, p::RngElt : MaximalOrders:= false) -> BoolElt, AlgQuatOrd, AlgQuatOrd
{Test if the completion of O at p is an Eichler order}
  ok, str, p:= IsSupported(O : Prime:= p);
  require ok : str;
  val:= Valuation(Discriminant(O), p) le 1 or
       (Valuation(Discriminant(Algebra(O)), p) eq 0 and EichlerInvariant(O, p) eq 1);
  if val and MaximalOrders then
    M1, M2:= ComputeMaximalOrders(O : Primes:= [p]);
    return true, M1, M2;
  end if;
  return val, _, _;
end intrinsic;

intrinsic IsEichler(O::AlgAssVOrd[RngOrd], p::RngOrdIdl : MaximalOrders:= false) -> BoolElt, AlgAssVOrd, AlgAssVOrd
{"} //"
  ok, str, p:= IsSupported(O: Prime:= p);
  require ok : str;
  val:= Valuation(Discriminant(O), p) le 1;
  if not val then 
      require CoefficientRing(CoefficientRing(O)) cmpeq Integers() : "Argument 1 must be over an extension of Z";
      val := (Valuation(Discriminant(Algebra(O)), p) eq 0 and EichlerInvariant(O, p) eq 1);
  end if;
  if val and MaximalOrders then
    M1, M2:= ComputeMaximalOrders(O : Primes:= [p]);
    return true, M1, M2;
  end if;
  return val, _, _;
end intrinsic;

/////////////////////////////////////////////
// IsHereditary

intrinsic IsHereditary(O:: AlgAssVOrd) -> Bool
{Returns true iff the order O of a quaternion algebra is hereditary.}
  ok, str:= IsSupported(O);
  require ok : str;
  return forall{f: f in FactoredDiscriminant(O) | f[2] eq 1};
end intrinsic;

intrinsic IsHereditary(O::AlgQuatOrd, p::RngElt) -> BoolElt
{Test if the completion of O at p is a hereditary order}
  ok, str, p:= IsSupported(O : Prime:= p);
  require ok : str;
  return Valuation(Discriminant(O), p) le 1;
end intrinsic;

intrinsic IsHereditary(O::AlgAssVOrd[RngOrd], p::RngOrdIdl) -> BoolElt
{"} //"
  ok, str, p:= IsSupported(O: Prime:= p);
  require ok : str;
  return Valuation(Discriminant(O), p) le 1;
end intrinsic;


/////////////////////////////////////////////
// IsGorenstein and GorensteinClosure

function Gorenstein_Internal(O)
  A:= Algebra(O);
  T:= Type(O);

  if T eq AlgQuatOrd then
    B:= Basis(O);
  else
    P:= PseudoBasis(O);
    B:= [ p[2] : p in P ];
  end if;
  M:= Matrix([A ! b : b in B ]);
  G:= InnerProductMatrix(NormSpace(A));
  GB:= M * G * Transpose(M);
  BDual:= [ &+[ B[i] * GI[j,i] : i in [1..4] ] : j in [1..4] ] where GI:= GB^-1;

  if T eq AlgAssVOrd then
    BDual:= [ g * BDual[i] : g in Generators(P[i, 1]^-1), i in [1..4] ];
  end if;

  GDual:= M * G * Transpose(M) where M:= Matrix( [ Eltseq(A ! x) : x in BDual ] );
  for i in [1..Ncols(GDual)] do GDual[i,i] /:= 2; end for;

  R:= BaseRing(O);
  if T eq AlgQuatOrd then
    e:= Eltseq(GDual);
    d:= LCM({ Denominator(x) : x in e });
    return ExactQuotient(d, GCD( { R | d*x: x in e } )), BDual;
  else
    return R !! (ideal< R | Eltseq(GDual) >^-1), BDual;
  end if;
end function;

intrinsic IsGorenstein(O::AlgAssVOrd) -> BoolElt, .
{Returns true iff O is a Gorenstein order in a quaternion algebra}
  ok, str:= IsSupported(O);
  require ok : str;
  lvl:= Gorenstein_Internal(O);
  B:= Discriminant(O) div lvl;
  return IsOne(B), B;
end intrinsic;

intrinsic IsGorenstein(O::AlgQuatOrd, p::RngElt) -> BoolElt, RngIntElt
{Test if the completion of O at p is a Gorenstein order}
  ok, str, p:= IsSupported(O : Prime:= p);
  require ok : str;
  v:= Valuation(Discriminant(O), p);
  if v le 2 then
    v:= 0;
  else
    lvl:= Gorenstein_Internal(O);
    v -:= Valuation(lvl, p);
  end if;
  return v eq 0, v;
end intrinsic;

intrinsic IsGorenstein(O::AlgAssVOrd[RngOrd], p::RngOrdIdl) -> BoolElt, RngIntElt
{"} //"
  ok, str, p:= IsSupported(O : Prime:= p);
  require ok : str;
  v:= Valuation(Discriminant(O), p);
  if v le 2 then 
    v:= 0; 
  else
    lvl:= Gorenstein_Internal(O);
    v -:= Valuation(lvl, p);
  end if;
  return v eq 0, v;
end intrinsic;

intrinsic GorensteinClosure(O::AlgAssVOrd) -> AlgAssVOrd, .
{Returns the smallest Gorenstein order containing the quaternion order O}
  ok, str:= IsSupported(O);
  require ok : str;
  lvl, Dual:= Gorenstein_Internal(O);
  B:= Discriminant(O) div lvl;
  if IsOne(B) then return O, B; end if;    // The order is its own closure.
  if Type(O) eq AlgQuatOrd then
    return QuaternionOrder([ lvl*x*y: x,y in Dual ]), B;
  end if;
  return Order([ g*x*y: x,y in Dual, g in Generators(lvl) ]), B;
end intrinsic;

/////////////////////////////////////////////
//// IsBass

intrinsic IsBass(O::AlgQuatOrd, p::RngElt) -> BoolElt
{Test if the completion of O at p is a Bass order}
  ok, str, p:= IsSupported(O : Prime:= p);
  require ok : str;
  v:= Valuation(Discriminant(O), p);
  if v le 2 or EichlerFast(O, p) ne 0 then return true; end if; 
  if not IsGorenstein(O, p) then return false; end if;
  if v le 3 then return true; end if;
  return b where b:= IsGorenstein(RadicalIdealizer(O, p), p); 
end intrinsic;

intrinsic IsBass(O::AlgAssVOrd[RngOrd[RngInt]], p::RngOrdIdl) -> BoolElt
{"} //"
  ok, str, p:= IsSupported(O: Prime:= p);
  require ok : str;
  v:= Valuation(Discriminant(O), p);
  if v le 2 then return true; end if;
  if EichlerFast(O, p) ne 0 then return true; end if;
  if not IsGorenstein(O, p) then return false; end if;
  if v le 3 then return true; end if;
  return b where b:= IsGorenstein(RadicalIdealizer(O, p), p);
end intrinsic;

intrinsic IsBass(O::AlgAssVOrd) -> BoolElt
{Returns true iff O is a Bass order in a quaternion algebra}
  ok, str:= IsSupported(O);
  require ok : str;
  F:= [ f: f in FactoredDiscriminant(O) | f[2] ge 3 and EichlerFast(O,f[1]) eq 0 ];
  if IsEmpty(F) then return true; end if;
  if not IsGorenstein(O) then return false; end if;
  for f in F do O:= RadicalIdealizer(O, f[1]); end for;
  return b where b:= IsGorenstein(O);
end intrinsic;

/////////////////////////////////////////////
// TernaryForm and QuaternionOrder from form

intrinsic TernaryForm(O::AlgQuatOrd) -> AlgMatElt
{Returns a representative of the similarity class of
 ternary forms associated to the quaternion order O}
  ok, str:= IsSupported(O);
  require ok : str;
  lvl, Dual:= Gorenstein_Internal(O);
  require lvl eq Discriminant(O): "The order is not Gorenstein";
  R:= BaseRing(O);
  K:= KernelMatrix(Matrix(R, 1, [Trace(b): b in Dual]));
  K *:= lvl;
  B0 := [ &+[k[j]*Dual[j] : j in [1..4]] where k is Eltseq(K[i]) : i in [1..3]];
  T:= Matrix(3, [ Trace(x*Conjugate(y))/2 : x,y in B0 ]);
  return T;
end intrinsic;

intrinsic TernaryForm(O::AlgAssVOrd) -> LatNF
{"} //"
  ok, str:= IsSupported(O);
  require ok : str;
  lvl, Dual:= Gorenstein_Internal(O);
  require lvl eq Discriminant(O): "The order is not Gorenstein";

  A:= Algebra(O);
  FF:= FieldOfFractions(BaseRing(O));
  P:= PseudoMatrix(Module([Vector(FF, Eltseq(A ! d)) : d in Dual]));

  M:= Matrix(P);
  N:= HorizontalJoin( M, Matrix(FF, 1, [ Trace(A ! M[i]): i in [1..4] ]) );

  P:= PseudoMatrix(CoefficientIdeals(P), Matrix(N));
  P:= HermiteForm(P);
  N:= Matrix(P);
  C:= CoefficientIdeals(P);

  assert [ i: i in [1..4] | N[i,5] eq 0 ] eq [1..3];
  NN:= [ A ! Eltseq(N[i])[1..4] : i in [1..3]];
  T:= Matrix(3, [ FF | Trace(x*Conjugate(y))/2 : x,y in NN ]);
  V:= VectorSpace(FF, 3, T);
  M:= Module([ < C[i], V.i> : i in [1..3] ]);
  return NumberFieldLattice(M);
end intrinsic;

intrinsic QuaternionOrder(T::AlgMatElt) -> AlgQuatOrd
{Returns the quaternion order associated to the ternary quadratic form T.}
  require Ncols(T) eq 3 and IsSymmetric(T) and Rank(T) eq 3: "The form must be a symmetric, ternary and non-degenerate";
  R:= BaseRing(T);
  if Type(R) in {RngInt, RngUPol} then R:= FieldOfFractions(R); T:= ChangeRing(T, R); end if;
  t:= Type(R);
  require t eq FldRat or 
    (t eq FldFunRat and IsFinite(BaseField(R)) and Characteristic(R) ne 2): 
    "The form must be over the rationals or F_q(x) with q odd";

  C, V, h:= CliffordAlgebra(T);
  S:= h(Basis(V));
  BB:= [ S[2]*S[3], S[3]*S[1], S[1]*S[2] ];
  CC:= sub< C | BB >;
  ok, Q, hh:= IsQuaternionAlgebra(CC);
  assert ok;

  n:= { T[i,j] * (i eq j select 1 else 2) : j in [1..i], i in [1..3] };
  d:= LCM( { Denominator(x) : x in n } );
  n:= d / GCD( { Integers(R) | Numerator(x*d) : x in n } );
  TT:=  [C ! 1,  S[1]*S[2]*n, S[2]*S[3]*n, S[3]*S[1]*n ];

  TT:= ChangeUniverse(TT, CC) @ hh;
  return QuaternionOrder(TT : IsBasis);
end intrinsic;

intrinsic QuaternionOrder(L::LatNF) -> AlgAssVOrd
{Returns the quaternion order associated to the ternary lattice L.}
  require Rank(L) eq 3: "The lattice must be ternary";
  // note that the degree of L might be larger then 3

  T:= Matrix( PseudoGramMatrix(L) );
  I:= CoefficientIdeals(L);

  C, V, h:= CliffordAlgebra(T);
  BB:= [ B[2]*B[3], B[3]*B[1], B[1]*B[2] ] where B:= h(Basis(V));
  CC:= sub< C | BB >;
  ok, Q, hh:= IsQuaternionAlgebra(CC);
  assert ok;

  S:= [ h( g * V.i ): g in Generators(I[i]), i in [1..3] ];
  NormGen:= Generators( Norm(L)^-1 );
  T:= [C ! 1] cat [ g*s*t : g in NormGen, s,t in S ];
  TT:= ChangeUniverse(T, CC) @ hh;
  return Order(TT);
end intrinsic;

intrinsic IsSameType(O1::AlgAssVOrd, O2::AlgAssVOrd) -> BoolElt
{Tests if the quaternion orders O1 and O2 are of the same type, i.e. locally isomorphic}
  require Type(Algebra(O1)) eq AlgQuat and Type(Algebra(O1)) eq AlgQuat : "Only implemented for quaternion orders";
  R:= BaseRing(O1);
  require Type(R) eq RngInt or ISA(Type(R), RngOrd) : "The base ring is not supported";
  require R cmpeq BaseRing(O2) : "the orders must have teh same base rings";

  // Easy cases:
  if Discriminant(O1) ne Discriminant(O2) then return false; end if;

  E1:= IsEichler(O1);
  E2:= IsEichler(O2);
  if E1 or E2 then return E1 and E2; end if;

  G1, b1:= GorensteinClosure(O1);
  G2, b2:= GorensteinClosure(O2);
  if b1 ne b2 then return false; end if;

  E1:= IsEichler(G1);
  E2:= IsEichler(G2);
  if E1 or E2 then return E1 and E2; end if;

  // Use the genus machinery of LatNF:
  L1:= TernaryForm(G1);
  L2:= TernaryForm(G2);
  if Type(R) eq RngInt then
    K:= QNF();
    L1:= NumberFieldLatticeWithGram( Matrix(K, L1) );
    L2:= NumberFieldLatticeWithGram( Matrix(K, L2) );
  end if;
  return IsSameGenus(L1, L2); 
end intrinsic;

function ComputeMaximalOrders(O : Primes:= [])
  flat:= Type(O) eq AlgQuatOrd;

  if IsEmpty(Primes) then
    FD:= FactoredDiscriminant(O);
  else
    D:= Discriminant(O);
    FD:= [ <p, Valuation(D, p) > : p in Primes ];  
  end if;
  N:= [ d : d in FD | d[2] gt 1 ];
  M:= O;
  R:= BaseRing(O);
  C:= CommutatorIdeal(O);
  A:= Algebra(O);
  As:= [A | ];

  if not IsEmpty(N) then
    q,h:= quo< R | &* [ n[1]^n[2] : n in N ] >;
    pp:= [ n[1]: n in N ];
    if flat then
      BC:= [ n*b: b in Basis(C) ] where n:= 1/Norm(C);
    else
      NC:= Norm(C);
      P:= PseudoBasis(C);
      BC:= [];
      for b in P do
        idl:= b[1] / NC;
        F:= [ f: f in Factorization(idl) | f[2] gt 0 and forall{p: p in pp | p ne f[1]} ];
        Vals:= [ Valuation(idl, p) : p in pp ] cat [f[2] : f in F];
        Append(~BC, b[2] * WeakApproximation(pp cat [f[1]: f in F], Vals));
      end for;
    end if;

    // get a basis for O at least mod &* N.
    G:= Matrix(4, [ Trace(b*Conjugate(c)) : b,c in BC])^-1;
    B:= [ &+[BC[j] * G[i,j] : j in [1..4]] : i in [1..4]];
    ok, G:= CanChangeRing(G, q);
    assert ok;

    qq, hh:= quo< Image( MatrixRing(q, 4) ! 1 ) | Image(G) >;
    m:= Moduli(qq);
    assert #m eq 2 and IsZero(m[1]) and IsZero(m[2]);
    // B acts linearly on qq by 2x2 matrices as follows.
    B2:= [ &+[ (R ! e[j]) * BC[j]: j in [1..4] ] where e:= Eltseq(qq.i @@ hh): i in [1..2] ];

    MM:= [ Matrix( [ Eltseq(Vector(Eltseq(A ! (x*b))) * T) @ hh : x in B2 ] ) : b in B ] 
      where T := Matrix([ Eltseq(A ! b) : b in BC ])^-1;
    MM:= [ ChangeRing(m, R): m in MM | not IsScalar(m) ];
    assert not IsEmpty(MM);
    CP:= [ CharacteristicPolynomial(m) : m in MM ];

    F:= BaseField(A);
    for n in N do
      _, hCF:= ResidueClassField(n[1]);
      CF, hC:= Completion(F, n[1] : Precision:= n[2] + 5);
      P:= Integers(CF);

      // let's find the matrix with two distinct eigenvalues
      // then we lift its eigenvalues / eigenspaces mod n[1]^n[2]
      i:= 0;
      for j in [1..#MM] do
	r:= Roots(Polynomial(Eltseq(CP[j]) @ hCF));
        if #r eq 2 then i:= j; break; end if;
      end for;
      assert i ne 0;
      f:= ChangeRing(Polynomial(Eltseq(CP[i]) @ hC), P);
      r:= [ HenselLift(f,  P ! ((x[1] @@ hCF) @ hC), n[2]) : x in r ];
      Rp:= quo< R | n[1]^n[2] >;
      MMp:= [ ChangeRing(m, Rp) : m in MM ];
      ES:= Matrix([ Kernel(MMp[i] - (Rp ! R ! (x @@ hC))).1 : x in r ]);
      assert IsInvertible(ES);
      MMp:= [ ES * m * ESI : m in MMp ] where ESI:= ES^-1;
      assert forall{m : m in MMp | IsDiagonal(m)};
      a:= B2[1] * R ! ES[1,1] + B2[2] * R ! ES[1,2];
      // a is the only choice at the place n[1]. Now we must get rid of
      // possible denominators coming from places different then n[1].
      if flat then
  	a *:= Discriminant(O) / n[1]^n[2];
      else
	PP:= [ p : p in FD | p ne n ];
	if not IsEmpty(PP) then
  	  a *:= WeakApproximation( [n[1]] cat [ p[1] : p in PP ], [0] cat [ p[2] : p in PP ] );
	end if;
      end if;
      //M:= flat select QuaternionOrder( Basis(M) cat [a] ) else Adjoin(M, a);
      Append(~As, a);
    end for;
  end if;

  // now the places that divide the level with valuation 1.
  for f in FD do
    if f[2] eq 1 and HilbertSymbol(A, f[1]) eq 1 then
      _, _, x, _:= get_coords(M, f[1]);
      pi:= flat select 1/f[1] else WeakApproximation([f[1]], [-1]);
      Append(~As, x * pi);
    end if;
  end for;

  M:= flat select QuaternionOrder( Basis(M) cat As ) else Order( As cat Generators(M) );
  MM:= LeftOrder( rideal< M | Generators(C) > );

  assert O eq M meet MM;
  if IsEmpty(Primes) then
    assert IsMaximal(M) and IsMaximal(MM);
  else
    assert forall{ p: p in Primes | IspMaximal(M, p) and IspMaximal(MM, p) };
  end if;

  return M, MM;
end function;
