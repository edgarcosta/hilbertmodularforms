freeze;

////////////////////////////////////////////////////////////////////////
//                                                                    //
//                         QUATERNION ALGEBRAS                        //
//                            by David Kohel                          //
//                                                                    //
////////////////////////////////////////////////////////////////////////

import "../AlgAss/enum.m" : get_coords;

forward LLLSeq, LLLAlgQuat, IntBasisClosure, enlarge_order;

////////////////////////////////////////////////////////////////////////
//                                                                    //
//                        Attribute declarations                      //
//                                                                    //
////////////////////////////////////////////////////////////////////////

declare attributes AlgQuat:
   NormSpace,
   ExtensionField;

declare attributes AlgQuatOrd:
   ReducedMatrix,
   ReducedGram,
   NormSpace,
   LeftIdealBases;

////////////////////////////////////////////////////////////////////////
//                                                                    //
//                       Creation Functions                           //
//                                                                    //
////////////////////////////////////////////////////////////////////////

intrinsic QuaternionAlgebra(F::Fld, a::RngElt, b::RngElt) -> AlgQuat
{Same as QuaternionAlgebra<F|a,b>. This is the quaternion algebra over F
 spanned by 1,i,j and i*j satisfying i^2=a, j^2=b and i*j=-j*i}
  return QuaternionAlgebra<F|a,b>;
end intrinsic;

function Discriminants(N,M,B)
   // PRE: N is a product of ODD prime powers, and M is 
   // relatively prime to N.
   // POST: Determines a list of discriminants in which all 
   // prime factors of N are inert, and all prime factors of 
   // M are split, up to a bound in N*M.

   B0 := Isqrt(4*N*M);
   error if GCD(N,M) ne 1,
      "Common prime in split and ramifying lists.";
   RamifyingFactors := Factorization(N);
   SplitFactors := Factorization(M);
   ReturnDiscs := [ -4*n+j : j in [1,0] , n in [Max(1,B0-B)..B0+B] ];
   for D in ReturnDiscs do
      for q in RamifyingFactors do 
         if KroneckerSymbol(D,q[1]) ne -1 then
            Exclude(~ReturnDiscs,D);
         end if;
      end for;
      for p in SplitFactors do 
         if KroneckerSymbol(D,p[1]) ne 1 then
            Exclude(~ReturnDiscs,D);
         end if;
      end for;
   end for;
   return ReturnDiscs;
end function;

function TraceValues(D1,D2,N,M)
   // PRE: All factors of N inert and all factors of M split 
   // in D1 and D2.
   // POST: For an integer T set D = (D1*D2 - T^2).  Returns 
   // the T for which D is positive, D mod 4*N*M is zero, 
   // Q = D div 4*N*M is relatively prime to N, and all 
   // factors of Q are either split in one of D1 or D2 or 
   // inert in D1 or D2 and divide Q to an even power.

   // Stupid, but here goes...
   Tmax := Isqrt(D1*D2 div 4);
   T := -Tmax;
   prms := PrimeDivisors(N) cat PrimeDivisors(M);
   rts := [ Integers() | ];
   Tvals := [ (D1 mod 2)*(D2 mod 2) ];
   m := 2; 
   if 2 in prms then
      Exclude(~prms,2);
      m := 8; 
      D := ((D1 mod 4)*(D2 mod 4)) mod 8;
      if D in { 0, 1 } then
         Tvals := [ D, D + 4 ];
      elif D eq 4 then
         Tvals := [ 2, 6 ];
      end if;
   end if;
   for p in prms do
      t := PolynomialRing(FiniteField(p)).1;
      a := Roots(t^2 - D1*D2)[1][1];
      Append(~rts,Integers()!a);
   end for;
   for i in [1..#prms] do 
      p := prms[i]; 
      a := rts[i];
      Tvals := &join[ { x : x in &join[ { y, p*m - y } : 
         y in [ CRT([a0,a1],[p,m]) : a0 in [-a,a] ] ]
         | Abs(x) le Tmax } : a1 in Tvals ];
      m *:= p;
   end for;
   for T in Tvals do
      Q := (D1*D2 - T^2) div (4*N*M);
      if Q eq 1 then 
         return [ T ];
      elif GCD(Q,N) ne 1 then
         Exclude(~Tvals,T);
      else
         OtherFactors := Factorization(Q);
         for p in OtherFactors do
            if KroneckerSymbol(D1,p[1]) ne 1 or 
               KroneckerSymbol(D2,p[1]) ne 1 then
               Exclude(~Tvals,T);
            end if;
         end for;
      end if;
   end for;
return [ T : T in Tvals ];
end function;

intrinsic QuaternionAlgebra(N::RngIntElt : Al := "Smallest",
                                           Optimized := true) -> AlgQuat
  {Returns a rational quaternion algebra of discriminant N, where
   N is squarefree.  If Al is set to "Random", then a faster, 
   probablistic algorithm is used; if Al is set to "TraceValues", 
   an algebra basis also gives a basis for a maximal order (of 
   discriminant N).}

  fact := Factorization(N);
  require N gt 0 and &and [p[2] eq 1 : p in fact] : 
    "Discriminant must be a square-free positive integer.";  
  oo := (-1)^(#fact mod 2);
  if Al eq "Smallest" then
    a := oo*N;
    b := 0;
    repeat
      b -:= 1;
      passed := Gcd(a,b) eq 1 and 
                &and[ KroneckerSymbol(b, p[1]) eq -1 : p in fact] and
                &and[ KroneckerSymbol(a, p[1]) eq 1 : p in Factorization(b)];
      if not passed and oo eq 1 then
        passed := Gcd(a,b) eq 1 and 
                  &and[ KroneckerSymbol(-b, p[1]) eq -1 : p in fact] and
                  &and[ KroneckerSymbol(a, p[1]) eq 1 : p in Factorization(b)];
        if passed then
          b *:= -1;
        end if;
      end if;
    until passed;
    A := QuaternionAlgebra<Rationals() | a,b>;
    if not Optimized then
      return A;
    end if;
    O := MaximalOrder(A);
  //return OptimizedRepresentation(O);
    return AA where AA is OptimizedRepresentation(O); // don't return the map too --SRD
  elif oo eq 1 or Al eq "Random" then
    a := oo*N;
    m := 4*N;

    cnt := 0;
    bnd := Max(10,Sqrt(m));
    repeat
      cnt +:= 1;
      repeat
        b := Random(Integers(m));
      until Gcd(b,m) eq 1;

      b := oo*(Integers()!b);
      passed := &and[ KroneckerSymbol(b, p[1]) eq -1 : p in fact] and
                IsPrime(b) and KroneckerSymbol(a,b) eq oo;

      if cnt gt bnd then
        cnt := 0;
        m *:= m;
        bnd *:= Sqrt(m);
      end if;
    until passed;

    A := QuaternionAlgebra<Rationals() | a,b>;
    if not Optimized then
      return A;
    end if;
    O := MaximalOrder(A);
  //return OptimizedRepresentation(O);
    return AA where AA is OptimizedRepresentation(O); // don't return the map too --SRD
  else
    // First test for the easy cases.
    if N eq 2 then 
      return QuaternionAlgebra(-3,-3,1);
    elif (N mod 4) eq 3 and 
      &and [ KroneckerSymbol(-4,p[1]) eq -1 : p in fact ] then
      return QuaternionAlgebra(-4,-N,0);
    elif (N mod 8) eq 5 and 
      &and [ KroneckerSymbol(-8,p[1]) eq -1 : p in fact ] then
      return QuaternionAlgebra(-8,-((N+1) div 2),2);
    end if;
    B := Ceiling(Log(N));
    for k in [1..8] do
      DiscList := Discriminants(N,1,2^k*B);
      DiscPairs := [ [D1,D2] : D2, D1 in DiscList | D1*D2 gt (4*N) ];
      for D in DiscPairs do
        TList := TraceValues(D[1],D[2],N,1); 
        if #TList gt 0 then 
          K := QuaternionAlgebra(D[1],D[2],TList[1]);
          if Discriminant(K) eq N then
            return K;
          end if;
        end if;
      end for;
    end for;             
    error "Error, no order found (please report).";
  end if;
end intrinsic;

intrinsic QuaternionAlgebra(N::RngUPolElt) -> AlgQuat
{Returns a quaternion algebra over F_q(x) of discriminant N, where
   N in F_q[x] is squarefree.}
  R:= Parent(N);
  K:= FieldOfFractions(R);
  k:= BaseField(K);
  require IsFinite(k) and IsOdd(Characteristic(k)) : "The discriminant must be a polynomial over F_q with q odd";
  f:= Factorization(N);
  require forall{ p : p in f | p[2] eq 1 } : "The discriminant must be square free";
  f:= [ p[1] : p in f ];
  e:= Nonsquare(k);
  // the obvious case
  if forall{p: p in f | IsOdd(Degree(p))} then
    b:= e;
  else
    V:= VectorSpace(GF(2), #f);
    ones:= V ! [ 1^^#f ];
    v:= V ! [ IsOdd(Degree(p)) select 1 else 0 : p in f ];
    if IsZero(v) then
      M:= [ V | ];
      List:= [ ];
    else
      M:= [ v ];
      List:= [ R | e ];
    end if;
    S:= sub< V | v >;

    i:= 0;
    // infinite place ramifies and even degree, so leading coeff. must be e.
    if IsEven(Degree(N)) and IsOdd(#f) then N := e * Normalize(N); end if;
    repeat
      i +:= 1;
//    if i mod 100 eq 0 then <i, #M>; end if;
      q:= RandomPrimePolynomial(R, Random(1, 1+(i div 5)));
      if JacobiSymbol(N, q) ne 1 then continue; end if;
      v:= V ! [ JacobiSymbol(q, p) eq 1 select 0 else 1 : p in f ];
      if v in S then continue; end if;
      Append(~M, v);
      Append(~List, q);
      S:= VectorSpaceWithBasis(M);
    until ones in S;
//    "needed", i, "tries";
    c:= Coordinates(S, ones);
    b:= &*[ List[k] : k in [1..#List] | c[k] ne 0 ];
  end if;
  Q:= QuaternionAlgebra< K | N, b >;
//  assert Set(RamifiedPrimes(Q)) eq Set(f);      // time consuming
  // Maybe we even set the ramified primes of Q to the list f?
  return Q;
end intrinsic;

function RandomElement(A,S)
   return A![ Random(S) : i in [1..4] ];
end function;

// The function "Squarefree" is not available over poly rings.
mysquarefree:= function(x)
  if Type(x) eq RngIntElt then return Squarefree(x); end if;
  s:= Parent(x) ! 1;
  for f in SquareFreeFactorization(x) do
    if f[2] ne 0 then
      s *:= f[1]^(f[2] div 2);
    end if;
  end for;
  return x div s^2, s;
end function;

function get_order(A)
  R:= Integers( BaseField(A) );
  x:= A.1 - Trace(A.1)/2;
  x*:= Denominator(Norm(x));
  _, k:= mysquarefree(R ! Norm(x)); x /:= k;
  y:= QuaternionicComplement(x);
  y*:= Denominator(Norm(y));
  _, k:= mysquarefree(R ! Norm(y)); y /:= k;
  return QuaternionOrder([A | 1, x, y, x*y ] : IsBasis:= true);
end function;

intrinsic MaximalOrder(K::AlgQuat[FldRat]) -> AlgQuatOrd
   {A maximal quaternion order in K.}
  if not assigned K`MaximalOrder then
    K`MaximalOrder:= MaximalOrder(get_order(K));
  end if;
  return K`MaximalOrder;
end intrinsic;

intrinsic MaximalOrder(K::AlgQuat[FldFunRat]) -> AlgQuatOrd
{"} // "
  if not assigned K`MaximalOrder then
    F:= BaseField(K);
    require Characteristic(F) ne 2 and IsFinite(BaseRing(F)) : "base field is not supported";
    K`MaximalOrder:= MaximalOrder(get_order(K));
  end if;
  return K`MaximalOrder;
end intrinsic;

intrinsic MaximalOrder(O::AlgQuatOrd[RngInt]) -> AlgQuatOrd
   {A maximal quaternion order containing O}

   m := Level(O);
   if IsOne(m) then return O; end if;
   fact := [ p[1] : p in Factorization(m) ];
   ZZ := Integers();
   B:= Basis(O);
   while #fact ne 0 do 
      p := fact[1];
      FF := FiniteField(p);
      B1 := Basis(Kernel(MatrixAlgebra(FiniteField(p),4) ! 
              [ Trace(x*Conjugate(y)) : x, y in B ] ) );
      if p eq 2 then
         X := [ &+[ (ZZ!v[i])*B[i] : i in [1..4] ] : v in B1 ];
         for c in CartesianPower({0,1},#B1) do
             if &or [ c[i] eq 1 : i in [1..#B1] ] then
                 z := &+[ c[i]*X[i] : i in [1..#B1] ];
                 if ZZ!Norm(z) mod 4 eq 0 then
                     break c;
                 end if;
             end if;
         end for;
      elif #B1 eq 1 then
         z := &+[ (ZZ!B1[1][i])*B[i] : i in [1..4] ];
      else    
	 // The inner product of elements in B1 with all other elements 
	 // in B1 is divisible by p.  Now we need to solve for a linear 
	 // combination z whose norm (i.e. inner product with itself) is
	 // divisible by p^2, so that z/p is integral.
	 X := [ &+[ (ZZ!v[i])*B[i] : i in [1..4] ] : v in B1 ];
	 T := Matrix(#X,[ FF | ZZ!(Trace(x*Conjugate(y))/p) : x, y in X ]);
         B2 := Basis(Kernel(T)); 
         if #B2 ne 0 then
	    z := &+[ (ZZ!B2[1][i])*X[i] : i in [1..#X] ];
         elif #B1 eq 2 then
	    assert #X eq 2; 
            P := PolynomialRing(GF(p));
            f := T[1,1]*P.1^2 + 2*T[1,2]*P.1 + T[2,2];
            z := (ZZ!r)*X[1] + X[2] where r := Roots(f)[1][1];
	 else // T defines Gram matrix of a nonsingular conic
	    assert #B1 eq 3; 
	    assert #X eq 3; 
	    P2 := ProjectiveSpace(GF(p),2); 
	    C := Conic(P2,&+[ T[i,j]*P2.i*P2.j : i, j in [1..3] ]);
	    s := Eltseq(RationalPoint(C));
	    z := &+[ (ZZ!s[i])*X[i] : i in [1..3] ];
         end if;
      end if;
      B := LLLAlgQuat(B cat [z/p]);
      m div:= p;
      if (m mod p) ne 0 then
         Exclude(~fact,p); 
      end if;
   end while;
   
   return QuaternionOrder([ u*x : x in B ]) where u is B[1]^-1;
end intrinsic;

intrinsic MaximalOrder(O::AlgQuatOrd[RngUPol]) -> AlgQuatOrd
{"} // "
  if assigned O`IsMaximal and O`IsMaximal then return O; end if;
  F:= BaseField(Algebra(O));
  require Characteristic(F) ne 2 and IsFinite(BaseRing(F)) : "base field is not supported";
  return enlarge_order(O, true);
end intrinsic;


function IntBasisClosure(S)
   // over the rationals!!!
   K := Universe(S);
   V := KSpace(RationalField(),4);
   if not &or [ x eq K!1 : x in S ] then
      S := [ K!1 ] cat S;
   end if;
   S := LLLAlgQuat(S);
   // Problems if #S > 4 seen...
   if #S lt 4 then
      S := LLLAlgQuat([ x*y : x, y in S ]);
      if #S lt 4 then
         return false, S;
      end if;
   elif #S gt 4 then
      print "Found inconsistent reduction data.";
      print "K =", K;
      print "Basis(K) =", Basis(K);
      print "Inner product matrix:";
      print Matrix(4,[ Trace(x*Conjugate(y)) : x, y in Basis(K) ]);
      print "Failed in reduction of S:";
      print S;
      // Let this one slide...
      // assert false;
      // Provided the bug is understood (and caught later)...
      assert (#S eq 5 and S[5] eq 0);
   end if;
   M := Matrix(4,&cat[ Eltseq(x) : x in S ])^-1;
   k := 1;
   while k lt 4 do
      T := [ (V!Eltseq(x*y))*M : x, y in S ];
      if &and [ &and[ Denominator(a) eq 1 
         : a in Eltseq(v) ] : v in T ] then
         return true, S;
      end if;
      S := LLLAlgQuat([ K!Eltseq(v) : v in LLLSeq(T) ]);  
      k +:= 1;
   end while;
   return false, S;
end function;

function PolyBasisClosure(S)
   // over k(x)
   K := Universe(S);
   F := BaseField(K);
   k := BaseRing(F);
   error if not IsField(k),
      "Base ring of function field must be a field.";
   M := RSpace(PolynomialRing(k),4);
   if not &or [ x eq K!1 : x in S ] then
      S := [ K!1 ] cat S;
   end if;
   g := F!LCM([ LCM([ Denominator(a) : a in Eltseq(x) ]) : x in S ]);
   T := [ M ! Eltseq(g*x) : x in S ];
   S := [ K![ f/g : f in Eltseq(v) ] : v in Basis(sub< M | T >) ]; 
   if #S gt 4 then
      S := [ K![ f/g : f in Eltseq(v) ] : v in Basis(sub< M | T >) ]; 
   elif #S lt 4 then
      S := [ x*y : x, y in S ];
      g := F!LCM([ LCM([ Denominator(a) : a in Eltseq(x) ]) : x in S ]);
      T := [ M ! Eltseq(g*x) : x in S ];
      S := [ K![ f/g : f in Eltseq(v) ] : v in Basis(sub< M | T >) ]; 
      if #S lt 4 then
         return false, S;
      end if;
   end if;
   V := KSpace(F,4); 
   A := ( MatrixAlgebra(F,4) ! &cat[ Eltseq(x) : x in S ] )^-1;
   k := 1;
   while k le 3 do
      X := [ (V!Eltseq(x*y))*A : x, y in S ];
      if &and [ &and [ Denominator(a) eq 1 
            : a in Eltseq(v) ] : v in X ] then
         return true, S;
      end if;
      S := [ x*y : x, y in S ];
      g := F!LCM([ LCM([ Denominator(a) : a in Eltseq(x) ]) : x in S ]);
      T := [ M ! Eltseq(g*x) : x in S ];
      S := [ K![ f/g : f in Eltseq(v) ] : v in Basis(sub< M | T >) ]; 
      k +:= 1;
   end while;
   return false, S;
end function;

intrinsic QuaternionOrder(S::[AlgQuatElt[FldRat]] : IsBasis := false) 
   -> AlgQuatOrd
   {Quaternion order generated by S, preserving S if it constitutes
   a basis with initial element 1.}

   if not IsBasis then
      test, S := IntBasisClosure(S);
      require #S eq 4 : "Sequence does not generate an order.";  
      require test : "Sequence not closed under multiplication.";  
      S := [ r*x : x in S ] where r := S[1]^-1; 
   else
      require #S eq 4 : "Generators do not define an order.";
   end if;
   return QuaternionOrder(Integers(),S);
end intrinsic;

intrinsic QuaternionOrder(S::[AlgQuatElt[FldFunRat]] : IsBasis := false)
   -> AlgQuatOrd
   {"} // "

   if not IsBasis then
      test, S := PolyBasisClosure(S);
      require #S eq 4 : "Sequence does not generate an order.";
      require test : "Sequence not closed under multiplication.";
   else
      require #S eq 4 : "Generators do not define an order.";
   end if;
   return QuaternionOrder(Integers(BaseField(Universe(S))),S);
end intrinsic;

intrinsic QuaternionOrder(K::AlgQuat[FldRat],M::RngIntElt) -> AlgQuatOrd
   {Returns a quaternion order of level M in K.}

   require Type(BaseField(K)) eq FldRat :
      "Constructor defined only for quaternion algebras over the rationals."; 
   M := Abs(M);
   N := Integers()!Discriminant(K);
   N1 := GCD(M,N);
   M1 := M div N1;
   A := MaximalOrder(K);
   if N1 ne 1 then
      require Max([ Valuation(M,p) : p in RamifiedPrimes(K) ]) le 1 :
         "Level can be divisible by at most 
          the first power of a ramified prime.";
      P := lideal< A | [ A | N1 ] cat 
              [ x*y - y*x : x, y in Basis(A) ] >;
      A := QuaternionOrder([ K!x : x in Basis(P) ]); 
   end if;
   fact := Factorization(M1);   
   for p in fact do 
      repeat 
         x := RandomElement(A,[-p[1] div 2..p[1] div 2]);
         D := Trace(x)^2 - 4*Norm(x);
      until KroneckerSymbol(D,p[1]) eq 1; 
      P := PolynomialRing(FiniteField(p[1])); 
      X := P.1;      
      a := Integers()!Roots(X^2 - Trace(x)*X + Norm(x))[1][1];
      I := lideal< A | [ A | p[1]^p[2], (x-a)^p[2] ]>;
      A := A meet RightOrder(I); 
   end for;
   return A;
end intrinsic;

intrinsic QuaternionOrder(N::RngIntElt) -> AlgQuatOrd
   {Returns a maximal order in the rational quaternion algebra of discrinant N.}

   require IsSquarefree(N) : "N must be squarefree";
   return MaximalOrder(QuaternionAlgebra(N));
end intrinsic;

intrinsic QuaternionOrder(N::RngIntElt,M::RngIntElt) -> AlgQuatOrd
   {Returns a quaternion order of level M in the rational quaternion 
   algebra of discrinant N.}
   prms := PrimeDivisors(N);
   if N ne 1 then
     require Max([ Valuation(N,p) : p in prms ]) le 1 :
        "Argument 1 can have valuation at most 1 at each prime.";
     require Max([ Valuation(M,p) : p in prms ]) le 1 :
        "Argument 2 can have valuation at most 1 
         at each prime divisor of argument 2.";
   end if;
   return QuaternionOrder(QuaternionAlgebra(N),M);
end intrinsic;

intrinsic Order(O::AlgQuatOrd,Lvl::RngElt) -> AlgQuatOrd
{Returns an order of level Lvl in O. The level of O and Lvl must be coprime.}
  R:= BaseRing(O);
  ok, Lvl:= IsCoercible(R, Lvl);
  require ok: "The level must lie in the base ring of the order.";

  T:= Type(R);
  if T eq RngUPol then
    F:= BaseRing(R);
    ok := IsField(F) and IsFinite(F) and Characteristic(F) ge 3;
    Lvl:= Normalize(Lvl);
  elif T eq RngInt then
    ok:= true; Lvl:= Abs(Lvl);
  else
    ok:= false;
  end if;
  require ok: "The base ring must be the integers or F_q(x) with q odd.";

  A:= Algebra(O);
  require forall{f: f in RamifiedPrimes(A) | Valuation(Lvl, f) le 1} : 
    "Level can be divisible by at most the first power of a ramified prime.";
  require GCD(Level(O), Lvl) eq 1:
    "The level of the order and the desired level must be coprime";

  DO:= Discriminant(O);
  Lvl1:= GCD(DO, Lvl);

  if Lvl1 ne 1 then
    P := ideal< O | Lvl1 > + CommutatorIdeal(O);
    O := QuaternionOrder( ChangeUniverse(Basis(P), A) ); 
  end if;

  for f in Factorization(Lvl div Lvl1) do
    a:= get_coords(O, f[1]);
    I:= lideal< O | a^f[2], f[1]^f[2] >;
    O:= O meet RightOrder(I);
  end for;

  assert Discriminant(O) eq DO*Lvl;
  return O;
end intrinsic;

////////////////////////////////////////////////////////////////////////
//                                                                    //
//                     Norm Spaces and Modules                        //
//                                                                    //
////////////////////////////////////////////////////////////////////////

intrinsic NormSpace(K::AlgQuat) -> ModFld, Map
   {The inner product space of A with respect to the norm.} 
   require Characteristic(BaseRing(K)) ne 2 : "Characteristic of the base ring cannot be 2";
   if not assigned K`NormSpace then
      F := BaseField(K);
      K`NormSpace := RSpace(F,4,MatrixAlgebra(F,4) ! 
   	    [ Norm(x+y) - Norm(x) - Norm(y) : x, y in Basis(K) ] ); 
   end if;
   V := K`NormSpace;
   return V, hom< V->K | x :-> V!Eltseq(x) >;
end intrinsic;

intrinsic NormSpace(B::[AlgQuatElt]) -> ModTupFld, Map
    {The inner product subspace with respect to the norm generated
    by the sequence B.} 
    V := NormSpace(Universe(B));
    return sub< V | [ V ! Eltseq(x) : x in B ] >;
end intrinsic;

intrinsic NormSpace(A::AlgQuatOrd) -> ModTupRng, Map
   {The inner product module of A with respect to the norm} 
   if not assigned A`NormSpace then
      K := QuaternionAlgebra(A);
      V := NormSpace(K);
      R := BaseRing(A);
      A`NormSpace := RSpace( R, 4,
 	 [ Norm(x+y) - Norm(x) - Norm(y) : x, y in Basis(A) ] ); 
   end if;
   M := A`NormSpace;
   return M, hom< A -> M | x :-> M!Eltseq(x) >;
end intrinsic;
 
intrinsic NormModule(A::AlgQuatOrd) -> ModTupRng, Map
    {The inner product space of A with respect to the norm.} 
    return NormSpace(A);
end intrinsic;

////////////////////////////////////////////////////////////////////////
//                                                                    //
//                     Arithmetic on Elements                         //
//                                                                    //
////////////////////////////////////////////////////////////////////////

intrinsic CharacteristicPolynomial(x::AlgQuatElt) -> RngUPolElt
   {The characteristic polynomial of x.}
   f := MinimalPolynomial(x);
   return f^(2 div Degree(f));
end intrinsic;

intrinsic CharacteristicPolynomial(x::AlgQuatOrdElt) -> RngUPolElt
   {The characteristic polynomial of x.}
   f := MinimalPolynomial(x);
   return f^(2 div Degree(f));
end intrinsic;

intrinsic Coordinates(x::AlgQuatElt) -> SeqEnum
   {The coordinates of x with respect to the basis of its parent.}
   return Eltseq(x);
end intrinsic;

////////////////////////////////////////////////////////////////////////
//                                                                    //
//                     Booleans for Algebras                          //
//                                                                    //
////////////////////////////////////////////////////////////////////////

intrinsic Conductor(A::AlgQuatOrd) -> RngElt
    {The conductor of the quaternion order, defined to be the index in
    a maximal order of its quaternion algebra.}
    R:= BaseRing(A);
    T:= Type(A);
    if T ne RngInt then
      require T eq RngUPol : "Base ring is not supported";
      F:= BaseRing(R);
      require IsField(F) and IsFinite(F) and Characteristic(F) ne 2: "Base ring is not supported";
    end if;
    return Level(A);
end intrinsic;

intrinsic Level(A::AlgQuatOrd[RngUPol]) -> RngUPolElt
{The index of O in a maximal order}
  F:= BaseRing(BaseRing(A));
  require IsField(F) and IsFinite(F) and Characteristic(F) ne 2: "Base ring is not supported";
  return Discriminant(A) div Discriminant(Algebra(A));
end intrinsic;

intrinsic IsIsomorphic(A::AlgQuat, B::AlgQuat : Isomorphism:= false) -> BoolElt
   {True if A is isomorphic to B.}

   F:= BaseField(A);
   require F cmpeq BaseField(B) :
      "Algebras must have the same base fields.";
   T:= Type(F);
   if T in {FldRat, FldFunRat} then
     if T eq FldFunRat then
       require IsFinite(BaseRing(F)) and Characteristic(F) ne 2 :
         "Base field is not supported.";
     end if;
     val:= Discriminant(A) eq Discriminant(B);
   else
     require ISA(T, FldNum) : "Base field is not supported.";
     D1, S1:= Discriminant(A);
     D2, S2:= Discriminant(B);
     val:= D1 eq D2 and S1 eq S2;
   end if;

   if not val or not Isomorphism then
     return val, _;
   end if;

   // This is quite inefficient since it solves two norm equations.
   // Another strategy is to split A \tensor B^op as M_4(F).
   // But such a splitting function is currently not implemented.
   bl1, _, phi:= IsMatrixRing(A : Isomorphism);		// Testing for an isomorphism is for free at this stage.
   if bl1 then
     bl2, _, tau:= IsMatrixRing(B : Isomorphism);
     assert bl2;
     phi:= phi * Inverse(tau);
   else
     i:= A.1 - Trace(A.1)/2;
     a:= -Norm(i);
     Fi:= ext< F | Polynomial([-a, 0, 1]) >;
     iB, phi:= Embed(Fi, B);
     j:= QuaternionicComplement(i);
     x:= QuaternionicComplement(iB);
     bl, y:= NormEquation(Fi, Norm(j)/Norm(x));
     assert bl;
     jB:= phi(y[1])*x;
     TA:= Matrix( [ Eltseq(t) : t in [A ! 1, i,  j,  i*j  ] ] );
     TB:= Matrix( [ Eltseq(t) : t in [B ! 1, iB, jB, iB*jB] ] );
     T1:= TA^-1*TB;
     T2:= TB^-1*TA;
     phi:= map< A -> B | a:-> B ! Eltseq(Vector(Eltseq(a)) * T1),
                         b:-> A ! Eltseq(Vector(Eltseq(b)) * T2) >;
   end if;
   return true, phi;
end intrinsic;

intrinsic IsDefinite(K::AlgQuat[FldRat]) -> BoolElt
   {True if and only if K is ramified at infinity, where K 
   must be a quaternion algebra over the rationals.}
   return (#RamifiedPrimes(K) mod 2) eq 1; 
end intrinsic;
 
intrinsic IsDefinite(K::AlgQuat[FldFunRat]) -> BoolElt
   {True if and only if K is ramified at the infinite place, 
   where K must be a quaternion algebra over F_q(X).}
   F:= BaseField(K);
   require IsFinite(BaseRing(F)) and Characteristic(F) ne 2 : "Base field is not supported";
   return IsOdd(#RamifiedPrimes(K)); 
end intrinsic;
 
////////////////////////////////////////////////////////////////////////
//                                                                    //
//                        Basis Reduction                             //
//                                                                    //
////////////////////////////////////////////////////////////////////////

intrinsic BasisMatrix(A::AlgQuatOrd) -> AlgMatElt
   {}
   K := QuaternionAlgebra(A);
   return Matrix(4,4,&cat[ Eltseq(K!x) : x in Basis(A) ]);
end intrinsic;

intrinsic ReducedBasis(I::AlgQuatOrdIdl[RngInt]) -> SeqEnum
   {A Minkowski-reduced basis for I, unique up to isomorphism.}
   require IsDefinite(Algebra(I)) :
      "Parent algebra is not definite.";
   _, U:= MinkowskiGramReduction(GramMatrix(I): Canonical);
   B:= Basis(I);
   return [ &+[B[j] * U[i,j] : j in [1..4] | U[i,j] ne 0] : i in [1..4] ];
end intrinsic;

function reduce_ideal_fqx(I, Canonical)
   A:= Algebra(I);
   G:= GramMatrix(NormSpace(A));
   B:= Basis(I);
   F:= BaseRing(A);
   BM:= Matrix( [ Eltseq(A ! b) : b in B ] );
   G:= BM * G * Transpose(BM);
   d:= Denominator(G);
   G:= ChangeRing(d*G, Integers(F));
   if Canonical and IsDefinite(A) then
     if assigned A`ExtensionField then
       GG, T:= DominantDiagonalForm(G: Canonical, ExtensionField:= A`ExtensionField);
     else
       GG, T, _, E:= DominantDiagonalForm(G: Canonical);
       A`ExtensionField:= E;
     end if;
   else
     GG, T:= DominantDiagonalForm(G: Canonical:= false);
   end if;
   GG:= 1/d * ChangeRing(GG, F);
   return GG, T*BM;
end function;

intrinsic ReducedBasis(I::AlgQuatOrdIdl[RngUPol] : Canonical:= false) -> SeqEnum
   {A basis for I such that the Gram matrix is reduced.
    It is unique if the enveloping algebra is definite and Canonical is set}
   A:= Algebra(I);
   k:= BaseField(BaseField(A));
   require IsFinite(k) and IsOdd(Characteristic(k)) : "Base ring must be F_q[X] with q odd.";
   require not Canonical or IsDefinite(A) : "Canonical reduction only works for definite algebras.";
   
   _, T:= reduce_ideal_fqx(I, Canonical);
   return [ A ! T[i]: i in [1..4] ]; 
end intrinsic;

intrinsic ReducedGramMatrix(I::AlgQuatOrdIdl[RngUPol] : Canonical:= false) -> AlgMatElt, SeqEnum
   {A reduced Gram matrix of the quaternion ideal I.
    It is unique if the enveloping algebra is definite and Canonical is set}
   A:= Algebra(I);
   k:= BaseField(BaseField(A));
   require IsFinite(k) and IsOdd(Characteristic(k)) : "Base ring must be F_q[X] with q odd.";
   require not Canonical or IsDefinite(A) : "Canonical reduction only works for definite algebras.";
   
   G, T := reduce_ideal_fqx(I, Canonical);
   return G, [ A ! T[i]: i in [1..4] ];
end intrinsic;

  
intrinsic ReducedBasis(A::AlgQuatOrd[RngInt]) -> SeqEnum
   {A Minkowski-reduced basis for A, unique up to isomorphism if A is definite.}
   if IsDefinite(QuaternionAlgebra(A)) then
     if not assigned A`ReducedMatrix then
        M, U := MinkowskiGramReduction(GramMatrix(A) : Canonical := true);
        // print U;
        u := A!Eltseq(U[1]); 
        if Norm(u) eq 1 and u ne 1 then
          u := A ! Conjugate(u);
          B := [ A | u*(A!Eltseq(U[i])) : i in [1..4] ];
          U := Matrix(4,4,[ Eltseq(x) : x in B ]);         
        end if;
        A`ReducedGram := M;
        A`ReducedMatrix := U;
     end if;
     return [ A ! Eltseq(A`ReducedMatrix[i]) : i in [1..4] ];
   else
     return Basis(A);  // Lame!
   end if;
end intrinsic; 

intrinsic ReducedGramMatrix(A::AlgQuatOrd[RngInt]) -> AlgMatElt
   {A canonical Minkowski-reduced Gram matrix for the norm 
   inner product on A.}
   require IsDefinite(QuaternionAlgebra(A)) : 
      "Parent algebra is not definite.";
   if not assigned A`ReducedGram then
     _:= ReducedBasis(A);
   end if;
   return A`ReducedGram;
end intrinsic;

intrinsic ReducedGramMatrix(O::AlgQuatOrd[RngUPol] : Canonical:= false) -> AlgMatElt, SeqEnum
{A Gram matrix for the norminner product on O which is in dominant diagonal form.
 It is unique if O is definite and Canonical is set}
  if not assigned O`ReducedGram or (Canonical and not O`ReducedGram[3]) then
    A:= Algebra(O);
    k:= BaseRing(BaseField(A));
    require IsField(k) and IsFinite(k) and Characteristic(k) ne 2 : "base ring is not supported";
    require not Canonical or IsDefinite(A) : "Canonical reduction only works for definite algebras";
    B:= ChangeUniverse(TraceZeroSubspace(O), A);
    BM:= Matrix( [ Eltseq(b) : b in B ] );
    R:= BaseRing(O);
    G:= ChangeRing(BM * GramMatrix(NormSpace(A)) * Transpose(BM), R);
    if Canonical then
      if assigned(A`ExtensionField) then
        G, T, N:= DominantDiagonalForm(G: Canonical, ExtensionField:= A`ExtensionField);
      else
        G, T, N, E:= DominantDiagonalForm(G: Canonical);
        A`ExtensionField:= E;
      end if;
      O`Normalizer:= N;
    else
      G, T:= DominantDiagonalForm(G: Canonical:= false);
    end if;
    GG:= DiagonalJoin( Matrix(1, [R | 2]), G );
    BB:= [A | 1] cat [ &+[ T[i,j] * B[j] : j in [1..3] | T[i,j] ne 0 ] : i in [1..3] ];
    O`ReducedGram:= < GG, BB, Canonical >;
  end if;
  return O`ReducedGram[1], O`ReducedGram[2];
end intrinsic;

intrinsic ReducedBasis(O::AlgQuatOrd[RngUPol] : Canonical:= false) -> SeqEnum
{A basis B of O such that the Gram matrix for the norminner product w.r.t. B is in dominant diagonal form.}
  return B where _, B:= ReducedGramMatrix(O : Canonical:= Canonical);
end intrinsic;


////////////////////////////////////////////////////////////////////////
//                      Some Basis Reduction                          //
////////////////////////////////////////////////////////////////////////

function LLLSeq(B)
   // {An LLL reduced basis of the sublattice generated by B.}
   V := Universe(B);
   if Category(V) eq Lat then
      return Basis(LLL(sub< V | B >));
   elif Category(V) in { ModTupFld, ModTupRng } then
      N := LLL( Matrix(B) );
      return [ N[i] : i in [1..Rank(N)] ];
   end if;
   error if false, "Invalid universe of argument";
end function;

function LLLAlgQuat(S)
    K := Universe(S);
    error if not Type(BaseRing(K)) eq FldRat,
       "Basis reduction valid only over the integers";
    if IsDefinite(K) then
	L := LatticeWithGram( MatrixAlgebra(BaseField(K),4) !
                 [ Trace(x*Conjugate(y)) : x, y in Basis(K) ] );
        T := &cat[ Eltseq(x) : x in S ];
	n := LCM([ Denominator(a) : a in T ]);
	M := LLL(sub< L | Matrix(4,[ Integers() | n*a : a in T ]) >);
	return [ (K!Eltseq(B[i]))/n : i in [1..4] ] where B := Basis(M);
    else
	V := RSpace(Integers(),4);
	T := &cat[ Eltseq(x) : x in S ];
	n := LCM([ Denominator(a) : a in T ]);
	M := Matrix(4,[ Integers() | n*a : a in T ]);
	U := sub< V | [ M[i] : i in [1..Nrows(M)] ] >;
	one := V![n,0,0,0];
	if one in U and GCD(Coordinates(U,one)) eq 1 then
	    W, pi := quo< U | one >;
	    B := [ one ] cat [ v@@pi : v in Basis(W) ];
	else
	    B := Basis(U);
	end if;
	return [ (K!Eltseq(B[i]))/n : i in [1..Rank(U)] ];
    end if;
end function;

////////////////////////////////////////////////////////////////////////
//                                                                    //
//                     Ideal and Order Operations                     //
//                                                                    //
////////////////////////////////////////////////////////////////////////

intrinsic LeftIdeal(A::AlgQuatOrd,S::SeqEnum) -> AlgQuatOrdIdl
   {Left ideal of A with generator sequence S.}

   K := Algebra(A);
   U := Universe(S); 
   if U cmpeq BaseRing(A) or U cmpeq BaseField(K) then
      S := [ K!x : x in S ];
   else
      require Type(U) in {AlgQuatOrd,AlgQuat}:
        "Incompatible ring and sequence universe.";
      ok, S:= CanChangeUniverse(S, K);
      require ok: "Incompatible ring and sequence universe.";
   end if;
   return lideal< A | S >;
end intrinsic;

intrinsic RightIdeal(A::AlgQuatOrd,S::SeqEnum) -> AlgQuatOrdIdl
   {Right ideal of A with generator sequence S.}

   K := Algebra(A);
   U := Universe(S); 
   if U cmpeq BaseRing(A) or U cmpeq BaseField(K) then
      S := [ K!x : x in S ];
   else
      require Type(U) in {AlgQuatOrd,AlgQuat}:
        "Incompatible ring and sequence universe.";
      ok, S:= CanChangeUniverse(S, K);
      require ok: "Incompatible ring and sequence universe.";
   end if;
   return rideal< A | S >;
end intrinsic;

intrinsic PrimeIdeal(A::AlgQuatOrd,p::RngElt) -> AlgQuatOrdIdl
   {The unique two-sided ideal over p.}
   ok, p:= IsCoercible(BaseRing(A), p);
   require ok and IsPrime(p): "Argument 2 must be a prime in the base ring of the first argument.";
   v:= Valuation(Discriminant(A), p);
   if v eq 1 then
      return ideal< A | [ A ! p ] cat [ x*y - y*x : x,y  in Basis(A) ]>;
   else
      // There is no proper twosided ideal between pA and A.
      return ideal< A | p >;
   end if;
end intrinsic;

intrinsic CommutatorIdeal(A::AlgQuatOrd) -> AlgQuatOrdIdl
   {The ideal of A generated by elements of the form x*y - y*x.}
   return ideal<A | [x*y - y*x : x, y in Basis(A)]>;
end intrinsic;

////////////////////////////////////////////////////////////////////////
//                                                                    //
//                      Units and Unit Groups                         //
//                                                                    //
////////////////////////////////////////////////////////////////////////

intrinsic Units(S::AlgQuatOrd[RngInt]) -> SeqEnum
   {The units in the quaternion order S over the integers.}
   K := QuaternionAlgebra(S);
   require IsDefinite(K) : "Quaternion algebra must be definite.";
   if K!1 notin S then return [ S | ]; end if;
   X := ShortestVectors(LatticeWithGram(GramMatrix(S)));
   U := [ u * S!Eltseq(v) : u in [1,-1], v in X ];   	

   // I guess the code below is not needed anymore
   // since the unit group code uses its own ordering of the units.
   // So we could just return U; here?

   ords := [ #{ u^j : j in [0..5] } : u in U ];
   if #U le 6 then // cyclic group
       i := Index(ords,#U);
       U := [ (-1)^t*U[i]^j : t in [0,1], j in [0..(#U div 2) -1] ];
   elif #U eq 8 then
       C4 := {@ {U[i],-U[i]} : i in [1..8] | ords[i] eq 4 @};
       U := [S!1,S!-1] cat &cat[ [u,-u] where u := Rep(c) : c in C4 ];
   elif #U eq 12 then
       i := Index(ords,4); j := Index(ords,3);
       U := [ (-1)^t*U[i]^n*U[j]^m : t in [0..1], n in [0..1], m in [0..2] ];
   elif #U eq 24 then
       i := Index(ords,3);
       C4 := {@ {U[i],-U[i]} : i in [1..24] | ords[i] eq 4 @};
       U4 := [S!1,S!-1] cat &cat[ [u,-u] where u := Rep(c) : c in C4 ];
       U := [ u*U[i]^j : u in U4, j in [0..2] ];
   end if;
   return U;
end intrinsic;

/*
function RightRegularRepresentation(U,X)
    G := Sym(#U);
    gens := [ G![ Index(U,x*u) : x in U ] : u in U ];
    if #X eq 1 then
	H := sub< G | gens >;
    else
	subgens := [ G![ Index(U,x*u) : x in U ] : u in X ];
	H := sub< G | gens >;
	K := sub< G | subgens >;
	m := RegularRepresentation(H,K);
	gens := [ m(g) : g in H ];
	H := Codomain(m);
    end if;
    iso := [ <gens[i],U[i]> : i in [1..#U] ];
    return H, map< H -> U | iso >;
end function;

intrinsic UnitGroup(S::AlgQuatOrd[RngInt]) -> GrpPerm, Map
{A permutation group G isomorphic to the unitgroup of a definite
 quaternion order S over the integers.
 The second return value is a map G -> S^*.}
   K := QuaternionAlgebra(S);
   require IsDefinite(K) : "Quaternion algebra must be definite.";
   require K!1 in S : "Argument must be a quaternion order.";
   U := Units(S);
   if #U ne 24 then
       X := [ U[1] ];
   else
       X := [ U[1], U[9], U[17] ];
   end if;
   // print X;
   return RightRegularRepresentation(U,X);
end intrinsic;
*/

function RightRegularRepresentation(U,gens,K)
    G := Sym(#U);
    perms := [ G | [ Index(U,x*u) : x in U ] : u in U ];
    H := sub< G | perms[gens] >;
    if not IsEmpty(K) then
        K := sub< H | perms[K] >;
        m := RegularRepresentation(H,K);
        perms:= perms @ m;
        H := Codomain(m);
    end if;
    assert #H eq #U;
    return H, map< H -> U | h:-> U[Index(perms, h)], u:-> perms[Index(U,u)] >;
end function;

function findtraces(U, t)
  Result:= [];
  for i in [1..#U] do
    idx:= Index(t, Trace(U[i]));
    if idx ne 0 then
      Undefine(~t, idx);
      Result[idx]:= i;
      if IsEmpty(t) then return Result; end if;
    end if;
  end for;
  error "Could not find the guessed traces";
end function;

// We find one or two generators of the unit group
// by looking at some traces.
// In case of SL(2,3), we take its faithful representation
// on the cosets of any cyclic subgroup of order 3.
intrinsic UnitGroup(O::AlgQuatOrd[RngInt] : ModScalars:= false) -> GrpPerm, Map
{ A permutation group G isomorphic to the unit group of a
  definite quaternion order O over the integers.
  The second return value is a map G -> O^*.}

  if not assigned(O`UnitMap) then
    require IsDefinite(Algebra(O)) : "Quaternion algebra must be definite.";
    S := ShortestVectors(LatticeWithGram(GramMatrix(O)));
    // In the D4 case, the code relies on the fact that u and -u
    // are in distinct halfs of the set U whenever u has order 4!!!
    U := {@ O | Eltseq(s) : s in S @};
    U join:= {@ -u: u in U @};

    traces:= case< #U |
            2: [  -2],          // cyclic
            4: [   0],          //  "
            6: [   1],          //  "
            8: [ 0,0],          // D4
      default: [-1,0] >;        // D6 or SL(2,3)

    gens:= findtraces(U, traces);
    K:= #U eq 24 select [gens[1]] else [];
    _, O`UnitMap:= RightRegularRepresentation(U, gens, K);
  end if;
  h:= O`UnitMap; G:= Domain(h);
  if ModScalars then
    G, hh:= quo< G | (O!-1) @@ h>;
    h:= hh^-1 * h;
  end if;
  return G, h;
end intrinsic;


////////////////////////////////////////////////////////////////////////
//                                                                    //
//         Maximal Orders over F_q[X] and pMaximalOrder               //
//                                                                    //
////////////////////////////////////////////////////////////////////////

function enlarge_order(O, maximal: prime:=0)
  if prime eq 0 then
    primes:= FactoredDiscriminant(O);
  else
    v:= Valuation(Discriminant(O), prime);
    primes:= v eq 0 select [] else [ <prime, v> ];
  end if;
  if IsEmpty(primes) then return O; end if;

  _, h:= RegularRepresentation(Algebra(O));
  R:= BaseRing(O);

  for x in primes do
    p:= x[1];
    e:= x[2];
    k, hk:= ResidueClassField(p);
    while e ge 2 do
      BM:= BasisMatrix(O);
      B:= Basis(O);
      AA:= AssociativeAlgebra< k, 4 | [ [x @ hk : x in Eltseq(BM * (b @ h) * BI)] :  b in B ] : Check:= false > where BI:= BM^-1;
      J:= JacobsonRadical(AA);
      M:= ideal< O | [O ! p] cat [ &+[(c[i] @@ hk) * B[i] : i in [1..4] | c[i] ne 0] where c:= Coordinates(AA, j): j in Basis(J) ] >;
      O:= RightOrder(M);
      e:= Valuation(Discriminant(O), p);
    end while;

    // We are now hereditary at p. Shall and can we enlarge once more?
    if maximal and e eq 1 and HilbertSymbol(Algebra(O), p) eq 1 then
      _, a, _, _ := get_coords(O, p);
      O:= QuaternionOrder(Append(Basis(O), 1/p*a));
      assert Valuation(Discriminant(O), p) eq 0;
    end if;
  end for;

  return O;
end function;

/*
// The standard way of getting the head order, a uniquely determined hereditary order containing O.
// See Reiner, Maximal orders. Works for all (semi-)simple algebras
intrinsic TameOrder(O::AlgQuatOrd) -> AlgQuatOrd
{Computes an order containing O whose reduced discriminant is squarefree.}
  if assigned O`IsMaximal and O`IsMaximal then return O; end if;
  return enlarge_order(O, false);
end intrinsic;
*/

intrinsic pMaximalOrder(O::AlgQuatOrd, p::RngElt) -> AlgQuatOrd
{A p-maximal order containing O.}
  ok, p:= IsCoercible(BaseRing(O), p);
  require ok and IsIrreducible(p) : "The second argument must be an irreducible element of the base ring of O";
  F:= BaseField(Algebra(O));
  require Type(F) eq FldRat or (Characteristic(F) ne 2 and IsFinite(BaseRing(F))) : "base field is not supported";
  OO:= enlarge_order(O, true : prime:= p);
  return OO, Valuation(Discriminant(OO), p);
end intrinsic;
