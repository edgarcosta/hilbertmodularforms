freeze;

//////////////////////////////////////////////////////////////////////////////
//
// Ramification in Quaternion Algebras over Number Fields
// February 2006, John Voight
//
// Last modified Nov 2011, SRD
//
//////////////////////////////////////////////////////////////////////////////

//-------------
//
// Algorithms for real places.
//
//-------------

// Stupid map, maps {-1,1} -> {1,0}
function h(x);
  if x eq -1 then
    return GF(2) ! 1;
  elif x eq 1 or x eq 0 then
    return GF(2) ! 0;
  else
    print x;
    error "Bad h!";
  end if;
end function;

// Returns the sequence of signs of the real embeddings of s.
function RealValuations(V, s);
  F := Parent(s);
  if not ISA(Type(F), FldNum) then
    F := NumberField(Parent(s));
    s := F ! s;
  end if;
  return [ h(Sign(Evaluate(s,v))) : v in V];  
end function;

intrinsic RealEmbeddings(s::RngOrdElt) -> SeqEnum
  {Returns the sequence of real embeddings of s.}

  return [Real(Evaluate(s,v)) : v in RealPlaces(NumberField(Parent(s)))];
end intrinsic;

intrinsic RealEmbeddings(s::FldAlgElt) -> SeqEnum
  {Returns the sequence of real embeddings of s.}

  return [Real(Evaluate(s,v)) : v in RealPlaces(Parent(s))];
end intrinsic;

intrinsic RealSigns(s::RngOrdElt) -> SeqEnum
  {Returns the sequence of signs of the real embeddings of s.}

  return RealSigns(s/1);
end intrinsic;

intrinsic RealSigns(s::FldAlgElt : real_places:=0) -> SeqEnum
  {Returns the sequence of signs of the real embeddings of s.}

  V := (real_places cmpne 0) select real_places 
                              else  RealPlaces(Parent(s));
  return [Integers()| (-1)^(Integers()!r) : r in RealValuations(V, s)];
end intrinsic;

function Convergent(s,i);
  m := Convergents(s[1..i]);
  if m[1,2] eq 0 then 
    return m[1,1];
  else
    return m[1,1]/m[1,2];
  end if;
end function;

intrinsic IsTotallyPositive(x::RngOrdElt) -> BoolElt
  {Returns true iff x is totally positive.}

  K := NumberField(Parent(x));
  require IsTotallyReal(K) : "x must lie in a totally real field";

  return forall{v : v in InfinitePlaces(K) | Real(Evaluate(x,v)) gt 0}; 
end intrinsic;

intrinsic IsTotallyPositive(x::FldAlgElt) -> BoolElt
  {"}//"

  K := NumberField(Parent(x));
  require IsTotallyReal(K) : "x must lie in a totally real field";

  return forall{v : v in InfinitePlaces(K) | Real(Evaluate(x,v)) gt 0}; 
end intrinsic;

function RationalBetween(x,y)
  d:= y-x;
  assert d gt 0;
  l:= Max(0, Ceiling(-Log(10, d))) + 1;
  r:= Round( (x+y)/2 * 10^l ) / 10^l;
  assert x lt r and r lt y;
  return r;
end function;

intrinsic RealWeakApproximation(V::SeqEnum[PlcNumElt], S::SeqEnum[RngIntElt]
                                : UnitOnly:=false, CoprimeTo := 1, UnitRealValuations:=<>, Al:= "CRT")
       -> RngOrdElt
  {Returns a element with valuation of sign S[i] at the place V[i],
   coprime to CoprimeTo if provided.}

  require #V eq #S : "The arguments must be sequences of the same length";
  if #V eq 0 then return 1; end if;
  require forall{v : v in V | IsReal(v) } : "The places must be real";
  if UnitOnly then Al:= "Small"; end if;
  require Al in {"CRT", "Small"}: "Al must be either \"CRT\" or \"Small\"";

  Z_F := Integers( NumberField(V[1]) );

  // Trivial cases +1 or -1
  SS := Seqset(S);
  if SS eq {1} then
    return Z_F ! 1;
  elif SS eq {-1} then
    return Z_F ! -1;
  end if;
  require SS eq {-1, 1}: "The sign vector can only contain -1 and 1";

  if ISA(Type(CoprimeTo), RngElt) then
    CoprimeTo:= CoprimeTo*Z_F;
  end if;
  require ISA(Type(CoprimeTo), RngOrdIdl) and Order(CoprimeTo) cmpeq Z_F: "Invalid optional parameter CoprimeTo";

  if Al eq "CRT" then
    Idx:= [ i where _, i:= IsInfinite(v) : v in V ];
    ParallelSort(~Idx, ~S);
    return CRT(CoprimeTo, Idx, Z_F ! 1, S);
  end if;

  // Maybe we move the unit stuff into some other intrinsic and cache the resulting matrix?
  W := VectorSpace(GF(2), #V);
  b := W ! [ s eq -1 select 1 else 0 : s in S ];

  if #UnitRealValuations eq 0 then
    U, fU := UnitGroup(Z_F: Al:= "ClassGroup"); Uvals:= [];
  else
    U, fU, Uvals := Explode(UnitRealValuations);
  end if;

  found := false;
  Basis := [ ];
  Signs := [ ];
  S:= sub< W | >;
  for i in [1..Ngens(U)] do
    u:= fU(U.i);
    s:= W ! (IsDefined(Uvals, i) select Uvals[i] else RealValuations(V, u));
    if s in S then continue; end if;
    Append(~Basis, u);
    Append(~Signs, s);
    S:= sub< W | S, s >;
    if b in S then found:= true; break; end if;
  end for;

  // There is no unit solution.
  if UnitOnly and not found then
    return false;
  end if;

  // enlarge by "small" elements.
  if not found then
    Cl, h:= ClassGroup(Z_F);
    trivial := Minimum(CoprimeTo) eq 1;
    Classes := {@ c : c in Cl @};
    Ideals  := [ ];
    for i in [1..#Classes] do
      I:= Classes[i] @ h;
      if trivial or Minimum(I + CoprimeTo) eq 1 then Ideals[i]:= I; end if;
    end for;
    full:= #Ideals eq #Classes and IsComplete(Ideals);

    p:= 1;
    while not found do
      p:= NextPrime(p);
      for d in Decomposition(Z_F, p) do
        if not trivial and Minimum(d[1] + CoprimeTo) ne 1 then continue; end if;
        c:= d[1] @@ h;
        if not full then
          for i in [1..Order(c)-1] do
            idx:= Index(Classes, i*c);
            if not IsDefined(Ideals, idx) then Ideals[idx]:= d[1]^i; end if;
          end for;
          full:= #Ideals eq #Classes and IsComplete(Ideals);
        end if;
        ok, x:= IsPrincipal(Ideals[Index(Classes, -c)] * d[1]); assert ok;
        s:= W ! RealValuations(V, x);
        if s in S then continue; end if;
        Append(~Basis, x);
        Append(~Signs, s);
        S:= sub< W | S, s >;
        if b in S then found:= true; break d; end if;
      end for;
    end while;
  end if;

  ok, x := IsConsistent(Matrix(Signs), b); assert ok;
  alpha := &*[ Basis[i] : i in [1..#Basis] | x[i] ne 0 ];
  assert W ! RealValuations(V, alpha) eq b;
  return alpha;
end intrinsic;

//-------------
//
// Legendre symbol.
//
//-------------

intrinsic RandomUnit(R::RngOrdRes) -> RngOrdResElt
  {Returns a random unit of R.}

  Rstar, f := UnitGroup(R);
  return f(Random(Rstar));
end intrinsic;

intrinsic LegendreSymbol(a::RngOrdElt, p::RngOrdIdl) -> RngIntElt
  {Returns the Legendre symbol (a/p).}

  Z_F := Parent(a);
  require IsPrime(p) and Valuation(ideal<Z_F|2>,p) eq 0 :
    "p must be an odd prime ideal";

  Q := quo<Z_F | p>;
  x := (Q ! a)^((AbsoluteNorm(p)-1) div 2);
  if x eq (Q ! 1) then
    return 1;
  elif x eq (Q ! 0) then
    return 0;
  else
    return -1;
  end if;
end intrinsic;

//-------------
//
// Constructor for quaternion algebras with specified ramification.
//
//-------------

intrinsic QuaternionAlgebra(S::SeqEnum[PlcNumElt] : Optimized := true) -> AlgQuat[FldNum]
  {Returns the quaternion algebra which is ramified only at the places in S.}
  
  require IsEven(#S): "The number of ramified places must be even.";
  F := NumberField(Universe(S));  
  Soo := [Universe(S) | v : v in S | IsInfinite(v)];
  require &and[ IsReal(v) : v in Soo ] : "Non-real infinite places cannot be ramified!";
  I := &*[ Parent(Ideal(Divisor(F!1))) | Ideal(v) : v in S | v notin Soo];
  return QuaternionAlgebra(I, Soo : Optimized := Optimized);
end intrinsic;

intrinsic QuaternionAlgebra(I::RngOrdIdl : Optimized := true) -> AlgQuat[FldNum]
  {Returns the quaternion algebra which is ramified only at the primes dividing I.}

  O := Order(I);
  F := FieldOfFractions(O);
  Foo := InfinitePlaces(F);
  return QuaternionAlgebra(I, [Universe(Foo)| ] : Optimized := Optimized);
end intrinsic;

intrinsic QuaternionAlgebra(I::RngOrdIdl, S::SeqEnum[PlcNumElt] : Optimized := true) 
     -> AlgQuat[FldNum]
  {Returns the quaternion algebra which is ramified only at the primes dividing
   I and at the real places specified by S.  By default, an optimized algebra
   (having small a,b) will be computed, which includes the computation of a maximal
   order; to avoid this, set Optimized to false.}

  Z_F := Order(I);
  F := FieldOfFractions(Z_F);

  P := Factorization(I);
  require IsEven(#P + #S): "The number of ramified places must be even.";

  // For the first generator, take an element with valuation 1 at the primes
  // dividing I;
  if #P eq 0 then
    a := F!1;
  else
    a := WeakApproximation([p[1] : p in P], [1 : i in [1..#P]]);
  end if;
  // We take care of the real places here.  For each v in S, we need v(a) < 0,
  // and for each v not in S, we need v(a) > 0.
  // First, try to multiply a by a unit to achieve this;
  T := [];
  if #S ne 0 then 
    Foo := RealPlaces(NumberField(S[1]));
  else
    Foo := RealPlaces(F);
  end if;

  for v in Foo do
    if (v in S and Evaluate(a,v) gt 0) or (v notin S and Evaluate(a,v) lt 0) then
      Append(~T, -1);
    else
      Append(~T, 1);
    end if;
  end for;

  u := RealWeakApproximation(Foo, T : CoprimeTo := I);
  a *:= u;
  a := Z_F!a;

  a0 := a;

  if #P eq 0 and forall{pp : pp in Factorization(2*a*Z_F) | HilbertSymbol(F!-1,F!a,pp[1]) eq 1} and IsUnit(Z_F!u) then
    b := a;
    a := -1;
  else
  repeat
    // Now we need to find b with the following properties:
    // - For each prime p which divides I, we need (b/p) = -1;
    // - For each prime p which divides (a) but which does not divide I,
    //   we need (b/p) = 1; 
    // - For each even prime p which does not divide (a), we need (b/p) = 1;
    // - For each v in S, we need v(b) < 0;
    // - b generates a (principal) prime ideal.
    // Already in the case of the integers, we would need to find nonsquares, 
    // for which deterministic algorithms are dodgy, so we content ourselves
    // with a probablistic approach.
    Ps := [<p[1],1,false> : p in P | Valuation(Z_F!2, p[1]) eq 0] cat
          [<p[1],2*RamificationIndex(p[1])+1,false> : p in P | 
           Valuation(Z_F!2, p[1]) ne 0];
    if #Ps eq 0 then
      ps2 := Factorization(ideal<Z_F | a>);
    else
      ps2 := &*[p[1]^p[2] : p in Ps];
      ps2 := Factorization(ideal<Z_F | a>/(ideal<Z_F | a> + ps2));
    end if;
    Ps cat:= [<p[1],1,true> : p in ps2 | Valuation(Z_F!2, p[1]) eq 0] cat 
             [<p[1],2*RamificationIndex(p[1])+1,true> : p in ps2 | 
              Valuation(Z_F!2, p[1]) ne 0] cat
             [<p[1],2*RamificationIndex(p[1])+1,true> : p in Decomposition(Z_F,2) | 
              Valuation(ideal<Z_F | a>,p[1]) eq 0];
    m := &*[p[1]^p[2] : p in Ps];
    mgen := Generators(m)[#Generators(m)];
    mapPs := <>;
    for p in Ps do
      if p[2] gt 1 then
        Append(~mapPs, map<Z_F -> Parent(true) | x :-> HilbertSymbol(F!a,F!x,p[1]) eq 1>);
      else
        Append(~mapPs, map<Z_F -> Parent(true) | x :-> LegendreSymbol(x,p[1]) eq 1>);
      end if;
    end for;

    cnt := 0;
    Z_Fm, mZ_Fm := quo<Z_F | m>;
    Nm := Norm(m);
    n := Degree(F);
    bbnd := Max(20, Sqrt(Norm(m)));
    bbnd := Min(bbnd, 10^4); // SRD, Dec 2011

    cntbigloop := 0;
    repeat
      // Strategy is to pick a random b modulo m, multiply by an appropriate
      // unit to get the real valuations correct, then test prime-by-prime to
      // see if it fulfills the conditions above.
      cntbigloop +:= 1;
      cnt +:= 1;
      repeat
        b := Inverse(mZ_Fm)(mZ_Fm(Z_F ! [Random(Norm(m)) : i in [1..n]]));
      until ideal<Z_F | b> + m eq ideal<Z_F | 1>;

      Sminus := [v : v in Foo | (v in S and Evaluate(F!b,v) gt 0)];
      Splus := [v : v in S | v notin Sminus];

      ub := RealWeakApproximation(Sminus cat Splus, 
                                  [-1 : v in Sminus] cat [1 : v in Splus]);
      b *:= ub;
      i := 1;
      while i le #Ps and mapPs[i](b) eq Ps[i][3] do
        i +:= 1;
      end while;
      passed := i gt #Ps;
      if passed and not (IsPrime(b*Z_F) or IsUnit(b)) then
        // TO DO: choose m1 coprime to b, otherwise this will take a long time
        m1 := Generators(m)[1];
        ubm1 := RealWeakApproximation(Foo, RealSigns(b*m1)); 
        while cnt le bbnd and not (IsPrime(b*Z_F) or IsUnit(b)) do
          b +:= ubm1 * m1;
          cnt +:= 1;
        end while;
      end if;

      // Keep track if there are too many failures, increase the size
      // of the space we're looking in.
      if cnt gt bbnd then
        cnt := 0;
        m *:= 2;
        Z_Fm, mZ_Fm := quo<Z_F | m>;
        passed := false;
      end if;
    until passed or cntbigloop gt 10;

    // Could choose new random a, but nevermind.
  until passed;
  end if;

  K := NumberField(F);
  A := QuaternionAlgebra<K | K!a, K!b>;
  D, Doo := Discriminant(A);
  if (#P eq 0 and D ne ideal<Z_F | 1>) or (#P gt 0 and D ne &*[pp[1] : pp in P]) or
    #Doo ne #S then
    error "Algebra improperly computed, please report!", D, Doo;
  end if;
 
  if not Optimized then
    return A;
  end if;
  O := MaximalOrder(A);

//return OptimizedRepresentation(O);
  return AA where AA is OptimizedRepresentation(O); // don't return the map too --SRD
end intrinsic;

//-------------
//
// Optimized representations.
//
//-------------

intrinsic OptimizedRepresentation(A::AlgQuat) -> AlgQuat, Map
  {Returns a quaternion algebra A' and a map Algebra(O) -> A' such that
   A' = ((a,b)/F) has a,b "small".}

  return OptimizedRepresentation(MaximalOrder(A));
end intrinsic;

intrinsic OptimizedRepresentation(O::AlgAssVOrd) -> AlgQuat, Map
  {"} // "

  require Type(Algebra(O)) eq AlgQuat : "O must be a quaternion order";

  A := Algebra(O);
  F := BaseField(A);

  cnt := 0;
  a,b := StandardForm(A);
  min := Norm(a)^2+Norm(b)^2;
  Ap := A;
  hfinal := hom<A -> A | 1, A.1, A.2, A.3>;
  repeat
    nochange := true;
    if Type(BaseRing(O)) eq RngInt or not IsTotallyReal(F) then
      B := Basis(O);
    else
      B := ReducedBasis(O);
    end if;

    // Try a few small linear combinations
    S := [ b-Trace(b)/2 : b in B | not IsScalar(b)];
    for i := 1 to #S do
      if not IsIntegral(S[i]) then
        S[i] *:= 2;
      end if;
    end for;
    for s,t0 in S do
      if s^2 eq 0 then
        M2F, phi := MatrixRing(A, s);
        smin := Inverse(phi)(2*M2F.1-1);
        tmin := Inverse(phi)(M2F.2);
        break s;     
      end if;
      t := t0-Trace(s*t0)/Trace(s^2)*s;
      d := Denominator(Norm(t));
      t *:= d;
      nst := Norm(Norm(s))^2 + Norm(Norm(t))^2;
      if t ne 0 and nst lt min then
        min := nst;
        smin := s;
        tmin := t;
        nochange := false;
      end if;
    end for;
    cnt +:= 1;

    // print cnt, -Norm(smin), -Norm(tmin);

    if not nochange and Norm(smin)*Norm(tmin) ne 0 then
      Ap := QuaternionAlgebra<F | -Norm(smin), -Norm(tmin)>;
      h := hom<Ap -> A | 1, smin, tmin, smin*tmin>;
      hfinal := h*hfinal;
      O := MaximalOrder(Ap);
      A := Ap;
    end if;
  until nochange or cnt gt 3;  

  // Now use a Legendre-like minimization
  cnt := 0;
  repeat
    nochange := true;
    cnt +:= 1;

    a,b := StandardForm(A);
    bool, asqrt:= IsSquare(a);
    if bool then
      M2F, phi := MatrixRing(A, A.1-asqrt);
      smin := Inverse(phi)(2*M2F.1-1);
      tmin := Inverse(phi)(M2F.2);
    else
      K<alpha> := NumberField(Polynomial([-a,0,1]));
      Z_K := AbsoluteOrder(Integers(K));

      bfact := Factorization((Integers(F)!b)*Integers(F));
      bb := 1*Z_K;
      for bf in bfact do
        Fbb := Factorization(Z_K!!bf[1])[1][1];
        if Degree(ResidueClassField(Fbb)) eq 1 then
          bb *:= Fbb^bf[2];
        end if;
      end for;
      beta := K!LLLBasis(bb^(-1))[1];
      smin := A.1;
      tmin := (Eltseq(beta)[1]*(A!1) + Eltseq(beta)[2]*A.1)*A.2;
    end if;
    assert IsCoercible(Integers(F),Norm(tmin));
    if Norm(Norm(smin))^2 + Norm(Norm(tmin))^2 lt 
       Norm(a)^2 + Norm(b^2) then
      nochange := false;

      Ap := QuaternionAlgebra<F | -Norm(tmin), -Norm(smin)>;
      h := hom<Ap -> A | 1, tmin, smin, tmin*smin>;
      hfinal := h*hfinal;
      O := MaximalOrder(Ap);
      A := Ap;
    end if;
  until nochange or cnt gt 3;

  return Ap, Inverse(hfinal);
end intrinsic;


/*
      // Check if an element is a square in an even p-adic field by checking
      // it up past modulo 4.
      G, f := quo<Z_F | p[1]^(p[2])>;
      GU, fU := UnitGroup(G);
      H, g := quo<GU | [2*GU.i : i in [1..#Generators(GU)]]>;
      h := map<H -> Parent(true) | x :-> x eq H ! 0>;
      Append(~mapPs, f*Inverse(fU)*g*h);
*/
