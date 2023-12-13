///////////////////////////////////////////////////////////////////////////////////////////////
//
//    Dedekind Zeta Exact
//
//    Compute the exact value of the Dedekind Zeta Function at negative integers.
//    Kindly contributed by Eran Assaf's Algebraic modular forms package.
//
///////////////////////////////////////////////////////////////////////////////////////////////

declare attributes FldNum:
  DedekindZetaOne; //

// Working with ideal class groups
intrinsic CGPrimes(I, S, Generators, CoprimeTo, Minimal, Quotient) -> Any
{}
  R:= Order(I);
  if not IsMaximal(R) or not IsAbsoluteOrder(R) then return false, "The order must be absolute and maximal"; end if;
  r1, r2:= Signature(NumberField(R));
  if not IsEmpty(S) then
    T:= Type(Universe(S));
    if T eq PlcNum then
      X:= S; S:= [];
      for s in X do
        ok, i:= IsInfinite(s);
        if not ok or not IsReal(s) then return false, "The places must be real"; end if;
        Append(~S, i);
      end for;
    elif (T eq RngInt) and Minimum(S) ge 1 and Maximum(S) le r1 then
      ;
    elif (Universe(S) cmpeq PowerStructure(Infty)) and AbsoluteDegree(R) eq 1 then
      S:= [1];
    else
      return false, "Wrong infinite places";
    end if;
    S:= Sort(S);
  end if;
  if not IsIntegral(I) then
    return false, "The ray is not integral";
  end if;

  if Type(Quotient) eq SetEnum then Quotient:= Setseq(Quotient); end if;
  if #Quotient ne 0 then
    T:= Type(Quotient[1]);
    if T in {RngIntElt, FldRatElt} then
      Quotient:= [ ideal< R | x> : x in Quotient ];
    elif T eq RngInt then
      Quotient:= [ ideal< R | Generator(x) > : x in Quotient ];
    elif not ISA(T, RngOrdFracIdl) or Order(Quotient[1]) cmpne R then
      return false, "Incompatible user defined generators";
    end if;
    if exists{ u: u in Quotient | not IsOne(I+u) } then
      return false, "The user defined generators must be comprime to the ray";
    end if;
  end if;

  if CoprimeTo cmpne 1 then
    if ISA(Type(CoprimeTo), RngElt) then
      ok, CoprimeTo:= IsCoercible(FieldOfFractions(R), CoprimeTo);
      if not ok then return ok, "IscoprimeTo must be an ideal or field element"; end if;
    end if;
  end if;

  L:= [ PowerIdeal(R) | ];
  C, h:= RayClassGroup(I, S);
  C0:= sub< C | {u @@ h : u in Quotient} >;
  if #C0 ne 1 then
    C, hh:= quo< C | C0 >;
    h:= hh^-1 * h;
  end if;

  if Generators then
    n:= #AbelianInvariants(C);  // We will end up with this number of gens.
    U:= sub< C | >;
    p:= 1; i:= 1; D:= [];
    while n ne 0 do
      if i ge #D then p:= NextPrime(p); D:= Decomposition(R, p); i:= 1; end if;
      if (CoprimeTo cmpeq 1 or Valuation( CoprimeTo, D[i,1] ) eq 0) and IsOne(I+D[i,1]) then
        g:= D[i,1] @@ h;
        if g notin U then
          nn:= #AbelianInvariants( quo< C | U, g > );
          if nn ne n then
            assert nn eq n-1;
            n:= nn;
            Append(~L, D[i,1]);
            U:= sub< C | U, g >;
          end if;
        end if;
      end if;
      i +:= 1;
    end while;
  else
    U:= {@ @};
    p:= 1; i:= 1; D:= [];
    while #U ne #C do
      if i ge #D then p:= NextPrime(p); D:= Decomposition(R, p); i:= 1; end if;
      if (CoprimeTo cmpeq 1 or Valuation( CoprimeTo, D[i,1] ) eq 0) and IsOne(I+D[i,1]) then
        g:= D[i,1] @@ h;
        if g notin U then
          Append(~L, D[i,1]);
          Include(~U, g);
        end if;
      end if;
      i +:= 1;
    end while;

    if Minimal then
      B:= Max([Norm(p): p in L]);
      P:= PrimesUpTo(B-1, NumberField(R): coprime_to:= CoprimeTo * I);

      for p in P do
        g:= p @@ h;
        i:= Index(U, g);
        if Norm(p) le Norm(L[i]) then
          L[i]:= p;
        end if;
      end for;
    end if;
  end if;

  Norms:= [ Norm(p): p in L ];
  ParallelSort(~Norms, ~L);

  return true, L;
end intrinsic;

intrinsic ClassGroupPrimeIdealGenerators(I, S : CoprimeTo:= 1, Quotient:= []) -> Any
{Returns prime ideals that generate the ray class group of I and the infinite places in S.}
 
  ok, L:= CGPrimes(I, S, true, CoprimeTo, true, Quotient);
  if not ok then
      error L;
  end if;
  return L;
end intrinsic;

intrinsic ExtensionToHeckeCharacter(E)-> Any
{}
  assert Degree(E) eq 2;
  K:= BaseField(E);
  //  if not IsAbsoluteField(K) then K:= AbsoluteField(K); end if;
  RE:= Integers(E);

  S:= [];
  for i in RealPlaces(K) do
    if #Decomposition(E, i) ne 2 then
      if Type(i) eq Infty then
        idx:= 1;
      else
        ok, idx:= IsInfinite(i); assert ok;
      end if;
      Append(~S, idx);
    end if;
  end for;
  S:= Sort(S);

  //  S:= [1..Degree(K)];
  bad:= Type(K) eq FldRat;
  if bad then
    DE:= Integers( QNF() ) * Discriminant(RE);
  else
    DE:= Discriminant(RE);
  end if;
  P:= ClassGroupPrimeIdealGenerators(DE, S);
  T:= < < p, IsSplit(bad select Minimum(p) else p, RE) select 1 else -1> : p in P >;
  h:= HeckeCharacter(DE, S, T);
  assert IsPrimitive(h);
  return h;
end intrinsic;


function myEval(K, z, Relative)
  if IsOdd(z) then
    k:= 1-z;
    if Type(K) eq FldRat then
      return BernoulliNumber(k)/-k;
    elif Degree(K) eq 2 then
      d:= Discriminant(Integers(K));
      if d gt 1 then
        return BernoulliNumber(k) * BernoulliNumber(k, KroneckerCharacter(d, Rationals())) / k^2;
      end if;
    end if;
  end if;

  if Relative then
    H:= ExtensionToHeckeCharacter(K);
    L:= LSeries(H);
    //    F:= BaseField(K);
    //    K:= OptimizedRepresentation(AbsoluteField(K));
    //    L:= LSeries(K : Method:= Degree(F) ge 5 select "Direct" else "Default") / LSeries(F);
  else
    print "ben";
    L:= LSeries(K);
  end if;

  i:= 0;
  repeat
    if i ge 1 then
      LSetPrecision(L, 40 + i*20);
      "increasing precision", i;
    end if;
    x:= Evaluate(L, z);
    if Type(x) eq FldComElt and Im(x) le 10^-20 then x:= Re(x); end if;
    X:= Type(x) eq FldReElt select { BestApproximation(x, 10^i) : i in [12, 14, 16, 18] } else [];
    i +:= 1;
  until #X eq 1;
  X:= Rep(X);

  //  if Relative then
  //    assert Abs(Real(Evaluate(LSeries(H), z)) - X) le 10^-10;
  //  end if;
  return X;
end function;


intrinsic DedekindZetaExact(K::FldNum, z::RngIntElt : Relative := false) -> Any
{Return the exact value of `DedekindZeta(K)` at the negative integer `z`.
The keyword `Relative` can be set to true. I have no idea what this does.}
    require ((Relative and z eq 0) or z lt 0): "The argument must be a negative integer";
    if z eq -1 and assigned K`DedekindZetaOne then
      return K`DedekindZetaOne;
    end if;
    val := myEval(K, z, Relative);
    if z eq -1 then
      K`DedekindZetaOne := val;
    end if;
    return val;
end intrinsic;


// For when we need other values of the Dedekind zeta function, which is never...
// This intrinsic is not used in the rest of the package.
intrinsic DedekindZeta(K::FldNum) -> LSer
{Return the Dedekind Zeta function of the number field K as an L-series.}
    M := MaximalOrder(K);
    r1,r2 := Signature(K);
    gamma := [0: k in [1..r1+r2]] cat [1: k in [1..r2]];
    disc := Abs(Discriminant(M));
    P<x> := PolynomialRing(Integers());
    cf := func<p,d|&*[1-x^Degree(k[1]): k in Decomposition(M,p)]>;
    h := #ClassGroup(M);
    reg := Regulator(K);
    mu := #TorsionSubgroup(UnitGroup(M));
    return LSeries(1, gamma, disc, cf: Parent:=K, Sign:=1, Poles:=[1],
				       Residues := [-2^(r1+r2)*Pi(RealField())^(r2/2)*reg*h/mu]);
end intrinsic;


// For when we compute the value of the Dedekind zeta at 2, which SHOULD be never, since
// Trace.m actually applies a functional equation and just uses Zeta(K, -1).
intrinsic DedekindZetatwo(M::ModFrmHilDGRng) -> Any
{}
  if not assigned M`DedekindZetatwo then
    F := BaseField(M);
    M`DedekindZetatwo := Evaluate(LSeries(F : Precision := 100),2); // Fixed Precision 100.
  end if;
  return M`DedekindZetatwo;
end intrinsic;
