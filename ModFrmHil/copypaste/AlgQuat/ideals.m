freeze;

////////////////////////////////////////////////////////////////////
//                                                                //  
//                        QUATERNION IDEALS                       //
//                     Last Modified April 2000                   // 
//                          by David Kohel                        // 
//                                                                // 
//////////////////////////////////////////////////////////////////// 

forward CompareOrders, CompareLeftIdeals, CompareGram; 
forward IsogenousIdeals, SplitIsogenousIdeals;

import "../AlgAss/ideals.m" : ColonInternalZ;
import "../AlgAss/enum.m" : RightIdealClassesAndOrders, get_coords;

////////////////////////////////////////////////////////////////////
//                   Auxiliary Random Functions                   //
////////////////////////////////////////////////////////////////////

function RandomElement(A,S)
   return A![ Random(S) : i in [1..4] ];
end function;

////////////////////////////////////////////////////////////////////
//                                                                //
//                       Isogeny Graphs                           //
//                                                                //
////////////////////////////////////////////////////////////////////

intrinsic RightIdealClasses(A::AlgQuatOrd[RngInt] : IsogenyPrime := 1, Support := 0) -> SeqEnum
   {Representatives for the right ideals classes of A.}
   if (IsogenyPrime cmpeq 1 or Support cmpne 0) and IsEichler(A) then
     if Support cmpeq 0 then Support:= []; end if;
     return RightIdealClassesAndOrders(A: Support:= Support);
   end if;
   return [ Conjugate(I) : I in LeftIdealClasses(A : IsogenyPrime := IsogenyPrime, Support:= Support) ];
end intrinsic;

intrinsic RightIdealClasses(O::AlgQuatOrd[RngUPol] : Support:= []) -> SeqEnum
{"} // "
  A:= Algebra(O);
  F:= BaseField(A);
  require IsOdd(Characteristic(F)) and IsFinite(BaseRing(F)) : "base field is not supported";
  require IsMaximalAtRamifiedPrimes(O) : "The order must be maximal at all ramified primes";
  if IsIndefinite(A) then return [ rideal< O | 1 > ]; end if; 
  RC:= RightIdealClassesAndOrders(O : Support:= Support);
  return RC;
end intrinsic;

function CharacterVector(prms,p)
   return Vector([ GF(2) | 
      (1 - KroneckerSymbol(p,q)) div 2 : q in prms ]);
end function;

intrinsic LeftIdealClasses(A::AlgQuatOrd[RngInt] : IsogenyPrime := 1, Support := 0 ) -> SeqEnum
   {Representatives for the left ideals classes of A.}
   /*
   Consider additional parameters: 
      IsogenyPrimeSequence, IdealSequence, GeneraSequences, etc.
   */

   K := QuaternionAlgebra(A);
   if IsIndefinite(K) then
     return [ ideal< A | 1 > ]; end if;

   if (IsogenyPrime cmpeq 1 or Support cmpne 0) and IsEichler(A) then
     // call the Voight/Kirschmer/Donnelly routine, which handles support
     if Support cmpeq 0 then Support:= []; end if;
     idls:= RightIdealClassesAndOrders(A : Support:= Support);
     return [ Conjugate(I) : I in idls ];
   end if;

   if assigned A`LeftIdealBases then
      return [ lideal< A | [ A!x : x in B ] > : B in A`LeftIdealBases ];
   end if;

   N := Discriminant(A);
   Q := RamifiedPrimes(K);
   CharacterPrimes := [ q : q in Q | q ne 2 and Valuation(N,q) gt 1 ];

   if IsogenyPrime ne 1 then
      require IsPrime(IsogenyPrime) : 
	  "IsogenyPrime parameter must be prime.";
      require N mod IsogenyPrime ne 0 :
         "IsogenyPrime parameter must be coprime to " * 
         "the discriminant of the argument.";
      p := IsogenyPrime; 
      CharacterPrimes := [ Integers() | ];
   else
      p := 2; 
      while N mod p eq 0 do 
         p := NextPrime(p); 
      end while;
   end if;

   if #CharacterPrimes eq 0 then
      Idls := IsogenousIdeals(A,p);
   else
      /*
      Currently the SplitIsogeny function computes the principal 
      left ideal class (that of A) and one coset, that generated 
      by odd p-power isogenies.  Therefore we have to construct 
      enough primes to represent all classes, not just to generate
      all classes.  
      Note that this incurs a significant overhead, not just in 
      the number of primes, but that each time the principal class 
      is recomputed. 
      A much more efficient algorithm would be to compute only the
      principal class and then to construct the rest by multiplying 
      on the left by the 2-sided ideals for A.
      This algorithm suffers two problems (1) (ALGORITHMIC) a 
      verifiable algorithm for the 2-sided ideal classes, and 
      (2) (THEORETICAL) some accounting for the fact that due to 
      extra automorphisms the idelic generators for 2-sided ideals 
      may have different kernels on different kernels under different 
      left and right orders.  Provided that the primes act by 
      characters which change the genus, then the action of the 
      elementary 2-abelian group is free, and (2) is not an 
      obstruction.  
      */  
      r := #CharacterPrimes;
      V := VectorSpace(GF(2),r);
      CharacterClasses := [ v : v in VectorSpace(GF(2),r) | v ne 0 ];
      IsogenyPrimes := [ Integers() | ];
      // U := sub< V | 0 >;
      // while Dimension(U) lt r do
      while #CharacterClasses gt 0 do
         v := CharacterVector(CharacterPrimes,p);
         while N mod p eq 0 or v notin CharacterClasses do
            p := NextPrime(p);
            v := CharacterVector(CharacterPrimes,p);
         end while;
         Include(~IsogenyPrimes,p);
         Exclude(~CharacterClasses,v);
      end while;
      if GetVerbose("Quaternion") ge 2 then
         print "Building p-isogenies for p in", IsogenyPrimes; 
      end if;
      IdealGenera := [ ];
      for p in IsogenyPrimes do 
         pGenera := SplitIsogenousIdeals(A,[1*A],p); 
         if Index(IsogenyPrimes,p) eq 1 then
            IdealGenera := pGenera;
         else 
            Append(~IdealGenera,pGenera[2]);
            assert #IdealGenera[1] eq #pGenera[1];
         end if;
      end for;  
      Idls := &cat IdealGenera;
   end if;
   A`LeftIdealBases := [ [ Eltseq(A!x) : x in Basis(I) ] : I in Idls ]; 
   return Idls; 
end intrinsic;

function IsogenousIdeals(A,p)
   // Construct the sequence of left ideal classes for A 
   // by means of p-isogenies. 

   D := Discriminant(A);
   I := LeftIdeal(A,[A!1]);
   MZ := RSpace(Integers(),2);
   EmptyList := [ MZ | ];
   Ideals := [ LeftIdeal(A,[1]) ];
   Orders := [ A ];

   if GetVerbose("Quaternion") ge 2 then
      printf "Ideal number 1, right order module\n%o\n", 
         NormModule(Orders[1]);
   end if;

   FF := FiniteField(p);
   PF := PolynomialRing(FF); X := PF.1;
   repeat 
      x1 := RandomElement(A,[-p div 2..p div 2]);
      D1 := Trace(x1)^2 - 4*Norm(x1);
   until KroneckerSymbol(D1,p) eq -1;
   repeat
      x2 := RandomElement(A,[-p div 2..p div 2]);
      D2 := Trace(x2)^2 - 4*Norm(x2);
   until KroneckerSymbol(D2,p) eq 1;

   a2 := Integers()!Roots(X^2 - Trace(x2)*X + Norm(x2))[1,1];
   x2 := x2 - a2;
   T := 2*Trace(x1*Conjugate(x2)) - Trace(x1)*Trace(x2);
   D := (D1*D2 - T^2) div 4;

   r := 1;
   Frontier := [ [ MZ!P : P in P1Classes(p) ] ]; 
   while #Frontier[r] gt 0 do
      if GetVerbose("Quaternion") ge 1 then
         printf "Frontier at %o-depth %o has %o elements.\n",
            p, r, #Frontier[r];
         print "Number of ideals =", #Ideals;
      end if;
      for Q in Frontier[r] do
         I := LeftIdeal(A,[x2^r*(A!Q[1] + Q[2]*x1), A!p^r]);
         B := RightOrder(I);

         i := 1;
         while i le #Orders and CompareOrders(B,Orders[i]) eq -1 do
            i +:= 1;
         end while; 

         while i le #Orders and IsIsomorphic(B,Orders[i]) do
            if CompareLeftIdeals(Ideals[i],I) eq 0 then
               Exclude(~Frontier[r],Q);
               i := #Orders + 1;
            end if; 
            i +:= 1;
         end while; 

         if i eq (#Orders + 1) then
            if GetVerbose("Quaternion") ge 2 then
               printf "Ideal number %o, new right order module\n%o\n", 
                  #Orders + 1, NormModule(B);
            end if;
            Append(~Orders,B);
            Append(~Ideals,I);
         elif i le #Orders then
            if GetVerbose("Quaternion") ge 2 then
               M := NormModule(B); 
               printf "Ideal number %o, right order module\n%o\n", 
                  #Orders + 1, NormModule(B);
            end if;
            Insert(~Orders,i,B);
            Insert(~Ideals,i,I);
         end if;
      end for;
      Append(~Frontier,EmptyList);
      for P in Frontier[r] do
         Q := P;
         if (P[2] mod p) ne 0 then // P[2] eq 1 by assumption.
            for t in [0..(p-1)] do
               Q[1] := P[1] + t*p^r;
               Append(~Frontier[r+1],Q);
            end for;
         else // P = Q equals <1,0 mod l>.
            for t in [0..(p-1)] do
               Q[2] := P[2] + t*p^r;
               Append(~Frontier[r+1],Q);
            end for;
         end if;
      end for;
      r +:= 1; // Increment and continue.
   end while;
   return Ideals;
end function;

function SplitIsogenousIdeals(A,S0,p)
   // Input a sequence S0 of left A-ideals, and a prime p such that 
   // all p-isogenous left ideals are in a different genus from S0,
   // build the p^(2r+1)-isogenous ideals sequence S1 while extending 
   // S0 with p^2r-isogenous ideals

   D := Discriminant(A);
   MZ := RSpace(Integers(),2);
   EmptyList := [ MZ | ];
   IdealSeq := [ S0, [ PowerIdeal(A) | ] ];
   OrderSeq := [ [ RightOrder(I) : I in S0 ], [ Parent(A) | ] ];   
   /* 
   Additionally for the input sequence of ideals we need a sequence 
   indicating whether we have visited or "touched" the ideal class. 

   We begin with (the class of) A, so mark this as touched; every 
   other class is initially untouched.  

   The secondary sequence is being built as we go, so every element 
   is by definition touched at the time of creation.  We include 
   the second sequence, but it will be the all true sequence.  
   This could be omitted if we test the parity of t for each operation 
   on the sequence(s). 

   Here we assume that A is in the sequence of ideals, but we do 
   not assume that it is the first element.
   */
   Touched := [ [ Norm(I) eq 1 : I in S0 ], [ Booleans() | ] ]; 

   if GetVerbose("Quaternion") ge 2 then
      printf "Beginning with %o + %o ideals " * 
             "in split isogeny routine.\n", #S0, 0; 
   end if;

   FF := FiniteField(p);
   PF := PolynomialRing(FF); X := PF.1;
   repeat 
      x1 := RandomElement(A,[-p div 2..p div 2]);
      D1 := Trace(x1)^2 - 4*Norm(x1);
   until KroneckerSymbol(D1,p) eq -1;
   repeat
      x2 := RandomElement(A,[-p div 2..p div 2]);
      D2 := Trace(x2)^2 - 4*Norm(x2);
   until KroneckerSymbol(D2,p) eq 1;

   a2 := Integers()!Roots(X^2 - Trace(x2)*X + Norm(x2))[1,1];
   x2 := x2 - a2;
   T := 2*Trace(x1*Conjugate(x2)) - Trace(x1)*Trace(x2);
   D := (D1*D2 - T^2) div 4;

   r := 1;
   Frontier := [ [ MZ!P : P in P1Classes(p) ] ]; 
   while #Frontier[r] gt 0 do
      t := (r mod 2) eq 0 select 1 else 2; 
      if GetVerbose("Quaternion") ge 1 then
         Parity := t eq 1 select "Odd" else "Even"; 
         printf "Frontier at %o-depth %o has %o elements.\n",
            p, r, #Frontier[r];
         h1 := #IdealSeq[1]; 
         h2 := #IdealSeq[2]; 
         printf "Number of ideals = %o + %o\n", h1, h2;
         printf "Number of untouched ideals = %o\n", 
            &+[ Integers() | 1 : i in [1..h1] | not Touched[1][i] ];
      end if;
      for Q in Frontier[r] do
         I := LeftIdeal(A,[x2^r*(A!Q[1] + Q[2]*x1), A!p^r]);
         B := RightOrder(I);

         i := 1;
         while i le #OrderSeq[t] and 
               CompareOrders(B,OrderSeq[t][i]) eq -1 do
            i +:= 1;
         end while; 

         while i le #OrderSeq[t] and IsIsomorphic(B,OrderSeq[t][i]) do
            if CompareLeftIdeals(IdealSeq[t][i],I) eq 0 then
               if not Touched[t][i] then 
   	          // Mark ideal as visited and continue.
                  Touched[t][i] := true;
               else 
                  Exclude(~Frontier[r],Q);
               end if;
               i := #OrderSeq[t] + 1; 
            end if; 
            i +:= 1;
         end while; 
         if i eq (#OrderSeq[t] + 1) then
            if GetVerbose("Quaternion") ge 2 then
               printf "%o ideal number %o, new right order module\n%o\n", 
                  Parity, #OrderSeq[t] + 1, NormModule(B);
            end if;
            Append(~OrderSeq[t],B);
            Append(~IdealSeq[t],I);
            Append(~Touched[t],true);
         elif i le #OrderSeq[t] then
            if GetVerbose("Quaternion") ge 2 then
               M := NormModule(B); 
               printf "%o ideal number %o, right order module\n%o\n", 
                  Parity, #OrderSeq[t] + 1, NormModule(B);
            end if;
            Insert(~OrderSeq[t],i,B);
            Insert(~IdealSeq[t],i,I);
            Insert(~Touched[t],i,true);
         end if;
      end for;
      Append(~Frontier,EmptyList);
      for P in Frontier[r] do
         Q := P;
         if (P[2] mod p) ne 0 then // P[2] eq 1 by assumption.
            for t in [0..(p-1)] do
               Q[1] := P[1] + t*p^r;
               Append(~Frontier[r+1],Q);
            end for;
         else // P = Q equals <1,0 mod l>.
            for t in [0..(p-1)] do
               Q[2] := P[2] + t*p^r;
               Append(~Frontier[r+1],Q);
            end for;
         end if;
      end for;
      r +:= 1; // Increment and continue.
   end while;
   return IdealSeq;
end function;

intrinsic LeftIdealClasses(O::AlgQuatOrd[RngUPol] : Support:= []) -> SeqEnum
{"} // "
  F:= BaseField(Algebra(O));
  require IsOdd(Characteristic(F)) and IsFinite(BaseRing(F)) : "base field is not supported";
  require IsMaximalAtRamifiedPrimes(O) : "The order must be maximal at all ramified primes";
  return [ Conjugate(I) : I in RightIdealClasses(O : Support:= Support) ];
end intrinsic;


////////////////////////////////////////////////////////////////////
//                     Comparison Functions                       //
////////////////////////////////////////////////////////////////////

function CompareOrders(A,B)
   MA := ReducedGramMatrix(A);
   MB := ReducedGramMatrix(B);
   return CompareGram(MA,MB);
end function;

function CompareLeftIdeals(I,J)
   A := RightOrder(J);
   MA := Norm(I)*Norm(J)*ReducedGramMatrix(A);
   MB := ReducedGramMatrix(Conjugate(I)*J); 
   return CompareGram(MA,MB);
end function;

function CompareGram(M1, M2)
   // Return 1 if M1 is less than M2, 0 if M1 and M2 are equal, 
   // and -1 if M2 is less than M1.
   dim := Degree(Parent(M1));
   for i in [1..dim] do
      if M1[i,i] lt M2[i,i] then 
         return 1;
      elif M1[i,i] gt M2[i,i] then
         return -1; 
      end if;
   end for;
   for j in [1..dim-1] do
      for i in [1..dim-j] do 
         if Abs(M1[i,i+j]) gt Abs(M2[i,i+j]) then 
            return 1;
         elif Abs(M1[i,i+j]) lt Abs(M2[i,i+j]) then
            return -1; 
         end if;
      end for;
   end for;
   for j in [1..dim-1] do
      for i in [1..dim-j] do 
         if M1[i,i+j] gt M2[i,i+j] then 
            return 1;
         elif M1[i,i+j] lt M2[i,i+j] then
            return -1; 
         end if;
      end for;
   end for;
   return 0;
end function;

intrinsic Norm(I::AlgQuatOrdIdl) -> RngElt
    {Computes the norm of the ideal I.}

    if not assigned I`Norm then
       O:= assigned I`LeftOrder select LeftOrder(I) else RightOrder(I);
       normit:= Type(BaseRing(O)) eq RngInt select Abs else Normalize;

       r:= Determinant(BasisMatrix(I, O));
       sq, r:= IsSquare(normit(r));
       assert sq;

       I`Norm:= normit(r);
    end if;
    return I`Norm;
end intrinsic;

intrinsic GramMatrix(I::AlgQuatOrdIdl) -> AlgMatElt
{The Gram matrix of the quaternion ideal I}
    O:= Order(I);
    BM:= BasisMatrix(I);
    return BM * GramMatrix(O) * Transpose(BM);
end intrinsic;

intrinsic ReducedGramMatrix(I::AlgQuatOrdIdl) -> AlgMatElt
{The canonically reduced Gram matrix of the quaternion ideal I}
    require IsDefinite(Algebra(I)) : "The algebra must be definite";
    return MinkowskiGramReduction(GramMatrix(I) : Canonical := true);
end intrinsic;

intrinsic 'meet'(I::AlgQuatOrdIdl, J::AlgQuatOrdIdl) -> AlgQuatOrdIdl
{Intersection of quaternion ideals I and J}
    A := Algebra(Order(I));
    require A eq Algebra(Order(J)) : "Ideals are not compatible";

    F := CoefficientField(A);
    dim := 4;

    B1 := BasisMatrix(I)*BasisMatrix(Order(I));
    B2 := BasisMatrix(J)*BasisMatrix(Order(J));

    den1 := LCM([Denominator(e) :  e in Eltseq(B1)]);
    den2 := LCM([Denominator(e) :  e in Eltseq(B2)]);

    den := LCM(den1, den2);

    B1 := Matrix(Integers(F), den*B1);
    B2 := Matrix(Integers(F), den*B2);

    B := VerticalJoin(B1, B2);
    B := BasisMatrix(Kernel(B));
    B := Submatrix(B, 1, 1, dim, dim);

    B1 := B*B1;
    B1 := Matrix(F, B1)/den;

    L := ColonInternalZ(B1, B1, A, true);
    R := ColonInternalZ(B1, B1, A, false);

    if L eq R then
        LO := QuaternionOrder([A!L[i] : i in [1 .. Nrows(L)]] : IsBasis);
        I := ideal<LO | B1*L^-1>;
	return I, I;
    else
	return lideal<QuaternionOrder([A!L[i] : i in [1 .. Nrows(L)]] : IsBasis) | B1*L^-1>, 
	       rideal<QuaternionOrder([A!R[i] : i in [1 .. Nrows(L)]] : IsBasis) | B1*R^-1>;
    end if;

end intrinsic;


////////////////////////////////////////////////////////////////////
//               Maximal integral ideals of norm p                //
////////////////////////////////////////////////////////////////////

mri:= function(O, p, Al)
  gens:= Type(O) eq AlgQuatOrd select [O ! p] else ChangeUniverse(Generators(p), O);

  if Al eq "Local" then
    case Valuation(Discriminant(O), p):
      when 0:
        e11, e12, e21, e22 := get_coords(O, p);
        k, mk:= ResidueClassField(p);
        X:= [[0,1]] cat [[1,x@@mk] : x in k];
        return [ rideal< O | Append(gens, x[1]*e11 + x[2]*e21) > : x in X ];
      when 1:
        if IspMaximal(O, p) then
          return [ ideal< O | p > + CommutatorIdeal(O) ];
        end if;
        k, mk:= ResidueClassField(p);
        e11, e12, e21, e22 := get_coords(O, p);
        X:= [[0,1]] cat [[1,x@@mk] : x in k];
        return [ rideal< O | Append(gens, x[1]*e22 + x[2]*e12 + e21) > : x in X ] cat
               [ rideal< O | Append(gens, e11 + (x@@mk)*e21) > : x in k ];
    end case;
    // The other cases do not work right now with this method, so let it slip through.
    // For locally Gorenstein orders, it would be possible to canonize
    // the quadratic form of the trace 0 module (if 2 \notin p say).
    // Then there is a description of all maximal ideals using this basis.
  end if;

  A:= Algebra(O);
  k,h:= ResidueClassField(p);
  B:= LocalBasis(O, p : Type:= "Submodule");
  BI:= Matrix(B)^-1;
  Mat:= [ Matrix([A | y*x: y in B])*BI : x in B ];
  Mat:= [ Matrix(k, 4, [h(x): x in Eltseq(m)]) : m in Mat ];

  Mod:= RModule(Mat);
  MM:= [m : m in Submodules(Mod: CodimensionLimit:= 2) | Dimension(m) eq 2];

  ok:= IsHereditary(O, p);	// in this case, all ideals below will have right order O.
  Result:= [];
  for m in MM do
    X:= Matrix(Morphism(m, Mod)) @@ h;
    I:= rideal< O | [ &+[ B[j] * X[i,j] : j in [1..4] | X[i,j] ne 0] : i in [1..2] ] cat gens >;
    if ok or (RightOrder(I) eq O) then
      Append(~Result, I); 
    end if;
  end for;

  return Result;
end function;

intrinsic MaximalRightIdeals( O :: AlgAssVOrd, p :: RngOrdIdl : Al:= "Local" ) -> SeqEnum
{The integral right ideals of O of norm p}
  R:= BaseRing(O);
  require Order(p) cmpeq R and IsPrime(p) : 
    "The ideal p must be prime ideal in the base ring of O";
  require Type(Algebra(O)) eq AlgQuat : "Only works for quaterion algebras";
  require Al in {"Local", "Submodules"} : "Al must be either 'Local' or 'Submodules'";
  
  return mri(O, p, Al);
end intrinsic;

intrinsic MaximalRightIdeals( O :: AlgQuatOrd, p :: RngElt : Al:= "Local" ) -> SeqEnum
{"} // "
  require Parent(p) cmpeq BaseRing(O) and IsPrime(p): 
    "The element p must be a prime in the base ring of O";
  require Al in {"Local", "Submodules"} : "Al must be either 'Local' or 'Submodules'";
  return mri(O, p, Al);
end intrinsic;

intrinsic MaximalLeftIdeals( O :: AlgAssVOrd, p :: RngOrdIdl : Al:= "Local" ) -> SeqEnum
{The integral left ideals of O of norm p}
  require Order(p) cmpeq BaseRing(O) and IsPrime(p): 
    "The ideal p must be a prime in the base ring of O";
  require Type(Algebra(O)) eq AlgQuat : "Only works for quaterion algebras";
  require Al in {"Local", "Submodules"} : "Al must be either 'Local' or 'Submodules'";
  return [ Conjugate(I): I in mri(O, p, Al) ];
end intrinsic;

intrinsic MaximalLeftIdeals( O :: AlgQuatOrd, p :: RngElt : Al:= "Local" ) -> SeqEnum
{"} // "
  require Parent(p) cmpeq BaseRing(O) and IsPrime(p): 
    "The element p must be a prime in the base ring of O";
  require Al in {"Local", "Submodules"} : "Al must be either 'Local' or 'Submodules'";
  return [ Conjugate(I): I in mri(O, p, Al) ];
end intrinsic;

////////////////////////////////////////////////////////////////////
//            For completeness and compatibility                  //
////////////////////////////////////////////////////////////////////

intrinsic ZBasis(O:: AlgQuatOrd) -> SeqEnum
  {A basis for the order O as a Z or F_q[X]-module}
  return Basis(O);
end intrinsic;

intrinsic ZBasis(I:: AlgQuatOrdIdl) -> SeqEnum
  {A basis for the ideal I as a Z or F_q[X]-module}
  return Basis(I);
end intrinsic;

intrinsic LocalBasis(O:: AlgQuatOrd, p::RngElt : Type := "") -> SeqEnum
  {A basis for the order O as a Z or F_q[X]-module}
  return Basis(O);
end intrinsic;

intrinsic LocalBasis(I:: AlgQuatOrdIdl, p::RngElt : Type := "") -> SeqEnum
  {A basis for the order O as a Z or F_q[X]-module}
  return Basis(O);
end intrinsic;

