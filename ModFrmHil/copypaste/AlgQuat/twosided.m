freeze;

/**********************************************************
* Computation of twosided ideal classes and normalizers   *
* in (definite) quaternion algebras                       *
*                                                         *
* December 2012, Markus Kirschmer                         *
*                                                         *
**********************************************************/

// This is very much work in progress

// Ideas / goals:
// Computing twosided ideal classes for (Eichler) orders
// is more or less the same as computing normalizers.

// Currently we support this:
// + Direct normalizer computations of any order
// + Twosided ideal classes of Eichler orders via direct method
// + Twosided ideal classes of Eichler orders via normalizers (only over Z, F_q[t]

import "../AlgAss/enum.m" : GramMatrices;

declare attributes AlgAssVOrd: Normalizer;

debug:= false;

////////////////////////////////////////////////////////////////////
//                      Normalizers                               //
////////////////////////////////////////////////////////////////////

function Reduce(x)
  i:= Depth(Vector(x));
  if x[i] ne 1 and x[i] ne -1 then
    x:= x/x[i];
  end if;
  return x*Denominator(x); 
end function;

function Mult(w, Gens)
  x:= Universe(Gens) ! 1;
  for i in Eltseq(w) do
    x:= x * Gens[Abs(i)]^Sign(i);
    if i mod 10 eq 0 then x:= Reduce(x); end if;
  end for;
  return Reduce(x);
end function;

function Action(O, B, x)
  ok, xinv:= IsInvertible(x);
  error if not ok, "The element is not a unit";
  if B cmpne 0 then
    Img:= [ xinv * b * x : b in B[1] ]; 
    ok, Img:= CanChangeUniverse(Img, O);
    error if not ok, "The element is not a normalizer";
    M:= Matrix( [ Eltseq(i): i in Img ] ) * B[2];
    ok, M:= CanChangeRing(M, BaseRing(BaseRing(O)));
    error if not ok, "The element is not a normalizer";
    return M;
  elif Type(O) eq AlgQuatOrd then
    Img:= [ xinv * b * x : b in Basis(O) ]; 
    ok, Img:= CanChangeUniverse(Img, O);
    error if not ok, "The element is not a normalizer";
  else
    Img:= [ xinv * b * x : b in Basis(Algebra(O)) ];
  end if;
  return Matrix( [ Eltseq(i): i in Img ] );
end function;

function SetupNormalizerMap(G, Gens, O, B)
  Gens:= [ Universe(Gens) | Reduce(x) : x in Gens ];
  W, h:= WordGroup(G);
  F:= FreeGroup(Ngens(W));
  return map< G -> Algebra(O) | g :-> Mult(Evaluate(g @@ h, F), Gens) , x :-> Action(O, B, x) >;
end function;

function det_kernel(A, conj, e)
  conj:= A ! conj;
  Gens:= [A | ];
  deg4:= Degree(A) eq 4;
  for i in [1..Ngens(A)] do
    mat:= Determinant(A.i) eq 1 select A.i else A.i * conj;
    Append(~Gens, deg4 and e*mat ne e select -mat else mat);
  end for;
  AA:= sub< A | Gens >; 
  assert #A eq #AA * (deg4 select 4 else 2);
  return AA;
end function;

intrinsic Normalizer(O::AlgQuatOrd[RngUPol]) -> Grp, Map
{Let O be an order in a definite quaternion algebra Q over a field F.
 This function returns the normalizer of O in Q^* modulo F^* as an abstract group G.
 A map from G to Q^* is also provided.}

  if not assigned O`Normalizer then
    require IsDefinite(Algebra(O)) : "The algebra must be definite";
    _:= ReducedGramMatrix(O : Canonical);
  end if;
  if Type(O`Normalizer) ne Map then
    N:= O`Normalizer;
    BO:= ChangeUniverse(O`ReducedGram[2][2..4], O);

    // Replace N by determinant 1 subgroup
    N:= det_kernel(N, ScalarMatrix(BaseRing(N), 3, -1), 0);
    Gens:= [ N.i: i in [1..Ngens(N)] ];

    // Find elements that induce these isometries.
    Q:= Algebra(O);
    QGens:= [ Q | ];
    if #Gens ne 0 then
      BQ:= Basis(Q);
      B:= Basis(O);
      for mat in Gens do 
        hBO:= [ &+[ mat[k,j] * BO[j] : j in [1..3] | mat[k,j] ne 0 ] : k in [1..2] ];
        K:= Kernel(Matrix([ &cat[ Eltseq(BO[i]*b - b*hBO[i]) : i in [1..2] ] : b in BQ ] ));
        assert Dimension(K) eq 1;
        assert not debug or O^(Q ! Eltseq(K.1)) eq O;
        Append(~QGens, Q ! Eltseq(K.1));
      end for;
    end if;

    BtoBO:= Submatrix(Matrix([ Eltseq(b) : b in Append(BO, 1) ])^-1, 1,1,4,3);
    O`Normalizer:= SetupNormalizerMap(N, QGens, O, <BO, BtoBO>);
  end if;

  return Domain(O`Normalizer), O`Normalizer;
end intrinsic;

/*
intrinsic Normalizer(O::AlgQuatOrd[RngInt]) -> Grp, Map
{"} //"

  if not assigned O`Normalizer then
    Q:= Algebra(O);
    require IsDefinite(Q) : "Only implemented for definite orders.";

    // Find automorphisms that fix O and send 1 to 1.
    G:= GramMatrix(O);
    one:= Eltseq(O ! 1);
    e:= Matrix(Integers(), 1, one);
    K:= KernelMatrix(G*e);
    eK:= Matrix(Rationals(), VerticalJoin(Transpose(e), K))^-1;
    F:= eK * DiagonalMatrix([Rationals() | 1,0,0,0]) * Transpose(eK);
    A:= AutomorphismGroup([ G, IntegralMatrix(F) ]);
    B:= Basis(O);
    conj:= Matrix(Integers(), [ Eltseq(O ! Conjugate(b)): b in B ]);
    AA:= det_kernel(A, conj, Vector(Integers(), one));

    QGens:= [ Q | ];
    BQ:= Basis(Q);
    R:= BaseRing(O);
    for i in [1..Ngens(AA)] do 
      hB:= [ Q | O ! Eltseq(mat[i]) : i in [1..4] ] where mat:= AA.i;
      K:= Kernel(Matrix([ &cat[ Eltseq(B[i]*b - b*hB[i]) : i in [1..4] ] : b in BQ ] ));
      assert Dimension(K) eq 1;
//      assert O^(Q ! Eltseq(K.1)) eq O;
      Append(~QGens, Q ! Eltseq(K.1));
    end for;
    O`Normalizer:= SetupNormalizerMap(AA, QGens, O, 0);
  end if;

  return Domain(O`Normalizer), O`Normalizer;
end intrinsic;
*/

find_stab:= function(A)
  Orb:= {@ MatrixRing(Rationals(), 4) ! 1 @};
  S:= sub< A | >;
  Paths:= [ A ! 1 ];
  i:= 1;
  while i le #Orb and 2*#S*#Orb le #A do
    for j in [1..Ngens(A)] do
      X, d:= IntegralMatrix(Orb[i] * A.j);
      X:= 1/d * HermiteForm(X);
      idx:= Index(Orb, X);
      if idx eq 0 then
        Include(~Orb, X);
        Append(~Paths, Paths[i]*A.j);
      else
        s:= Paths[i]*A.j*Paths[idx]^-1;
        if s notin S then S:= sub< A | S, s>; end if; 
      end if;
    end for;
    i +:= 1;
  end while;
  return S;
end function;

intrinsic Normalizer(O::AlgQuatOrd[RngInt]) -> Grp, Map
{"} //"

  if not assigned O`Normalizer then
    Q:= Algebra(O);
    require IsDefinite(Q) : "Only implemented for definite orders.";

    // Find automorphisms that fix O and send 1 to 1.
    B:= Basis(O);
    K:= KernelMatrix( Matrix(Integers(), 1, [Trace(b) : b in B]) );
    G:= K * GramMatrix(O) * Transpose(K);
    A:= AutomorphismGroup(LatticeWithGram(G));
    A:= det_kernel(A, ScalarMatrix(Integers(), 3, -1), 0);
    T:= GL(4, Rationals()) ! VerticalJoin(Matrix(Integers(), 4, Eltseq(O ! 1)), K);
    TI:= T^-1;
    one:= Matrix(Rationals(), 1, [1]);
    AA:= sub< GL(4, Rationals()) | [ TI * DiagonalJoin(one, Matrix(Rationals(), A.i)) * T: i in [1..Ngens(A)] ] >;
    AA`Order:= #A;
    AA:= ChangeRing(find_stab(AA), Integers());

    QGens:= [ Q | ];
    BQ:= Basis(Q);
    R:= BaseRing(O);
    for i in [1..Ngens(AA)] do
      hB:= [ Q | O ! Eltseq(mat[i]) : i in [1..4] ] where mat:= AA.i;
      K:= Kernel(Matrix([ &cat[ Eltseq(B[i]*b - b*hB[i]) : i in [1..4] ] : b in BQ ] ));
      assert Dimension(K) eq 1;
      assert not debug or O^(Q ! Eltseq(K.1)) eq O;
      Append(~QGens, Q ! Eltseq(K.1));
    end for;
    O`Normalizer:= SetupNormalizerMap(AA, QGens, O, 0);
  end if;

  return Domain(O`Normalizer), O`Normalizer;
end intrinsic;


intrinsic Normalizer(O::AlgAssVOrd[RngOrd]) -> Grp, Map
{"} //"

  if not assigned O`Normalizer then
    Q:= Algebra(O);
    require Type(Q) eq AlgQuat: "Only implemented by quaternion orders.";
    require IsDefinite(Q): "Only implemented for definite orders.";

    G, B:= GramMatrices(O);
    R:= BaseRing(O); 

    BR:= Basis(R); assert IsOne(BR[1]);
    BR:= Coordinates([Q ! b : b in BR], B);
    K:= KernelMatrix( Matrix( [ Flat(Trace(b)) : b in B ] ) );
    T:= VerticalJoin( Matrix(Rationals(), BR), K )^-1;
    F:= T * DiagonalMatrix( [1] cat [0^^(4*#BR-1)] ) * Transpose(T);

    A:= AutomorphismGroup(Append(G, IntegralMatrix(F)));
    BQ:= Basis(Q);
    C:= Coordinates(BQ, B);
    AGens:= [ Matrix(Rationals(), A.i) : i in [1..Ngens(A)] ];
    Gens:= [ Matrix([ Q | &+[ B[j] * x[j] : j in [1..#B] | x[j] ne 0 ] where x:= Vector(Rationals(), c) * a : c in C ]) : a in AGens];
    K:= BaseField(Q);
    AK:= sub< GL(4, K) | Gens >;
    assert not debug or #A eq #AK;
    Conj:= Matrix( [Eltseq(Conjugate(b)): b in BQ] );
    AA:= det_kernel(AK, Conj, Vector([K | 1,0,0,0]));

    QGens:= [ Q | ];
    for i in [1..Ngens(AA)] do
      hB:= [ Q | Eltseq(mat[i]) : i in [1..4] ] where mat:= AA.i;
      K:= Kernel(Matrix([ &cat[ Eltseq((BQ[i]*b - b*hB[i])) : i in [1..4] ] : b in BQ ] ));
      assert Dimension(K) eq 1;
      assert not debug or O^(Q ! Eltseq(K.1)) eq O;
      Append(~QGens, Q ! Eltseq(K.1));
    end for;
    O`Normalizer:= SetupNormalizerMap(AA, QGens, O, 0);
  end if;

  return Domain(O`Normalizer), O`Normalizer;
end intrinsic;


////////////////////////////////////////////////////////////////////
//                      Two Sided Ideals                          //
////////////////////////////////////////////////////////////////////

intrinsic CommutatorIdeal(O:: AlgAssVOrd) -> AlgAssVOrdIdl
  { The twosided ideal of O generated by elements of the form x*y - y*x. }

  G:= Generators(O);
  C:= ideal< O | [G[i]*G[j]-G[j]*G[i]: i in [1..j-1], j in [1..#G]] >;
  C`LeftOrder:= O; C`RightOrder:= O;
  if assigned O`IsMaximal and O`IsMaximal then
    C`Norm := Discriminant(O); end if;
  // TO DO: assign Norms to everything also when O is an Eichler order?
  return C;
end intrinsic;

intrinsic Factorization(I:: AlgAssVOrdIdl) -> SeqEnum
  { Given a twosided ideal I of an hereditary quaternion order,
    the function returns the unique factorization of I into twosided O-ideals. }

  A:= Algebra(I);
  require Type(A) eq AlgQuat: "Currently only defined for quaternion algebras";
  O:= Order(I);
  require IsHereditary(O): "The order of the ideal is not hereditary";
  require O eq RightOrder(I) and O eq LeftOrder(I): 
    "The left and right orders of the ideal must be the order over which the ideal was created";

  C:= CommutatorIdeal(O);
  List:= [];
  Primes:= { f[1]: f in FactoredDiscriminant(O) };
  F:= Type(I) eq AlgQuatOrdIdl select FactorizationOfQuotient(Norm(I)) else Factorization(Norm(I));
  for f in F do
    if f[1] in Primes then
      Append( ~List, < ideal< O | f[1] > + C, f[2] > );
    else
      Append( ~List, < ideal< O | f[1] >, f[2] div 2 > );
    end if;
  end for;
  return List;
end intrinsic;


// Get a list of reps of the class group which is supported at 
// FD[1..d] with d minimal.
function good_reps(O, A, hinv, FD)
  I:= ideal< O | 1 >; I`Norm:= 1; I`LeftOrder:= O; I`RightOrder:= O;
  List:= [I];
  Words:= {@ A | 0 @};
  Norms:= { BaseRing(O) | };
  C:= Basis(CommutatorIdeal(O));
  S:= sub< A | >;
  d:= 1;
  while #S ne #A do
    nrm:= FD[d,1]^FD[d,2];
    I:= ideal< O | Append(C, nrm) >;
    I`LeftOrder:= O; I`RightOrder:= O; I`Norm:= nrm;
    s:= hinv(I);
    if s notin S then
      Append(~List, I);
      Include(~Words, s);
      Include(~Norms, FD[d,1]);
      B:= Basis(I);
      for i in [2..#List-1] do
        J:= ideal< O | [b*c: b in B, c in Basis(List[i])] >;
        J`LeftOrder:= O; J`RightOrder:= O; J`Norm:= nrm * List[i]`Norm;
	Append(~List, J);
        Include(~Words, Words[i] + s);
      end for;
      S:= sub< A | S, s >;
    end if;
    d +:= 1;
  end while;
  return List, Words, Norms;
end function;

function test(O, I)
  error if LeftOrder(I) ne O or RightOrder(I) ne O, "The ideal is not an invertible twosided ideal of the correct order.";
  return I;
end function;

support_error:= "The support must be a sequence of primes of the base ring of the order";
gram:= func< I, R | Type(R) eq RngInt select MinkowskiGramReduction(G : Canonical) 
         else DominantDiagonalForm(G : Canonical) where G:= Matrix(R, GramMatrix(I)/Norm(I)) >;

intrinsic TwoSidedIdealClassGroup(O::AlgQuatOrd : Support:= [], Al:= "") -> GrpAb, Map
{ The abelian group generated by the invertible twosided O-ideal
  classes together with a map to a system of representatives.
  The optional parameter is explained in TwoSidedIdealClasses}

  R:= BaseRing(O);
  if Type(R) ne RngInt then
    K:= BaseRing(R);
    require IsField(K) and IsFinite(K) and IsOdd(#K): "The base ring is not supported";
  end if;

  if not IsDefinite(Algebra(O)) then
    A:= AbelianGroup([]);
    I:= ideal< O | 1 >; I`Norm:= 1;
    return A, map< A -> PowerIdeal(O) | x :-> I, y :-> 0 where tmp:= test(O, I) >;
  end if;

  FD:= FactoredDiscriminant(O);
  if Al eq "" then
    Al:= assigned O`Normalizer or #FD gt 2 select "Normalizer" else "Direct";
  end if;

  require Al in {"Normalizer", "Direct", "Forms"}:
    "The algorithm must be one of \"Normalizer\", \"Direct\" or \"Forms\"";

  require Type(Support) in {SetEnum, SeqEnum} : support_error;
  if not IsEmpty(Support) then
    if Type(Rep(Support)) eq Type(R) then Support:= { Generator(p): p in Support }; end if;
    require Universe(Support) cmpeq R and forall{ p: p in Support | IsPrime(p) } : support_error;
    Support:= Type(R) eq RngInt select { Abs(p): p in Support } else { Normalize(p): p in Support };
    Support:= { p: p in Support | D mod p eq 0 } where D:= Discriminant(O);
    FD:= [ f: f in FD | f[1] in Support ] cat [ f: f in FD | f[1] notin Support ];
  end if;

  if assigned O`TwoSidedIdealClassMaps then
    // the entries x are of the form < map, given support, resulting support >
    if exists(x){x : x in O`TwoSidedIdealClassMaps | IsEmpty(Support) or Support eq x[2] or x[3] subset Support } then
      return Domain(x[1]), x[1];
    end if;
    x:= O`TwoSidedIdealClassMaps[1];
    AA:= Domain(x[1]);
    List, Words, Norms:= good_reps(O, AA, x[1]^-1, FD);
    m:= map< AA -> PowerIdeal(O) | a :-> List[Index(Words, a)], I :-> I @@ x[1] >;
    Append(~O`TwoSidedIdealClassMaps, < m, Support, Norms >);
    if debug then
      "checking multiplication of twosided ideal class group.";
      assert forall{s: s in AA | s@m@@m eq s };
      assert forall{ < s,t > : s,t in AA | IsLeftIsomorphic( (s@m) * (t@m), (s+t)@m ) };
    end if;
    return AA, m;
  end if;

  // A.i corresponds to the ideal of norm FD[i,1]^FD[i,2].
  // We now look for relations Rel between these ideals.
  // Then AA:= A / Rel is the result.
  Primes:= [ f[1]: f in FD ];
  A:= AbelianGroup([2^^#Primes]);

  if Al eq "Normalizer" then
    // We work out a relation matrix Rel inside A and a map from the ideals to A.
    N, Nh:= Normalizer(O);
    Rel:= [];
    if Ngens(N) ne 0 then
      BM:= BasisMatrix(O)^-1;
      for i in [1..Ngens(N)] do
        x:= Nh(N.i);
        v:= Vector(Eltseq(x)) * BM;
	d:= Denominator(v);
	c:= Content(ChangeRing(v*d, R));
	nrm:= R ! (Norm(x) * (d/c)^2);
	Append(~Rel, [ nrm mod p eq 0 select 1 else 0 : p in Primes ]);
      end for;
      Rel:= Matrix(GF(2), Rel);
      B:= Matrix(Integers(), BasisMatrix(Image(Rel)));
      Rel:= [ Eltseq(B[i]) : i in [1..Nrows(B)] ];
    end if;
  else
    I:= ideal< O | 1 >; I`Norm:= 1; I`LeftOrder:= O; I`RightOrder:= O;
    List:= [I];
    Words:= {@ A ! 0 @};
    Norms:= { R | };
    UseForms:= Al eq "Forms";
    if UseForms then Grams:= {@ gram(I, R) @}; end if;
    C:= Basis(CommutatorIdeal(O));
    Rel:= [];
    for d in [1..#FD] do
      nrm:= FD[d,1]^FD[d,2];
      I:= ideal< O | Append(C, nrm) >;
      I`Norm:= nrm; I`LeftOrder:= O; I`RightOrder:= O;

      if UseForms then
        G:= gram(I, R);
        j:= Index(Grams, G);
      elif exists(jj){j: j in [1..#List] | IsIsomorphic(List[j], I)} then
        j:= jj;
      else
        j:= 0;
      end if;

      if j eq 0 then
        Append(~List, I);
        Include(~Words, A.d);
        if UseForms then Include(~Grams, G); end if;
        B:= Basis(I);
        for i in [2..#List-1] do
          J:= ideal< O | [b*c: b in B, c in Basis(List[i])] >;
	  J`Norm:= nrm * List[i]`Norm; J`LeftOrder:= O; J`RightOrder:= O;
          Append(~List, J);
          Include(~Words, Words[i] + A.d);
          if UseForms then Include(~Grams, gram(J, R)); end if;
        end for;
      else
        Append(~Rel, Words[j] + A.d);
      end if;
    end for;
  end if;

  // Setup AA:= A/Rel which is the result.
  if IsEmpty(Rel) then
    AA:= A; AtoAA:= func< x | x >;
  else
    AA, AtoAA:= quo< A | Rel >;
  end if;

  // Given an ideal, this returns the corresponding element in AA.
  factors:= function(I)
    B:= BasisMatrix(I, O);
    d:= Denominator(B);
    n:= R ! (Norm(I) * (d/Content(Matrix(R, d*B)))^2);
    return (A ! [ n mod p eq 0 select 1 else 0 : p in Primes ]) @ AtoAA;
  end function;

  if Al eq "Normalizer" then
    // Get a list of suitable representatives etc.
    List, Words, Norms:= good_reps(O, AA, factors, FD);
  else
    // Update the word list.
    Words:= {@ w @ AtoAA : w in Words @};
  end if;

  // Setup a map from AA to these reps.
  m:= map< AA -> PowerIdeal(O) | a :-> List[Index(Words, a)], I :-> factors(test(O, I)) >;

  if debug then
    "checking multiplication of twosided ideal class group.";
    assert forall{s: s in AA | s@m@@m eq s };
    assert forall{ < s,t > : s,t in AA | IsLeftIsomorphic( (s@m) * (t@m), (s+t)@m ) };
  end if;

  O`TwoSidedIdealClassMaps := [* < m, Support, Norms > *];
  return AA, m;
end intrinsic;



// The old (direct) method. These days, it is only used over number fields.

procedure addfactor(~List, ~Words, I, Word, O, o)
  flat:= Type(BaseRing(O)) in {RngInt, RngUPol};
  size:= #List;
  assert(#Words eq #List);
  I`RightOrder:= O; I`LeftOrder:= O;
  for i in [1..o-1] do
    for j in [(i-1)*size+1..i*size] do
      J:= flat select ideal< O | [ x*y: x in Basis(I), y in Basis(List[j]) ] >
                 else '*'(I, List[j] : Check:= false, Sides:= "Left");
      J`RightOrder:= O; J`LeftOrder:= O;
      if not assigned(J`Norm) then J`Norm:= Norm(I) * Norm(List[j]); end if;
      Append(~List, J);
      if Type(Words) eq SeqEnum then
        Append(~Words, Word+Words[j]);
      else
        Include(~Words, Word+Words[j]);
      end if;
      assert(#Words eq #List);
    end for;
  end for;
end procedure;

function GetTwoSidedIdealClassMapDefinite(O : Supp:= [])
  R:= BaseRing(O);
  flat:= Type(R) in {RngInt, RngUPol};
  FD:= FactoredDiscriminant(O);
  I1:= ideal< O | 1 >;
  I1`LeftOrder:= O; I1`RightOrder:= O; I1`Norm:= flat select 1 else ideal< R | 1 >;
  List:= [I1];
  clgens:= 0;

  if not flat then
    Cl, Clh:= ClassGroup(R);
    AR, hh:= quo< Cl | >;
    Words:= [ Cl | 0 ];
    kernel:= []; Rels:= [];

    for g in Generators(Cl) do
      o:= Order(g @ hh);
      if o eq 1 then continue; end if;
      // First, we compute the order of ideal< O | p > in Cl_2(O).
      p:= g @ Clh;
      D:= Divisors(o);
      for i in [1..#D] do
        pow:= p^D[i];
        I:= ideal< O | Generators(pow) >;
        I`LeftOrder:= O; I`RightOrder:= O; I`Norm:= pow^2;
        if exists(j){j: j in [1..#List] | IsLeftIsomorphic(I,List[j])} then
          o:= D[i];
          Append(~kernel, Words[j] - o*g);
          AR, hh:= quo< Cl | kernel >;
          break;
        end if;
      end for;
      if o ne 1 then
        I:= ideal< O | Generators(p) >; I`Norm:= p^2;
        addfactor(~List, ~Words, I, g, O, o);
      end if;
    end for;

    // Adjust the graph of the map
    if #List ne 1 then
      clgens:= Ngens(AR);
      Words:= [ Eltseq(x @ hh) : x in Words ];
      Rels:= [ Eltseq(R[i]) : i in [1..Nrows(R)] ] where R:= RelationMatrix(AR);
    end if;
  end if;

  F:= FreeAbelianGroup(clgens + #FD);
  if clgens eq 0 then
    Words:= [ F | 0 ];
    Rels := [ F | ];
    IdltoF:= func< x | F ! 0 >;
  else
    Words := [ &+[F | x[i] * F.i : i in [1..#x] | x[i] ne 0 ] : x in Words ];
    Rels  := [ &+[F | x[i] * F.i : i in [1..#x] | x[i] ne 0 ] : x in Rels  ];
    IdltoF:= func< x | F ! (Eltseq((x @@ Clh) @ hh) cat [0^^#FD]) >;
  end if;

  if not IsEmpty(FD) then
    C:= CommutatorIdeal(O);
    for i in [1..#FD] do
      nrm:= FD[i,1]^FD[i,2];
      I:= ideal< O | nrm > + C;
      I`LeftOrder:= O; I`RightOrder:= O; I`Norm:= nrm;
      if exists(j){j: j in [1..#List] | IsLeftIsomorphic(List[j], I)} then
        Append(~Rels, Words[j] - F.(i+clgens));
      else
        addfactor(~List, ~Words, I, F.(i+clgens), O, 2);
        Append(~Rels, IdltoF(nrm) - 2*F.(i+clgens));
      end if;
    end for;
  end if;

  P:= PowerIdeal(O);
  if #List eq 1 then
    return map< AbelianGroup([]) -> P | x:-> I1, y:-> 0 >;
  else
    A, h:= quo< F | Rels >;
    // We could do without the Words list, but then every map application would result in several ideal multiplications.
    // That's too expensive.
    Words:= {@ A | x @ h : x in Words @};
    assert #Words eq #A;

    MyInverse:= function(I)
      error if LeftOrder(I) ne O or RightOrder(I) ne O, "The ideal is not a twosided ideal of the correct order!";
      x:= F ! 0;
      nrm:= Norm(I);
      if exists{ f : f in FD | f[2] gt 1 } then
        if flat then
          B:= BasisMatrix(I, O);
          d:= LCM( { Denominator(x) : x in Eltseq(B) } );
          e:= GCD(Eltseq(Matrix(R, d*B)));
          nrm *:= d^2;
        else
          e:= ElementaryDivisors(PseudoMatrix(O), PseudoMatrix(I))[1];
        end if;
      end if;
      // Idea: Guess a factorization. Let x be the image of these factors in F.
      for i in [1..#FD] do
        v:= Valuation(nrm, FD[i,1]);
        if FD[i,2] eq 1 then                    // p-hereditary case. The norm tells it all.
          if IsOdd(v) then
            nrm /:= FD[i,1];
            x +:= F.(clgens + i);
          end if;
        else
          w:= v-2*Valuation(e, FD[i,1]);        // The norm part coming from the commutator ideal factors
          nrm /:= FD[i,1]^w;
          assert w mod FD[i,2] eq 0;
          x +:= (w div FD[i,2]) * F.(clgens + i);
        end if;
      end for;
      ok, nrm:= IsSquare(nrm);                  // The factor coming from the center
      assert(ok);
      return x + IdltoF(nrm);
    end function;

    m:= map< A -> P | x:-> List[Index(Words, x)], y:-> MyInverse(y) @ h >;
    if debug then
      "checking multiplication of twosided ideal class group.";
      assert forall{s: s in A | s@m@@m eq s };
      assert forall{ < s,t > : s,t in A | IsLeftIsomorphic( (s@m) * (t@m), (s+t)@m ) };
    end if;
    return m;
  end if;
end function;


function GetTwoSidedIdealClassMapIndefinite(O, Supp)
  List:= [ ideal< O | 1 > ];
  R:= BaseRing(O);
  P:= PowerIdeal(O);
  if Type(R) in {RngInt, RngUPol} then
    G:= AbelianGroup([]);
  else
    _, Inf:= RamifiedPlaces(Algebra(O));
    if IsEmpty(Inf) then
      G, hRCl := ClassGroup(R);
    else
      G, hRCl := RayClassGroup(&+Inf);
    end if;
  end if;

  if IsTrivial(G) then
    return map< G -> P | x:-> List[1], y:-> 0 >;
  end if;

  nrcentral:= #(2*G);                                   // number of ideals coming from the center
  FD:= FactoredDiscriminant(O);
  done:= [];
  Words:= {@ G | 0 @};
  // First we get the subgroup coming from the center.
  if nrcentral gt 1 then
   if IsEmpty(Supp) then
      // The generators of the class group would do. But since we work in G directly, this is not slower.
      gens:= [ 2*G.i : i in [1..Ngens(G)] ];
      idls:= [ g @ hRCl : g in gens ];
    else
      idls:= Supp;
      gens:= [ 2*(p @@ hRCl) : p in idls ];
      S:= sub< G | gens >;
      if #S ne nrcentral then
        // According to the description of the intrinsic, the user can/must assume that we insert ideals with norm coming from FD
        for f in FD do
          g:= 2*(f[1] @@ hRCl);
          if g notin S then
            Append(~Supp, f[1]);        // Make sure we add them first later on to keep the number of factors small
            S:= sub< G | S, g >;
            if #S eq nrcentral then break; end if;
          end if;
        end for;
        // Check if we got enough
        error if #sub< G | gens > ne nrcentral, "The given support is too small.";
      end if;
    end if;

    Q, h:= quo< G | >;
    for k in [1..#gens] do
      g:= gens[k];
      Range:= [1..#List];
      o:= Order(g @ h);
      if o gt 1 then
        I:= ideal< O | Generators(idls[k]) >; I`Norm:= idls[k]^2;
        addfactor(~List, ~Words, I, g, O, o);
        Append(~done, g);
        if #List eq nrcentral then break; end if;
        Q, h:= quo< G | done >;
      end if;
    end for;
  end if;

  S:= sub< G | done >;
  if #S ne #G then
    C:= CommutatorIdeal(O);
    FD:= [ f : f in FD | IsOdd(f[2]) ];
    if not IsEmpty(Supp) then
      FD:= [ f : f in FD | f[1] in Supp ] cat [ f : f in FD | f[1] notin Supp ];
    end if;
    for f in FD do
      nrm:= f[1]^f[2];
      g:= nrm @@ hRCl;
      if g notin S then
        I:= ideal< O | nrm > + C;
        I`LeftOrder:= O; I`RightOrder:= O; I`Norm:= nrm;
        for j in [1..#List] do
          J:= List[j] * I;
          J`LeftOrder:= O; J`RightOrder:= O;
          if not assigned(J`Norm) then J`Norm:= Norm(List[j]) * nrm; end if;
          Append(~List, J);
          Append(~Words, Words[j] + g);
        end for;
        S:= sub< G | S, g >;
        if #S eq #G then break; end if;
      end if;
    end for;
  end if;

  assert #List eq #S;
  return map< S -> P | x:-> List[Index(Words, x)], y:-> Norm(y) @@ hRCl >;
end function;

intrinsic TwoSidedIdealClassGroup(O :: AlgAssVOrd : Support:= []) -> GrpAb, Map
{"} //"

  A:= Algebra(O);
  require Type(A) eq AlgQuat: "Currently, we only support quaternion orders";
  R:= BaseRing(O);
  flat:= Type(R) in {RngInt, RngUPol};
  Support:= Set(Support);
  if not IsEmpty(Support) then
    if flat and Type(Rep(Support)) cmpeq Type(R) then Support:= { R | Generator(s) : s in Support }; end if;
    require forall{p : p in Support | IsPrime(p) and ((flat and p in R) or (not flat and Order(p) cmpeq R))}:
            "The support must only contain prime ideals of the base ring of O.";
  end if;

  if flat then
    _Support:= Type(R) eq RngInt select func< x | Set(PrimeDivisors(Integers() ! x)) >
                                   else func< x | { f[1] : f in FactorizationOfQuotient(x) } >;
    Support := {p : p in Support | D mod p eq 0 } where D:= Discriminant(O);
  else
    _, _Support:= IsIntrinsic("Support");
    // try to reduce the support
    if not IsEmpty(Support) then
      Cl, Clh:= ClassGroup(R);
      temp:= {p : p in Support | Valuation(D, p) ge 1 } where D:= Discriminant(O);
      S:= sub< Cl | [ p @@ Clh : p in temp ] >;
      if #S ne #Cl then
        for p in {p : p in Support | p notin temp} do
          x:= p @@ Clh;
          if x notin S then
            S:= sub< Cl | S, x >;
            Include(~temp, p);
            if #S eq #Cl then break; end if;
          end if;
        end for;
      end if;
      Support:= temp;
    end if;
  end if;

  if assigned O`TwoSidedIdealClassMaps then
    // the entries X are of the form < map, given support, resulting support >
    for X in O`TwoSidedIdealClassMaps do
      if Support eq X[2] or X[3] subset Support then
        return Domain(X[1]), X[1];
      end if;
    end for;
  end if;

  if IsDefinite(A) then
    if assigned O`TwoSidedIdealClassMaps then
      X:= O`TwoSidedIdealClassMaps[1];
      h:= X[1];
      G:= Domain(h);
    else
      h:= GetTwoSidedIdealClassMapDefinite(O);
      G:= Domain(h);
      X:= < h, {}, &join [ _Support(Norm(g @ h)) : g in Generators(G) ] >;
      O`TwoSidedIdealClassMaps := [* X *];
      if IsEmpty(Support) or X[3] subset Support then
        return G, h;
      end if;
    end if;

    // Looks like we have to adjust the map h.
    // Let's see what we got to work with.
    Words:= {@ g: g in G | _Support(Norm(g @ h)) subset Support @};
    List:= [ s @ h : s in Words ];
    gens:=  [ G | S.i : i in [1..Ngens(S)] ] where S:= sub< G | Words >;
    Q, hh:= quo< G | gens >;

    if not flat then
      // add the central elements first.
      for p in Support do
        // This just costs the factorization of the norm
        I:= ideal< O | p >;
        I`LeftOrder:= O; I`RightOrder:= O;
        if not flat then I`Norm:= p^2; end if;
        g:= I @@ h;
        o:= Order(g @ hh);
        if o ne 1 then
          addfactor(~List, ~Words, I, g, O, o);
          Append(~gens, g);
          Q, hh:= quo< G | gens >;
          if #Q eq 1 then break; end if;
        end if;
      end for;
    end if;

    if #Q ne 1 then
      // apparently we cannot do without the factors from the CommutatorIdeal.
      FD:= FactoredDiscriminant(O);
      FD:= [ f : f in FD | f[1] in Support ] cat [ f : f in FD | f[1] notin Support ];
      C:= CommutatorIdeal(O);
      for f in FD do
        nrm:= f[1]^f[2];
        I:= ideal< O | nrm > + C;
        I`LeftOrder:= O; I`RightOrder:= O;
        if not flat then I`Norm:= nrm; end if;
        g:= I @@ h;
        o:= Order(g @ hh);
        if o ne 1 then
          addfactor(~List, ~Words, I, g, O, o);
          Append(~gens, g);
          Q, hh:= quo< G | gens >;
          if #Q eq 1 then break; end if;
        end if;
      end for;
    end if;

    error if #Q ne 1, "The given support was too small";
    assert #{#G, #List, #Words} eq 1;
    h:= map< G -> PowerIdeal(O) | x:-> List[Index(Words, x)], y:-> y @@ h >;
  else
    // Indefinite case.
    // Recomputing is not more expensive than fixing an already existing map
    // since the cost comes from multiplying ideals entirely.
    h:= GetTwoSidedIdealClassMapIndefinite(O, Support);
    G:= Domain(h);
  end if;

  X:= < h, Support, &join [ _Support(Norm(g @ h)) : g in Generators(G) ] >;
  if assigned O`TwoSidedIdealClassMaps then
    Append(~O`TwoSidedIdealClassMaps, X);
  else
    O`TwoSidedIdealClassMaps := [* X *];
  end if;
  return G, h;
end intrinsic;


intrinsic TwoSidedIdealClasses(O :: AlgAssVOrd : Support:= []) -> SeqEnum
 { A system of representatives for the twosided ideal classes of O.
   Support can be set to a sequence of prime ideals that generate the
   class group of the base ring. In that case the representents will
   have norm only supported in Support and the ramified primes of O}

  require Type(Algebra(O)) eq AlgQuat: 
    "Currently, we only support quaternion orders";

  G, h:= TwoSidedIdealClassGroup(O : Support:= Support);
  return [ g @ h : g in G ];
end intrinsic;
