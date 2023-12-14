freeze;

//////////////////////////////////////////////////////////////////////////////
//
// Hilbert modular forms: Main routines for the definite algorithm
//
// Original version by Lassina Dembele, October 2008
//
// Substantially rewritten and extended by Steve Donnelly
//
// Last modified November 2013
//
//////////////////////////////////////////////////////////////////////////////

// hack begins
// We replace the import by our own function
// import "hackobj.m" : HMF0;
import "../hackobj.m" : HMF0;
import "../hecke_field.m" : WeightRepresentation;
// hack ends

import "hecke.m" : please_report, pseudo_inverse, basis_is_honest;

import "precompute.m" : get_rids, get_tps;

import "proj1.m" : residue_class_reps;

debug := false;

//////////////////////////////////////////////////////////////////////////////

/* Here we define several record formats. */

ProjectiveLineData:=recformat<FD:SeqEnum,                  // This is a fundamental domain for the the
                                                           // for the action of the unit group on 
							   // in some quaternion algebra on P^1(O/n).

                              Stabs:SeqEnum,               // Generators of the group of stabilizers, for each element in FD.

                              StabOrders:SeqEnum,          // Order of the group of stabilizers, for each element in FD.

                              P1List:SetIndx,              // Elements of the projective line P^1(O/n).

                              P1Rep:UserProgram,           // Function sending [u,v] to an element of P1List.

			      Lookuptable:Assoc,           // Array indexed by P1List with values < FD index, unit index >

			      splitting_map,               // The splitting map mod n for the quaternion order.

             		      Level:RngOrdIdl>;            // The level.
                              

ModFrmHilDirFact:=recformat<PLD,                           // A record with format ProjectiveLineData.

                            CFD:SetIndx,                   // Contributing elements of FD.

                            basis_matrix:Mtrx,             // The rows of this matrix provide a basis for
                                                           // the direct factor of the HMS.

                            basis_matrix_inv:Mtrx,         // basis_matrix*basis_matrix_inv=id.

                            weight_rep:Map,                // The splitting map B -> M_2(K)^g -> GL(V_k) by 
			    				   // which the quaternion algebra acts on the 
							   // weight space V_k.

                            weight_dimension:RngIntElt,    // Dimension of weight space.                
            
                            weight_base_field,             // The base field of the weight representation.

			    max_order_units:SeqEnum>;      // The unit group in the maximal order.

////////////////////////////////////////////////////////////////////////////
// Low-level interface to the raw definite spaces.
// This is a quick first draft, and may change completely in later versions.

hmf_raw_definite_record := recformat< QuaternionOrder, 
                                      EichlerLevel,
                                      SplittingMap,
                                      RightIdealClassReps, 
                                      Basis
                                    >;

forward HilbertModularSpaceDirectFactors;

intrinsic InternalHMFRawDataDefinite(M::ModFrmHil : Verbose:=true) -> Rec
{For a space M of Hilbert modular forms computed using the definite algorithm,
this provides access to the underlying space of quaternionic forms.
WARNING: this may change completely in later versions of Magma!!!}

  F := BaseField(M);
  ZF := Integers(F);
  QO := QuaternionOrder(M);
  N := Level(M);
  k := Weight(M);
  weight2 := Seqset(k) eq {2};

  require IsDefinite(M) : 
         "The given space is not computed with the definite algorithm";
  require weight2 : "Currently available only for parallel weight 2";
  require not assigned M`Ambient :
         "This space is computed as a subspace of another space: use M`Ambient";

  // Compute the space, if not already done
  HMDFs := HilbertModularSpaceDirectFactors(M);
  PLD1 := HMDFs[1]`PLD;

  Rec := rec< hmf_raw_definite_record | >;

  Rec`RightIdealClassReps := get_rids(M);
  Rec`EichlerLevel := PLD1`Level;
  Rec`SplittingMap := PLD1`splitting_map;

  if Minimum(N) ne 1 then 
    Rec`Basis :=  [* HMDF`PLD`FD : HMDF in HMDFs *];
  end if;

  if Verbose then
    printf "\nInternal data for:\n%o\n\n", M; 
    if Minimum(N) eq 1 then
      print "The basis is given by \'RightIdealClassReps\'."; 
    else
      printf "The basis is given by \'Basis\': this is a list containing,\n"*
             "for each ideal in \'RightIdealClassReps\', a sequence of\n"*
             "elements (expressed as 2 x 1 matrices) in P^1 of %O modulo\n%o\n", 
             ZF, "Minimal", Rec`EichlerLevel;
    end if;
    if weight2 then
      printf "\nThe space is larger than the space of cusp forms:\n"*
             "it contains the %o Eisenstein series of level 1.\n", 
             #NarrowClassGroup(ZF);
    end if;
    printf "\n";
  end if;

  return Rec;
end intrinsic;

forward HeckeOperatorDefiniteBig;

intrinsic InternalHMFRawHeckeDefinite(M::ModFrmHil, p::RngOrdIdl) -> Mtrx
{The Hecke operator T_p on the raw space containing M}

  require not assigned M`Ambient :
         "This space is computed as a subspace of another space: use M`Ambient";

  return HeckeOperatorDefiniteBig(M, p);
end intrinsic;

intrinsic HeckeMatrixRaw(M::ModFrmHil, p::RngOrdIdl) -> Mtrx
{"}//"
  require not assigned M`Ambient :
         "This space is computed as a subspace of another space: use M`Ambient";

  return HeckeOperatorDefiniteBig(M, p);
end intrinsic;

////////////////////////////////////////////////////////////////////////////

function IsSIntegral(x,S) // (x::FldNumElt, S::SeqEnum[RngOrdIdl]) -> BoolElt, RngOrdElt, RngOrdElt
//  Given an element x in a number field F and a sequence of primes S in F, this determines whether x is
//  S-integral or not. If so, returns two algebraic integers a and b such that x=a/b, with b an S-unit.

   error if not forall{p: p in S|IsPrime(p)}, "The sequence of ideals in second argument must be prime!";
   
   if forall{p: p in S|Valuation(x, p) ge 0} then
      F:=Parent(x); O:=Integers(F);
      a:=Numerator(x); d:=Denominator(x);
      val_seq:=[-Valuation(O!d, p): p in S];
      n:=WeakApproximation(S, val_seq);
//     assert (a*n in O) and forall{p: p in S|Valuation(d*n, p) eq 0};
      return true, O!(a*n), O!(d*n);
   else
      return false, _, _;
   end if; 
end function;


function SIntegralPseudoBasis(OH,S) // (OH::AlgAssVOrd, S::SeqEnum) -> SeqEnum
//  Given a maximal order OH and a sequence of prime ideals S, this returns a new pseudo-basis 
//   <I_i, e_i>, i=1,..,4, such that v_p(I_i)>=0 for all p in S. 
   
   error if not forall{p: p in S|IsPrime(p)}, "Elements in the second argument must be primes!";

   OHB:=PseudoBasis(OH); H:=Algebra(OH); O:=Order(OHB[1][1]); NOHB:=[];
   for l:=1 to 4 do
      d:=Denominator(OHB[l][1]);
      T:=[p: p in SequenceToSet([s[1]: s in Factorization(O!!(d*OHB[l][1]))] 
                                                        cat [s[1]: s in Factorization(d*O)] cat S)];
      T:=Sort(T, func<a,b|Norm(a)-Norm(b)>);
      scal:=WeakApproximation(T, [Valuation(OHB[l][1], pr): pr in T]);
      assert (scal in OHB[l][1]); // and (scal*OHB[l][2] in OH);
                                  // This scaling factor must belong to the ideal in the pseudo-basis.
      Append(~NOHB, <scal^-1*OHB[l][1], scal*OHB[l][2]>);
   end for;
   return NOHB;
end function;


function QuotientSplittingData0(OH, OHB, pr, e)
   // Given a maximal order OH, a prime ideal pr and an integer e, this return a sequence of matrices
   // (M_i) in M_2(OK/pr^e) which is a basis of the reduction OH\otimes OK/pr^e\cong M_2(OK/pr^e) as 
   // an (OK/pr^e)-algebra.

   assert IsPrime(pr); 
   assert forall{m: m in [1..4] | Valuation(OHB[m][1], pr) ge 0};

   OK:=Order(pr); R:=quo<OK|pr^e>; 
   embed_mats:=[];
   _, fp2, gp2:=pMatrixRing(OH, pr: Precision:=e+20);
   for m:=1 to 4 do    
      mat_ents:=Eltseq(fp2(OHB[m][2]));
      mat:=Matrix(OK, 2, [OK!(R!(OK!(s@@gp2))): s in mat_ents]);
      Append(~embed_mats, mat);
   end for;

   return embed_mats;
end function;



function QuotientSplittingData(OH, d)
   // Given a maximal order OH and an ideal d, this return a sequence of matrices (M_i) in M_2(OK/d) which 
   // form a basis of the reduction OH\otimes (OK/d)\cong M_2(OK/d) as an (OK/d)-algebra.

   if Minimum(d) eq 1 then
      OHBd:=PseudoBasis(OH); splitting_mats:=[MatrixRing(Order(d), 2)!1: m in [1..4]];
   else 
      OK:=Order(d); div_fact:=Factorization(d); Sd:=[s[1]: s in div_fact];
      div_seq:=[div_fact[m][1]^div_fact[m][2]: m in [1..#div_fact]];
      OHBd:=SIntegralPseudoBasis(OH, Sd);
      embed_mats:=[QuotientSplittingData0(OH, OHBd, div_fact[l][1], div_fact[l][2]): l in [1..#div_fact]];
      splitting_mats:=[];
      for l:=1 to 4 do
         split_mat_ents:=[];
         for m:=1 to 4 do
            elt_red_comp:=[Eltseq(embed_mats[n][l])[m]: n in [1..#div_fact]];
            Append(~split_mat_ents, CRT(elt_red_comp, div_seq));
         end for;
         Append(~splitting_mats, Matrix(OK, 2, split_mat_ents));
      end for;
   end if;
   return OHBd, splitting_mats;
end function;


// ResidueMatrixRing: the intrinsic returns a Map, not a UserProgram
// (but within package code, avoid this extra layer of time-wasting: 
//  use _ResidueMatrixRing instead)

/* This is now in C
function InternalResidueMatrixRingSub(xxx, d, mats, cobi)
   // d    = RngOrdIdl with order OK
   // mats = sequence of 2x2 matrices over OK
   // cobi = 4x4 matrix over K
   // q (below) = AlgQuatElt over K

   "WARNING: Not using internal InternalResidueMatrixRingSub!!!";

   OK := Order(d);
   K  := NumberField(OK);
   Rd := quo<OK|d>;

   // Use coercion OK!Rd!x because x may have denominators (prime to d)

   function split_map(q)
      c := Vector(K, Eltseq(q)) * cobi;
      mat := Matrix(OK, 2, 2, []);
      for l := 1 to 4 do
         mat +:= (OK!Rd!c[l]) * mats[l];
      end for;
      return mat;
   end function;

   return split_map;
end function;
*/

function _ResidueMatrixRing(OH, d)

   K := NumberField(Order(d));
   OHB, mats := QuotientSplittingData(OH, d); 
   cobi := Matrix(K, [Eltseq(s[2]): s in OHB]) ^ -1;

   return InternalResidueMatrixRingSub(Algebra(OH), d, mats, cobi);
end function;

declare attributes AlgAssVOrd: ResidueMatrixRings;

intrinsic ResidueMatrixRing(OH::AlgAssVOrd, d::RngOrdIdl) -> AlgMat, Map
   {Given a maximal order OH in a quaternion algebra H over a number field F, 
    and an integral ideal d of the ring of integers O of F that is coprime to 
    the discriminant of OH, this returns a residue map OH -> Mat_2(O/d).  This map 
    can be applied to any element of H that is integral locally at primes dividing d.}

   // check cache
   if not assigned OH`ResidueMatrixRings then
      OH`ResidueMatrixRings := AssociativeArray(PowerIdeal(BaseRing(OH)));
   end if;
   bool, m := IsDefined(OH`ResidueMatrixRings, d);
   if bool then 
      return Codomain(m), m;
   end if;

   H := Algebra(OH);

   require BaseRing(OH) eq Order(d) : 
          "The second argument must be an ideal of the base ring of the first argument";
   require Norm(d + Discriminant(H)) eq 1 : 
          "The quaternion order does not split at the given ideal";
   
   split_map := _ResidueMatrixRing(OH, d);

   MO2 := MatrixRing(BaseRing(OH), 2);
   m := map< H -> MO2 | q :-> split_map(q) >;

   OH`ResidueMatrixRings[d] := m;
   return MO2, m;
end intrinsic;



/* The following two routines define the weight representation of a quaternion order OH modulo a prime pr 
   in the base maximal order O of OH. This is a map OH -> GL(2,F) -> GL(V), where F is an extension of
   O/pr. The map is then extended to all pr-integral elements in H. */

function weight_rep_pr(q, pr, hp, F, split_matpr, a_seq, b_seq)
   if IsSIntegral(Trace(q), [pr]) and IsSIntegral(Norm(q), [pr]) then
      weight_output:=MatrixRing(F, 1)!1; l_F:=Characteristic(F);
      matq:=Matrix(F, 2, [hp(s): s in Eltseq(split_matpr(q))]);
      for l2:=1 to #b_seq do
         frob:=l_F^(l2-1); matq1:=Matrix(F, 2, [a^frob: a in Eltseq(matq)]);
         matq2:=Determinant(matq1)^a_seq[l2]*SymmetricPower(matq1, b_seq[l2]-1);
         weight_output:=TensorProduct(weight_output, matq2);
      end for;
      return weight_output;
   else
      return 0;
   end if;
end function;



/* Here we define the weight representation in characteristic zero. 

   Representation at the ith place is det^(m[i]) tensor Sym^(n[i]). 
   Here n[i] = k[i] - 2, and n[i] + 2*m[i] = C (a constant).
   We take C = Max(k) - 2.  The central character is z :-> Norm(z)^C.
*/

intrinsic IsArithmeticWeight(F::Fld, k::SeqEnum[RngIntElt] : CentralCharacter:="default")
       -> BoolElt, SeqEnum, SeqEnum
   {Given a totally real number field F and a sequence k of integers, this determines whether 
    k is an arithmetic weight for F. 
    If so, integer sequences m and n are returned, and also an integer C.
    The representation on the ith infinite place of F is det^(m[i]) tensor Sym^(n[i]).
    This has central character t :-> Norm(t)^C }
  
   require Type(F) eq FldRat or ISA(Type(F), FldAlg) and IsAbsoluteField(F) :
          "The first argument should be Q or an absolute extension of Q";
   require Degree(F) eq #k: 
          "The number of components of k must equal the degree of the base field";
   if not forall{m: m in k| IsEven(m) and (m ge 2)} and
      not forall{m: m in k| IsOdd(m) and (m ge 2)} 
   then
     return false, _, _; 
   end if;

   if Type(CentralCharacter) eq RngIntElt then
     C := CentralCharacter;
     kmax := Max(k);
     require C ge kmax - 2 and IsEven(C - kmax) : 
            "Invalid value given for CentralCharacter";
   else
     C := Max(k) - 2;
   end if;

   n := [k[i] - 2 : i in [1..#k]];
   m := [Integers()| (C - n[i])/2 : i in [1..#k]];

//printf "Arithmetic weight: m = %o, n = %o, C = %o\n", m, n, C;
   return true, m, n, C;
end intrinsic;



// Tensor product is associative; for efficiency always do
// TensorProduct(small_mat, large_mat)

function weight_map_arch(q, splittings, K, m, n)
   d := #m;
   M := MatrixRing(K,1)!1;
   for l := d to 1 by -1 do 
      if m[l] eq 0 and n[l] eq 0 then
         // don't need to modify M
         continue;
      else
         matq := splittings[l](q);
         if n[l] eq 0 then
            M *:= Determinant(matq)^m[l];
         else
            if n[l] eq 1 then
               Ml := matq;
            else  
               Ml := SymmetricPower2(matq, n[l]);
            end if;
            if m[l] ne 0 then
               Ml *:= Determinant(matq)^m[l];
            end if;
            if l eq d then
               M := Ml;
            else
               M := TensorProduct(Ml, M);
            end if;
         end if;
      end if;
   end for;
   return M;
end function;


/*
function WeightRepresentation(M) // ModFrmHil -> Map
//  Given a space of Hilbert modular forms over a totally real number field F. This determines if the 
//  weight k is an arithmetic. If so, an extension of F which is Galois over Q and splits H is found. Then,
//  map H^* -> GL(2, K)^g -> GL(V_k) is contructed, where g is the degree of F and V_k the weight space.

   if assigned M`weight_rep then
      return M`weight_rep, M`weight_dimension, M`weight_base_field;
   else
      H:=Algebra(QuaternionOrder(M)); 
      F:=BaseField(H); 
      k:=M`Weight;
      bool, m, n, C := IsArithmeticWeight(F,k);  
      assert bool;
      assert C eq M`CentralCharacter;

      if Seqset(k) eq {2} then // parallel weight 2
         I := IdentityMatrix(Rationals(), 1);
         Mat1 := Parent(I);
         M`weight_rep := map< H -> Mat1 | q :-> I >;
         M`weight_base_field := Rationals();
         M`weight_dimension := 1; 
      else
         // define weight_base_field = extension K/F containing Galois closure of F and 
         // containing a root of every conjugate of the minimal polynomial of H.1
         if assigned F`SplittingField then
           K,rts:=Explode(F`SplittingField);
         else
           K,rts:=SplittingField(F : Abs:=true, Opt:=false);
           F`SplittingField:=<K, rts>;
         end if;
         embeddings_F_to_K:=[hom<F->K | r> : r in rts];
         H1coeffs:=Coefficients(MinimalPolynomial(H.1));
         alphas:=[K| ];
         for FtoK in embeddings_F_to_K do
             hh:=PolynomialRing(K)! [c@FtoK : c in H1coeffs];
             if IsIrreducible(hh) then
                K:=ext<K|hh>;
                alphas:=ChangeUniverse(alphas,K) cat [K.1];
            else
                Append(~alphas, Roots(hh)[1][1]);
            end if;
         end for;
         // make weight_base_field an (optimized) absolute field, for efficiency in later calculations 
         weight_field := K; // names appears in verbose output
         K := AbsoluteField(K);
         K := OptimizedRepresentation(K);
         embeddings_F_to_K := [hom<F->K | K!r> : r in rts]; // same embeddings, now into extended field K
         M`weight_base_field:=K;
         vprintf ModFrmHil: "Field chosen for weight representation:%O", weight_field, "Maximal";
         vprintf ModFrmHil: "Using model of weight_field given by %o over Q\n", DefiningPolynomial(K);

         assert H.1*H.2 eq H.3; // this is assumed in the defn of the splitting homomorphism below
         splitting_seq:=[];
         for i:=1 to Degree(F) do
            h:=embeddings_F_to_K[i];
            // need a splitting homomorphism (H tensor K) -> Mat_2(K) whose restriction to K is h 
            alpha:=alphas[i];
            b:= K! h(F!(H.2^2));
            iK:=Matrix(K, 2, [alpha, 0, 0, -alpha]); 
            jK:=Matrix(K, 2, [0, 1, b, 0]); 
            kK:=iK*jK;
            assert K! h(H.3^2) eq (kK^2)[1,1]; 
            Append(~splitting_seq, 
                   map< H -> MatrixRing(K,2)|
                        q:-> h(s[1])+h(s[2])*iK+h(s[3])*jK+h(s[4])*kK where s:=Eltseq(q) >);
         end for;
         M`weight_dimension := &* [x+1 : x in n];
         M2K:=MatrixRing(K, M`weight_dimension);
         M`weight_rep:=map<H -> M2K|q :-> weight_map_arch(q, splitting_seq, K, m, n)>;
      end if;
      return M`weight_rep, M`weight_dimension, M`weight_base_field;
   end if;
end function;
*/


// Canonical representatives of elements of the projective line $P^1(OK/level)$ 

// For a vector v = (a,b) in OK^2, this determines whether v defines an element in P^1(OK/d). 
// Returns a representative (a0, b0) such that, writing d = d1 * d2 where d1 = gcd(d,aa), 
// we have a0 == 1 mod d1 and b0 == 1 mod d2

// TO DO: The third argument is unused!

function _ProjectiveLineRepresentative(v, d, xxx : check1 := true)

   OK:=Order(d); 
   if check1 and Minimum(d) eq 1 then
      return true, Matrix(OK,2,1,[0,0]), OK!1;
   end if;

   // the most frequent case is d = d1, the least frequent is d = d2

   aa,bb:=Explode(Eltseq(v));
   gcd1 := aa*OK + d; 
   d1_eq_d := Minimum(gcd1) eq 1;
   if d1_eq_d then
      d2:=1*OK;
      d1:=d; 
   elif gcd1 + bb*OK ne 1*OK then
      return false, _, _;
   else
      d2:=&*[p[1]^p[2] : p in Factorization(d) | Valuation(aa,p[1]) ne 0];
      d1:=OK!!(d/d2);
   end if;

   if d1_eq_d then
      s:= aa mod d;  b:= (bb*Modinv(s,d)) mod d;  a:= OK!1;
   elif d2 eq d then
      s:= bb mod d;  a:= (aa*Modinv(s,d)) mod d;  b:= OK!1;
   else
      a1:= aa mod d1;  b1:= (bb*Modinv(a1,d1)) mod d1;
      b2:= bb mod d2;  a2:= (aa*Modinv(b2,d2)) mod d2;
      a:=CRT(d1, d2, OK!1, a2);
      b:=CRT(d1, d2, b1, OK!1);
      s:=CRT(d1, d2, a1,   b2);
      // this is crucial (CRT satisfies this):
      // assert a eq a mod d; assert b eq b mod d; assert s eq s mod d;
   end if;

   return true, Matrix(OK, 2, 1, [a,b]), s;
end function;


function ProjectionMap(v, d, Rd, P1rep)
   // Given an element in the projetive space $P^(OK/level)$, and a divisor $d$ of $level$, this returns
   // its projection onto $P^1(OK/d)$.

   OK:=Order(d); 
   mat:= Matrix(OK, 2, 1, [OK!(Rd!s): s in Eltseq(v)]); // TO DO: skip?
   _, mat:=P1rep(mat, false, false);
   return mat;
end function;


/* The following routines compute the orbits of a unit group in a quaternion order acting on a
   projective line $P^1(O/d)$ for some ideal d in the ring of integer of a number field. Also, we compute
   the corresponding coinvariant module that defines a direct factor the space of Hilbert modular forms.*/

function _ProjectiveLine(d) // RngOrdIdl -> SetIndx
//  Given an integral ideal d in the ring of integers O_K of a number field K, 
//  this returns the projective line P^1(O_K/d)

   if Minimum(d) eq 1 then
      return {@ Matrix(Order(d), 2, 1, [0,0]) @};
   end if;

   proj_card:=1; d_facts:=Factorization(d);
   for s in d_facts do
      proj_card:=proj_card*(Norm(s[1])+1)*Norm(s[1])^(s[2]-1);
   end for;

   OK:=Order(d); R, h:=quo<OK|d>; div_seq:=Divisors(d);
   _, n_seq:=residue_class_reps(d);
   Rset:=[OK!(R![s[m]: m in [1..#s]]): s in Set(CartesianProduct(<[0..n_seq[l]-1]: l in [1..#n_seq]>))];
   proj:=[Matrix(OK, 2, 1, [1, a]): a in Rset];
   for A in div_seq do
      if (Norm(A) ne 1) and (GCD(A, OK!!(d*A^-1)) eq 1*OK) then
         radA:=Radical(A); 
         d_fact:=Factorization(A);
         B:=OK!!(A*radA^-1); 
         C:=OK!!(d*A^-1); 
         _, nB:=residue_class_reps(B); 
         _, nC:=residue_class_reps(C);
         RB:=[OK![s[m]: m in [1..#s]]: s in Set(CartesianProduct(<[0..nB[l]-1]: l in [1..#nB]>))];
         u:=OK!WeakApproximation([s[1]: s in d_fact], [1: l in [1..#d_fact]]);
         RC:=[OK![s[m]: m in [1..#s]]: s in Set(CartesianProduct(<[0..nC[l]-1]: l in [1..#nC]>))]; 
         S:=[[OK!(R!CRT([a*u,1], [A,C])), OK!(R!CRT([1,b], [A,C]))]: a in RB, b in RC];
         proj:=proj cat [Matrix(OK, 2, 1, s): s in S];
      end if;
   end for;
   assert #proj eq proj_card;
   return {@ p : p in Sort(proj) @};
end function;

function minimal_generators(G)
   gens0 := Generators(G);
   gens := [];
   S := sub<G | >;
   for g in gens0 do 
      if g notin S then
         Append(~gens, g);
         S := sub<G | gens>;
         if S eq G then
            break g;
         end if;
      end if;
   end for;
   return gens;
end function;

function ProjectiveLineOrbits(P1, P1rep, d, unit_map, units, split_map : DoStabs:=true)
   // d is an ideal in the ring of integers of a number field, 
   // P1 is ProjectiveLine(d) which comes with the function P1rep,
   // unit_map is the map returned by UnitGroup for a quaternion order O,
   // units contains its images, in a fixed ordering,
   // split_map is the map to the ResidueMatrixRing(O,d).
   // Returns the orbits of the unit group acting on P1, 
   // and the stabilizers of the first element in each orbit.
  
   OK := Order(d); 
   Rd := quo<OK|d>;
   _, n_seq := residue_class_reps(d);

   U := Domain(unit_map);
   UU := Universe(units);
   assert Type(UU) eq AlgQuat;
   assert units[1] in {UU|1,-1};
   split_units := [u @ split_map : u in units];

   Lookuptable := AssociativeArray(P1);

   if Minimum(d) eq 1 then  // the trivial case
      Lookuptable[P1[1]] := < 1, 1 >;
      PLD := rec< ProjectiveLineData |
                  Level := d,
                  P1List := P1,
                  P1Rep := P1rep,
                  FD := [P1[1]],
                  Lookuptable := Lookuptable,
                  StabOrders := [#units],
                  splitting_map:=split_map 
                >;
      if DoStabs then
         PLD`Stabs := [[ [* UU!(u@unit_map), 1 *]
                       : u in minimal_generators(sub< U | [u@@unit_map : u in units] >)]];
      end if;
      return PLD;
   end if;

   FD := [Universe(P1)| ]; 
   Stabs := [];
   StabOrders := [Integers()| ];

   elts := Set(P1);
 
   vprintf ModFrmHil, 2: "ProjectiveLineOrbits: "; 
   vtime ModFrmHil, 2:

   while not IsEmpty(elts) do 
      e := Rep(elts);
      Append(~FD, e);
      orbit := {};
      stab := [];
      // run through images of e under units,
      // TO DO: skip acting by units[1] = +-1
      for j := 1 to #units do
         e0 := split_units[j] * e;
         _, e1 := P1rep(e0, false, false);
         if e1 notin orbit then
            Exclude(~elts, e1);
            Include(~orbit, e1);
            Lookuptable[e1] := < #FD, j >;
         elif e1 eq e then
            Append(~stab, [* units[j] *]);
         end if;
      end for;

      // assert #units eq (1+#stab) * #orbit;
      Append(~StabOrders, 1+#stab);

      if DoStabs then
         // want stab to contain just generators of the stabilizer
         stab_U := [s[1] @@ unit_map : s in stab];
         stab_U_gens := minimal_generators(sub< U | stab_U >);
         stab_gens := [stab[i] : i in [1..#stab] | stab_U[i] in stab_U_gens];
         Append(~Stabs, stab_gens);
      end if;
   end while;

   vprintf ModFrmHil, 2: "Stabilizers %o\n", Multiset(StabOrders);

   PLD := rec< ProjectiveLineData |
               Level:=d,
               P1List:=P1,
               P1Rep:=P1rep,
               FD:=FD,
               Lookuptable:=Lookuptable,
               StabOrders:=StabOrders,
               splitting_map:=split_map
          >;
   if DoStabs then
      PLD`Stabs:=Stabs;
   end if;
   return PLD;

end function;



function InvariantSpace(stab, weight_map, weight_dim, wt_base_field)
   // Given a stabilizer stab (as sequence of quaternions), and a weight representation, 
   // this returns the corresponding invariant space. 

   A:=Domain(weight_map); 
   F:=wt_base_field; 
   V:=VectorSpace(F, weight_dim); 
   V1:=V;
   S := [A| u@Umap : u in Generators(U)] where U, Umap := UnitGroup(BaseField(A));
   S cat:= [s[1] : s in stab | s[1] notin {A|1,-1}]; 
   for s in S do 
      w := weight_map(s);
      V1 meet:= Kernel(w - IdentityMatrix(F, weight_dim));
      if Rank(V1) eq 0 then break; end if;
   end for;

   return BasisMatrix(V1);
end function;


// This is called by HilbertModularSpaceDirectFactors (now only for nontrivial weight)
// P1 = projective line mod d, 
// LO is a quaternion order, 
// split_map LO -> M_2(O/d),
// weight_map = weight_rep

function HMSDF(P1, P1rep, LO, d, split_map, weight_map, weight_dim, wt_base_field)

   U, unit_map:=UnitGroup(LO); 
   units:=[Algebra(LO)! unit_map(s): s in U];
   PLD:=ProjectiveLineOrbits(P1, P1rep, d, unit_map, units, split_map); 
   F:=wt_base_field;
   stabs:=PLD`Stabs; 
   l:=1; 
   repeat 
      M:=InvariantSpace(stabs[l], weight_map, weight_dim, F);
      if Rank(M) eq 0 then l:=l+1; end if;
   until (l gt #stabs) or (Rank(M) ne 0);

   if l gt #stabs then
      return rec<ModFrmHilDirFact|PLD:=PLD, CFD:={@ @}, basis_matrix:=ZeroMatrix(F, 0, 0), 
                 basis_matrix_inv:=ZeroMatrix(F, 0, 0), weight_rep:=weight_map, 
                 weight_dimension:=weight_dim, weight_base_field:=F, max_order_units:=units>;
   else
      contrib_orbs:=[l];
      for m0:=l+1 to #stabs do
         N:=InvariantSpace(stabs[m0], weight_map, weight_dim, F);
         if Rank(N) ne 0 then
            Append(~contrib_orbs, m0);
            nb_rows:=Nrows(M)+Nrows(N); 
            nb_cols:=Ncols(M)+Ncols(N);
            Q:=RMatrixSpace(F, nb_rows, nb_cols)!0; 
            InsertBlock(~Q, M, 1, 1);
            InsertBlock(~Q, N, Nrows(M)+1, Ncols(M)+1); 
            M:=Q;
         end if;
      end for;
      contrib_orbs := {@ x : x in contrib_orbs @}; // SetIndx is better than SeqEnum
   end if;
   N:=Transpose(Solution(Transpose(M), ScalarMatrix(F, Rank(M), 1)));

   return rec<ModFrmHilDirFact|PLD:=PLD, CFD:=contrib_orbs, basis_matrix:=M, basis_matrix_inv:=N, 
   	  		        weight_rep:=weight_map, weight_dimension:=weight_dim, 
                                weight_base_field:=F, max_order_units:=units>;
end function;


// The space M is a direct sum of one "direct factor" (or "component")
// for each right ideal class

function HilbertModularSpaceDirectFactors(M)
  
   if not assigned M`ModFrmHilDirFacts then 
      
      F := BaseField(M);
      A := Algebra(QuaternionOrder(M));
      d := Level(M)/Discriminant(A);

      vprintf ModFrmHil, 2: "Projective line modulo ideal of norm %o: ", Norm(d);
      vtime ModFrmHil, 2:
      P1, P1rep := ProjectiveLine(quo<Order(d)|d> : Type:="Matrix");

      if not assigned M`splitting_map then
         M`splitting_map := _ResidueMatrixRing(M`QuaternionOrder, d);
      end if;
      split_map := M`splitting_map;

      LOs := [I`LeftOrder: I in get_rids(M)]; 

      if Seqset(Weight(M)) eq {2} then // parallel weight 2

         HMDFs := [];
         Q := Rationals();

         for LO in LOs do 

            U, mU := UnitGroup(LO); 
            units := [A| s @ mU : s in U];

            PLD := ProjectiveLineOrbits(P1, P1rep, d, mU, units, split_map : DoStabs:=false);

            dim := #PLD`FD;
            Id := MatrixRing(Rationals(), dim) ! 1;

            Append(~HMDFs, 
               rec< ModFrmHilDirFact | 
                    PLD := PLD, 
                    CFD:= IndexedSet([1 .. dim]), // TO DO: get rid of this, and the basis_matrices
                    basis_matrix := Id, 
                    basis_matrix_inv := Id, 
                    weight_dimension := 1, 
                    weight_base_field := Q, 
                    max_order_units := units
                  > );
         end for;

      else 

         if not assigned M`weight_rep then
            _ := WeightRepresentation(M);
         end if;
 
         wr := M`weight_rep;
         wd := M`weight_dimension;
         wF := M`weight_base_field;
 
         HMDFs := [HMSDF(P1, P1rep, LO, d, split_map, wr, wd, wF) : LO in LOs];

      end if; // parallel weight 2

      M`ModFrmHilDirFacts := HMDFs;
   end if;
   
   return M`ModFrmHilDirFacts;
end function;



function InnerProductMatrixBig(M)
  if not assigned M`InnerProductBig then
    assert not assigned M`Ambient;
    bool, w := IsParallelWeight(M);
    if bool and w eq 2 then
      // Weight 2: inner product is given by the usual mass = 1/#stabilizer
      easy := Level(M) eq Discriminant(QuaternionOrder(M));
      rids := get_rids(M);
      unit_orders := [#UnitGroup(LeftOrder(I)) : I in rids];
      ulcm := LCM(unit_orders);
      if easy then
        masses := [Integers()| ulcm div u : u in unit_orders];
      else
        HMDFs := HilbertModularSpaceDirectFactors(M); assert #HMDFs eq #rids;
        masses := [Integers()| ulcm div x : x in HMDFs[i]`PLD`StabOrders, i in [1..#rids]];
      end if;
      masses := [Integers()| x div g : x in masses] where g is GCD(masses);
      M`InnerProductBig := SparseMatrix(DiagonalMatrix(masses));
    else
      error "Only implemented for weight 2";
    end if;
  end if;
  return Matrix(M`InnerProductBig);
end function;


// Given a vector w of positive integers,
// return a basis matrix B for the orthogonal complement
// (preferably over Z to make Hecke matrices integral)
// and a pseudo inverse Bi

function Zcomplement(w)
  assert Universe(w) eq Integers();
  Q := Rationals();
  n := #w;
  g := GCD(w);
  k := Index(w, g);
  if k eq 0 then
    // TO DO: choose carefully
    g := Min(w);
    k := Index(w, g);
  end if;
  // B  : basis of the kernel of w
  // Bi : pseudo inverse, B*Bi = I
  B := Matrix(Q, n-1, n, []);
  Bi := Matrix(Q, n, n-1, []);
  for i := 1 to k-1 do
    B[i,i] := 1;
    B[i,k] := -w[i]/g;
    Bi[i,i] := 1;
  end for;
  for i := k+1 to n do
    B[i-1,i] := 1;
    B[i-1,k] := -w[i]/g;
    Bi[i,i-1] := 1;
  end for;
  assert IsOne(B * Bi);
  return B, Bi;
end function;


// In parallel weight 2, there are Eisenstein series in the raw space.
// They are easy to write down as "indicator vectors" corresponding 
// to ideal classes.
// TO DO: if CentralCharacter is not 0, can't easily write down the eigenvectors,
// but instead can compute the subspace using that its dimension = h and that it 
// is killed by T_p^e - (Np+1)^e , where e is the exponent of the narrow class group.

function EisensteinBasis(M)
  if assigned M`eisenstein_basis then
    return M`eisenstein_basis;
  end if;

  // M must be an ambient of weight 2
  assert not assigned M`Ambient;
  assert Seqset(Weight(M)) eq {2};

  Cl, Clmap := NarrowClassGroup(BaseField(M));
  // list elts in the same order as the rids
  Clelts := [Cl | cl : cl in Cl]; 
  eltseqs := [Eltseq(cl) : cl in Cl];
  ParallelSort(~eltseqs, ~Clelts); 

  rids := get_rids(M);
  easy := Level(M) eq Discriminant(QuaternionOrder(M));

  if easy then
    // basis is given by rids
    Eis := Matrix(Integers(), #Cl, #rids, []);
    for j := 1 to #rids do 
      cl := Norm(rids[j]) @@ Clmap;
      i := Index(Clelts, cl);
      Eis[i,j] := 1;
    end for;
  else
    b := [Ncols(X`basis_matrix) : X in M`ModFrmHilDirFacts];
    Eis := Matrix(Integers(), #Cl, &+b, []);
    bsum := 0;
    for k := 1 to #b do
      cl := Norm(rids[k]) @@ Clmap;
      i := Index(Clelts, cl);
      for j := bsum + 1 to bsum + b[k] do 
        Eis[i,j] := 1;
      end for;
      bsum +:= b[k];
    end for;
  end if;

  // Check Eis consists of consecutive blocks of ones
  assert Eis eq EchelonForm(Eis);
  assert &+ Eltseq(Eis) eq Ncols(Eis);

  Eis := ChangeRing(Eis, Rationals());
  M`eisenstein_basis := Eis;
  return Eis;
end function;


procedure RemoveEisenstein(~M)
  vprintf ModFrmHil: "Quotienting out the Eisenstein subspace: ";
  time0_eis := Cputime();

  Eis := EisensteinBasis(M);

  IP := InnerProductMatrixBig(M);
  assert IsDiagonal(IP);
  IP := Diagonal(IP);

  Q := Rationals(); // = hecke_matrix_field = weight_base_field
  CEis := Matrix(Q, 0, 0, []);
  BMI := Matrix(Q, 0, 0, []);
  
  b := [&+Eltseq(Eis[i]) : i in [1..Nrows(Eis)]];
  bsum := 0;
  for k := 1 to #b do 
    w := IP[ bsum + 1 .. bsum + b[k] ];
    bsum +:= b[k];
    C, Cinv := Zcomplement(w);
    CEis := DiagonalJoin(CEis, C);
    BMI := DiagonalJoin(BMI, Cinv);
  end for;

  M`basis_matrix := CEis;
  M`basis_matrix_inv := BMI;
  M`basis_is_honest := true;

  if debug then
    dim := Nrows(M`basis_matrix);
    assert Rank(M`basis_matrix) eq dim;
    assert M`basis_matrix * M`basis_matrix_inv eq IdentityMatrix(Q, dim);
  end if;

  vprintf ModFrmHil: "%os\n", Cputime(time0_eis);
end procedure;


// Main function for the basis of a definite space

// Only to be called by basis_matrix, Dimension and within this file;
// and M`basis_matrix, M`basis_matrix_big etc are assigned only here.

// Returns two matrices A and B such that 
// M is given by the rows of A, with A*B=I
// The base ring of A and B is M`weight_base_field

forward ComputeBasisMatrixOfNewSubspaceDefinite;

function BasisMatrixDefinite(M : EisensteinAllowed:=false)

   if assigned M`basis_matrix then
      return M`basis_matrix, M`basis_matrix_inv, M`Dimension;
   elif EisensteinAllowed and not assigned M`Ambient and 
      assigned M`basis_matrix_big 
   then
      return M`basis_matrix_big;
   end if;

   if assigned M`Ambient then

      ComputeBasisMatrixOfNewSubspaceDefinite(M);
      dim := Nrows(M`basis_matrix);

   else // M is ambient

      weight2 := Seqset(Weight(M)) eq {2};

      if not assigned M`basis_matrix_big then
        easy := weight2 and Level(M) eq Discriminant(QuaternionOrder(M));
        // easy = basis of space is given by the rids (ie each P^1 is trivial)

        if weight2 then
          M`weight_base_field := Rationals();
          M`weight_dimension := 1;
        end if;

        if easy then
          // basis of M is given by rids
          d := #get_rids(M);
          Id := MatrixAlgebra(Rationals(), d) ! 1;
          M`basis_matrix_big := Id;
          M`basis_matrix_big_inv := Id;
        else
          HMDF := HilbertModularSpaceDirectFactors(M);
          nrows := &+ [Nrows(HMDF[m]`basis_matrix): m in [1..#HMDF]];
          ncols := &+ [Ncols(HMDF[m]`basis_matrix): m in [1..#HMDF]];
          B := Matrix(BaseRing(HMDF[1]`basis_matrix), nrows, ncols, []);
          row := 1; 
          col := 1;
          for hmdf in HMDF do 
             if not IsEmpty(hmdf`CFD) then
                InsertBlock(~B, hmdf`basis_matrix, row, col);
                row +:= Nrows(hmdf`basis_matrix);
                col +:= Ncols(hmdf`basis_matrix);
             end if;
          end for;
          Binv := Transpose(Solution(Transpose(B), IdentityMatrix(BaseRing(B), Nrows(B))));
          M`basis_matrix_big := B; 
          M`basis_matrix_big_inv := Binv; 
        end if;
      end if;
        
      if weight2 and not EisensteinAllowed then
        RemoveEisenstein(~M);
        dim := Nrows(M`basis_matrix);
      elif weight2 then
        dim := Nrows(M`basis_matrix_big) - #NarrowClassGroup(BaseField(M));
      else
        M`basis_matrix := M`basis_matrix_big;
        M`basis_matrix_inv := M`basis_matrix_big_inv;
        dim := Nrows(M`basis_matrix);
      end if;

   end if;

   if not assigned M`Dimension then
      M`Dimension := dim;
   else 
      error if M`Dimension ne dim,
           "The space has been computed incorrectly!!!\n" * please_report;
   end if;
  
   // Retrieve the answer (now cached)
   return BasisMatrixDefinite(M : EisensteinAllowed:=EisensteinAllowed);
end function;


/********************************************************************
  HECKE OPERATORS AND DEGENERACY MAPS                    
*********************************************************************/

// TO DO: sparse

function HeckeOperatorDefiniteBig(M, p : Columns:="all")

   assert not assigned M`Ambient; // M is an ambient

   // Caching
   // HeckeBig and HeckeBigColumns must be assigned together

   cached, Tp := IsDefined(M`HeckeBig, p);
   if cached then 
     Tp := Matrix(Tp);
     _, old_cols := IsDefined(M`HeckeBigColumns, p);
     if Columns cmpeq "all" then
       Columns := [1..Ncols(Tp)];
     end if;
     columns := [j : j in Columns | j notin old_cols];
     if IsEmpty(columns) then
       return Tp;
     end if;
   else
     old_cols := [];
     columns := Columns;
   end if;

   A := Algebra(QuaternionOrder(M));
   N := Level(M);
   weight2 := Seqset(Weight(M)) eq {2};
   easy := weight2 and N eq Discriminant(QuaternionOrder(M));
   // easy = basis of big space is given by the rids

   if not assigned M`basis_matrix then
     _ := BasisMatrixDefinite(M : EisensteinAllowed);
   end if;
   dim := Ncols(M`basis_matrix_big);

   F := M`weight_base_field; // = Q for parallel weight 2
   if easy then
     h := dim;
   else
     HMDF := M`ModFrmHilDirFacts; 
     nCFD := [#xx`CFD : xx in HMDF];
     h := #HMDF;
     wd := M`weight_dimension; // = 1 for weight2
   end if;

   // Columns/columns refer to actual columns of the big matrix, 
   // Bcolumns to columns of large blocks, bcolumns to small blocks

   if columns cmpeq "all" then
     columns := [1..dim];
   else
     columns := Sort([Integers()| i : i in columns]);
   end if;
   assert not IsEmpty(columns) and columns subset [1..dim];

   if not weight2 then // currently, higher weight doesn't use Columns
     columns := [1 .. dim];
   end if;

   if easy then
     bcolumns := columns;
     Bcolumns := columns;
   elif columns eq [1 .. dim] then // full matrix 
     bcolumns := [1 .. dim div wd];
     Bcolumns := [1 .. h];
   elif weight2 then 
     bcolumns := columns;
     Bcolumns := [];
     b := 1;
     for i := 1 to #HMDF do
       e := b + nCFD[i] - 1;
       if exists{x: x in [b..e] | x in columns} then
         Append(~Bcolumns, i);
       end if;
       b := e + 1;
     end for;
   else
     bcolumns := [];
     Bcolumns := [];
     b := 1;
     for i := 1 to #HMDF do
       for j := 1 to nCFD[i] do
         e := b + wd - 1;
         if exists{x: x in [b..e] | x in columns} then
           Append(~bcolumns, e div wd);
           Append(~Bcolumns, i);
         end if;
         b := e + 1;
       end for;
     end for;
   end if;

   if not cached then
     Tp := MatrixRing(F, dim) ! 0; 
   end if;

//"Starting with"; Tp;

//"Columns:"; Columns; old_cols; columns; bcolumns; Bcolumns;

   tp := get_tps(M, p : rows:=Bcolumns); // rows in precompute_tps are columns here

   vprintf ModFrmHil: "%o%o column%o%o of big Hecke matrix (norm %o): ", 
                      #columns eq dim select "All " else "", 
                      #columns, 
                      #columns gt 1 select "s" else "", 
                      #columns gt 1 select "" else " (#"*Sprint(columns[1])*")", 
                      Norm(p);
   vtime ModFrmHil:

   if easy then

      for j in Bcolumns, i in [1..h] do 
         bool, tpji := IsDefined(tp, <j,i>);
         if bool then
            Tp[i,j] := #tpji;
         end if;
      end for;

   else

     sm := M`splitting_map;
     
     checkP1 := Valuation(N,p) gt 0;

     inds := [l : l in [1..#HMDF] | nCFD[l] ne 0];
     row := 0; 
     col := 0;

     for m in inds do 
        if m in Bcolumns then
           for l in inds do 
              bool, tpml := IsDefined(tp, <m,l>);
              if bool then
                 if weight2 then

                    PLDl := HMDF[l]`PLD;
                    FDl   := PLDl`FD; 
                    FDm   := HMDF[m]`PLD`FD; 
                    lookup:= PLDl`Lookuptable; 
                    P1rep := PLDl`P1Rep;

                    Tplm := ExtractBlock(Tp, row+1, col+1, #FDl, #FDm);
                    mms := [mm : mm in [1..#FDm] | col+mm in bcolumns];
                    for ll := 1 to #tpml do
                       mat := tpml[ll] @ sm;
                       for mm in mms do 
                          u := mat * FDm[mm];
                          bool, u0 := P1rep(u, checkP1, false);
                          if bool then
                             n := lookup[u0,1]; 
                             // assert n eq Index(HMDF[l]`CFD, n);
                             Tplm[n,mm] +:= 1;
                          end if;
                       end for;
                    end for;
                    InsertBlock(~Tp, Tplm, row+1, col+1);

                 else

                    PLDl  := HMDF[l]`PLD;
                    FDl   := PLDl`FD; 
                    FDm   := HMDF[m]`PLD`FD; 
                    lookup:= PLDl`Lookuptable; 
                    P1rep := PLDl`P1Rep;

                    CFDl := HMDF[l]`CFD; 
                    CFDm := HMDF[m]`CFD; 
                    units1 := HMDF[l]`max_order_units; 
                    weight_map := HMDF[l]`weight_rep; 

                    Tplm := Matrix(F, wd*#CFDl, wd*#CFDm, []);

                    for ll := 1 to #tpml do
                       mat := tpml[ll] @ sm;
                       for mm := 1 to #CFDm do
                          u := mat * FDm[CFDm[mm]];
                          bool, u0 := P1rep(u, checkP1, false);
                          if bool then
                             elt_data := lookup[u0]; 
                             n := Index(CFDl, elt_data[1]);
                             if n ne 0 then
                                quat1 := units1[elt_data[2]]^-1 * tpml[ll]; 
                                X := ExtractBlock(Tplm, (n-1)*wd+1, (mm-1)*wd+1, wd, wd);
                                X +:= weight_map(quat1);
                                InsertBlock(~Tplm, X, (n-1)*wd+1, (mm-1)*wd+1);
                             end if;
                          end if;
                       end for;
                    end for;
                    InsertBlock(~Tp, Tplm, row+1, col+1);

                 end if;
              end if;
              row +:= nCFD[l] * wd;
           end for;
        end if;
        col +:= nCFD[m] * wd;
        row := 0;
     end for;

   end if;

   // new columns were computed, so renew the cache
   M`HeckeBig[p] := SparseMatrix(Tp);
   M`HeckeBigColumns[p] := Sort(old_cols cat columns);
//"Now got columns",  M`HeckeBigColumns[p]; M`HeckeBig[p];

   // Check Hecke invariance of Eisenstein subspace and its complement
   if debug and M`HeckeBigColumns[p] eq [1..dim] then
     if assigned M`InnerProductBig and Norm(p + N) eq 1 
        and p@@cl eq NCl.0 where NCl, cl is NarrowClassGroup(BaseField(M))
     then
       assert Tp * M`InnerProductBig eq M`InnerProductBig * Transpose(Tp);
     end if;
     if assigned M`eisenstein_basis then
       assert Rowspace(M`eisenstein_basis * Tp) subset Rowspace(M`eisenstein_basis);
     end if;
     if assigned M`basis_matrix then
       printf "[debug] Checking space is preserved by Tp: "; time 
       assert Rowspace(M`basis_matrix * Tp) subset Rowspace(M`basis_matrix);
     end if;
   end if;

   return Tp;
end function;



// TO DO: columns option

function AtkinLehnerDefiniteBig(M, p)

   assert not assigned M`Ambient; // M is an ambient

   if not assigned M`ALBig then
      M`ALBig := AssociativeArray(Parent(p));
   else
      cached, Wp := IsDefined(M`ALBig, p);
      if cached then
         return Matrix(Wp);
      end if;
   end if;

   N := Level(M) / Discriminant(QuaternionOrder(M));
   e := Valuation(N, p); 
   assert e gt 0;
   pe := p^e;
   NN := N/pe;
   assert ISA(Type(NN), RngOrdIdl); // integral
   ZF := Order(p);
   quope, modpe := quo<ZF|pe>;
   _, P1pe := ProjectiveLine(quope : Type:="Vector");
   // TO DO: if pe = N, use existing P1N

   if not assigned M`basis_matrix then
     _ := BasisMatrixDefinite(M : EisensteinAllowed);
   end if;
   dim := Ncols(M`basis_matrix_big);

   HMDF := M`ModFrmHilDirFacts; 
   nCFD := [#xx`CFD : xx in HMDF];
   h := #HMDF;
   wd := M`weight_dimension; // = 1 for weight2
   F := M`weight_base_field; // = Q for weight2
   sm := M`splitting_map;

   tp := get_tps(M, pe);

   weight2 := Seqset(Weight(M)) eq {2};

   Wp := MatrixRing(F, dim) ! 0; 

   // block[l] = sum of dimensions of blocks [1..l-1]
   block := [0 : l in [1..#HMDF]];
   for l := 1 to #HMDF-1 do
      block[l+1] := block[l] + nCFD[l];
   end for;

   inds := [l : l in [1..#HMDF] | nCFD[l] ne 0];

   for m in inds do 
      ls := {@ l : l in inds | IsDefined(tp, <m,l>) @};

      tp_split_N := AssociativeArray(ls);
      tp_split_pe := AssociativeArray(ls);
      tp_ker := AssociativeArray(ls);
      tp_elt := AssociativeArray(ls); // used when not weight2
      for l in ls do 
         tp_split_N[l]  := {@ @};
         tp_split_pe[l] := {@ @};
         tp_ker[l]      := {@ @};
         tp_elt[l]      := {@ @};
         for t in tp[<m,l>] do
            // this is where we get rid of the extra elements in tps (if e > 1)
            tsN := t@sm;
            tspe := Matrix(2, [x@modpe : x in Eltseq(Transpose(tsN))]);
            bool, tk := P1pe(ChangeRing(Kernel(tspe).1,ZF), true, false);
            if bool then
               Include(~tp_split_N[l],  tsN);
               Include(~tp_split_pe[l], tspe);
               Include(~tp_ker[l],      tk);
               Include(~tp_elt[l],      t);
            end if;
         end for;
         if debug then
            assert forall{t : t in tp_split_pe[l] | Determinant(t) eq 0};
            assert forall{t : t in tp_split_pe[l] | #Kt eq Norm(pe) and Kt subset sub<Kt|Kt.1> where Kt is Kernel(t)};
            assert forall{t : t in tp_split_pe[l] | #It eq Norm(pe) and It subset sub<It|It.1> where It is Image(t)};
            // Kt and It are rank 1 modules; basis in Howell normal form can have 2 elements, but the first generates it
         end if;
      end for;
      if debug and #inds eq #HMDF then
         // The elements tp[<m,?>] are in bijection with P1 under the map t :-> ker(t mod p)
         assert # &join [tp_ker[l] : l in ls] eq (Norm(p)+1)*Norm(p)^(e-1);
      end if;
   
      FDm := HMDF[m]`PLD`FD; 
      for mm in HMDF[m]`CFD do

         // identify the unique t which kills this element in P1 mod p
         _, vpe := P1pe(Eltseq(FDm[mm]), false, false);
         if debug then
            assert #{l : l in ls | vpe in tp_ker[l]} eq 1;
         end if;
         for l_ in ls do
            k := Index(tp_ker[l_], vpe);
            if k ne 0 then
               l := l_;
               break;
            end if;
         end for;

         // get image mod p and then mod N
         imt := Image(tp_split_pe[l,k]);  
         impe := ChangeUniverse(Eltseq(Basis(imt)[1]), ZF);
         if IsOne(NN) then
            imN := impe;
         else
            tv := Eltseq(tp_split_N[l,k] * FDm[mm]);
            imN := [ZF| ChineseRemainderTheorem(pe, NN, impe[i], tv[i]) : i in [1,2]];
         end if;
         // get rep in P1 mod N
         PLDl := HMDF[l]`PLD;
         if debug then
            bool, imN := PLDl`P1Rep(Matrix(1, imN), true, false); assert bool;
         else
            _, imN := PLDl`P1Rep(Matrix(1, imN), false, false);
         end if;

         if weight2 then

            ll := PLDl`Lookuptable[imN, 1];  
            assert ll gt 0;

            r := block[l] + ll;
            c := block[m] + mm;
            assert Wp[r,c] eq 0;
            Wp[r,c] := 1;

         else

            ll, u := Explode(PLDl`Lookuptable[imN]);
            assert ll gt 0;
            rr := Index(HMDF[l]`CFD, ll) - 1;
            cc := Index(HMDF[m]`CFD, mm) - 1;
            assert rr ge 0;
            assert cc ge 0;
            if rr ge 0 then
               r := (block[l] + rr) * wd + 1;
               c := (block[m] + cc) * wd + 1;
               assert IsZero(Submatrix(Wp, r, c, wd, wd));

               units1     := HMDF[l]`max_order_units; 
               weight_map := HMDF[l]`weight_rep; 

               quat1 := units1[u] ^ -1 * tp_elt[l,k];
               InsertBlock(~Wp, weight_map(quat1), r, c);
            end if;

         end if;
           
      end for; // mm
   end for; // m
  
   M`ALBig[p] := SparseMatrix(Wp);
   return Wp;
end function;


// The operator from level N to level N/p 
// given by double cosets of diagonal matrix [1,p]

function DegeneracyDownpDefiniteBig(M, p)

   N := Level(M);
   vp := Valuation(N, p); 
   assert vp gt 0;
 
   D := HeckeOperatorDefiniteBig(M, p);
 
   if vp eq 1 then
      D +:= AtkinLehnerDefiniteBig(M, p);
   end if;
 
   return D;
end function;


// Partition P^1(N) into congruence classes mod N/p
// ie fibres of the map P^1(N) -> P^1(N/p)
// We could do this with P1rep calls in either P^1(N) or P^1(N/p)
// Either way, we would need one P1rep call per element of P^1(N)
// Use P^1(N/p) because the smaller P^1 will sometimes be cheaper

function P1_congruence_classes(P1N, N, Np)

   P1Np, P1repNp := ProjectiveLine(quo<Order(Np)|Np> : Type:="Vector");

   C := [{@ P1N | @} : x in P1Np];
   for v in P1N do
      vNp := Vector([x mod Np : x in Eltseq(v)]);
      _, vNp1 := P1repNp(vNp, false, false);
      i := Index(P1Np, vNp1);
      Include(~C[i], v);
   end for;

   if debug then
      p := N/Np;
      num := Valuation(Np,p) eq 0 select Norm(p)+1 else Norm(p);
      assert forall{c : c in C | #c eq num};
      assert &join C eq P1N;
   end if;

   return C;

end function;


// Up1 and Down1 have a lot in common
// (but keep separate, since we always call only one or the other)

// The operator from level N to level N/p 
// given by double cosets of the identity matrix

function DegeneracyDown1DefiniteBig(M, p)  

   assert not assigned M`Ambient; // M is an ambient

   if not assigned M`DegDown1Big then
      M`DegDown1Big := AssociativeArray(Parent(p));
   else
      cached, D := IsDefined(M`DegDown1Big, p);
      if cached then
         return Matrix(D);
      end if;
   end if;

   N := Level(M) / Discriminant(QuaternionOrder(M));
   Np := N/p;
   assert ISA(Type(Np), RngOrdIdl); // integral

   if not assigned M`basis_matrix then
      _ := BasisMatrixDefinite(M : EisensteinAllowed);
   end if;
   dim := Ncols(M`basis_matrix_big);

   HMDF := M`ModFrmHilDirFacts; 
   h := #HMDF;
   wd := M`weight_dimension; // = 1 for weight2
   F := M`weight_base_field;

   P1N := HMDF[1]`PLD`P1List;

   assert forall{x : x in HMDF | IsIdentical(x`PLD`P1List, P1N)};
   // (the same P1 was attached to each block)

   C := P1_congruence_classes(P1N, N, Np);

   weight2 := Seqset(Weight(M)) eq {2};
assert weight2;
assert M`DirichletCharacter cmpeq 1;

   // TO DO: easy case where N/p = 1, get the matrix just using stab_orders

   D := MatrixRing(F, dim) ! 0; 
   row := 0; 

   for l := 1 to #HMDF do 

      dl := wd*#HMDF[l]`CFD;
      if dl eq 0 then
assert false;
         continue;
      end if;

      FDl    := HMDF[l]`PLD`FD; 
      lookup := HMDF[l]`PLD`Lookuptable; 

      Dl := MatrixRing(F, dl) ! 0;

      ii := {};
      for i := 1 to #FDl do
         if i in ii then
            continue;
         end if;

         v := FDl[i];

         // find the congruence class of v
         assert exists(c){c : c in C | v in c}; 
         
         // express its congruence class as an indicator vector relative to FDl
         cvec := Matrix(F, #FDl, 1, []);
         for y in c do
            n := lookup[y,1];
            cvec[n,1] +:= 1;
         end for;

         // each element of FDl which meets the class c has image given by the row cvec
         s := {t[1] : t in Support(cvec)};
         ii := ii join s;
         for j in s do
            InsertBlock(~Dl, cvec, 1, j);
         end for;

      end for;
      assert #ii eq #FDl;

      InsertBlock(~D, Dl, row+1, row+1);
      row +:= dl;
   end for; // l

   M`DegDown1Big[p] := SparseMatrix(D);
   return D; 
end function;


/************ NOT USED YET

// Stuff used in both Up1 and Upp

function DegeneracyUpDefiniteBigStuff(M, p)  

   N := Level(M) / Discriminant(QuaternionOrder(M));
   Np := N/p;
   assert ISA(Type(Np), RngOrdIdl); // integral

   if not assigned M`basis_matrix then
      _ := BasisMatrixDefinite(M : EisensteinAllowed);
   end if;
   dim := Ncols(M`basis_matrix_big);

   HMDF := M`ModFrmHilDirFacts; 
   h := #HMDF;
   wd := M`weight_dimension; // = 1 for weight2
   F := M`weight_base_field;

   assert forall{l : l in [1..#HMDF] | #HMDF[l]`CFD gt 0};

   P1N := HMDF[1]`PLD`P1List;

   assert forall{x : x in HMDF | IsIdentical(x`PLD`P1List, P1N)};
   // (the same P1 was attached to each block)

   P1Np, P1repNp := ProjectiveLine(quo<Order(Np)|Np> : Type:="Vector");

   C := P1_congruence_classes(P1N, N, Np);

   Orbits := [* *];

   for l := 1 to #HMDF do
      FDl := HMDF[l]`PLD`FD; 
      lookup := HMDF[l]`PLD`Lookuptable; 

      // Important: 
      // these are not the orbits given by ProjectiveLineOrbits(P1Np),
      // so the degeneracy matrices do not give maps between the spaces

      // TO DO: fast

      function P1Np_rep(x)
         assert exists(i){i : i in [1..#P1Np] | x in C[i]};
         return P1Np[i];
      end function;
      orbits := {@ {P1Np_rep(x) : x in P1N | lookup[x,1] eq i} : i in [1..#FDl] @};
U := &cat [Setseq(o) : o in orbits];
assert #U eq #P1Np;
assert Seqset(U) eq P1Np;

      Append(~Orbits, orbits);
   end for;

   return <HMDF, h, wd, F, dim, N, Np, P1N, P1Np, C, Orbits>;
end function;


// The operator from level N/p to level N 
// given by double cosets of the identity matrix

function DegeneracyUp1DefiniteBig(M, p, stuff)

   assert not assigned M`Ambient; // M is an ambient

   if not assigned M`DegUp1Big then
      M`DegUp1Big := AssociativeArray(Parent(p));
   else
      cached, D := IsDefined(M`DegUp1Big, p);
      if cached then
         return Matrix(D);
      end if;
   end if;

   weight2 := Seqset(Weight(M)) eq {2};
assert weight2;
assert M`DirichletCharacter cmpeq 1;

   // TO DO: easy case where N/p = 1

   HMDF, h, wd, F, dim, N, Np, P1N, P1Np, C, Orbits := Explode(stuff);

   D := < >;

   for l := 1 to #HMDF do 
      // dl := wd * #HMDF[l]`CFD;
      FDl := HMDF[l]`PLD`FD; 
      orbits := Orbits[l];

      Dl := RMatrixSpace(F, #orbits, #FDl) ! 0;
      ii := {};
      for i := 1 to #FDl do
         if i in ii then
            continue;
         end if;
         v := FDl[i];

         assert exists(rv){P1Np[c] : c in [1..#P1Np] | v in C[c]};
         assert exists(j){j : j in [1..#orbits] | rv in orbits[j]};

         Dl[j, i] := 1;
      end for;

      Append(~D, Dl);
   end for;

   D := DiagonalJoin(D);

   M`DegUp1Big[p] := SparseMatrix(D);
   return D; 
end function;


// The operator from level N/p to level N/p 
// given by double cosets of diagonal matrix [p,1]

function DegeneracyUppDefiniteBig(M, p, stuff)

   assert not assigned M`Ambient; // M is an ambient

   if not assigned M`DegUppBig then
      M`DegUppBig := AssociativeArray(Parent(p));
   else
      cached, D := IsDefined(M`DegUppBig, p);
      if cached then
         return Matrix(D);
      end if;
   end if;

   weight2 := Seqset(Weight(M)) eq {2};
assert weight2;
assert M`DirichletCharacter cmpeq 1;

   // TO DO: easy case where N/p = 1

   HMDF, h, wd, F, dim, N, Np, P1N, P1Np, C, Orbits := Explode(stuff);

   tp := get_tps(M, p);

   D := < >;

   for l := 1 to #HMDF do 
      // dl := wd * #HMDF[l]`CFD;
      FDl := HMDF[l]`PLD`FD; 
      orbits := Orbits[l];

      Dl := RMatrixSpace(F, #orbits, #FDl) ! 0;

      for i := 1 to #FDl do
         // TO DO ???
         // if i in ii then
         v := FDl[i];

         t := tp elt "associated" to v mod p

         assert exists(rv){P1Np[c] : c in [1..#P1Np] | v in C[c]};
         rvt := rv * t;
         assert exists(j){j : j in [1..#orbits] | rvt in orbits[j]};

         Dl[j, i] := 1;
      end for;

      Append(~D, Dl);
   end for;

   D := DiagonalJoin(D);

   M`DegUppBig[p] := SparseMatrix(D);
   return D;
end function;


function DegeneracyImage(M, p)

// if D1 not cached...
   stuff := DegeneracyUpDefiniteBigStuff(M, p);
   D1    := DegeneracyUp1DefiniteBig(M, p, stuff);

   AL := AtkinLehnerDefiniteBig(M, p);
   Dp := D1 * AL;

   return VerticalJoin(D1, Dp);
end function;

************/


// The following functions are for degeneracy maps 
// in the upward direction, from lower level to higher level.
// Only implemented when p divides the level only once.

function DegeneracyMapBlock(M1, M2, Tp, sm)

   M1PLD  := M1`PLD;
   M2PLD  := M2`PLD;
   d1     := M1PLD`Level; 
   d2     := M2PLD`Level; 
   FD1    := M1PLD`FD; 
   FD2    := M2PLD`FD; 
   P1rep1 := M1PLD`P1Rep;
   P1rep2 := M2PLD`P1Rep;
   lookup := M1PLD`Lookuptable; 

   F := M1`weight_base_field; 
   w := M1`weight_dimension; 

   Rd1 := quo< Order(d1) | d1 >; // TO DO: don't need this?

   if w eq 1 then // parallel weight 2

      B := Matrix(F, w*#FD1, w*#FD2, []);

      for l := 1 to #Tp do
         tpl := Tp[l] @ sm;
         for m:=1 to #FD2 do
            u := tpl * FD2[m];
            bool, u0 := P1rep2(u, true, false);
            if bool then 
               u01 := ProjectionMap(u0, d1, Rd1, P1rep1); 
               n := lookup[u01,1]; 
               // assert n gt 0;
               // assert n eq Index(M1`CFD, n);
               B[n,m] +:= 1;
            end if;
         end for;
      end for;
                 
   else

      units1:=M1`max_order_units; 
      weight_map:=M1`weight_rep; 
      CFD1:=M1`CFD; 
      CFD2:=M2`CFD; 

      B := Matrix(F, w*#CFD1, w*#CFD2, []);

      for l := 1 to #Tp do
         tpl := Tp[l] @ sm;
         for m := 1 to #CFD2 do
            u := tpl * FD2[CFD2[m]];
            bool, u0 := P1rep2(u, true, false);
            if bool then 
               u01 := ProjectionMap(u0, d1, Rd1, P1rep1); 
               elt_data := lookup[u01]; 
               n := Index(CFD1, elt_data[1]);
               if n ne 0 then 
                  quat1:=units1[elt_data[2]]^-1*Tp[l]; 
                  mat1:=ExtractBlock(B, (n-1)*w+1, (m-1)*w+1, w, w);
                  mat1+:=weight_map(quat1);
                  InsertBlock(~B, mat1, (n-1)*w+1, (m-1)*w+1);
               end if;
            end if;
         end for;
      end for;

   end if; // parallel weight 2

   return B;
end function;


// The upward degeneracy map from M1 to M2, where q*Level(M1) = Level(M2)
// for some prime q, and either p = q or p = (1)
// Only valid if M1 was created as a DegeneracyMapDomain of M2.

function DegeneracyMap(M1, M2, p : Big:=false)

   assert IsPrime(p) or Norm(p) eq 1;
   assert GCD(p*(M1`Level), M2`Level) eq p*(M1`Level);
   assert IsIdentical(M1`QuaternionOrder, M2`QuaternionOrder);
   assert IsIdentical(M1`splitting_map, M2`splitting_map); 
   if Seqset(Weight(M1)) ne {2} then // nontrivial weight
      assert IsIdentical(M1`weight_rep, M2`weight_rep); 
   end if;

   HMDF1 := HilbertModularSpaceDirectFactors(M1);
   HMDF2 := HilbertModularSpaceDirectFactors(M2);

   if Minimum(p) eq 1 then
      tp:=AssociativeArray(CartesianProduct([1..#HMDF1],[1..#HMDF1]));
      for l:=1 to #HMDF1 do
         tp[<l,l>]:=[Algebra(M1`QuaternionOrder)!1];
      end for;
   else
      tp:=get_tps(M1,p);
   end if;

   F := M1`weight_base_field; 
   sm := M1`splitting_map;

   w1 := M1`weight_dimension;
   w2 := M2`weight_dimension;
   assert w1 eq w2;

   nCFD1 := [#xx`CFD : xx in HMDF1];
   nCFD2 := [#xx`CFD : xx in HMDF2];
   inds1 := [l : l in [1..#HMDF1] | nCFD1[l] ne 0];
   inds2 := [m : m in [1..#HMDF2] | nCFD2[m] ne 0];
   row := 1; 
   col := 1;
   D := Matrix(F, &+nCFD1 * w1, &+nCFD2 * w2, []); 

   for m in inds2 do
      for l in inds1 do 
         bool, tpml := IsDefined(tp, <m,l>);
         if bool then
            Dlm := DegeneracyMapBlock(HMDF1[l], HMDF2[m], tpml, sm);
            InsertBlock(~D, Dlm, row, col); 
//assert Nrows(Dlm) eq nCFD1[l] * w1;
//assert Ncols(Dlm) eq nCFD2[m] * w2;
         end if;
         row +:= nCFD1[l] * w1;
      end for;
      col +:= nCFD2[m] * w2;
      row := 1;
   end for;

   // Two differences here
   if Big then
      M1bm := BasisMatrixDefinite(M1 : EisensteinAllowed);
      return M1bm * D;
   else
      M1bm := BasisMatrixDefinite(M1);
      _, M2bmi := BasisMatrixDefinite(M2);
      return M1`basis_matrix * D * M2bmi;
   end if;

end function;


function DegeneracyMapDomain(M, d)
   // Given an ambient space M and an integral ideal d such that NewLevel(M) | d | Level(M), 
   // returns a space of level d and same weight as M, defined using internals that are
   // compatible with M (same quaternion algebra, same splitting map and weight representation)

   QO:=M`QuaternionOrder;
   assert NewLevel(M) eq Discriminant(QO);
   assert IsIntegral(d/NewLevel(M));
   assert IsIntegral(Level(M)/d); 

   // MUST use identical internal data: in particular, rids and weight_rep.
   // Call low-level constructor to avoid complications with caching, and don't cache DM
   // TO DO: use cached spaces, to avoid recomputing ModFrmHilDirFacts (that's the only advantage)
   DM:=HMF0(BaseField(M), d, NewLevel(M), DirichletCharacter(M), Weight(M), CentralCharacter(M));
   DM`QuaternionOrder:=QO;
   DM`rids:=get_rids(M);
   DM`splitting_map:=M`splitting_map; // can use same splitting_map even though its level is larger than needed
   DM`weight_base_field:=M`weight_base_field;
   DM`weight_dimension:=M`weight_dimension;
   if Seqset(Weight(M)) ne {2} then // nontrivial weight
      DM`weight_rep:=M`weight_rep; print "in DM";
   end if;
   return DM;
end function;


// Basis of a newspace (called only by BasisMatrixDefinite)

procedure ComputeBasisMatrixOfNewSubspaceDefinite_general(M)
   assert IsDefinite(M); 
   MA := M`Ambient; // must be assigned with QuaternionOrder (unless NewLevel = Level)
   A,B:= BasisMatrixDefinite(MA);

weight2 := Seqset(Weight(M)) eq {2};
assert not weight2;

   O := Integers(BaseField(M));
   D := Discriminant(QuaternionOrder(M));
   L := Level(M);
   Lnew := NewLevel(M);
   assert NewLevel(MA) eq D; 
   N := Lnew/D; 
   assert ISA(Type(N), RngOrdIdl); // integral
   Nfact := Factorization(N);

   V := VectorSpace(BaseRing(A), Nrows(A)); 
   W := sub<V|>;
   for m := 1 to #Nfact do
      if Dimension(W) eq Dimension(V) then 
         break; 
      end if;

      vprint ModFrmHil: "Computing oldforms relative to prime of norm", Norm(Nfact[m][1]);
      time0 := Cputime();
      IndentPush(); 
      N1 := DegeneracyMapDomain(MA, L/Nfact[m][1]);
      if Dimension(N1) eq 0 then
         IndentPop();
         continue;
      end if;

      P, eP := Explode(Nfact[m]);

      vprintf ModFrmHil: "Degeneracy maps between dimensions %o and %o: ", Dimension(MA), Dimension(N1);
      vtime ModFrmHil:
      D1 := DegeneracyMap(N1, MA, 1*O);

      if eP eq 1 then
         vtime ModFrmHil:
         D2old := DegeneracyMap(N1, MA, P);
      end if;

      if eP gt 1 or debug then
         AL := AtkinLehnerOperator(MA, P);
         D2new := D1 * AL;
      end if;

      D2 := eP eq 1 select D2old else D2new;
      old_space_mat := VerticalJoin(D1, D2);

      // checks
      if eP eq 1 then
         assert Rank(old_space_mat) eq 2*Rank(D1);
         assert Rank(old_space_mat) eq 2*Rank(D2);
         if debug then
            assert RowSpace(old_space_mat) eq RowSpace(D1) + RowSpace(D2new);
         end if;
      end if;

      vprintf ModFrmHil, 2: "Sum of oldspaces: ";
      vtime ModFrmHil, 2:
      W := W + RowSpace(old_space_mat);

      IndentPop(); 
      vprint ModFrmHil: "Time:", Cputime(time0);
      vprint ModFrmHil: "Remaining new space has dimension", Dimension(V) - Dimension(W);
   end for;

   M`basis_is_honest := false;
   M`basis_matrix_wrt_ambient := BasisMatrix(Complement(V, W));
   M`basis_matrix_wrt_ambient_inv := pseudo_inverse(M`basis_matrix_wrt_ambient, BasisMatrix(W));
   M`basis_matrix := M`basis_matrix_wrt_ambient * MA`basis_matrix;
   M`basis_matrix_inv := MA`basis_matrix_inv * M`basis_matrix_wrt_ambient_inv;
end procedure;

procedure ComputeBasisMatrixOfNewSubspaceDefinite(M)
   assert IsDefinite(M); 

   weight2 := Seqset(Weight(M)) eq {2};
   if not weight2 then
      // TO DO implement IP
      ComputeBasisMatrixOfNewSubspaceDefinite_general(M);
      return;
   end if;         

   MA := M`Ambient; // must be assigned with QuaternionOrder (unless NewLevel = Level)
   _ := BasisMatrixDefinite(MA : EisensteinAllowed);
   K := Rationals(); // TO DO: in general MA`weight_base_field;

   F := BaseField(M);
   D := Discriminant(QuaternionOrder(M));
   L := Level(M);
   Lnew := NewLevel(M);
   assert NewLevel(MA) eq D; 
   N := Lnew/D; 
   assert ISA(Type(N), RngOrdIdl); // integral
   assert not IsOne(N);

   vprintf ModFrmHil: "Degeneracy maps for (Eichler) level of norm %o = %o\n",
                       Norm(N), [<Norm(t[1]), t[2]>  : t in Factorization(N)];
   IndentPush();

   eisenstein_present := weight2;
   Ds := <>;
   for t in Factorization(N) do
      P, e := Explode(t);
/*
stuff := DegeneracyUpDefiniteBigStuff(MA, P);
D1new := DegeneracyUp1DefiniteBig(MA, P, stuff);
*/
      // Use upward or downward degeneracy maps? 
      use_up := e eq 1; // for now keep it simple, use up whenever possible

      check := debug and Norm(L) lt 1000 and e eq 1;

      if use_up or check then

         MP := DegeneracyMapDomain(MA, L/P);
         _ := BasisMatrixDefinite(MP : EisensteinAllowed);
         dP := Dimension(MP);
         if dP eq 0 then
            continue t;
         end if;

         vprintf ModFrmHil: "First upward degeneracy operator for prime of norm %o:\n", Norm(P);
         t0 := Cputime();
         IndentPush(); 
         D1 := DegeneracyMap(MP, MA, 1*Integers(F) : Big);
/*
assert    Nrows(D1) eq Nrows(D1new);
assert RowSpace(D1) eq RowSpace(D1new);
*/
         IndentPop(); 
         vprintf ModFrmHil: "%os\n", Cputime(t0);

         vprintf ModFrmHil: "Second upward degeneracy operator for prime of norm %o:\n", Norm(P);
         t0 := Cputime();
         IndentPush(); 
         DP := DegeneracyMap(MP, MA, P : Big);
         IndentPop(); 
         vprintf ModFrmHil: "%os\n", Cputime(t0);
/*
DI := DegeneracyImage(MA, P);
assert RowSpace(DI) eq RowSpace(VerticalJoin(D1,DP)); "okay up";
*/
         IP := ChangeRing(InnerProductMatrixBig(MA), K);
         D1 := Transpose(D1 * IP);
         DP := Transpose(DP * IP);

      end if;
      if not use_up then

         if check then
            D11 := D1;
            DP1 := DP;
            dP1 := dP;
         end if;

         dP := Dimension(NewSubspace(HilbertCuspForms(F, L/P, Weight(M)), D) : UseFormula:=false); 
         if check then
            assert dP eq dP1;
         end if;
         if dP eq 0 then
            continue t;
         end if;

         eisenstein_present := false; // the eisenstein part is not in these kernels

         vprintf ModFrmHil: "First downward degeneracy operator for prime of norm %o:\n", Norm(P);
         t0 := Cputime();
         IndentPush(); 
         D1 := DegeneracyDown1DefiniteBig(MA, P);
         IndentPop(); 
         vprintf ModFrmHil: "%os\n", Cputime(t0);
   
         vprintf ModFrmHil: "Second downward degeneracy operator for prime of norm %o:\n", Norm(P);
         t0 := Cputime();
         IndentPush(); 
         DP := DegeneracyDownpDefiniteBig(MA, P);
         IndentPop(); 
         vprintf ModFrmHil: "%os\n", Cputime(t0);

         // In this situation, delete the precomputation at large primes (or prime powers)
         // (it's too much memory, and the user is not likely to expect it has been done/saved)
         if Norm(P) gt 1000 then
            DeleteHeckePrecomputation(QuaternionOrder(MA), P);
         end if;

         // TO DO: why isn't the sum of the images equal to the P-oldspace?
         if check then
            printf "[debug] Checking that up/down degeneracy agree ... ";
            IP := ChangeRing(InnerProductMatrixBig(MA), K);
            E := Transpose(EisensteinBasis(MA) * IP);
            assert Kernel(HorizontalJoin(D1, DP)) eq Kernel(HorizontalJoin(<D11, DP1, E>));
            /*
            assert Kernel(D1) eq Kernel(HorizontalJoin(D11,E));
            assert Kernel(DP) eq Kernel(HorizontalJoin(DP1,E));
            */
            printf "okay\n";
         end if;

      end if;
/*
IP := ChangeRing(InnerProductMatrixBig(MA), K);
DI := DegeneracyImage(MA, P);
assert Kernel(HorizontalJoin(D1,DP)) eq Kernel(IP*Transpose(DI)); "okay down";
*/
      Append(~Ds, D1);
      Append(~Ds, DP);
   end for;

   if eisenstein_present then
     // the eisenstein part might not have been removed by the kernels
     IP := ChangeRing(InnerProductMatrixBig(MA), K);
     Append(~Ds, Transpose(EisensteinBasis(MA) * IP) );
   end if;

   IndentPop();

   vprintf ModFrmHil: "Kernel of degeneracy maps: ";
   vtime ModFrmHil:
   B := KernelMatrix(HorizontalJoin(Ds));
/*
IP := ChangeRing(InnerProductMatrixBig(MA), K);
for t in Factorization(N) do
 DI := DegeneracyImage(MA, t[1]);
 D1new := DegeneracyUp1DefiniteBig(MA, t[1], 0);
 assert B * IP * Transpose(D1new) eq 0;
 assert B * IP * Transpose(DI) eq 0;
end for;
*/
   vprintf ModFrmHil: "Inverse basis matrix for new space: "; 
   vtime ModFrmHil:
   M`basis_matrix_inv := Transpose(Solution(Transpose(B), MatrixRing(BaseRing(B),Nrows(B))!1));
   M`basis_matrix  := B; 
   M`basis_is_honest := true;
end procedure;

