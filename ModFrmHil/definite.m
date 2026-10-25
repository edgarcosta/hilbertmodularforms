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

import "hecke_field.m" : WeightRepresentation, hecke_matrix_field;
import "hecke.m" : please_report, pseudo_inverse, basis_is_honest, ComputeNewSubspaceBasisMatricesUsingHeckeAction;
import "weight_rep.m" : FiniteModulusCharFromHeckeChar, is_paritious;
import "precompute.m" : get_rids, get_tps;
import !"Geometry/ModFrmHil/proj1.m" : residue_class_reps;
import "hackobj.m" : HMF0;

debug := false;

//////////////////////////////////////////////////////////////////////////////

/* Here we define several record formats. */

ProjectiveLineData:=recformat<
  FD:SeqEnum,                  // This is a fundamental domain for the the
                               // for the action of the unit group on 
                               // in some quaternion algebra on P^1(O/n).

  Stabs:SeqEnum,               // Generators of the group of stabilizers, for each element in FD.

  StabOrders:SeqEnum,          // Order of the group of stabilizers, for each element in FD.

  P1List:SetIndx,              // Elements of the projective line P^1(O/n).

  P1Rep:UserProgram,           // Function sending [u,v] to an element of P1List.

  Lookuptable:Assoc,           // Array indexed by P1List with values < FD index, unit index >

  splitting_map:Map,           // The splitting map mod n for the quaternion order.

  Level:RngOrdIdl,             // The level.

  Quotient:Tup,                // The quotient ring ZF/N along with a map from
                               // ZF to the ring
                                                   
  Character,                   // 0 if the nebentypus is trivial.
                               // Otherwise, the output of 
                               // FiniteModulusCharFromHeckeChar applied
                               // to a Hecke character chi. 
                               
  CosetRepDict>;               // 0 if the nebentypus is trivial
                               // Otherwise, an array indexed by P1List.
                               // If the key is (b \\ d), 
                               // the value is a matrix (a b \\ c d) in GL2(ZF/N),
                               // i.e. a representative for (b \\ d) in GL2(ZF/N) / B
                               // where B is the lower triangular Borel. 


ModFrmHilDirFact:=recformat<
  PLD,                         // A record with format ProjectiveLineData.

  CFD:SetIndx,                 // Contributing elements of FD.

  basis_matrix:Mtrx,           // The rows of this matrix provide a basis for
                               // the direct factor of the HMS.

  basis_matrix_inv:Mtrx,       // basis_matrix*basis_matrix_inv=id.

  weight_rep:Map,              // The splitting map B -> M_2(K)^g -> GL(V_k) by 
                               // which the quaternion algebra acts on the 
                               // weight space V_k.

  weight_dimension:RngIntElt,  // Dimension of weight space.                

  weight_base_field,           // The base field of the weight representation.

  max_order_units:SeqEnum>;    // The unit group in the maximal order.

hmf_raw_definite_record := recformat< 
  QuaternionOrder, 
  EichlerLevel,
  SplittingMap,
  RightIdealClassReps, 
  Basis>;

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
function get_compositum_field(wt_base_field, chi)
  /*
   * Computes the compositum of the weight base field and the field of definition
   * of the nebentypus character chi. This is needed because twist_factor can
   * produce elements in the cyclotomic field when chi is nontrivial.
   *
   * Input:
   *   wt_base_field - The base field for the weight representation
   *   chi - The nebentypus character (GrpHeckeElt)
   *
   * Output:
   *   The compositum field over which quaternionic modular forms should be defined
   */
  if IsTrivial(chi) then
    // Trivial nebentypus case - just use the weight base field
    return wt_base_field;
  else
    // Nontrivial nebentypus - need compositum with cyclotomic field
    chi_field := (Order(chi) le 2) select Rationals() else CyclotomicField(Order(chi));
    if chi_field cmpeq Rationals() then
      return wt_base_field;
    else
      return Compositum(wt_base_field, chi_field);
    end if;
  end if;
end function;

declare attributes ModFrmHil : weight_base_field_twisted;

function big_hecke_matrix_field(M)
  /*
   * The stable field over which the definite big Hecke matrix (and the
   * weight-representation blocks it is assembled from) lives: the weight base
   * field, extended by Q(zeta_d) when the nebentypus is nontrivial (a no-op
   * for order <= 2). Unlike hecke_matrix_field, this field is NEVER descended
   * to the minimal field -- the big matrix is built once, before eigenform
   * extraction, and must stay consistent with its (undescended) blocks.
   *
   * It is MEMOIZED on M because get_compositum_field builds a fresh Compositum
   * on each call for order > 2, and Magma does not recognize independently
   * constructed isomorphic number fields as equal: without memoization the
   * several big-matrix call sites would each get a distinct field object and
   * InsertBlock/coercion between them would fail.
   */
  if not assigned M`weight_base_field_twisted then
    M`weight_base_field_twisted :=
      get_compositum_field(M`weight_base_field, DirichletCharacter(M));
  end if;
  return M`weight_base_field_twisted;
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
  if Type(CentralCharacter) eq RngIntElt then
     C := CentralCharacter;
     kmax := Max(k);
     require C ge kmax - 2 and IsEven(C - kmax) : 
            "Invalid value given for CentralCharacter";
   else
     C := Max(k) - 2;
   end if;

   n := [k[i] - 2 : i in [1..#k]];

   if not forall{m: m in k| IsEven(m) and (m ge 2)} and
      not forall{m: m in k| IsOdd(m) and (m ge 2)}
   then
     // TODO abhijitm this is terrible practice
     return false, _, n, C;
   end if;
   m := [Integers()| (C - n[i])/2 : i in [1..#k]];

//printf "Arithmetic weight: m = %o, n = %o, C = %o\n", m, n, C;
   return true, m, n, C;
end intrinsic;

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
function coset_rep_dict(P1, P1rep, level, quot)
  // Use ProjectiveLine to get all projective points [b:d]
  // For each point, construct a matrix [a b \\ c d] in GL2(ZF)
  
  N := level;
  ZF := Order(N);
  F := NumberField(ZF);
  R, phi := Explode(quot);

  coset_reps := AssociativeArray();
  if Minimum(N) eq 1 then
    assert #P1 eq 1;
    coset_reps[Rep(P1)] := Matrix(ZF, 2, 2, [1, 0, 0, 1]);
    return coset_reps;
  end if;
  
  for p in P1 do
    // p is a 2x1 matrix representing [b; d]
    b := ZF!(p[1,1] @@ phi);
    d := ZF!(p[2,1] @@ phi);
    
    // Simple approach: try standard patterns
    // Pattern 1: [1, b; 0, d] if d is a unit
    if GCD(ideal<ZF | d>, N) eq 1*ZF then
      mat := Matrix(ZF, 2, 2, [1, b, 0, d]);
    // Pattern 2: [0, b; 1, d] if b is a unit  
    elif GCD(ideal<ZF | b>, N) eq 1*ZF then
      mat := Matrix(ZF, 2, 2, [0, b, 1, d]);
    // Pattern 3: [1, b; 1, d] if d-b is a unit
    elif GCD(ideal<ZF | d-b>, N) eq 1*ZF then
      mat := Matrix(ZF, 2, 2, [1, b, 1, d]);
    else
      // Exhaustive search for small a, c
      found := false;
      all_elems := [ZF!(x @@ phi) : x in R];
      // Sort elements to ensure deterministic iteration order
      Sort(~all_elems);
      for a in all_elems do
        if found then break; end if;
        for c in all_elems do
          det_val := a*d - b*c;
          if GCD(ideal<ZF | det_val>, N) eq 1*ZF then
            mat := Matrix(ZF, 2, 2, [a, b, c, d]);
            found := true;
            break c;
          end if;
        end for;
      end for;
      
      if not found then
        // This really shouldn't happen for a valid projective point
        error "Could not find valid GL2 matrix for projective point", p;
      end if;
    end if;
    
    coset_reps[p] := mat;
  end for;

  assert Keys(coset_reps) eq P1;
  return coset_reps;
end function;

function ProjectiveLineOrbits(P1, P1rep, d, unit_map, units, split_map : DoStabs:=true, chi:=0)
  // d is an ideal in the ring of integers of a number field, 
  // P1 is ProjectiveLine(d) which comes with the function P1rep,
  // unit_map is the map returned by UnitGroup for a quaternion order O,
  // units contains its images, in a fixed ordering,
  // split_map is the map to the ResidueMatrixRing(O,d).
  // chi is a Hecke character
  //
  // Returns the orbits of the unit group acting on P1, 
  // and the stabilizers of the first element in each orbit.
  
  OK := Order(d); 
  Rd, phi := quo<OK|d>;
  quot := <Rd, phi>;

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
                Quotient := quot,
                P1List := P1,
                P1Rep := P1rep,
                FD := [P1[1]],
                Lookuptable := Lookuptable,
                StabOrders := [#units],
                splitting_map := split_map,
                CosetRepDict := 0,
                Character := 0>;
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
      // split_units[j] contains the image of the jth unit
      // under the residue map to M_2(ZF/N)
      e0 := split_units[j] * e;

      _, e1 := P1rep(e0, false, false);
      if e1 notin orbit then
        Exclude(~elts, e1);
        Include(~orbit, e1);
        // Lookuptable is keyed by e1 in P1reps (elements of P1)
        // and stores the orbit representative index (#FD) and index
        // of the unit (j) taking the representative e to e1
        Lookuptable[e1] := < #FD, j >;
      elif e1 eq e then
        // we also store the stabilizers of each orbit representative e0
        Append(~stab, [* units[j] *]);
      end if;
    end for;

    // assert #units eq (1+#stab) * #orbit;
    Append(~StabOrders, 1+#stab);

    if DoStabs then
      // want stab to contain just generators of the stabilizer
      stab_U := [s[1] @@ unit_map : s in stab];
      // takes the group generated by stab_U and returns the indices
      // in stab_U which are required to generate this group
      stab_U_gens := minimal_generators(sub< U | stab_U >);
      // just the elements of stab whose indices appear in stab_U_gens
      stab_gens := [stab[i] : i in [1..#stab] | stab_U[i] in stab_U_gens];
      Append(~Stabs, stab_gens);
    end if;
  end while;

  vprintf ModFrmHil, 2: "Stabilizers %o\n", Multiset(StabOrders);

  // if the nebentypus is nontrivial, we compute its 
  // "Dirichlet part" (its restriction to the ramified primes)
  // as well as matrices in GL2(ZF/N) representing the 
  // elements of P1 which get used later.
  assert Type(chi) eq GrpHeckeElt;
  if not IsTrivial(chi) then
    psi := FiniteModulusCharFromHeckeChar(chi);
    CosetRepDict := coset_rep_dict(P1, P1rep, d, quot);
  else
    psi := 0;
    CosetRepDict := 0;
  end if;

  PLD := rec< ProjectiveLineData |
             Level:=d,
             Quotient:=quot,
             P1List:=P1,
             P1Rep:=P1rep,
             FD:=FD,
             Lookuptable:=Lookuptable,
             StabOrders:=StabOrders,
             splitting_map:=split_map,
             Character:=psi,
             CosetRepDict:=CosetRepDict
        >;
  if DoStabs then
    PLD`Stabs:=Stabs;
  end if;
  return PLD;

end function;

function twist_factor(PLD, gamma, x : F:=0)
  /*
   * inputs
   *   PLD::ProjectiveLineData - The record data of a projective line ZF/N
   *   gamma::AlgAssVOrdElt - An element of an order of a quaternion algebra over F
   *     We require that PLD`splitting_map(gamma), which sends gamma to a 2x2 matrix
   *     over ZF/N, is invertible, and throw an error otherwise. 
   *   x - An element of PLD`P1List
   * returns 
   *   A factor which shows up in the formulas for Brandt matrices with character
   */
  if PLD`Character cmpeq 0 then
    // if the nebentypus is trivial
    return 1;
  else
    N := PLD`Level;
    ZF := Order(N);
    assert x in PLD`P1List;
    gamma_mod_N := PLD`splitting_map(gamma);

    // print "gamma_mod_N", gamma_mod_N;

    det_gamma := Determinant(gamma_mod_N);
    // print "det_gamma integral", det_gamma in ZF;
    // print "det_gamma", det_gamma, Parent(det_gamma);
    // print "is coprime", IsCoprime(ideal<ZF | det_gamma>, N);

    coset_rep_x_mod_N := PLD`CosetRepDict[x];

    mat := gamma_mod_N * coset_rep_x_mod_N;
    // do it in this way for type coercion reasons
    mat_second_col := Matrix(ZF, [[mat[1][2]], [mat[2][2]]]);
    // print "mat_second_col", mat_second_col, mat[1][2] in N, mat[2][2] in N, Norm(ideal<ZF | mat[1][2], mat[2][2]>);
    // print mat[1][1] in N, mat[1][2] in N, mat[2][1] in N, mat[2][2] in N;
    // pp := 2*ZF;
    // print mat[1][1] in pp, mat[1][2] in pp, mat[2][1] in pp, mat[2][2] in pp;

    _, y := PLD`P1Rep(mat_second_col, false, false);
    
    // a lower triangular (mod N) matrix
    coset_rep_y_mod_N := PLD`CosetRepDict[y];
    det_coset_rep_y := Determinant(coset_rep_y_mod_N);

    coset_rep_y_detinv_lift := det_coset_rep_y @@ PLD`Quotient[2];
    assert IsCoprime(ideal<ZF | det_coset_rep_y>, N);
    coset_rep_y_invdet := Matrix(ZF, 
                            [[coset_rep_y_mod_N[2][2], -coset_rep_y_mod_N[1][2]],
                            [-coset_rep_y_mod_N[2][1], coset_rep_y_mod_N[1][1]]]);
    borel_mat := coset_rep_y_detinv_lift * coset_rep_y_invdet * mat;
    // check that it's actually lower triangular mod N!
    assert borel_mat[1][2] in N;
    if F cmpeq 0 then
      return PLD`Character(borel_mat[2][2]);
    else
      return StrongCoerce(F, PLD`Character(borel_mat[2][2]));
    end if;
  end if;
end function;



function InvariantSpace(PLD, orbit_idx, weight_map, weight_dim, compositum_field : weight:=0)
  // Given a projective line record and the index of some orbit,
  // along with a weight representation,
  // returns the corresponding invariant space. 

  stab := PLD`Stabs[orbit_idx];
  x := PLD`FD[orbit_idx];
  A:=Domain(weight_map); 
  F:=compositum_field; 
  V:=VectorSpace(F, weight_dim); 
  V1:=V;
  S := [A| u@Umap : u in Generators(U)] where U, Umap := UnitGroup(BaseField(A));
  S cat:= [s[1] : s in stab | s[1] notin {A|1,-1}]; 
  for s in S do 
    if (weight cmpeq 0) or is_paritious(weight) then
      w := weight_map(s);
    else
      nrd_s := Norm(s);
      // TODO abhijitm remove later for performance
      assert IsUnit(nrd_s) and IsTotallyPositive(nrd_s);
      // To avoid dealing with square roots, weight_map doesn't include the
      // usual determinant twist on the weight representation. 
      // As such, we need to deal with it separately. 
      w := EltToShiftedHalfWeight(nrd_s, weight) * weight_map(s);
    end if;
      
    V1 meet:= Kernel(w - twist_factor(PLD, s, x) * IdentityMatrix(F, weight_dim));
    if Rank(V1) eq 0 then break; end if;
  end for;

  // This is a matrix with weight_dim columns and
  // r rows.
  // When the nebentypus is trivial, r is the dimension
  // of the subspace invariant under the stabilizer of the 
  // chosen orbit. Otherwise, it's the dimension of a subspace
  // on which each element of the stabilizer acts by a particular
  // scalar determined by the nebentypus.
  return BasisMatrix(V1);
end function;


// This is called by HilbertModularSpaceDirectFactors (now only for nontrivial weight)
// P1 = projective line mod d, 
// LO is a quaternion order, 
// split_map LO -> M_2(O/d),
// weight_map = weight_rep

function HMSDF(P1, P1rep, LO, d, split_map, weight_map, weight_dim, hecke_matrix_field : chi:=0, weight:=0)
  U, unit_map:=UnitGroup(LO); 
  units:=[Algebra(LO)! unit_map(s): s in U];
  // Dembele-Voight write the units as Gamma (or Gamma_i).
  // Now, we compute the action of Gamma on P^1(ZF / d)
  PLD:=ProjectiveLineOrbits(P1, P1rep, d, unit_map, units, split_map : chi:=chi); 
  F := hecke_matrix_field;
  // the jth entry of stabs consists of a list of 
  // elements in Gamma which stabilize the 
  // chosen representative of the jth orbit
  stabs:=PLD`Stabs; 
  // l indexes orbits of the Gamma action on P1(ZF / d) 
  l:=1; 
  repeat 
    // this is a matrix with weight_dim columns and 
    // some number of rows depending on the dimension
    // of the subspace of the weight representation where
    // the stabilizer of the lth orbit acts in a prescribed
    // way (according to the nebentypus). 
    M:=InvariantSpace(PLD, l, weight_map, weight_dim, F : weight:=weight);
    if Rank(M) eq 0 then l:=l+1; end if;
  until (l gt #stabs) or (Rank(M) ne 0);

  // TODO abhijitm wait so max order units is being set to units??
  if l gt #stabs then
    return rec<ModFrmHilDirFact|PLD:=PLD, CFD:={@ @}, basis_matrix:=ZeroMatrix(F, 0, 0), 
               basis_matrix_inv:=ZeroMatrix(F, 0, 0), weight_rep:=weight_map, 
               weight_dimension:=weight_dim, weight_base_field:=F, max_order_units:=units>;
  else
    contrib_orbs:=[l];
    for m0:=l+1 to #stabs do
      // As before, this is a r x weight_dim matrix,
      // where r depends on the orbit m0.
      N:=InvariantSpace(PLD, m0, weight_map, weight_dim, F : weight:=weight);
      if Rank(N) ne 0 then
        Append(~contrib_orbs, m0);
        // TODO abhijitm this seems really inefficient, 
        // it looks like we are re-making the matrix from
        // scratch each time instead of e.g. collecting the blocks
        // and then synthesizing the space after.
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
  // All in all, M looks like a block "diagonal" matrix, except the diagonal
  // blocks are rectangular. Each diagonal block has weight_dim columns but
  // a variable number of rows. As such, M has R rows and 
  // weight_dim x #contrib_orbs columns.
  // Don't forget that this M is the contribution from a single
  // right ideal class of the quaternion order O.
  
  // This is a left inverse of M but Magma is bad with coercions
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

    // These can also be thought of as 
    // \hat{alpha} \hat{O}_0(1) \hat{\alpha}^{-1} \cap B
    // where \hat{alpha} ranges over double coset representatives
    // for B* \ B*(A_F) / O_0(1)
    LOs := [I`LeftOrder: I in get_rids(M)]; 

    // parallel weight 2 and trivial nebentypus
    if Seqset(Weight(M)) eq {2} and (Order(DirichletCharacter(M)) eq 1) then

      HMDFs := [];
      Q := Rationals();
      
      // For weight 2, the weight representation is the identity map
      I := IdentityMatrix(Q, 1);
      Mat1 := Parent(I);
      weight_rep := map< A -> Mat1 | q :-> I >;

      for LO in LOs do 

        U, mU := UnitGroup(LO); 
        units := [A| s @ mU : s in U];

        PLD := ProjectiveLineOrbits(P1, P1rep, d, mU, units, split_map : DoStabs:=false, chi:=DirichletCharacter(M));

        // number of orbits is the dimension
        dim := #PLD`FD;
        Id := MatrixRing(Rationals(), dim) ! 1;

        Append(~HMDFs, 
           rec< ModFrmHilDirFact | 
                PLD := PLD, 
                CFD := IndexedSet([1 .. dim]), // TO DO: get rid of this, and the basis_matrices
                basis_matrix := Id, 
                basis_matrix_inv := Id, 
                weight_rep := weight_rep,
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
 
      chi := DirichletCharacter(M);

      // The big Hecke matrix lives over the field its weight-representation
      // blocks live in: weight_base_field, extended by Q(zeta_d) when the
      // nebentypus is nontrivial (twist_factor produces cyclotomic values).
      // This is a STABLE field (a no-op = weight_base_field for order <= 2);
      // it must not be the descending hecke_matrix_field, which can be shrunk
      // to the minimal field during eigenform extraction and would then be
      // inconsistent with the (undescended) weight-rep blocks.
      hecke_mtrx_field := big_hecke_matrix_field(M);
      
      // print "number of left orders", #LOs, LOs;
      // Each HMSDF returns a ModFrmHilDirFact record, and there's one for each
      // right ideal class of the maximal order of B. 
      //
      // The basis_matrix of each HMSDF is a matrix with R rows and
      // (weight_dim x #{orbits of P1 under the action of the units of the LO}) columns,
      // where R is whatever it is.
      //
      // CFD for each HMSDF stores the indices of the orbits which 
      // contribute nontrivially to R. 
      HMDFs := [HMSDF(P1, P1rep, LO, d, split_map, wr, wd, hecke_mtrx_field : chi:=chi, weight:=Weight(M)) : LO in LOs];

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

    weight2trivchar := Seqset(Weight(M)) eq {2} and (Order(DirichletCharacter(M)) eq 1);

    if not assigned M`basis_matrix_big then
      easy := weight2trivchar and Level(M) eq Discriminant(QuaternionOrder(M));
      // easy = basis of space is given by the rids (ie each P^1 is trivial)

      if weight2trivchar then
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
        // This will be the dimension of the space
        nrows := &+ [Nrows(HMDF[m]`basis_matrix): m in [1..#HMDF]];
        // This will be some multiple of weight_rep, 
        ncols := &+ [Ncols(HMDF[m]`basis_matrix): m in [1..#HMDF]];
        B := Matrix(BaseRing(HMDF[1]`basis_matrix), nrows, ncols, []);
        row := 1; 
        col := 1;
        // B is a block "diagonal" matrix with rectangular blocks
        // for each right ideal class of O. 
        // Each block is itself a block diagonal matrix.
        for hmdf in HMDF do 
          if not IsEmpty(hmdf`CFD) then
            InsertBlock(~B, hmdf`basis_matrix, row, col);
            row +:= Nrows(hmdf`basis_matrix);
            col +:= Ncols(hmdf`basis_matrix);
          end if;
        end for;
        // As before, this is just a left inverse 
        Binv := Transpose(Solution(Transpose(B), IdentityMatrix(BaseRing(B), Nrows(B))));
        M`basis_matrix_big := B; 
        M`basis_matrix_big_inv := Binv; 
      end if;
    end if;
      
    // There are no "Eisenstein series" when we are not
    // in parallel weight 2, I think.
    eisenstein_present := Seqset(Weight(M)) eq {2}
      and Conductor(DirichletCharacter(M)) eq 1*Integers(BaseField(M));
    if eisenstein_present and not EisensteinAllowed then
      RemoveEisenstein(~M);
      dim := Nrows(M`basis_matrix);
    elif eisenstein_present then
      dim := Nrows(M`basis_matrix_big) - #NarrowClassGroup(BaseField(M));
    else
      M`basis_matrix := M`basis_matrix_big;
      M`basis_matrix_inv := M`basis_matrix_big_inv;
      // This is the dimension of the space of quaternionic modular forms.
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

function HeckeOperatorDefiniteBig(M, p : Columns:="all", opposite_mode:=false)

  // print "HeckeOperatorDefiniteBig", IdealOneLine(p);
  assert not assigned M`Ambient; // M is an ambient

  // Caching
  // HeckeBig and HeckeBigColumns must be assigned together

  cached, tup := IsDefined(M`HeckeBig, p);
  if cached then 
    Tp, p_rep := Explode(tup);
    Tp := Matrix(Tp);
    _, old_cols := IsDefined(M`HeckeBigColumns, p);
    if Columns cmpeq "all" then
      Columns := [1..Ncols(Tp)];
    end if;
    columns := [j : j in Columns | j notin old_cols];
    if IsEmpty(columns) then
      return Tp, p_rep;
    end if;
  else
    old_cols := [];
    columns := Columns;
  end if;

  A := Algebra(QuaternionOrder(M));
  N := Level(M);
  weight2trivchar := Seqset(Weight(M)) eq {2} and (Order(DirichletCharacter(M)) eq 1);

  // easy = basis of big space is given by the rids
  easy := weight2trivchar and N eq Discriminant(QuaternionOrder(M));

  if not assigned M`basis_matrix then
    _ := BasisMatrixDefinite(M : EisensteinAllowed);
  end if;
  // The big Hecke operator will be a dim x dim matrix.
  // Note that this dim is *not* generally the 
  // dimension of the space of quaternionic modular forms,
  // but rather the dimension of the space in which we embed them.
  dim := Ncols(M`basis_matrix_big);

  F := big_hecke_matrix_field(M); // = Q for parallel weight 2, trivial nebentypus
  if easy then
    h := dim;
  else
    HMDF := M`ModFrmHilDirFacts; 
    // i.e the number of orbits in the projective line
    // (associated to each direct factor)
    // which contribute nontrivially to the basis
    nCFD := [#xx`CFD : xx in HMDF];
    // the number of direct factors, i.e. the class number
    // of O_0(1)
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

  if not weight2trivchar then // currently, higher weight and nontrivial nebentypus don't use Columns
    columns := [1 .. dim];
  end if;

  if easy then
    bcolumns := columns;
    Bcolumns := columns;
  elif columns eq [1 .. dim] then 
    // Full matrix - this always happens
    // outside of parallel weight 2
    // 
    // Each large block, coming from a left order/right ideal class,
    // has an associated P1, and the matrix consists of 
    // small blocks for each orbit of this P1 (under the action under
    // the units of the left order) which contribute nontrivially
    // to the basis.
    bcolumns := [1 .. dim div wd];
    // one large block for each direct factor
    Bcolumns := [1 .. h];
  elif weight2trivchar then 
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
  end if;
  
  if not cached then
    Tp := MatrixRing(F, dim) ! 0; 
  end if;

//"Starting with"; Tp;

//"Columns:"; Columns; old_cols; columns; bcolumns; Bcolumns;

  // This is independent of the weight and level -- it captures information
  // about the ideals of the maximal quaternion order O (and in particular
  // those of p-power reduced norm, I think). 
  tp := get_tps(M, p : rows:=Bcolumns); // rows in precompute_tps are columns here

  vprintf ModFrmHil: "%o%o column%o%o of big Hecke matrix (norm %o): ", 
                     #columns eq dim select "All " else "", 
                     #columns, 
                     #columns gt 1 select "s" else "", 
                     #columns gt 1 select "" else " (#"*Sprint(columns[1])*")", 
                     Norm(p);
  vtime ModFrmHil:
  // dummy value, in case it doesn't get set later
  lambda := 1;
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

    // the indices of direct factors where there are actually
    // orbits that contribute to the basis
    inds := [l : l in [1..#HMDF] | nCFD[l] ne 0];
    row := 0; 
    col := 0;

    for m in inds do 
      // When not parallel weight 2 trivial nebentypus,
      // Bcolumns is [1 .. h], where h is the class number 
      // of the maximal order O.
      if m in Bcolumns then
        for l in inds do 
          // I'm guessing it's undefined only if tpml is empty.
          bool, tpml := IsDefined(tp, <m,l>);
          // print "Norm p", Norm(p), "size of tpml", #tpml;

          if bool then
            // this isn't actually used if we are in paritious weight
            // so we don't bother with the check in this case
            // lambda := Norm(tpml[1]);
            if not is_paritious(Weight(M)) then
              // require that all the pi_i have the same reduced norm
              // print "-------------- hi", [Norm(x) : x in tpml];
              assert #{Norm(x) : x in tpml} le 1;
              // TODO abhijitm can remove some of these asserts later
              // print "-------- hi", Norm(lambda), Norm(p);
              if m eq l and #tpml gt 0 then
                lambda := Norm(tpml[1]);
                assert Norm(lambda) eq Norm(p);
                assert IsTotallyPositive(lambda);
              end if;
            end if;

            if weight2trivchar then

              PLDl := HMDF[l]`PLD;
              FDl   := PLDl`FD; 
              FDm   := HMDF[m]`PLD`FD; 
              lookup:= PLDl`Lookuptable; 
              P1rep := PLDl`P1Rep;

              // get the #FDl x #FDm submatrix starting
              // at row+1, col+1
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
              // This stores elements of the P1 associated
              // to the lth right ideal class of O representing 
              // each orbit (contributing or not)
              FDl   := PLDl`FD; 

              // Same for the mth right ideal class of O
              FDm   := HMDF[m]`PLD`FD; 
              // This maps a P1 element x to a unit of the lth left order
              // which takes the orbit representative of x to x.
              lookup:= PLDl`Lookuptable; 
              P1rep := PLDl`P1Rep;

              chi := DirichletCharacter(M);
              // true iff the order of the nebentypus is bigger than 2
              irrat_neb_field := not IsTrivial(chi) and Order(chi) gt 2;

              // This is an indexed set of the contributing orbits of the
              // lth P1 
              CFDl := HMDF[l]`CFD; 
              // Same for the mth P1
              CFDm := HMDF[m]`CFD; 
              // These are the units of the lth left order
              units1 := HMDF[l]`max_order_units; 
              weight_map := HMDF[l]`weight_rep; 

              // the row/column block corresponding to the
              // pair of direct factors (l, m) has dimension
              // (wd * #CFDl) x (wd * #CFDm) because #CFDl 
              // and #CFDm are the respective numbers of (contributing) 
              // projective line orbits, and for each of these we have 
              // an element of Wk(C).
              //
              // As a sanity check, these are the number of columns associated
              // to the respective big blocks in basis_matrix. 
              Tplm := Matrix(F, wd*#CFDl, wd*#CFDm, []);
              
              // print "norm prime", Norm(p), "number of tpml", #tpml;
              // print "#CFDm", #CFDm;
              for ll := 1 to #tpml do
                // tpml[ll] is an element of O, and mat is the element mod N
                mat := tpml[ll] @ sm;
                // over contributing orbits of mm
                for mm := 1 to #CFDm do
                  // FDm[CFDm[mm]] is an element of the projective line,
                  // so applying mat to it makes sense
                  u := mat * FDm[CFDm[mm]];
                  bool, u0 := P1rep(u, checkP1, false);
                  // not totally sure why yet (TODO!) but when p | N, for
                  // each mm there will be a unique ll such that not bool,
                  // at least when #(Cls O) = 1. Importantly, I guess this 
                  // means that unlike the level 1 story (or the story where
                  // we don't do this projective line stuff), it's not as simple
                  // as omitting a single element in tpml. 
                  // if not bool then
                    // print ll, mm, "not bool!";
                  // end if;
                  if bool then
                    // this lookup is in the P1 associated to l!
                    // It finds the orbit in l's P1 associated to 
                    // mat(tpml[ll]) * FDM[CFDm[mm]]
                    elt_data := lookup[u0]; 
                    // elt_data[1] is an index in the fundamental domain of the 
                    // P1 associated to l. 
                    n := Index(CFDl, elt_data[1]);
                    // If n is 0 then u0 corresponds to an orbit in l's P1 which does not 
                    // have any quaternionic modular forms.
                    if n ne 0 then
                      // units1[elt_data[2]]^-1 is the unit which takes
                      // the orbit rep of u0 to u0. 
                      quat1 := units1[elt_data[2]]^-1 * tpml[ll]; 
                      X := ExtractBlock(Tplm, (n-1)*wd+1, (mm-1)*wd+1, wd, wd);
                      weight_matrix := weight_map(quat1);
                      // Only use StrongCoerceMatrix when nebentypus order > 2 to avoid unnecessary overhead
                      if irrat_neb_field then
                        weight_matrix := StrongCoerceMatrix(F, weight_matrix);
                      end if;
                      Y := twist_factor(PLDl, quat1, FDm[CFDm[mm]])^-1 * weight_matrix;
                      X := X + Y;
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
  M`HeckeBig[p] := <SparseMatrix(Tp), [lambda]>;
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

  return Tp, [lambda];
end function;



// TO DO: columns option

function AtkinLehnerDefiniteBig(M, p)

   // print "!!!!!!!!!!!!!!!! ATKIN LEHNER !!!!!!!!!!!!!!!!!!!!", Norm(p), IdealOneLine(p);
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
   F := big_hecke_matrix_field(M);
   sm := M`splitting_map;

   tp := get_tps(M, pe);

   weight2trivchar := (Seqset(Weight(M)) eq {2}) and (Order(DirichletCharacter(M)) eq 1);

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

         if weight2trivchar then

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

               quat1 := units1[u]^-1 * tp_elt[l,k];
               // TODO abhijitm double check twist factor
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
   F := big_hecke_matrix_field(M);

   P1N := HMDF[1]`PLD`P1List;

   assert forall{x : x in HMDF | IsIdentical(x`PLD`P1List, P1N)};
   // (the same P1 was attached to each block)

   C := P1_congruence_classes(P1N, N, Np);

   weight2 := Seqset(Weight(M)) eq {2};
   assert weight2;
   assert Order(DirichletCharacter(M)) eq 1;

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

function DegeneracyMapBlock(M1, M2, Tp, sm : weight2trivchar:=false)

   // M1 and M2 are ModFrmHilDirFact records
   
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

   if weight2trivchar then // parallel weight 2 trivial nebentypus
      assert w eq 1; // parallel weight 2

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

      // When called from DegeneracyMap, Tp contains the output of 
      // get_tps(M1, p) for some prime p and M1 the domain of the 
      // degeneracy map
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
                  quat1 := units1[elt_data[2]]^-1*Tp[l]; 
                  mat1 := ExtractBlock(B, (n-1)*w+1, (m-1)*w+1, w, w);
                  mat1 +:= twist_factor(M1PLD, quat1, ProjectionMap(FD2[CFD2[m]], d1, Rd1, P1rep1))^-1 * weight_map(quat1);
                  InsertBlock(~B, mat1, (n-1)*w+1, (m-1)*w+1);
               end if;
            end if;
         end for;
      end for;

   end if; 

   return B;
end function;

function DegeneracyMapDomain(M, d)
   // Given an ambient space M and an integral ideal d such that NewLevel(M) | d | Level(M), 
   // returns a space of level d and same weight as M, defined using internals that are
   // compatible with M (same quaternion algebra, same splitting map and weight representation)

   QO:=M`QuaternionOrder;
   assert NewLevel(M) eq Discriminant(QO);
   assert IsIntegral(d/NewLevel(M));
   assert IsIntegral(Level(M)/d); 

   if Order(DirichletCharacter(M)) eq 1 then
      new_chi := DirichletCharacter(M);
   else
      chi := DirichletCharacter(M);
      N := Level(M);
      _, m_inf := Modulus(chi);
      // ensure that the conductor of chi divides d
      assert d subset Conductor(chi);
      new_chi := Restrict(chi, d, m_inf);
   end if;

   // MUST use identical internal data: in particular, rids and weight_rep.
   // Call low-level constructor to avoid complications with caching, and don't cache DM
   // TO DO: use cached spaces, to avoid recomputing ModFrmHilDirFacts (that's the only advantage)
   DM:=HMF0(BaseField(M), d, NewLevel(M), new_chi, Weight(M), CentralCharacter(M));
   DM`QuaternionOrder:=QO;
   DM`rids, DM`support:=get_rids(M);
   DM`splitting_map:=M`splitting_map; // can use same splitting_map even though its level is larger than needed
   DM`weight_base_field:=M`weight_base_field;
   DM`weight_dimension:=M`weight_dimension;
   if Seqset(Weight(M)) ne {2} then // nontrivial weight
      DM`weight_rep:=M`weight_rep;
      // Mod-p spaces from finitefield.m do not set this embedding.
      if assigned M`splitting_field_emb_weight_base_field then
         DM`splitting_field_emb_weight_base_field := M`splitting_field_emb_weight_base_field;
      end if;
   end if;
   return DM;
end function;


// The upward degeneracy map from M1 to M2, where q*Level(M1) = Level(M2)
// for some prime q, and either p = q or p = (1)
// Only valid if M1 was created as a DegeneracyMapDomain of M2.

function DegeneracyMap(M1, M2, p : Big:=false, EisensteinAllowed:=false)

   assert IsPrime(p) or Norm(p) eq 1;
   assert GCD(p*(M1`Level), M2`Level) eq p*(M1`Level);
   assert IsIdentical(M1`QuaternionOrder, M2`QuaternionOrder);
   assert IsIdentical(M1`splitting_map, M2`splitting_map); 
   if Seqset(Weight(M1)) ne {2} then // nontrivial weight
      assert IsIdentical(M1`weight_rep, M2`weight_rep); 
   end if;

   // these have the same number of entries because 
   // the quaternion orders are the same
   HMDF1 := HilbertModularSpaceDirectFactors(M1);
   HMDF2 := HilbertModularSpaceDirectFactors(M2);

   if Minimum(p) eq 1 then
      // trivial degeneracy map
      tp:=AssociativeArray(CartesianProduct([1..#HMDF1],[1..#HMDF1]));
      for l:=1 to #HMDF1 do
         tp[<l,l>]:=[Algebra(M1`QuaternionOrder)!1];
      end for;
   else
      // nontrivial degeneracy map
      tp:=get_tps(M1,p);
   end if;

   F := M1`weight_base_field; 
   sm := M1`splitting_map;

   w1 := M1`weight_dimension;
   w2 := M2`weight_dimension;
   assert w1 eq w2;

   weight2trivchar := (w1 eq 1) and (Order(DirichletCharacter(M1)) eq 1) and (Order(DirichletCharacter(M2)) eq 1);
   // #xx`CFD is the number of orbits in the projective line
   // of xx which contribute nontrivially to the basis
   nCFD1 := [#xx`CFD : xx in HMDF1];
   nCFD2 := [#xx`CFD : xx in HMDF2];
   // we restrict to the right ideal classes which contribute
   // nontrivially to keep the linear algebra efficient
   inds1 := [l : l in [1..#HMDF1] | nCFD1[l] ne 0];
   inds2 := [m : m in [1..#HMDF2] | nCFD2[m] ne 0];
   row := 1; 
   col := 1;
   // we have a copy of the weight rep for each orbit in each P1 
   D := Matrix(F, &+nCFD1 * w1, &+nCFD2 * w2, []); 

   for m in inds2 do
      for l in inds1 do 
         bool, tpml := IsDefined(tp, <m,l>);
         if bool then
            Dlm := DegeneracyMapBlock(HMDF1[l], HMDF2[m], tpml, sm : weight2trivchar:=weight2trivchar);
            InsertBlock(~D, Dlm, row, col); 
//assert Nrows(Dlm) eq nCFD1[l] * w1;
//assert Ncols(Dlm) eq nCFD2[m] * w2;
         end if;
         // the contribution from the lth right ideal class
         row +:= nCFD1[l] * w1;
      end for;
      // the contribution from the mth right ideal class
      col +:= nCFD2[m] * w2;
      row := 1;
   end for;

   // Two differences here
   if Big then
      M1bm := BasisMatrixDefinite(M1 : EisensteinAllowed:=EisensteinAllowed);
      return M1bm * D;
   else
      M1bm := BasisMatrixDefinite(M1 : EisensteinAllowed:=EisensteinAllowed);
      _, M2bmi := BasisMatrixDefinite(M2);
      return M1`basis_matrix * D * M2bmi;
   end if;

end function;

// Basis of a newspace (called only by BasisMatrixDefinite)

procedure ComputeBasisMatrixOfNewSubspaceDefinite_general(M)
  assert IsDefinite(M); 
   MA := M`Ambient; // must be assigned with QuaternionOrder (unless NewLevel = Level)
   A,B:= BasisMatrixDefinite(MA);

   weight2 := Seqset(Weight(M)) eq {2};
   weight2trivchar := weight2 and (Order(DirichletCharacter(M)) eq 1);
   assert not weight2trivchar;

   chi := DirichletCharacter(M);
   
   // If nebentypus is nontrivial, use Hecke action approach (shared helper function)
   if Order(chi) ne 1 then
      ComputeNewSubspaceBasisMatricesUsingHeckeAction(M, MA);
      return;
   end if;

   // Otherwise, use degeneracy map + Atkin-Lehner approach (original code)
   O := Integers(BaseField(M));
   D := Discriminant(QuaternionOrder(M));
   L := Level(M);
   Lnew := NewLevel(M);
   assert NewLevel(MA) eq D; 
   N := Lnew/D; 
   assert ISA(Type(N), RngOrdIdl); // integral
   valid_primes := [fact_tup : fact_tup in Factorization(N)];

   V := VectorSpace(BaseRing(A), Nrows(A)); 
   W := sub<V|>;
   for m := 1 to #valid_primes do
      if Dimension(W) eq Dimension(V) then 
         break; 
      end if;

      vprint ModFrmHil: "Computing oldforms relative to prime of norm", Norm(valid_primes[m][1]);
      time0 := Cputime();
      IndentPush(); 
      N1 := DegeneracyMapDomain(MA, L/valid_primes[m][1]);
      if Dimension(N1) eq 0 then
         IndentPop();
         continue;
      end if;

      P, eP := Explode(valid_primes[m]);

      vprintf ModFrmHil: "Degeneracy maps between dimensions %o and %o: ", Dimension(MA), Dimension(N1);
      vtime ModFrmHil:
      D1 := DegeneracyMap(N1, MA, 1*O);

      if (eP eq 1) and IsOne(GCD(P, N / P^eP)) and (not debug) then
         vtime ModFrmHil:
         D2 := DegeneracyMap(N1, MA, P);
      else 
         AL := AtkinLehnerOperator(MA, P);
         D2 := D1 * AL;
      end if;

      old_space_mat := VerticalJoin(D1, D2);

      // checks
      if eP eq 1 then
         assert Rank(old_space_mat) eq 2*Rank(D1);
         assert Rank(old_space_mat) eq 2*Rank(D2);
         if debug then
            assert RowSpace(old_space_mat) eq RowSpace(D1) + RowSpace(D2);
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
   weight2trivchar := weight2 and (Order(DirichletCharacter(M)) eq 1);
   if not weight2trivchar then
      // TO DO implement IP for nontrivial nebentypus
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

   eisenstein_present := weight2trivchar;
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

