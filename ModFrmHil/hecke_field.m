import "definite.m":
  _ResidueMatrixRing,
  HMSDF,
  get_compositum_field;
import "hackobj.m" :
  Ambient,
  BMF_with_ambient,
  IsBianchi,
  TopAmbient;

import "hecke.m" :
  CharacteristicPolynomialViaCRT,
  NewformsOfDegree1Implemented,
  basis_is_honest,
  dimension_lower_bound,
  get_red_vector,
  hecke_algebra,
  hecke_algebra_dimension,
  pseudo_inverse,
  rational_basis,
  red_eigenvector,
  reduction;

import "precompute.m" :
  get_rids;

import "indefinite.m" : ElementOfNormMinusOne;

import "weight_rep.m" : weight_map_arch, is_paritious;
import "hecke.m" : get_image_of_eps_nonparit;

declare attributes ModFrmHil : minimal_hecke_field_emb,
	                       splitting_field_emb_weight_base_field,
	                       strong_descent_embs; // Assoc: marked-place-consistent H -> K embeddings, cached for descent

forward WeightRepresentation;

/********************************************************/
//
// The field objects used for Hecke computations, from largest to smallest:
//
//   weight_base_field (set in WeightRepresentation)
//     The field of the weight representation H^* -> GL(V_k): Rationals() for
//     parallel weight 2, otherwise the field K from Splittings(H) -- an
//     extension of F, Galois over Q, that splits the quaternion algebra and
//     contains the roots realizing the weight. It does NOT depend on the
//     nebentypus character.
//
//   big_hecke_matrix_field = weight_base_field (x) Q(zeta_d)   (in definite.m)
//     The STABLE field over which the definite big Hecke matrix is assembled
//     from its weight-representation blocks. Equal to weight_base_field for a
//     trivial or quadratic (order <= 2) character; extended by the cyclotomic
//     field of the character otherwise. Memoized, and NEVER descended.
//
//   hecke_matrix_field (below)
//     The field the Hecke operators returned to callers currently live over.
//     It STARTS equal to big_hecke_matrix_field but is STATEFUL: SetRationalBasis
//     descends M`hecke_matrix_field to the minimal field below. Do not use it
//     where a stable field is required (e.g. assembling the big matrix).
//
//   minimal_hecke_matrix_field (below)
//     The smallest field the Hecke algebra can be defined over. Governed by the
//     Galois stabilizer of the weight, composed with Q(zeta_d): Rationals() for
//     parallel weight with order <= 2 character, Q(zeta_d) for parallel weight
//     with higher-order character, and FixedField(weight stabilizer) (x) Q(zeta_d)
//     in general. This is the descent target used by SetRationalBasis.
//
/********************************************************/

function splitting_field_embedding_to_weight_field(F, K, target)
  Fspl, rts := Explode(F`SplittingField);
  if Degree(Fspl) eq 1 then
    return hom<Fspl -> K | >;
  end if;

  // StrongCoerce pins the embedding to the right Galois conjugate.
  emb := hom<Fspl -> K | StrongCoerce(K, Fspl.1)>;
  assert emb(rts[1]) eq target;
  return emb;
end function;

// originally from hecke.m

function hecke_matrix_field(M)
  if assigned M`hecke_matrix_field then
    return M`hecke_matrix_field;
  elif IsBianchi(M) then
    return Rationals();
  else
    if not assigned TopAmbient(M)`weight_base_field then
      _ := WeightRepresentation(TopAmbient(M));
    end if;
    if is_paritious(Weight(M)) or IsDefinite(M) then
      // Hecke matrices live over the weight base field, extended by Q(zeta_d)
      // for a nontrivial nebentypus (a no-op for order <= 2). The IsDefinite
      // guard is routing, not pinning: the K(sqrt(z)) +/- extension in the
      // else-branch below only exists for the indefinite method; the definite
      // method builds its matrices over weight_base_field (x) Q(zeta_d) even
      // in nonparitious weight. We do NOT cache this onto M`hecke_matrix_field,
      // so SetRationalBasis stays free to descend it to the minimal field.
      H := TopAmbient(M)`weight_base_field;
      if not (Order(DirichletCharacter(M)) eq 1) then
        chi := DirichletCharacter(M);
        H := get_compositum_field(H, chi);
      end if;
      return H;
    else
      // if the weight is nonparitious and we are using
      // the indefinite method, the Hecke matrices on the entire
      // H1 will be over the weight base field but the + and - subspaces
      // will be defined over a quadratic extension
      O := QuaternionOrder(M);
      F := BaseField(M);
      mu := ElementOfNormMinusOne(O);
      eps := Norm(mu);
      auts := AutsOfKReppingEmbeddingsOfF(F, F);
      k := Weight(M);
      k0 := Max(Weight(M));
      z := get_image_of_eps_nonparit(M);

      // There are several assumptions being made here
      // - the quaternion algebra is split at exactly one infinite prime
      // - at this prime, the weight is k0
      // We check for these assumptions when constructing the space,
      // but it's worth keeping in mind nonetheless.
      K := TopAmbient(M)`weight_base_field;
      R<x> := PolynomialRing(F);
      poly := x^2 - z;
      if IsIrreducible(poly) then
        // TODO abhijitm I'm a little bit worried about returning a
        // relative extension here instead of an absolute one...
        // We must adjoin Sqrt(z) coercing z into K via the SAME embedding F -> K that builds
        // the archimedean splittings (the marked/first place), NOT Magma's natural coercion:
        // the two agreed in Magma 2.29-6 but diverge in 2.29-8, which would put Sqrt(z) in the
        // wrong square class and desynchronize the +/- split from the involution T.
        embs := WeightBaseEmbeddings(O);
        K := ext<K | PolynomialRing(K) ! [-embs[1](z), 0, 1]>;
      end if;
      return K;
    end if;
  end if;
end function;

// Returns the field currently used as the BaseRing of each HeckeOperator.
// M`hecke_matrix_field is not always assigned; when it is not,
// HeckeOperator returns matrices over the weight_base_field.

function minimal_hecke_matrix_field(M)
  bool, minimal := HasAttribute(M, "hecke_matrix_field_is_minimal");
  if bool and minimal then
    H := M`hecke_matrix_field;
    M`minimal_hecke_field_emb := IdentityHomomorphism(H);
  elif assigned M`Ambient then
    H := minimal_hecke_matrix_field(M`Ambient);
    M`minimal_hecke_field_emb := M`Ambient`minimal_hecke_field_emb;
  elif IsParallelWeight(M) then
    K := hecke_matrix_field(M);
    if Order(DirichletCharacter(M)) le 2 then
      H := Rationals();
      M`minimal_hecke_field_emb := hom<H -> K | >;
    else
      // parallel weight is paritious, so the Hecke matrices descend via
      // StrongCoerce and no minimal_hecke_field_emb is needed.
      H := CyclotomicField(Order(DirichletCharacter(M)));
    end if;
  else
    vprintf ModFrmHil: "Figuring out the \'Hecke matrix field\' ... "; 
    time0 := Cputime();

    // The field where they currently live was created as an ext of Kgal.
    // The hecke_matrix_field is the subfield of Kgal corresponding to
    // the subgroup of the Galois group that fixes Weight(M).
    K := BaseField(M);
    assert assigned K`SplittingField; // WeightRepresentation should set it 
    Kgal, rts := Explode(K`SplittingField);
    assert IsAbsoluteField(Kgal);
    Aut, _, Autmap := AutomorphismGroup(Kgal);
    // figure out the Galois group as a permutation group acting on rts
    Sym := SymmetricGroup(AbsoluteDegree(K));
    gens := [Aut.i@Autmap : i in [1..Ngens(Aut)]];
    images := [Sym| [Index(rts, r@a) : r in rts] : a in gens];
    G := sub< Sym | images >;
    Aut_to_G := hom< Aut -> G | images >;
    act := func< w,g | [w[i] : i in Eltseq(g^-1)] >;
    Gw := sub< G | [g : g in G | act(w,g) eq w] > where w is Weight(M);
    Gw_in_Aut := sub< Aut | [h@@Aut_to_G : h in Generators(Gw)] >;
    H := FixedField(Kgal, Gw_in_Aut);
    is_sub, emb_fixed := IsSubfield(H, Kgal);
    assert is_sub;
    assert assigned M`weight_rep;
    assert assigned M`splitting_field_emb_weight_base_field;
    M`minimal_hecke_field_emb := M`splitting_field_emb_weight_base_field * emb_fixed;
    assert Domain(M`minimal_hecke_field_emb) eq H;

    H := get_compositum_field(H, DirichletCharacter(M));

    vprintf ModFrmHil: "Time: %o\n", Cputime(time0);
  end if;

  return H;
end function;

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
      _, m, n, C := IsArithmeticWeight(F,k);  
      assert C eq M`CentralCharacter;

      if Seqset(k) eq {2} then // parallel weight 2
         I := IdentityMatrix(Rationals(), 1);
         Mat1 := Parent(I);
         M`weight_rep := map< H -> Mat1 | q :-> I >;
         M`weight_base_field := Rationals();
         M`weight_dimension := 1;
         QQ := Rationals();
         M`splitting_field_emb_weight_base_field := hom<QQ->QQ|>;
      else
         splitting_seq, K, weight_field := Splittings(H);
         Fspl := F`SplittingField[1];
         target := WeightBaseEmbeddings(H)[1](F.1);
         M`splitting_field_emb_weight_base_field :=
           splitting_field_embedding_to_weight_field(F, K, target);
         M`weight_base_field:=K;
         vprintf ModFrmHil: "Field chosen for weight representation:%O", weight_field, "Maximal";
         vprintf ModFrmHil: "Using model of weight_field given by %o over Q\n", DefiningPolynomial(K);
         M`weight_dimension := &* [x+1 : x in n];
         M2K:=MatrixRing(K, M`weight_dimension);
         if is_paritious(Weight(M)) then
            M`weight_rep:=map<H -> M2K|q :-> weight_map_arch(q, n : m:=m)>;
         else
            M`weight_rep:=map<H -> M2K|q :-> weight_map_arch(q, n : m:=[0 : _ in [1 .. #Weight(M)]])>;
         end if;
      end if;
      return M`weight_rep, M`weight_dimension, M`weight_base_field;
   end if;
end function;
