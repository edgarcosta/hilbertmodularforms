import !"Geometry/ModFrmHil/definite.m":
  _ResidueMatrixRing,
  HMSDF,
  weight_map_arch;
import !"Geometry/ModFrmHil/hackobj.m" :
  Ambient,
  BMF_with_ambient,
  IsBianchi,
  TopAmbient;

import !"Geometry/ModFrmHil/hecke.m" :
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

import !"Geometry/ModFrmHil/precompute.m" :
  get_rids;

import "hackobj.m" : HMF0;

/**************** New Attributes **********************/

declare attributes ModFrmHil : minimal_hecke_field_emb,
	                       splitting_field_emb_weight_base_field;

/********************************************************/

// originally from hecke.m

function hecke_matrix_field(M : hack := true)
  if assigned M`hecke_matrix_field then
    return M`hecke_matrix_field;
  elif IsBianchi(M) or not IsDefinite(M) then
    return Rationals();
  else
      if hack then
	  // hack begins
	  return TopAmbient(M)`weight_base_field;
	  // hack ends
      else
	  return Ambient(M)`weight_base_field;
      end if;
  end if;
end function;

// Returns the field currently used as the BaseRing of each HeckeOperator.
// M`hecke_matrix_field is not always assigned; when it is not,
// HeckeOperator returns matrices over the weight_base_field.

function minimal_hecke_matrix_field(M : hack := true)
  bool, minimal := HasAttribute(M, "hecke_matrix_field_is_minimal");
  if bool and minimal then
    H := M`hecke_matrix_field;
    if hack then
	M`minimal_hecke_field_emb := IdentityHomomorphism(H);
    end if;
  elif assigned M`Ambient then
    H := minimal_hecke_matrix_field(M`Ambient);
    if hack then
	M`minimal_hecke_field_emb := M`Ambient`minimal_hecke_field_emb;
    end if;
  elif IsParallelWeight(M) then
     H := Rationals();
     if hack then
	 K := hecke_matrix_field(M);
	 M`minimal_hecke_field_emb := hom<H->K|>;
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
    // add here the field embedding once we fix that
    is_sub, emb_fixed := IsSubfield(H, Kgal);
    assert is_sub;
    assert assigned M`weight_rep;
    assert assigned M`splitting_field_emb_weight_base_field; // WeightRepresentation should set it
    M`minimal_hecke_field_emb := M`splitting_field_emb_weight_base_field * emb_fixed;

    // Making sure we composed in the right order
    assert Domain(M`minimal_hecke_field_emb) eq H;
    
    vprintf ModFrmHil: "Time: %o\n", Cputime(time0);
  end if;
  return H;
end function;

// from definite.m

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
      DM`weight_rep:=M`weight_rep;
      DM`splitting_field_emb_weight_base_field := M`splitting_field_emb_weight_base_field;
   end if;
   return DM;
end function;

function WeightRepresentation(M : hack := true) // ModFrmHil -> Map
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
	 if hack then
	     QQ := Rationals();
	     M`splitting_field_emb_weight_base_field := hom<QQ->QQ|>;
	 end if;
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
	 if hack then
	     Fspl := F`SplittingField[1];
	     M`splitting_field_emb_weight_base_field := hom<Fspl->K | K!Fspl.1>;
	 end if;
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
