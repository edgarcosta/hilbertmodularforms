declare attributes AlgQuat : Splittings;

//-------------
//
// Compute a projective line
//
//-------------

function GetOrMakeP1(Gamma, N)
  // Gamma - GrpPSL2
  // N - RngOrdIdl
  //
  // Returns the cached output of ProjectiveLine(Gamma, N)
  Z_F := Order(N);
  Z_FN := quo<Z_F | N>;
  if not assigned Gamma`P1s_dict then
    Gamma`P1s_dict := AssociativeArray();
  end if;
  if IsDefined(Gamma`P1s_dict, N) then
    return Explode(Gamma`P1s_dict[N]);
  else
    P1N, P1Nrep := ProjectiveLine(Z_FN);
    Gamma`P1s_dict[N] := <P1N, P1Nrep>;
    return P1N, P1Nrep;
  end if;
end function;

//-------------
//
// Computing the weight representation
//
//-------------

function FastSymmetricPower(mat, n)
  K := BaseRing(mat);
  case n:
    when 0:
      return MatrixRing(K, 1)!1;
    when 1:
      return mat;
    else
      return SymmetricPower2(mat, n);
  end case;
end function;

function FiniteModulusCharFromHeckeChar(chi)
  // input:
  //   chi::GrpHeckeElt - A Hecke character over a field F
  //     of modulus N
  // returns:
  //   UserProgram - A function from FldNumElt to C* obtained as the restriction 
  //   of the Hecke character chi to the nonarchimedean primes dividing N.
  //   This is *not* the same as the Dirichlet restriction, which is the
  //   character on principal ideals induced by chi viewed as a ray class character.
  //   In particular, the Dirichlet restriction is trivial on units, whereas
  //   psi can be nontrivial on units (in practice we expect psi(e) = sign(e)^k)
  //   when k has odd components.
  comps := Components(chi);
  level, places := Modulus(chi);

  F := NumberField(Order(level));
  ZF := Integers(F);
  // require places eq [1..Degree(F)] : "Chi is not a narrow class group character.";
  // require (Degree(F) eq #InfinitePlaces(F)) : "The field is not totally real.";

  // implementing the character psi which is described above
  // as the product of the components of chi on the finite places
  psi := function(x); // x is a FldNumElt
    return (level eq 1*ZF) select 1 else &*[comps[v[1]](x) : v in Factorization(level)];
  end function;
  return psi;
end function;

function weight_map_arch(b, n : m:=[0 : _ in #n], X:=0, K:=0, splittings:=0)
  // b::AlgQuatElt or AlgAssVOrdElt
  // n::SeqEnum[RngIntElt]
  //
  // m::SeqEnum[FldRatElt] or SeqEnum[RngIntElt]
  // X::IdealDatum - A struct encoding a character chi of 
  //   modulus N and the mod N map from O to M2(ZF/N) produced by 
  //   ResidueMatrixRing.
  // K - FldNum
  // splittings - SeqEnum[AlgMatElt]
  //
  // returns a matrix corresponding to the action of b on
  // Wk = ⊗_i (Sym^(n_i) ⊗ det^(m_i)) ⊗ chi,
  // where b acts on the ith component via its image under
  // the ith embedding B -> M_2(K) coming from Splittings(B).
  //
  // Note that chi only makes sense when b lies in O_0(N) \cap B^*,
  // where O_0(N) is the Eichler order in a chosen maximal order 
  // consisting of elements whose bottom left entry (this makes sense
  // as long as N is coprime to the discriminant of B) is congruent to 0 mod N.
  //
  // If m is not assigned, we ignore the determinant factors above.
  // This comes up when Wk is being used as the coefficient module
  // for group cohomology of an arithmetic Fuchsian group.
  // In this setting, the reduced norm is always 1 so we can ignore the determinant terms. 

  // In practice, n = k - 2 and m depends on the choice of central character.
  // m will usually be integral but in the non-paritious case it is not possible
  // for it to be integral (but even then it will be at worst half-integral). 
  d := #m;
  
  if K cmpeq 0 and splittings cmpeq 0 then
    splittings, K, _ := Splittings(Parent(b));
  end if;

  // parallel weight 2 case
  // TODO abhijitm should account for m
  if n eq [0 : _ in [1 .. #n]] and Order(X`Character) eq 1 then
    return MatrixRing(Integers(), 1)!1;
  end if;

  M := MatrixRing(K, 1)!1;
  for l := d to 1 by -1 do
    // this casework looks gross because this function needs to be performant.
    if m[l] eq 0 and n[l] eq 0 then
      // don't need to modify M
      continue;
    else
      mat := splittings[l](b);
      if m[l] eq 0 then
        Ml := FastSymmetricPower(mat, n[l]);
      elif n[l] eq 0 then
        Ml := MatrixRing(K, 1)!(Determinant(mat)^m[l]);
      else
        // TODO abhijitm m[l] is a fraction then this probably needs to be in a
        // bigger number field, but I'm going to ignore this issue for now.
        Ml := Determinant(mat)^m[l] * FastSymmetricPower(mat, n[l]);
      end if;
      // Tensor product is associative; for efficiency always do
      // TensorProduct(small_mat, large_mat)
      M := TensorProduct(Ml, M);
    end if;
  end for;

  if X cmpne 0 then
    // if X is given then X`Character should be defined
    assert Type(X) eq IdealDatum;

    // if chi is trivial then we don't need to do anything
    chi := X`Character;
    if not IsTrivial(chi) then
      b_mod_N := X`ResidueMap(b);
      // TODO abhijitm this should maybe be removed for performance
      // The character only really makes sense (it's only really a character) if
      // b is in O_0(N) \cap B^*. 
      assert b_mod_N[2][1] in Modulus(chi);

      psi := FiniteModulusCharFromHeckeChar(chi);

      // if the order of chi is bigger than 2 then we need to work in a
      // bigger field extension, and strong coerce to make sure that things get
      // embedded properly. If the order of chi is 2 then we just multiply
      // by the value.
      if Order(chi) gt 2 then
        K := Compositum(K, CyclotomicField(Order(chi)));
        // the character should be evaluated on the bottom right entry
        M := psi(b_mod_N[1][1]) * StrongCoerceMatrix(K, M);
      else
        M := psi(b_mod_N[1][1]) * M;
      end if;
    end if;
  end if;

  return M;
end function;

function weight_rep_dim(k)
  return &*[k_i - 1 : k_i in k];
end function;

function is_paritious(k)
  return &and[((k_i - k[1]) mod 2 eq 0) : k_i in k];
end function;

// computes m (an input to weight_map_arch) from k
// TODO abhijitm eventually this should be a parameter
// that the user can set on instantiation of ModFrmHil
function m_from_k(k)
  if is_paritious(k) then
    k_0 := Max(k);
    return [(k_0 - k_i) div 2 : k_i in k];
  else
    // If the weight is nonparitious, we don't handle the
    // determinant twists in the weight representation, instead
    // handling it downstream so as to avoid dealing with
    // square roots.
    return [0 : k_i in k];
  end if;
end function;

function n_from_k(k)
  return [k_i - 2 : k_i in k];
end function;

function is_par_wt_2(k)
  return &and[k_i eq 2 : k_i in k];
end function;

// Computes the weight_rep_dim x weight_rep_dim matrix
// of the action of b (which is assumed to be in O_0(N) for
// N the ideal of X) on the weight representation. 
function matrix_of_action(b, k, X)
  n := n_from_k(k);
  m := m_from_k(k);

  if is_par_wt_2(k) and IsTrivial(X`Character) then
    return IdentitySparseMatrix(Integers(), weight_rep_dim(k));
  else
    return weight_map_arch(b, n : m:=m, X:=X);
  end if;
end function;

function matrix_of_induced_action(b, k, X)
  /*********************************************************************
   * b::AlgAssVOrdElt - An element of a quaternion order O / F. 
   * k::SeqEnum[RngIntElt] - Weight of the space of modular forms being computed
   * X::LevelDatum - A struct encoding (among other things) the level N, 
   *   nebentypus chi, a map iota_mod_N from O to M2(Z_F), where Z_F is the ring
   *   of integers of F, and coset representatives N_cosets of Gamma(N)\Gamma(1),
   *   where Gamma(1) and Gamma(N) are Fuchsian groups associated to O and an Eichler
   *   order O_0(N) respectively. 
   
   * returns->SparseMtrx - The matrix of the action of b on 
   *   V := Ind_(Gamma(N))^(Gamma(1)) Wk, 
   *   where Wk is defined in weight_map_arch.
   
   * Write {gamma_j} for the set N_cosets. Assuming b is in O, for each j there
   * exists a jb (right action) such that 
   * gamma_j * b = b' * gamma_(bj),
   * where b' is in O_0(N). 
   *
   * Write r for the number of cosets (this will be the order of the projective
   * line P1(ZF/N)). The matrix we produce is a r x r block matrix where each block
   * is square of dimension 
   * dim Wk = prod_i (k_i - 1).
   * In total dim V = r * prod_i (k_i - 1). 
   *
   * The nonzero blocks are block coordinates (j, bj), and in this block we have
   * the action of b' on Wk, where
   * b' := gamma_j * b * gamma_(bj)^-1. 
   * Note that this is in O_0(N), so there is a well defined action on Wk. 
   * To compute each block, we call weight_map_arch on b'. 
   ***********************************************************************/

  dim_W := weight_rep_dim(k);
  n := n_from_k(k);
  m := m_from_k(k);

  // R will be the ring over which our matrices are defined
  if is_par_wt_2(k) and IsTrivial(X`Character) then
    R := Integers();
  else
    _, K, _ := Splittings(Parent(b));
    R := Compositum(K, CyclotomicField(Order(X`Character)));
  end if;

  r := #X`P1Elements;

  blocks := [ZeroMatrix(R, dim_W) : _ in [1 .. r^2]];
  for u in X`P1Elements do
    x := (X`CosetRepsByP1[u][2]) * b;
    _, v := X`P1Rep(X`ResidueMap(x)[2], false, false);

    // this should now be in O_0(N) so we can apply weight_map_arch to it
    bp := x * (X`CosetRepsByP1[v][2])^(-1);
    // print bp;
    
    // The matrix for bp should live in the block whose row corresponds to
    // u and whose column corresponds to v.

    // X`CosetRepIdx[w] gives the index of the coset corresponding to the 
    // element w of P1(ZF/N). 
    row_major_idx := r * (X`CosetRepsByP1[u][1] - 1) + X`CosetRepsByP1[v][1];
    // print row_major_idx;

    if is_par_wt_2(k) and IsTrivial(X`Character) then
      blocks[row_major_idx] := MatrixRing(R, 1)!1;
    else
      blocks[row_major_idx] := weight_map_arch(bp, n : m:=m, X:=X);
    end if;

  end for;
  return SparseMatrix(BlockMatrix(r, r, blocks));
end function;

//-------------
//
// Computing splittings of quaternion algebras
//
//-------------

intrinsic Splittings(B::AlgQuat) -> SeqEnum[Map], FldNum, FldNum
  {
    input:
      B - A quaternion algebra defined over a degree n field F.
    returns:
      A SeqEnum of n maps from B to M2(K), where K is the minimal field
      over which such a sequence can be defined. Each map in the sequence
      corresponds to one of the infinite places of F. 

      We also return the field K as well as (TODO abhijitm no clue why but 
      I didn't want to change it) an unoptimized version of K. 
  }
  if assigned B`Splittings then
    return Explode(B`Splittings);
  end if;

  F := BaseField(B);
  vs := InfinitePlaces(F);
  // define weight_base_field = extension K/F containing Galois closure of F and 
  // containing a root of every conjugate of the minimal polynomial of B.1
  if assigned F`SplittingField then
    K,rts := Explode(F`SplittingField);
  else
    K,rts := SplittingField(F : Abs := true, Opt := false);
    F`SplittingField := <K, rts>;
  end if;

  embeddings_F_to_K := [hom<F->K | r> : r in rts];
  B1coeffs := Coefficients(MinimalPolynomial(B.1));
  alphas := [K| ];
  for FtoK in embeddings_F_to_K do
    hh := PolynomialRing(K)! [c@FtoK : c in B1coeffs];
    if IsIrreducible(hh) then
       K := ext<K|hh>;
       alphas := ChangeUniverse(alphas,K) cat [K.1];
    else
       Append(~alphas, Roots(hh)[1][1]);
    end if;
  end for;
  // make weight_base_field an (optimized) absolute field, for efficiency in later calculations 
  weight_field := K; // names appears in verbose output 
                     // TODO abhijitm I don't really get why we can't let K be the optimized
                     // representation but I'm too lazy to think about it now and this is how
                     // it was so we return this separately. 
  K := AbsoluteField(K);
  K := OptimizedRepresentation(K);

  // sort the embeddings so that they are consistent with the order of the embeddings
  // coming from InfinitePlaces(F)
  prim_elt_emb_dict, f := PrimitiveEltEmbedDict(F);
  embeddings_F_to_K  :=  [hom<F->K | K!r> : r in rts]; // same embeddings, now into extended field K
  sorted_embs := embeddings_F_to_K;
  sorted_alphas := alphas;
  a := PrimitiveElement(F);
  for j in [1 .. #embeddings_F_to_K] do
    emb := embeddings_F_to_K[j];
    alpha := alphas[j];
    b, i := IsDefined(prim_elt_emb_dict, f(Evaluate(emb(a), MarkedEmbedding(K))));
    require b : "Something's gone wrong with finding embeddings of F into K";
    sorted_embs[i] := emb;
    sorted_alphas[i] := alpha;
  end for;

  embeddings_F_to_K := sorted_embs;
  alphas := sorted_alphas;


  require B.1*B.2 eq B.3 : "We assume B.1 * B.2 == B.3 when defining\
    the splitting homomorphisms.";
  splitting_seq := [];
  for i := 1 to Degree(F) do
    h := embeddings_F_to_K[i];
    // need a splitting homomorphism (B tensor K) -> Mat_2(K) whose restriction to K is h 
    alpha := alphas[i];
    b := K! h(F!(B.2^2));
    iK := Matrix(K, 2, [alpha, 0, 0, -alpha]); 
    jK := Matrix(K, 2, [0, 1, b, 0]); 
    kK := iK*jK;
    assert K! h(B.3^2) eq (kK^2)[1,1]; 
    Append(~splitting_seq, 
        map< B -> MatrixRing(K,2)|
          q:-> h(s[1])+h(s[2])*iK+h(s[3])*jK+h(s[4])*kK where s := Eltseq(q) >);
  end for;
  B`Splittings := <splitting_seq, K, weight_field>;
  return splitting_seq, K, weight_field;
end intrinsic;

intrinsic Splittings(O::AlgAssVOrd) -> SeqEnum[Map], FldNum, FldNum
  {}
  return Splittings(Algebra(O));
end intrinsic;

