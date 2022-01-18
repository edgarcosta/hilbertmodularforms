

import "copypastefunctions.m" : hecke_matrix_field,
                                random_large_split_prime_using_max_order,
                                random_large_split_prime,
                                reduction,
                                dimension_lower_bound,
                                hecke_algebra_dimension,
                                hecke_algebra,
                                CharacteristicPolynomialViaCRT,
                                NewformsOfDegree1Implemented,
                                basis_is_honest,
                                pseudo_inverse,
                                red_eigenvector,
                                get_red_vector,
                                IsBianchi,
                                Ambient,
                                BMF_with_ambient,
                                HMF0,
                                weight_map_arch;


forward WeightRepresentationFiniteField;

/**************** New intrinsics **********************/

intrinsic HilbertCuspForms(
  F::FldNum,
  N::RngOrdIdl,
  k::SeqEnum[RngIntElt],
  pp::RngOrdIdl
  :
  QuaternionOrder:=0
  ) -> ModFrmHil
{The space of Hilbert modular forms over the totally real number field F,
 with level N and weight k with coefficients over GF(pp).
 Here N should be an ideal in the maximal order of F, and k should be a
 sequence of integers.
 If the optional argument QuaternionOrder is specified, this order
 will be used for all computations of the space.}
  require Seqset(k) ne {2} : "not suported for parallel weight 2";
  M := HilbertCuspForms(F, N, k : QuaternionOrder:=QuaternionOrder);
  _ := WeightRepresentationFiniteField(M, pp);
  return M;
end intrinsic;

intrinsic HilbertCuspForms(
  F::FldNum,
  N::RngOrdIdl,
  k::SeqEnum[RngIntElt],
  p::RngIntElt
  :
  QuaternionOrder:=0
  ) -> ModFrmHil
{The space of Hilbert modular forms over the totally real number field F,
  with level N and weight k with coefficients over an extension of GF(p).
  Here N should be an ideal in the maximal order of F, and k should be a
  sequence of integers.
  If the optional argument QuaternionOrder is specified, this order
  will be used for all computations of the space.}
  require Seqset(k) ne {2} : "not suported for parallel weight 2";
  M := HilbertCuspForms(F, N, k : QuaternionOrder:=QuaternionOrder);
  _ := WeightRepresentationFiniteField(M, p);
  return M;
end intrinsic;


intrinsic HilbertCuspFormsFiniteField(
  F::FldNum,
  N::RngOrdIdl,
  k::SeqEnum[RngIntElt]
  :
  QuatOrder:=0 // need to use the intrinsic inside QuaternionOrder
  ) -> ModFrmHil, RngOrdIdl
{The space of Hilbert modular forms over the totally real number field F,
  with level N and weight k with coefficients over GF(pp).
  Here N should be an ideal in the maximal order of F, and k should be a
  sequence of integers.
  If the optional argument QuatOrder is specified, this order
  will be used for all computations of the space.}
  require Seqset(k) ne {2} : "not suported for parallel weight 2";
  M := HilbertCuspForms(F, N, k : QuaternionOrder:=QuatOrder);


  //find a large split prime

  // copy paste from WeightRepresentationFiniteField
  // thus, we recompute K twice... c'est la vie

  H:=Algebra(QuaternionOrder(M));
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
    end if;
  end for;
  K := AbsoluteField(K);
  K := OptimizedRepresentation(K);
  pp := random_large_split_prime(K);

  _ := WeightRepresentationFiniteField(M, pp);
  return M;
end intrinsic;

/************** end of new intrinsic ****************/

// originally from hecke.m
function reduction_mod_random_large_split_prime(T, F)
  // hack begins
  if IsFinite(F) then
    return T, Characteristic(F);
  end if;
  // hack ends
  repeat
    P := random_large_split_prime(F);
    bool, U := reduction(T, P);
  until bool;
  return U, P;
end function;

// originally from definite.m
function WeightRepresentationFiniteField(M, p) // ModFrmHil -> Map
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

      // hack begins
      if Type(p) eq RngIntElt then
        pp := PrimeIdealsOverPrime(K, p)[1];
      else
        bool, iso := IsIsomorphic(NumberField(Order(p)), K);
        assert bool;
        pp := ideal<Integers(K) | [iso(K!g) : g in Generators(p)]>;
      end if;
      FF, OKtoFF := ResidueClassField(pp);
      KtoFF := map<K->FF | x :-> OKtoFF(x*d)/FF!d where d:= Denominator(x)>;
      splitting_seq_FF := [];
      M2KtoFF := hom<MatrixRing(K, 2) -> MatrixRing(FF, 2) | KtoFF>;
      splitting_seq_FF := [s*M2KtoFF : s in splitting_seq];

      M2FF:=MatrixRing(FF, M`weight_dimension);
      M`weight_rep:=map<H -> M2FF|q :-> weight_map_arch(q, splitting_seq_FF, FF, m, n)>;
      M`weight_base_field := FF;
      print "hack rulezzzz";
      // hack ends
    end if;
    return M`weight_rep, M`weight_dimension, M`weight_base_field;
  end if;
end function;




intrinsic NewformDecomposition(M::ModFrmHil : Dimensions:=0) -> List
{Given a new space M of Hilbert modular forms, this decomposes M into subspaces
 that are irreducible as Hecke modules, and returns this list of new spaces}

  // Check if full decomposition is stored
  bool, ND := HasAttribute(M, "NewformDecomposition");
  if bool and Dimension(M) eq &+ [Integers()| Dimension(N) : N in ND] then
    if Dimensions cmpeq 0 then
      return ND;
    elif Type(Dimensions) eq RngIntElt then
      return [* N : N in ND | Dimension(N) eq Dimensions *];
    else
      return [* N : N in ND | Dimension(N) in Dimensions *];
    end if;
  end if;

  dim := Dimension(M : UseFormula := false);

  if Dimensions cmpeq 0 then
    Dimensions := [1..dim];
  elif Type(Dimensions) eq RngIntElt then
    Dimensions := [Dimensions];
  else
    require ISA(Type(Dimensions), Setq) and Type(Universe(Dimensions)) eq RngInt:
            "'Dimensions' should be a sequence of integers";
  end if;

  require IsNew(M) or dim eq 0 :
         "Currently implemented only for new spaces (constructed using NewSubspace)";

  if assigned M`HeckeIrreducible and M`HeckeIrreducible then
    // M was constructed by NewformDecomposition
    if not assigned M`HeckeMethod then
      M`HeckeMethod := 1;
    end if;
    ND := [* M *];

  elif dim eq 0 then
    ND := [* *];

  /* TO DO
  elif dim eq 1 then
    endow M with the attributes of an eigenspace
    ND := [* M *];
  */

  elif Dimensions eq [1] and NewformsOfDegree1Implemented(M)
and dim ne 1 // beware recursion
  then
    return [* Parent(f) : f in NewformsOfDegree1(M) *];

  else

// !!!!! possibly don't SetRationalBasis first !!!!!
// SetRationalBasis(M);

    K := hecke_matrix_field(M); // Hecke matrices should be over this, currently

    T, primes, v, _, P, t, comb := Explode(hecke_algebra(M : generator));
    assert BaseRing(t) eq K;

    vprintf ModFrmHil: "Characteristic polynomial of Hecke algebra generator: ";
    vtime ModFrmHil:
    // hack starts
    if K cmpeq Rationals() or not IsParallelWeight(M) or IsFinite(K) then
    // hack ends
      chi := CharacteristicPolynomial(t);
    else
      // parallel weight ==> poly is over Z
      apbound := &+ [Abs(comb[i])*HeckeEigenvalueBound(M,primes[i])
                    : i in [1..#primes] | comb[i] ne 0];
      bound := dim*apbound^dim;
      chi := CharacteristicPolynomialViaCRT(t, bound);
    end if;

    // decomposition should be over the true hecke field (= Q for parallel weight)
    // chi := ChangeRing(chi, minimal_hecke_matrix_field(M));

    vprintf ModFrmHil: "Factoring the polynomial: ";
    vtime ModFrmHil:
    fact := Factorization(chi);
    assert forall{tup: tup in fact | tup[2] eq 1};

    if #fact eq 1 then
      M`HeckeIrreducible := true;
    end if;

    vprintf ModFrmHil: "Decomposition dimensions: %o = %o\n", dim, [Degree(tup[1]) : tup in fact];

    fact1 := Dimensions cmpeq 0 select fact
                                else [tup: tup in fact | Degree(tup[1]) in Dimensions];
    if IsEmpty(fact1) then
      return [* *];
    end if;
    // TO DO: elif #fact eq 1 then

    // CHECK: each field should either be totally real or a CM field
    /* another day
    vprintf ModFrmHil, 2: "Checking the eigenvalue fields look okay: ";
    vtime ModFrmHil, 2:
    for tup in fact1 do
      if BaseRing(K) cmpeq Rationals() then
        real_pols := [* tup[1] *];
      else
        real_pols := [* Polynomial([Real(Conjugate(c,i)) : c in Eltseq(tup[1])])
                      : i in [1..Degree(K)] *];
      end if;
      real_roots := [#Roots(pol) : pol in real_pols];
      okay := &and [num eq Degree(tup[1]) : num in real_roots] or &and [num eq 0 : num in real_roots];
      error if not okay,
        "Serious bug detected!!!\nThe eigenvalue fields are not of the expected kind.\n" * please_report;
    end for;
    */

    // Construct the irreducible subspaces, in some form.
    // Here we have lots of choices:
    // (1) proceed as Allan did over Q: write down trivial basis of each component
    //     using the trick below, then echelon using rational reconstruction.
    // (2) write down a nicer basis by taking images, so that action of known
    //     heckes is integral.  Use LLL.  Don't find inverse change of basis:
    //     obtain hecke matrices in new basis via CRT, since they are integral.
    // (3) Don't write down a basis.  Compute an eigenform by doing Nullspace
    //     over an extension (use rational reconstruction).  Hecke operators on
    //     each subspace are obtained as representation matrices of eigenvalues.

HeckeMethod := assigned M`HeckeMethod
               select M`HeckeMethod else 1;

if HeckeMethod eq 4 then
 "\nWARNING!!!  Method 4 was specified in NewformDecomposition!" *
 "\n\nThis method transcends normal dimensions: it exists in a" *
 "\nhyperspatial paradigm whose existentiality is not known to be" *
 "\nconsistent with the Magma philosophy. This may be dangerous.";
end if;
    if HeckeMethod eq 0 then

      // Obvious way to decompose:
      components := [* KernelMatrix(Evaluate(tup[1], t)) : tup in fact *];

      "WARNING: Method 0 was selected!!! (Usefulness = 0)";

    elif HeckeMethod eq 1 then

      // Write down basis of each component.
      // For each prime factor f with chi = f*g, the corresponding newform space is
      // Ker f(t) = Im g(t) which has (rational) basis [v*g(t)*t^i : 0 <= i < deg(g)]

      // First write down (rational) basis [v*t^i : 0 <= i < dim]
      v_images := ZeroMatrix(K, dim, dim);
      InsertBlock(~v_images, v, 1, 1);
      vti := v;
      vprintf ModFrmHil: "Spinning: ";
      vtime ModFrmHil:
      for i := 1 to dim-1 do
        vti := vti * t;
        InsertBlock(~v_images, vti, i+1, 1);
      end for;

      components := [* *];
      vprintf ModFrmHil: "Decomposing: ";
      vtime ModFrmHil:
      for tup in fact do
        f := tup[1];
        g := chi div f;
        d := Degree(f);
        vprintf ModFrmHil: "%o ", d;
        gcoeffs := ChangeRing(Vector(Eltseq(g)), K);
        // build left-multiplier matrix (rows determine basis elements)
        coeff_mat := ZeroMatrix(K, d, dim);
        for i := 1 to d do
          InsertBlock(~coeff_mat, gcoeffs, i, i);
        end for;
        bas_mat := coeff_mat * v_images;
        // better echelonize now, will be needed immediately below (in method 1)
        vprintf ModFrmHil, 3: "Echelonizing basis: ";
        vtime ModFrmHil, 3:
        bas_mat := EchelonForm(bas_mat);
        Append(~components, bas_mat);
      end for;

    end if;

    if HeckeMethod le 1 then

      // TO DO: the hecke_matrix_field business here might not be correct
      // Previously we had SetRationalBasis on M and its ambient at the start.
      // Here we do have a rational basis of each component (at least in method 1).

      MA := Ambient(M);
      ND := [* *];
      vprintf ModFrmHil: "Setting up newform spaces: ";
      vtime ModFrmHil:

      for k := 1 to #components do
        kmat := components[k];
        if Nrows(kmat) notin Dimensions then
          continue;
        end if;

        if IsBianchi(M) then
          N := BMF_with_ambient(MA);
          N`NewLevel := N`Level;
        else
          N := HMF0(BaseField(M), Level(M), Level(M), DirichletCharacter(M), Weight(M), CentralCharacter(M));
          N`Ambient := MA;
        end if;
        // give N same ambient as M (TO DO: but reconsider when to make M wrt ambient, rather than wrt raw?)
        N`is_new := true;
        N`HeckeIrreducible := true;
        if assigned M`hecke_matrix_field then
          N`hecke_matrix_field := M`hecke_matrix_field;
        end if;
        field := hecke_matrix_field(N`Ambient);
        if #components eq 1 then
          pseudo_inv := kmat ^ -1;
        else
          complement := VerticalJoin(<components[i] : i in [1..#components] | i ne k>);
          pseudo_inv := pseudo_inverse(kmat, complement);
        end if;
        N`Dimension := Nrows(kmat);
        if assigned M`basis_matrix_wrt_ambient then
          N`basis_matrix_wrt_ambient := ChangeRing(kmat, BaseRing(A)) * A
                                                   where A is M`basis_matrix_wrt_ambient;
          N`basis_matrix_wrt_ambient_inv := Ai * ChangeRing(pseudo_inv, BaseRing(Ai))
                                                   where Ai is M`basis_matrix_wrt_ambient_inv;
          N`basis_matrix := ChangeRing(N`basis_matrix_wrt_ambient, BaseRing(A)) * A
                                                   where A is MA`basis_matrix;
          N`basis_matrix_inv := Ai * ChangeRing(N`basis_matrix_wrt_ambient_inv, BaseRing(Ai))
                                                   where Ai is MA`basis_matrix_inv;
        else
          N`basis_matrix := ChangeRing(kmat, BaseRing(A)) * A
                                                   where A is M`basis_matrix;
          N`basis_matrix_inv := Ai * ChangeRing(pseudo_inv, BaseRing(Ai))
                                                   where Ai is M`basis_matrix_inv;
        end if;
        if assigned M`basis_is_honest then
          N`basis_is_honest := M`basis_is_honest;
        end if;
        Append(~ND, N);
      end for; // k

    else
      assert HeckeMethod ge 3; // Method 2 does not exist!

      if HeckeMethod eq 3 then
        "WARNING: Method 3 was selected for Hecke eigenform computations!!!";
        "         It's a very inefficient method (just warm-up for method 4)";
      end if;

      ND := [* *];

      assert K eq BaseRing(t);
      vprintf ModFrmHil, 2: "Checking hecke_algebra_generator (should take no time): ";
      vtime ModFrmHil, 2:
      assert t eq &+ [comb[i]*HeckeOperator(M,primes[i]) : i in [1..#primes]];
      M`hecke_algebra_generator := <primes, comb, t>; // this must never be changed

      vprintf ModFrmHil: "Setting up newform spaces: ";
      vtime ModFrmHil:
      for tup in fact1 do
        // Construct eigenvalue field E
        f := tup[1];
        if Degree(f) eq 1 then
          E := BaseRing(f);
          e := Roots(f)[1][1];
        else
  	  E := ext< BaseRing(f) | f >; e:=E.1;// TO DO: Check:=false ?
        end if;

        // This space will not need any basis matrix stuff.
        // Hecke eigenvalues will be calculated from data stored in the eigenform.

        N := HMF0(BaseField(M), Level(M), Level(M), DirichletCharacter(M), Weight(M), CentralCharacter(M));
        N`Ambient := M;    // eigenvectors are expressed wrt the basis of M
        N`NewSpace := M;   // (this is used in best_column -- why not use ambient?)
        N`HeckeIrreducible := true;
        N`is_new := true;
        N`Dimension := Degree(f);

        // eigenvalue corresponding to N`Ambient`hecke_algebra_generator
        // TO DO: if debug, check it really is an eigenvalue of that
        N`hecke_algebra_generator_eigenvalue := e;

        Append(~ND, N);
      end for;

    end if; // HeckeMethod

    for i := 1 to #ND do
      ND[i]`HeckeMethod := HeckeMethod;
    end for;

  end if;

  if &+ [Integers()| Dimension(N) : N in ND] eq Dimension(M) then
    M`NewformDecomposition := ND;
  end if;

  return ND;
end intrinsic;

intrinsic Eigenform(M::ModFrmHil) -> ModFrmHilElt
{An eigenform in the space M of Hilbert modular forms
 (which must be an irreducible module under the Hecke action)}

  require assigned M`HeckeIrreducible and M`HeckeIrreducible :
         "This is implemented only for spaces constructed using NewformDecomposition";

  require Dimension(M) gt 0 : "The given space M should not be zero-dimensional";

   if not assigned M`Eigenform then

METHOD := M`HeckeMethod;

     vprintf ModFrmHil: "Setting up eigenform for space of dimension %o", Dimension(M);
     vprintf ModFrmHil, 2: " (using METHOD %o)", METHOD;
     vprintf ModFrmHil: "\n";

     nf := New(ModFrmHilElt);
     nf`Parent := M;

if METHOD lt 3 then

     // Old way: determine the Hecke algebra of this newform space

     T, _, _, _, _, t := Explode(hecke_algebra(M : generator));

     vprintf ModFrmHil: "CharacteristicPolynomial: ";
     vtime ModFrmHil:
     chi := CharacteristicPolynomial(t);
     //chi := ChangeRing(chi, minimal_hecke_matrix_field(M)); // decomposition over this field
     require IsIrreducible(chi) :
            "The space M is not an irreducible module under the Hecke action";

     if Degree(chi) eq 1 then
       E := BaseRing(chi);
       e := t[1][1];
     else
       // begin hack
       //E := NumberField(chi); e:=E.1;
       E := ext<BaseRing(chi)|chi>; e:=E.1;
       // end hack
     end if;
     nf`BaseField := E;

     K := BaseRing(t);
     if K eq E then
       EK := K;
     else
       //begin hack
       if IsFinite(E) then
         EK := ext<E| DefiningPolynomial(K)>;
       else
         EK := CompositeFields(K, E)[1];
       end if;
       // end hack
     end if;

     tEK := ChangeRing(t, EK);
     eEK := EK!e;

     nf`BaseField := E;
     nf`EK := EK;
     nf`tEK := tEK;
     nf`eEK := eEK;

     vprintf ModFrmHil: "Eigenspace: ";
     vtime ModFrmHil:
     espace := Eigenspace(tEK, eEK);
     assert Dimension(espace) eq 1;
     nf`coords_wrt_parent := Basis(espace)[1];
     if basis_is_honest(M) then
       nf`coords_raw := nf`coords_wrt_parent * ChangeRing(M`basis_matrix, EK);
     end if;

elif METHOD ge 3 then

     // M is a component of the NewformDecomposition of M`Ambient
     // Write down an eigenvector relative to M`Ambient
     // TO DO: using rational reconstruction

     // Note: E is already defined above

     t := M`Ambient`hecke_algebra_generator[3];
     e := M`hecke_algebra_generator_eigenvalue;
     E := Parent(e);
     K := BaseRing(t);

     // Construct a composite EK
     f := DefiningPolynomial(E);
     if Degree(f) eq 1 then
       EK := K;
     else
       vprintf ModFrmHil, 2: "Factorization: ";
       vtime ModFrmHil, 2:
       fact := Factorization(ChangeRing(f,K));
       fK := fact[1][1];
       if Degree(fK) eq 1 then
         EK := K;
         if EK ne E then
           Embed(E, EK, Roots(fK)[1][1]);
         end if;
       else
         EK := ext< K | fK >;
         Embed(E, EK, EK.1);
        /*
         // old work around
         // use the absolute field so that coercion works for EK to E
         EKrel := ext< K | fK >;
         EK := AbsoluteField(EKrel);
         Embed(E, EK, EK!EKrel.1);
        */
       end if;
       // Doesn't help to use absolute, optimized EK
     end if;

     tEK := ChangeRing(t, EK);
     eEK := EK!e;

     nf`BaseField := E;
     nf`EK := EK;
     nf`tEK := tEK;
     nf`eEK := eEK;

end if;

if METHOD eq 3 then

     vprintf ModFrmHil: "Eigenspace of degree %o: ", Degree(f);
     vtime ModFrmHil:
     V := Eigenspace(tEK, eEK);
     assert Dimension(V) eq 1;
     v := Vector(V.1);
     nf`coords_wrt_ambient := v;

     MA := M`Ambient;
     if basis_is_honest(MA) then
       nf`coords_raw := ChangeRing(v, EK) * ChangeRing(MA`basis_matrix, EK);
     end if;

elif METHOD eq 4 then

     // collect some eigenvectors mod P
     nf`red_coords_wrt_ambient := [* *];
     // TO DO: delay until needed (this is here for testing only)
     get_red_vector(EK, tEK, eEK, ~nf`red_coords_wrt_ambient : NUM:=10);

end if; // METHOD

     nf`hecke_eigenvalues := AssociativeArray(PowerIdeal(Integers(BaseField(M))));
     M`Eigenform := nf;

   end if; // not assigned M`Eigenform

   return M`Eigenform;
end intrinsic;
