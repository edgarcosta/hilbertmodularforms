intrinsic HeckeStableSubspace(
    V::SeqEnum,
    pp::RngQuadIdl
    ) -> SeqEnum
    {
    Given a sequence of forms V and an ideal pp, compute a basis of the subspace of span(V) that is stable under the Hecke operator T_pp. 
    }
    
    // compute the kernel of Tp
    // we include the kernel in our final output
    // because it is also Hecke stable
    TpV := [HeckeOperator(f, pp) : f in V];
    lindep := LinearDependence(TpV);
    Tp_kernel := [&+[vec[i]*V[i] : i in [1 .. #V]] : vec in lindep];

    // removing the kernel before entering the 
    // iterative intersection loop
    V := [V[i] : i in PivotRows(CoefficientsMatrix(TpV))];
    Vprev := V;
    dimprev := #V;
    
    for _ in [1 .. #V] do
        vprintf HilbertModularForms:  "Current dim = %o\n", dimprev;
        TpVprev := [HeckeOperator(g, pp) : g in Vprev];
        lindep := LinearDependence(Vprev cat TpVprev);
        dimnew := #lindep;
        
        vprintf HilbertModularForms: "New dim = %o\n", dimnew;
        
        if dimnew eq 0 then
            return Tp_kernel;
        end if;
        
        require dimnew le dimprev: "Something went wrong, probably need to increase precision.";

        Vnew := [];
        for vec in lindep do
            f := &+[vec[i]*Vprev[i] : i in [1 .. #Vprev]];
            M := CoefficientsMatrix([f]); 
            d := Denominator(M);
            M := Matrix(Integers(),d*M);
            gcd_M := GCD(Eltseq(M));
            // If the generalization of Schaeffer's theorem to HMFs is true,
            // then this can never happen
            require gcd_M ne 0 : "We didn't think this could happen -- you may have found\
                    an interesting example! Please email TODO.";
            Append(~Vnew, f/gcd_M);
        end for;

        // If the iterative intersection process has stabilized,
        // then exit the loop.
        if dimprev eq dimnew then
            return Vnew cat Tp_kernel;
        end if;

        assert #Vnew eq dimnew;
        
        Vprev := Vnew;
        dimprev := #Vprev;
    end for;
end intrinsic;


// Computes a basis of cuspidal weight 1 forms.
intrinsic HeckeStabilityCuspBasis(
    Mk::ModFrmHilD
    :
    prove := true
    ) -> SeqEnum[ModFrmHilDElt]
    {Compute the space Mk using the Hecke stability method. 
        - The optional parameter prove is true or false. If true, we verify that we had enough precision to check the equality of the potentially meromorphic form with a holomorphic one.
    }
    
    M := Parent(Mk);
    k := Weight(Mk);
    N := Level(Mk);
    chi := Character(Mk);
    chi_prim := AssociatedPrimitiveCharacter(chi);

    // This comes from the fact that we don't currently support 
    // computation of cusp spaces with nebentypus of nontrivial 
    // Dirichlet restriction. If and when this changes, 
    // this line should be removed and the code modified. 
    require IsGamma1EisensteinWeight(chi, 1) : "Hecke stability does not work for characters which are not totally odd";

    F := BaseField(M);
    ZF := Integers(M);
    n := Degree(F);

    par_wt_1 := [1 : _ in [1 .. n]];
    MEis := HMFSpace(M, N, par_wt_1, chi^-1);
    triv_char := HeckeCharacterGroup(1*ZF, [1,2]).0;
    MEis := HMFSpace(M, N, par_wt_1, chi^-1);
    triv_char := HeckeCharacterGroup(1*ZF, [1 .. n]).0;
    // By Proposition 2.1 in DDP11 (https://annals.math.princeton.edu/wp-content/uploads/annals-v174-n1-p12-s.pdf)
    // this Eisenstein series should be nonzero at the cusp at infinity in
    // every component. Thus, we should be able to divide by it
    // and obtain something with nebentypus character chi. 
    myarray := EisensteinConstantCoefficient(M, par_wt_1, chi_prim^-1, triv_char);
    require &*[myarray[key] : key in Keys(myarray)] ne 0 : "The Eisenstein series you've chosen is 0 at some cusps at infinity";
    
    // TODO abhijitm there's something annoying going on here
    // with imprimitive characters,
    // possibly to do with our constructions of Eisenstein series
    // I'll come back to it after I've fixed some of the issues
    // with coefficient rings and stuff, but this should be
    // functional for now. 
    //
    // We take the primitive character 
    Eis := EisensteinSeries(MEis, chi_prim^-1, triv_char);
        
    //Load space of Cusp forms of weight [k1 + 1, ..., kn + 1], level N, and trivial character
    vprintf HilbertModularForms: "Computing basis of cusp forms of weight %o, level %o\n", [k[i] + 1 : i in [1 .. n]], N;
    Mkl := HMFSpace(M, N, [k[i] + 1 : i in [1 .. n]]);
    Bkl := CuspFormBasis(Mkl);
    vprintf HilbertModularForms: "Size of basis is %o.\n", #Bkl;
    
    require #Bkl eq CuspDimension(Mkl) : "Need to increase precision to compute this space"; 

    if #Bkl eq 0 then
      return [];
    end if;

    vprintf HilbertModularForms: "Dividing by the Eisenstein series\n";
    
    //Our initial candidate for our desired space.
    V := [f/Eis : f in Bkl];
   
    // We want to choose the prime pp of smallest norm among
    // the primes not dividing N
    bound := 20;
    primes := PrimesUpTo(bound, F:coprime_to := N);
    // if N divides every prime of norm up to 20, which seems
    // unlikely, but just in case 
    if #primes eq 0 then 
        primes := PrimesUpTo(Norm(N), F:coprime_to := N)[1];
    end if;
    pp := primes[1];

    vprintf HilbertModularForms: "Computing Hecke stable subspace for prime %o\n of norm %o.\n", pp, Norm(pp);
    
    V := HeckeStableSubspace(V, ZF!!pp);

    if #V eq 0 then
        return V;
    end if;
    
    //Now V is our updated candidate for the space of weight 1 forms. We need to check if the forms are holomorphic by squaring.
    vprintf HilbertModularForms: "Checking that forms are holomorphic by squaring\n";

    d := Order(chi);
    Mk_dth_power := HMFSpace(M, N, [d*k[i] : i in [1 .. n]]);
    Bmod := Basis(Mk_dth_power);
    Bcusp := CuspFormBasis(Mk_dth_power);
    
    require #Bcusp eq CuspDimension(Mk_dth_power): "Need to increase precision to compute this space";
    
    vprintf HilbertModularForms: "Done?\n";
    done := true;
    for f in V do
        assert Character(Parent(f)) eq chi;
        assert Level(Parent(f)) eq N;
        Bmodandfd := Append(Bmod, f^d);
        // If f^d is not in the upstairs (weight dk) space 
        // of modular forms then V must not have been Hecke stable
        if #LinearDependence(Bmodandfd) eq 0 then
            done := false;
            vprintf HilbertModularForms: "No!\n";
            break f;
        end if;
    end for;
    if done then
        vprintf HilbertModularForms: "Found a Hecke stable subspace!\n";

        // We should now remove any Eisenstein series that ended up in this space
        // so that we are left with only cusp forms
        eigs := Eigenbasis(Mk, V);
        V := [];
        for eig in eigs do
          // if eig^2 is a cusp form in the upstairs space, 
          if #LinearDependence(Append(Bcusp, eig^d)) ne 0 then
            Append(~V, eig);
          end if;
        end for;
        
        if prove then
            vprintf HilbertModularForms: "Need to verify that the precision is large enough to compute the space larger space\n";

            Vcheck := Basis(HMFSpace(M, N, [2*k[1] + 2,2*k[2] + 2]));
            assert #LinearDependence(Vcheck) eq 0;
        end if;

        return V;
    end if;
    return [];
end intrinsic;

// Computes a basis of cuspidal weight 1 forms.
intrinsic Weight1CuspBasis(
  Mk::ModFrmHilD
  :
  prove := true
  ) -> SeqEnum[ModFrmHilDElt]
  {Compute the basis of cuspidal parallel weight 1 forms using the Hecke stability method.
   - The optional parameter prove is true or false. If true, we verify that we had enough precision to check the equality of the potentially meromorphic form with a holomorphic one.
  }
  return HeckeStabilityCuspBasis(Mk : prove := prove);
end intrinsic;

///////////// Eigenbasis computation ////////////////

// This code computes an eigenbasis for a Hecke-stable space 
// of meromorphic ModFrmHilDElt objects by examining the action
// on the Fourier coefficients. 
//
// At the time of writing, the only code we have for computing
// Hecke matrices is via the quaternion algebra methods in 
// ModFrmHil/copypaste/hecke.m. These do not work for the
// spaces of ratios of forms we obtain in Hecke stability. 
//
// For most applications, the ModFrmHil code should be used. 

intrinsic Eigenbasis(M::ModFrmHilD, basis::SeqEnum[ModFrmHilDElt] : P := 60) -> SeqEnum[ModFrmHilDElt]
  {
    inputs:
      M: A space of forms on which the Hecke algebra acts by
           commuting self-adjoint operators.
      basis: A sequence of linearly independent ModFrmHilDElts
             whose span is preserved by all the Hecke operators.
      P: The largest norm of a prime ideal we check to establish a simultaneous eigenbasis
    returns:
      A sequence of HMFs which are an eigenbasis for the Hecke operators of primes
      up to P. The forms are normalized where possible.
  }
  
  MGRng := Parent(M);
  F := MGRng`BaseField;
  ZF := Integers(F);
  dd := Different(ZF);
  hecke_matrices := [HeckeMatrix(basis, pp) : pp in PrimesUpTo(P, F)];

  // B stores a matrix such that B * M * B^-1 is
  // diagonal for every Hecke matrix M. 
  // If e_i denotes the ith standard basis vector
  // and v_i denotes the ith eigenvector in the 
  // given basis, then this means that B^-1 e_i = v_i. 
  // Therefore, the ith column of B^-1 is v_i.
  _, B := Diagonalization(hecke_matrices);
  Binv := B^-1;

  eigs := [];

  // the columns of P should be the coefficients
  // of linear combinations of basis vectors giving
  // rise to eigenvectors
  // TODO is there really no way to get the columns of an AlgMatElt? 
  for v in Rows(Transpose(Binv)) do
    Append(~eigs, &+[v[i] * basis[i] : i in [1 .. #basis]]);
  end for;

  frob_traces := AssociativeArray();
  for eig in eigs do
    frob_traces[eig] := AssociativeArray(); 
    bb_1 := NarrowClassRepresentative(MGRng, dd);
    a_1 := Coefficients(eig)[bb_1][MGRng`IdealShitaniReps[bb_1][ideal<ZF|1>]];

    for nn in IdealsUpTo(P, F) do
      bb := NarrowClassRepresentative(MGRng, nn^-1 * dd);
      frob_traces[eig][nn] := Coefficients(eig)[bb][MGRng`IdealShitaniReps[bb][nn]] / a_1;
    end for;
  end for;
  return eigs, frob_traces;
end intrinsic;

intrinsic HeckeMatrix(basis::SeqEnum[ModFrmHilDElt], nn::RngOrdIdl) -> Mtrx
  {
    inputs:
      basis: A sequence of linearly independent ModFrmHilDElts
             whose span is preserved by all the Hecke operators.
      nn: An integral ideal indexing the Hecke operator
    returns:
      A matrix over corresponding to the action of the Hecke operator on
      this space. 
  }

  assert #LinearDependence(basis) eq 0;
  rows := [];

  for f in basis do
    g := HeckeOperator(f, nn);
    lindep := LinearDependence(basis cat [g]);
    assert #lindep eq 1;
    lindep := lindep[1];
    // We will transpose at the end. 
    // For now, each row stores the
    // coefficients of the linear combination 
    // of basis vectors which give rise to g
    Append(~rows, [-1 * lindep[i] / lindep[#basis + 1] : i in [1 .. #basis]]);
  end for;

  return Transpose(Matrix(rows));
end intrinsic;
