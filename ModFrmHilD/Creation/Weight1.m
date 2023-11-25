intrinsic HeckeStableSubspace(
    V::SeqEnum,
    pp::RngOrdIdl
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
            // TODO abhijitm should do something like this in general too,
            // but clearing denominators seems annoying over number fields.
            if Parent(M[1][1]) eq Rationals() then
              d := Denominator(M);
              M := Matrix(Integers(),d*M);
              gcd_M := GCD(Eltseq(M));
              // If the generalization of Schaeffer's theorem to HMFs is true,
              // then this can never happen
              require gcd_M ne 0 : "We didn't think this could happen -- you may have found\
                      an interesting example! Please email TODO.";
              Append(~Vnew, f/gcd_M);
            else 
              Append(~Vnew, f);
            end if;
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

    par_wt_k := func<k | [k : _ in [1 .. n]]>;
    eis_k := (N ne 1*ZF) select 1 else 3;
    eis_wt := par_wt_k(eis_k);
    MEis := HMFSpace(M, N, eis_wt, chi^-1);

    triv_char := HeckeCharacterGroup(1*ZF, [1 .. n]).0;

    // By Proposition 2.1 in DDP11 (https://annals.math.princeton.edu/wp-content/uploads/annals-v174-n1-p12-s.pdf)
    // this Eisenstein series should be nonzero at the cusp at infinity in
    // every component. Thus, we should be able to divide by it
    // and obtain something with nebentypus character chi. 
    myarray, _ := EisensteinConstantCoefficient(M, eis_wt, chi_prim^-1, triv_char);
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

    //Load space of Cusp forms of weight [k1 + eis_k, ..., kn + eis_k], level N, and trivial character
    vprintf HilbertModularForms: "Computing basis of cusp forms of weight %o, level %o\n", [k[i] + eis_k : i in [1 .. n]], N;
    Mkl := HMFSpace(M, N, [k[i] + eis_k : i in [1 .. n]]);
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
