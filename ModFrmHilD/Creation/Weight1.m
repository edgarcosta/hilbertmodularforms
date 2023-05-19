intrinsic HeckeStableSubspace(
    V::SeqEnum,
    pp::RngQuadIdl
    ) -> SeqEnum
    {
    Given a sequence of forms V and an ideal pp, compute a basis of the subspace of span(V) that is stable under the Hecke operator T_pp. 
    }
    
    Vprev := V;
    dimprev := #V;
    
    for _ in [1 .. #V] do
        vprintf HilbertModularForms:  "Current dim = %o\n", dimprev;
        TpVprev := [];
        for g in Vprev do
            Append(~TpVprev, HeckeOperator(g, pp));
        end for;
        
        if IsZero(CoefficientsMatrix(TpVprev)) then
            vprintf HilbertModularForms: "Tpp acts as 0 on V, so V is stable\n";
            return Vprev;
        end if;

        lindep := LinearDependence(Vprev cat TpVprev);
        dimnew := #lindep;
        
        vprintf HilbertModularForms: "New dim = %o\n", dimnew;
        
        if dimnew eq 0 then
            return [];
        end if;
        
        require dimnew le dimprev: "Something went wrong, probably need to increase precision.";

        Vnew := [];
        for vec in lindep do
            f := &+[vec[i]*Vprev[i] : i in [1 .. #Vprev]];
            M := CoefficientsMatrix([f]); 
            d := Denominator(M); M := Matrix(Integers(),d*M);
            Append(~Vnew, f/GCD(Eltseq(M)));
        end for;

        if dimprev eq dimnew then
            return Vnew;
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
    bound := 100,
    prove := true
    ) -> SeqEnum[ModFrmHilDElt]
    {Compute the space Mk using the Hecke stability method. 
        - The optional parameter bound is the maximum norm of primes pp we will check T_pp-stability for before we declare defeat,
        - The optional parameter prove is true or false. If true, we verify that we had enough precision to check the equality of the potentially meromorphic form with a holomorphic one.
    }
    
    M := Parent(Mk);
    k := Weight(Mk);
    N := Level(Mk);
    chi := Character(Mk);
    chiinv := chi^(-1);
    F := BaseField(M);
    ZF := Integers(M);

    //Try to find appropriate Eisenstein series to use. Currently, we only support level one characters, so we look for Eisenstein series that put us in such spaces.
    H := HeckeCharacterGroup(1*ZF, [1,2]);

    ok := false;

    for psi0 in Elements(H) do
        psi := psi0*chiinv;
        if IsGamma1EisensteinWeight(psi, 1) then
            MEis := HMFSpace(M, N, [1,1], psi);
            AdmChars := EisensteinAdmissibleCharacterPairs(MEis);

            for pair in AdmChars do
                myarray := EisensteinConstantCoefficient(M, [1,1], pair[1], pair[2]); 
                if not (&*[myarray[key] : key in Keys(myarray)] eq 0) then
                    ok := true;
                    mypair := pair;
                    l := 1;
                    break psi0;
                end if;
            end for;
        end if;
    end for;
    
    if not ok then
        vprintf HilbertModularForms: "No appropriate weight 1 Eisenstein series, need to go to weight 3\n";

        for psi0 in Elements(H) do
            psi := psi0*chiinv;
            if IsGamma1EisensteinWeight(psi, 3) then
                MEis := HMFSpace(M, N, [3,3], psi);
                AdmChars := EisensteinAdmissibleCharacterPairs(MEis);

                for pair in AdmChars do
                    myarray := EisensteinConstantCoefficient(M, [3,3], pair[1], pair[2]); 
                    if not (&*[myarray[key] : key in Keys(myarray)] eq 0) then
                        ok := true;
                        mypair := pair;
                        l := 3;
                        break psi0;
                    end if;
                end for;
            end if;
        end for;    
    end if;
    
    require ok : "There are no appropriate Eisenstein series - I don't think this should ever happen...\n";
    
    
    vprintf HilbertModularForms: "We will use an Eisenstein series of weight %o and character %o\n", l, psi;

    Eis := EisensteinSeries(MEis, mypair[1], mypair[2]);
    
        
    //Load space of Cusp forms of weight [k1 + l,k2 + l] and level N.
    vprintf HilbertModularForms: "Computing basis of cusp forms of weight [%o,%o] and level %o\n", k[1] + l, k[2] + l, N;
    Mkl := HMFSpace(M, N, [k[1] + l, k[2] + l], chi*Character(MEis));
    Bkl := CuspFormBasis(Mkl);
    vprintf HilbertModularForms: "Size of basis is %o.\n", #Bkl;
    
    require #Bkl eq CuspDimension(Mkl) : "Need to increase precision to compute this space"; 

    vprintf HilbertModularForms: "Dividing by the  Eisenstein series\n";
    
    //Our initial candidate for our desired space.
    V := [];
    for f in Bkl do
        Append(~V, f/Eis);
    end for;

    //We will next loop over primes pp and compute the stable subspaces under T_pp.
    //We skip over primes dividing level just to be safe. We try primes up to 100, but we usually just need 1 or 2.
    primes := PrimesUpTo(bound, F:coprime_to := N);

    for pp in primes do
        vprintf HilbertModularForms: "Computing Hecke stable subspace for prime %o\n of norm %o.\n", pp, Norm(pp);
        
        V := HeckeStableSubspace(V, ZF!!pp);

        if #V eq 0 then
            return V;
        end if;
        
        //Now V is our updated candidate for the space of weight 1 forms. We need to check if the forms are holomorphic by squaring.
        vprintf HilbertModularForms: "Checking that forms are holomorphic by squaring\n";

        Mksquared := HMFSpace(M, N, [2*k[1], 2*k[2]], chi^2);
        B := CuspFormBasis(Mksquared);
        
        require #B eq CuspDimension(Mksquared): "Need to increase precision to compute this space";
        
        vprintf HilbertModularForms: "Done?\n";
        done := true;
        for f in V do
            assert Character(Parent(f)) eq chi;
            assert Level(Parent(f)) eq N;
            Bandf2 := Append(B, f^2);
            if #LinearDependence(Bandf2) eq 0 then
                done := false;
                vprintf HilbertModularForms: "No!\n";
//                vprintf HilbertModularForms: "Linear dependence:\n %o \n", LinearDependence(Bandf2);
                break f;
            end if;
        end for;
        if done then
             vprintf HilbertModularForms: "Yes!\n";
            if prove then
                vprintf HilbertModularForms: "Need to verify that the precision is large enough to compute the space larger space\n";

                Vcheck := Basis(HMFSpace(M, N, [2*k[1] + 2*l,2*k[2] + 2*l]));
                assert #LinearDependence(Vcheck) eq 0;
            end if;

            return V;
        end if;
    end for;
    
    require false : "Not enough primes to ensure our forms are holomorphic.";

    return [];
end intrinsic;

// Computes a basis of cuspidal weight 1 forms.
intrinsic Weight1CuspBasis(
  Mk::ModFrmHilD
  :
  bound := 100,
  prove := true
  ) -> SeqEnum[ModFrmHilDElt]
  {Compute the basis of cuspidal parallel weight 1 forms using the Hecke stability method.
   - The optional parameter bound is the maximum norm of primes pp we will check T_pp-stability for before we declare defeat,
   - The optional parameter prove is true or false. If true, we verify that we had enough precision to check the equality of the potentially meromorphic form with a holomorphic one.
  }
  return HeckeStabilityCuspBasis(Mk : bound := bound, prove := prove);
end intrinsic;