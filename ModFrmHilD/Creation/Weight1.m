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


    ok := false;

    for I in IdealsUpTo(20, F) do
      H := HeckeCharacterGroup(I, [1,2]);

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
                      eis_level := I;
                      break I;
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
                          eis_level := I;
                          break I;
                      end if;
                  end for;
              end if;
          end for;    
      end if;
    end for;
      
    require ok : "There are no appropriate Eisenstein series - I don't think this should ever happen...\n";
    
    vprintf HilbertModularForms: "We will use an Eisenstein series of weight %o, level %o, and character %o\n", l, IdealOneLine(eis_level), psi;

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
        Bmod := Basis(Mksquared);
        Bcusp := CuspFormBasis(Mksquared);
        
        require #Bcusp eq CuspDimension(Mksquared): "Need to increase precision to compute this space";
        
        vprintf HilbertModularForms: "Done?\n";
        done := true;
        for f in V do
            assert Character(Parent(f)) eq chi;
            assert Level(Parent(f)) eq N;
            Bmodandf2 := Append(Bmod, f^2);
            // If f^2 is not in the upstairs (weight 2k character chi^2) space 
            // of modular forms then V must not have been Hecke stable
            if #LinearDependence(Bmodandf2) eq 0 then
                done := false;
                vprintf HilbertModularForms: "No!\n";
//                vprintf HilbertModularForms: "Linear dependence:\n %o \n", LinearDependence(Bandf2);
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
              if #LinearDependence(Append(Bcusp, eig^2)) ne 0 then
                Append(~V, eig);
              end if;
            end for;
            
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
  hecke_matrices := [];

  for pp in PrimesUpTo(P, F) do
    Append(~hecke_matrices, HeckeMatrix(basis, pp));
  end for;

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
