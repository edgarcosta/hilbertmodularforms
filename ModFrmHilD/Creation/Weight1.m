// Computes a basis of cuspidal weight 1 forms.
intrinsic Weight1CuspBasis(
  Mk::ModFrmHilD
  :
  pp := false,
  prove := true
  ) -> SeqEnum[ModFrmHilDElt]
  {Compute the basis of cuspidal parallel weight 1 forms using the Hecke stability method.
    The optional parameter pp specifies which Hecke operator T_pp to use;
    otherwise use smallest pp coprime to the level.
    The optional paramter prove should be true or false. If true, we verify that the candidates
    for the weight one forms obtained from the Hecke stability method are indeed holomorphic.
  }
  M := Parent(Mk);
  k := Weight(Mk);
  assert k[1] eq 1 and k[2] eq 1;
  N := Level(Mk);
  chi := Character(Mk);
  chiinv := chi^(-1);
  ZF := Integers(M);

  assert IsGamma1EisensteinWeight(chi, k);

  //Load space of Cusp forms of weight [2,2] and level N.
  vprintf HilbertModularForms: "Computing basis of cusp forms of weight [2,2] and level \n %o\n", N;
  M2 := HMFSpace(M, N, [2,2]);
  B2 := CuspFormBasis(M2);
  vprintf HilbertModularForms: "Size of basis is %o.\n", #B2;

  //Load an Eisenstein series of weight [1,1], character chi.
  vprintf HilbertModularForms: "Computing an Eisenstein series of weight [1, 1] and character %o\n", chiinv;
  M1 := HMFSpace(M, N, [1,1], chiinv);
  AdmChars := EisensteinAdmissibleCharacterPairs(M1);
  require #AdmChars gt 0: "No Eisenstein series of correct character";
  pair := AdmChars[1];
  E1 := EisensteinSeries(M1, pair[1], pair[2]);

  //Choosing the prime pp, skipping primes dividing level just to be safe. Probably not needed?
  if pp cmpeq false then
    for p in PrimesUpTo(100) do
      if Norm(N) mod p eq 0 then
        continue;
      end if;
    pp := Factorization(p*ZF)[1][1];
    break;
    end for;
  end if;
  vprintf HilbertModularForms: "Using Hecke operator at prime \n %o \n of norm %o.\n", pp, Norm(pp);

  //Now we start the big computation.
  vprintf HilbertModularForms: "Starting the big computation...\n";
  cont := true;

  V := [];
  for f in B2 do
    Append(~V, f/E1);
  end for;

  Vprev := V;
  dimprev := #V;

  while cont do
    vprintf HilbertModularForms:  "Current dim = %o\n", dimprev;
    TpVprev := [];
    for g in Vprev do
      Append(~TpVprev, HeckeOperator(g, pp));
    end for;

    lindep := LinearDependence(Vprev cat TpVprev);
    dimnew := #lindep;
    vprintf HilbertModularForms: "New dim = %o\n", dimnew;

    if dimprev eq dimnew then
      cont := false;
    end if;

    Vnew := [];
    for vec in lindep do
      f := &+[vec[i]*Vprev[i] : i in [1 .. #Vprev]];
      Append(~Vnew, f);
    end for;

    assert #Vnew eq dimnew;

    Vprev := Vnew;
    dimprev := #Vprev;
  end while;

  if prove then
    vprintf HilbertModularForms: "Checking that forms are holomorphic by squaring\n";

    M2chi2 := HMFSpace(M, N, [2,2], chi^2);
    B2chi2 := CuspFormBasis(M2);

    for f in Vnew do
      V2 := Append(B2chi2, f^2);
      assert #LinearDependence(V2) gt 0;
    end for;


  vprintf HilbertModularForms: "Need to verify that the precision is large enough to compute the space larger space\n";

  B4 := Basis(HMFSpace(M, N, [4,4]));
  assert #LinearDependence(B4) eq 0;
  end if;

  return Vnew;
end intrinsic;

// Computes a basis of cuspidal weight 1 forms.
intrinsic Weight1CuspBasisNew(
  Mk::ModFrmHilD
  :
  pp := false,
  prove := true
  ) -> SeqEnum[ModFrmHilDElt]
  {Compute the basis of cuspidal parallel weight 1 forms using the Hecke stability method.
    The optional parameter pp specifies which Hecke operator T_pp to use;
    otherwise use smallest pp coprime to the level.
    The optional paramter prove should be true or false. If true, we verify that the candidates
    for the weight one forms obtained from the Hecke stability method are indeed holomorphic.
  }
  M := Parent(Mk);
  k := Weight(Mk);
  assert k[1] eq 1 and k[2] eq 1;
  N := Level(Mk);
  chi := Character(Mk);
  chiinv := chi^(-1);
  ZF := Integers(M);

  assert IsGamma1EisensteinWeight(chi, k);

  //Load an Eisenstein series of weight [1,1], character chi.
  vprintf HilbertModularForms: "Computing an Eisenstein series of weight [1, 1] and character %o\n", chiinv;
  M1 := HMFSpace(M, N, [1,1], chiinv);
  AdmChars := EisensteinAdmissibleCharacterPairs(M1);
  require #AdmChars gt 0: "No Eisenstein series of correct character";
    
    ok := false;

    for pair in AdmChars do
        myarray := EisensteinConstantCoefficient(M, [1,1], pair[1], pair[2]); 
        if not (&*[myarray[key] : key in Keys(myarray)] eq 0) then
            ok := true;
            mypair := pair;
            break;
        end if;
    end for;
    
    if ok then
        vprint HilbertModularForms: "There is a non-vanishing Eisenstein series of weight 1.";
      pair := mypair;
      E1 := EisensteinSeries(M1, pair[1], pair[2]);
    
        
      //Load space of Cusp forms of weight [2,2] and level N.
      vprintf HilbertModularForms: "Computing basis of cusp forms of weight [2,2] and level \n %o\n", N;
      M2 := HMFSpace(M, N, [2,2]);
      B2 := CuspFormBasis(M2);
      vprintf HilbertModularForms: "Size of basis is %o.\n", #B2;

      //Choosing the prime pp, skipping primes dividing level just to be safe. Probably not needed?
      if pp cmpeq false then
        for p in PrimesUpTo(100) do
          if Norm(N) mod p eq 0 then
            continue;
          end if;
        pp := Factorization(p*ZF)[1][1];
        break;
        end for;
      end if;
      vprintf HilbertModularForms: "Using Hecke operator at prime \n %o \n of norm %o.\n", pp, Norm(pp);

      //Now we start the big computation.
      vprintf HilbertModularForms: "Starting the big computation...\n";
      cont := true;

      V := [];
      for f in B2 do
        Append(~V, f/E1);
      end for;

      Vprev := V;
      dimprev := #V;

      while cont do
        vprintf HilbertModularForms:  "Current dim = %o\n", dimprev;
        TpVprev := [];
        for g in Vprev do
          Append(~TpVprev, HeckeOperator(g, pp));
        end for;

        lindep := LinearDependence(Vprev cat TpVprev);
        dimnew := #lindep;
        vprintf HilbertModularForms: "New dim = %o\n", dimnew;

        if dimprev eq dimnew then
          cont := false;
        end if;

        Vnew := [];
        for vec in lindep do
          f := &+[vec[i]*Vprev[i] : i in [1 .. #Vprev]];
          Append(~Vnew, f);
        end for;

        assert #Vnew eq dimnew;

        Vprev := Vnew;
        dimprev := #Vprev;
      end while;

      if prove then
        vprintf HilbertModularForms: "Checking that forms are holomorphic by squaring\n";
        
        if Order(chi) eq 1 then
            B2chi2 := B2;
        else
            M2chi2 := HMFSpace(M, N, [2,2], chi^2);
            B2chi2 := CuspFormBasis(M2chi2);
        end if;

        for f in Vnew do
          V2 := Append(B2chi2, f^2);
          assert #LinearDependence(V2) gt 0;
        end for;


      print "Need to verify that the precision is large enough to compute the space larger space\n";

      B4 := Basis(HMFSpace(M, N, [4,4]));
      assert #LinearDependence(B4) eq 0;
      end if;

      return Vnew;
    else
        vprint HilbertModularForms: "There is no non-vanishing Eisenstein series of weight 1, we go to weight 3.";
        
        vprintf HilbertModularForms: "Computing an Eisenstein series of weight [3, 3] and character %o\n", chiinv;
        M3 := HMFSpace(M, N, [3,3], chiinv);
        AdmChars := EisensteinAdmissibleCharacterPairs(M3);
        require #AdmChars gt 0: "No Eisenstein series of correct character";
    
        ok := false;

        for pair in AdmChars do
            myarray := EisensteinConstantCoefficient(M, [3,3], pair[1], pair[2]); 
            if not (&*[myarray[key] : key in Keys(myarray)] eq 0) then
                ok := true;
                mypair := pair;
                break;
            end if;
        end for;
        
        require ok: "We would need to go to weight 5... Not implemented yet.";

        pair := mypair;
        E3 := EisensteinSeries(M3, pair[1], pair[2]);
        
        //Load space of Cusp forms of weight [4, 4] and level N.
        vprintf HilbertModularForms: "Computing basis of cusp forms of weight [4,4] and level \n %o\n", N;
        M4 := HMFSpace(M, N, [4,4]);
        B4 := CuspFormBasis(M4);
        vprintf HilbertModularForms: "Size of basis is %o.\n", #B4;

        //Choosing the prime pp, skipping primes dividing level just to be safe. Probably not needed?
        if pp cmpeq false then
        for p in PrimesUpTo(100) do
          if Norm(N) mod p eq 0 then
            continue;
          end if;
        pp := Factorization(p*ZF)[1][1];
        break;
        end for;
        end if;
        vprintf HilbertModularForms: "Using Hecke operator at prime \n %o \n of norm %o.\n", pp, Norm(pp);

          //Now we start the big computation.
          vprintf HilbertModularForms: "Starting the big computation...\n";
          cont := true;

          V := [];
          for f in B4 do
            Append(~V, f/E3);
          end for;

          Vprev := V;
          dimprev := #V;

          while cont do
            vprintf HilbertModularForms:  "Current dim = %o\n", dimprev;
            TpVprev := [];
            for g in Vprev do
              Append(~TpVprev, HeckeOperator(g, pp));
            end for;

            lindep := LinearDependence(Vprev cat TpVprev);
            dimnew := #lindep;
            vprintf HilbertModularForms: "New dim = %o\n", dimnew;

            if dimprev eq dimnew then
              cont := false;
            end if;

            Vnew := [];
            for vec in lindep do
              f := &+[vec[i]*Vprev[i] : i in [1 .. #Vprev]];
              Append(~Vnew, f);
            end for;

            assert #Vnew eq dimnew;

            Vprev := Vnew;
            dimprev := #Vprev;
          end while;

          if prove then
            vprintf HilbertModularForms: "Checking that forms are holomorphic by squaring\n";

            M2chi2 := HMFSpace(M, N, [2,2], chi^2);
            B2chi2 := CuspFormBasis(M2chi2);

            for f in Vnew do
              V2 := Append(B2chi2, f^2);
              assert #LinearDependence(V2) gt 0;
            end for;


          print "Need to verify that the precision is large enough to compute the space larger space\n";

          B4 := Basis(HMFSpace(M, N, [8,8]));
          assert #LinearDependence(B4) eq 0;
          end if;

          return Vnew;
    end if;
end intrinsic;
