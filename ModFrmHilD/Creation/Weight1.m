// Computes a basis of cuspidal weight 1 forms.
intrinsic Weight1CuspBasis(
  Mk::ModFrmHilD
  :
  pp := false
  ) -> SeqEnum[ModFrmHilDElt]
  {Compute the basis of cuspidal parallel weight 1 forms using Hecke operator at pp.
    If pp not specified, choose the smallest pp prime to the level and discriminant.
  }
  M := Parent(Mk);
  k := Weight(Mk);
  assert k[1] eq 1 and k[2] eq 1;
  N := Level(Mk);
  chi := Character(Mk);
  chiinv := chi^(-1);
  ZF := Integers(M);

  assert IsCompatibleWeight(chi, k);

  //Load space of Cusp forms of weight [2,2] and level N.
  vprintf HilbertModularForms: "Computing basis of cusp forms of weight [2,2] and level \n %o\n", N;
  M2 := HMFSpace(M, N, [2,2]);
  B2 := CuspFormBasis(M2);
  printf "Size of basis is %o.\n", #B2;

  //Load an Eisenstein series of weight [1,1], character chi.
  vprintf HilbertModularForms: "Computing an Eisenstein series of weight [1, 1] and character %o\n", chiinv;
  M1 := HMFSpace(M, N, [1,1], chiinv);
  AdmChars := EisensteinAdmissibleCharacterPairs(M1);
  require #AdmChars gt 0: "No Eisenstein series of correct character";
  pair := AdmChars[1];
  E1 := EisensteinSeries(M1, pair[1], pair[2]);

  //Choosing the prime pp.
  if pp cmpeq false then
    for p in PrimesUpTo(100) do
      if 2*Norm(N) mod p eq 0 then
        continue;
      end if;
      if Factorization(p*ZF)[1][2] eq 2 then
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

  return Vnew;
end intrinsic;
