intrinsic QuadraticExtensionsWithConductor(NN::RngOrdIdl, InfinityModulus::SeqEnum[RngIntElt] : Dividing := true)
  -> SeqEnum[FldAlg]
  {
    Naive!  Returns the set of quadratic field extensions of conductor equal to NN*oo where 
    oo is InfinityModulus, indexing a subset of real places (as Magma numbers them)
    as in their class field theory machinery.  Use Dividing to allow those with 
    conductor dividing NN*oo.
  }

  ZZF := Order(NN);
  F := NumberField(ZZF);
  _<x> := PolynomialRing(F);
  oo := InfinityModulus;

  U, m := SUnitGroup(NN);
  Usq, msq := quo<U | [2*u : u in Generators(U)]>;
  Ks := [];
  for usq in Usq do
  if usq eq Id(Usq) then continue; end if;
  delta := m(usq@@msq);
  K := ext<F | x^2-delta>;
  ff, ooff := Conductor(AbelianExtension(K));
  if ff eq NN or (Dividing and IsIntegral(NN/ff) and &and[c in oo : c in ooff]) then
    Append(~Ks, K);
  end if;
  end for;
  return Ks;
end intrinsic;

// This should be improved to the smarter way of doing it: take generators for the ideal and generate ideal using the Galois conjugates...
intrinsic ConjugateIdeal(K::FldNum, N::RngOrdIdl) -> RngOrdIdl
  {Given a quadratic extension K/F and an ideal N, compute the conjugate of the character N.}
  ZK := Integers(K);
  F := BaseField(K);
  ZF := Integers(F);
  
  if N eq 1*ZK then
    return N;
  end if;

  Fact := Factorization(ZK !! N); 
  Fact_Conj := [];

  for foo in Fact do
    P := foo[1];
    PF := P meet ZF;
    FactPF := Factorization(ZK !! PF);
    if #FactPF eq 2 then // PF is split in PK
      p1 := FactPF[1][1];
      p2 := FactPF[2][1];
      if p1 eq P then
        Append(~Fact_Conj, [* p2, foo[2] *]);
      else 
        Append(~Fact_Conj, [* p1, foo[2] *]);
      end if;
    else // PF is inert or ramified in PK
      Append(~Fact_Conj, [* FactPF[1][1], foo[2] *]);
    end if;
  end for;

  return &*[ Fact_Conj[i][1]^Fact_Conj[i][2] : i in [1 .. #Fact_Conj] ];
end intrinsic;

intrinsic IsSelfConjugate(K::FldNum, chi::GrpHeckeElt) -> BoolElt
  {
    Given a quadratic extension K/F and an ideal chi of a ray class field of K,
    check if chi is equal to its conjugate.
  }
  
  ZK := Integers(K);
  foo, bar := Modulus(chi);
  G, m := RayClassGroup(Conductor(chi), bar);
  
  for g in Generators(G) do
    if not chi( Integers(AbsoluteField(K)) !! ConjugateIdeal(K, m(g))  ) eq chi(m(g)) then
      return false;
    end if;
  end for;
  return true;
end intrinsic;

intrinsic PossibleHeckeCharactersOfK(
  F::FldNum, 
  N::RngOrdIdl, 
  K::FldNum, 
  chi::GrpHeckeElt : 
  prune := true
  ) -> SeqEnum[GrpHeckeElt]
  {
    Given a totally real field F, an ideal N of F, a character chi of modulus N,
    and a quadratic extension K of discriminant dividing N, computes all finite 
    order non-Galois-invariant Hecke characters of conductor dividing N/disc(K) 
    whose restriction is chi.

    If the optional parameter prune is true, we only keep on copy of chi and  
    the conjugate of chi, since both of these lift to the same Hilbert modular form.
  }
  ZK := Integers(K);
  Disc := Discriminant(ZK);

  M := N/Disc;
  assert IsIntegral(M);
  M := Integers(AbsoluteField(K)) !! M;
  H := HeckeCharacterGroup(M); // Is this correct or do I allow ramification at infinite places? I think I should allow ramification and and check some compatibility of the character with the weight [1,1]... 
  G, m := RayClassGroup(M);

  GF, mF := RayClassGroup(N, [1,2]);

  ans := [];

  for psi in Elements(H) do
    if Norm(ZK !! Conductor(psi))*Disc eq N then
      ok := false;
      for g in Generators(G) do
        if not psi( Integers(AbsoluteField(K)) !! ConjugateIdeal(K, m(g))  ) eq psi(m(g)) then
          ok := true;
          break g;
        end if;
      end for;
      
      okk := true;
      if ok then
        for g in Generators(GF) do
          I := mF(g);
          // A short interlude to evaluate the character associated with K/F at I. This will be (-1) to the number of inert primes in the factorization.
          Fact := Factorization(I); 
          sum_inert := 0;
          for foo in Fact do
            P := foo[1];
            PK := ZK !! P;
            FactPK := Factorization(PK);
            if #FactPK eq 1 and FactPK[1][2] eq 1 then // P is inert in K
              sum_inert := sum_inert + foo[2];
            end if;
          end for;
          if not chi(I) eq psi(Integers(AbsoluteField(K)) !! I)*(-1)^(sum_inert) then
            okk := false;
          end if;
        end for;
        if okk then
          Append(~ans, psi); 
        end if;
      end if;
    end if;
  end for;
  
  if prune then
    newlist := []; // New list of characters
    pairlist := []; // List of paired characters, to be thrown away
    
    for i in [1 .. #ans] do // Loop over possible characters
      psi := ans[i];
      if i in pairlist then // This character was already paired
        continue;
      else 
        Append(~newlist, i); // It wasn't in the list of paired characters, so add it to the new lsit of characters.
      end if;
      
      for j in [1 .. #ans] do // Find the pair of psi
        if j eq i then
          continue; // Skip i
        end if;
        
        psiconj := true; 
        for g in Generators(G) do
          if psi( Integers(AbsoluteField(K)) !! ConjugateIdeal(K, m(g)) ) eq ans[j](m(g)) then
            continue;
          else 
            psiconj := false;
          end if;
        end for;
        if psiconj then
          Append(~pairlist, j);
          break j;
        end if;
      end for;
    end for;
    assert #newlist eq #pairlist; // The characters should pair up since we removed conjugation-invariant ones.
    ans := [ans[i] : i in newlist];
  end if;
  
  return ans;
  
end intrinsic;

intrinsic PossibleHeckeCharacters(
  F::FldNum, 
  N::RngOrdIdl,
  chi::GrpHeckeElt
  : 
  prune := true
  ) -> SeqEnum[GrpHeckeElt]
  {
    Given a totally real field F, an ideal N of F, and a character chi of modulus N,
    computes all finite order non-Galois-invariant Hecke characters of 
    conductor dividing N whose restriction is chi.
  }
  ans := [];
  fields := QuadraticExtensionsWithConductor(N, [1,2]);
  for K in fields do
    ans := ans cat PossibleHeckeCharactersOfK(F, N, K, chi);
  end for;

  return ans;
end intrinsic;

intrinsic PossibleHeckeCharacters(
    Mk::ModFrmHilD
    ) -> SeqEnum[GrpHeckeElt]
{
Given a totally real field F, an ideal N of F, and a character chi of modulus N, computes all finite order non-Galois-invariant Hecke characters of conductor dividing N whose restriction is chi.
}
    return PossibleHeckeCharacters(BaseField(Parent(Mk)), Level(Mk), Character(Mk));
end intrinsic;


intrinsic ThetaSeries(
  Mk::ModFrmHilD,
  psi::GrpHeckeElt
  ) -> ModFrmHilDElt
  {
    Given a totally real field F, a quadratic extension K of F,
    and a finite order Hecke character of K,
    compute the associated theta series of weight (1,1).
  }
  M := Parent(Mk);
  F := BaseField(M);
  ZF := Integers(F);
  prec := Precision(M);
  K := NumberField(Order(Modulus(psi))); 
  
  // We create an associative array indexed by prime ideals pp up to Precision(Parent(Mk)) and populate them with traces associated to psi.
  

  a_pps := AssociativeArray();
  for pp in PrimeIdeals(M) do
  fact := Factorization(Integers(K) !! pp);
  g := #fact;
  d := InertiaDegree(pp);
  a_pps[pp] := (g eq 2) // pp is split in K 
    select psi(fact[1][1]) + psi(fact[2][1]) 
    else // pp is inert or ramified in K
    (
    (fact[1][2] eq 1) select 0 else psi(fact[1][1])
    );
  end for;

  return CuspFormFromEigenvalues(Mk, a_pps);
end intrinsic;

intrinsic DihedralForms(Mk::ModFrmHilD) -> SeqEnum[ModFrmHilDElt]
  {
    Given a space of weight one forms, compute the subspace of dihedral forms.
  } 
  require IsParallel(Weight(Mk)) and Weight(Mk)[1] eq 1 : "Dihedral forms are only defined for spaces of weight one forms.";
  
  ans := [];
  
  for psi in PossibleHeckeCharacters(Mk) do
    Append(~ans, ThetaSeries(Mk, psi));
  end for;
  
  return ans;
end intrinsic;
