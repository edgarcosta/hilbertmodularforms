//////////////////////////////// Compute quadratic extensions with conductor

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

function QuadraticCharacter(I, K)
  // I::RngOrdIdl - An ideal of a field F
  // K::Fld - A quadratic extension of F
  //
  // Returns the value of the quadratic character evaluated 
  // at I. This is equal to (-1)^(#{inert primes factors of I})
  ZK := Integers(K);
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
  return (-1)^(sum_inert);
end function;

//////////////////////////////// Conjugates of Grossencharacters

intrinsic ConjugateIdeal(K::FldNum, N::RngOrdIdl) -> RngOrdIdl
  {
    inputs:
      K - A relative quadratic extension
      N - An ideal of K
    returns
      The conjugate of N.
  }
  require Degree(K) eq 2 : "K is not a quadratic extension of its base field";
  ZK := Integers(K);

  // the nontrivial automorphism of K
  aut := Automorphisms(K)[2];
  conj_gens := [aut(gen) : gen in Generators(N)];
  return ideal<ZK| conj_gens>;
end intrinsic;

//////////////////////////////// Computing Grossencharacters

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
          if not chi(I) eq psi(Integers(AbsoluteField(K)) !! I) * QuadraticCharacter(I, K) then
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

intrinsic PossibleGrossencharacters(
  F::FldNum, 
  N::RngOrdIdl,
  chi::GrpHeckeElt
  : 
  prune := true
  ) -> SeqEnum[GrpHeckeElt]
  {
    Given a totally real field F, an ideal N of F, and a character chi of modulus N,
    computes all finite order non-Galois-invariant Hecke characters of conductor dividing N
    whose restriction is chi.
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

//////////////////////////////// Computing spaces of dihedral forms

intrinsic ThetaSeries(Mk::ModFrmHilD, K::FldNum, psi::HMFGrossenchar) -> ModFrmHilDElt
  {
    Given a totally real field F, a quadratic extension K of F,
    and a finite order Hecke character of K, compute the associated theta series.
  }
  M := Parent(Mk);
  F := BaseField(M);
  ZF := Integers(F);
  prec := Precision(M);
  K := NumberField(Order(Modulus(psi))); 
  
  // We create an associative array indexed by prime ideals pp up to 
  // Precision(Parent(Mk)) and populate them with traces associated to psi.
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
