intrinsic QuadraticExtensionsWithConductor(NN::RngOrdIdl, InfinityModulus::SeqEnum[RngIntElt] : Dividing := true)
    -> SeqEnum[FldAlg]
  {Naive!  Returns the set of quadratic field extensions of conductor equal to NN*oo where 
   oo is InfinityModulus, indexing a subset of real places (as Magma numbers them)
   as in their class field theory machinery.  Use Dividing to allow those with 
   conductor dividing NN*oo.}

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

intrinsic ConjugateIdeal(K::FldNum, N::RngOrdIdl) -> RngOrdIdl
    {Given a quadratic extension K/F and an ideal N, compute the conjugate of the character N.}
    ZK := Integers(K);
    F := BaseField(K);
    ZF := Integers(F);
    
    if N eq 1*ZK then
        return N;
    end if;

    Fact := Factorization(ZK !! N); 
//    print Fact;
    Fact_Conj := [];

    for foo in Fact do
        P := foo[1];
        PF := P meet ZF;
//        print PF;
        FactPF := Factorization(ZK !! PF);
//        print FactPF;
        if #FactPF eq 2 then //PF is split in PK
            p1 := FactPF[1][1];
            p2 := FactPF[2][1];
            if p1 eq P then
                Append(~Fact_Conj, [* p2, foo[2] *]);
            else 
                Append(~Fact_Conj, [* p1, foo[2] *]);
            end if;
        else //PF is inert or ramified in PK
            Append(~Fact_Conj, [* FactPF[1][1], foo[2] *]);
        end if;
    end for;

    return &*[ Fact_Conj[i][1]^Fact_Conj[i][2] : i in [1 .. #Fact_Conj] ];
end intrinsic;

//intrinsic ConjugateIdealNew(K::FldNum, N::RngOrdIdl) -> RngOrdIdl
//    {Given a quadratic extension K/F and an ideal N, compute the conjugate of the character N.}
//    ZK := Integers(K);
//    F := BaseField(K);
//    ZF := Integers(F);
//    
//    if N eq 1*ZK then
//        return N;
//    end if;
//
//    Fact := Factorization(ZK !! N); 
////    print Fact;
//    Fact_Conj := [];
//
//    for foo in Fact do
//        P := foo[1];
//        PF := P meet ZF;
////        print PF;
//        FactPF := Factorization(ZK !! PF);
////        print FactPF;
//        if #FactPF eq 2 then //PF is split in PK
//            p1 := FactPF[1][1];
//            p2 := FactPF[2][1];
//            if p1 eq P then
//                Append(~Fact_Conj, [* p2, foo[2] *]);
//            else 
//                Append(~Fact_Conj, [* p1, foo[2] *]);
//            end if;
//        else //PF is inert or ramified in PK
//            Append(~Fact_Conj, [* FactPF[1][1], foo[2] *]);
//        end if;
//    end for;
//
//    return &*[ Fact_Conj[i][1]^Fact_Conj[i][2] : i in [1 .. #Fact_Conj] ];
//end intrinsic;

intrinsic IsSelfConjugate(K::FldNum, chi::GrpHeckeElt) -> BoolElt
    {Given a quadratic extension K/F and an ideal chi of a ray class field of K, check if chi is equal to its conjugate.}
    
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

intrinsic PossibleHeckeCharacters(F::FldNum, N::RngOrdIdl, K::FldNum) -> SeqEnum[GrpHeckeElt]
{
Given a totally real field F, an ideal N of F, and a quadratic extension K of discriminant dividing N, computes all finite order non-Galois-invariant Hecke characters of conductor dividing N/disc(K).
}

    ZK := Integers(K);
    Disc := Discriminant(ZK);

    M := N/Disc;
    M := Integers(AbsoluteField(K)) !! M;
    H := HeckeCharacterGroup(M); //Is this correct or do I allow ramification at infinite places?
    

    ans := [];

    for chi in Elements(H) do
        if Norm(ZK !! Conductor(chi))*Disc eq N and not IsSelfConjugate(K, chi) then
            Append(~ans, chi);
        end if;
    end for;

    return ans;
    
end intrinsic;


intrinsic PossibleHeckeCharactersNew(F::FldNum, N::RngOrdIdl, K::FldNum) -> SeqEnum[GrpHeckeElt]
{
Given a totally real field F, an ideal N of F, and a quadratic extension K of discriminant dividing N, computes all finite order non-Galois-invariant Hecke characters of conductor dividing N/disc(K).
}

    ZK := Integers(K);
    Disc := Discriminant(ZK);

    M := N/Disc;
    assert IsIntegral(M);
    M := Integers(AbsoluteField(K)) !! M;
    H := HeckeCharacterGroup(M); //Is this correct or do I allow ramification at infinite places?
    G, m := RayClassGroup(M);

    ans := [];

    for chi in Elements(H) do
        if Norm(ZK !! Conductor(chi))*Disc eq N then
            for g in Generators(G) do
                if not chi( Integers(AbsoluteField(K)) !! ConjugateIdeal(K, m(g))  ) eq chi(m(g)) then
                    Append(~ans, chi);
                    break g;
                end if;
            end for;
        end if;
    end for;

    return ans;
    
end intrinsic;