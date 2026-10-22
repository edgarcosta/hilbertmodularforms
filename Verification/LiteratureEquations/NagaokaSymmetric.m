// Nagaoka, "On the ring of Hilbert modular forms over Z", J. Math. Soc. Japan
// 35 (1983), 589-608: Theorems 1-2, equations (5.2), (5.6), and Lemma 5.2.
// G_k has constant coefficient 1. The printed J6 coefficient is 2^-5;
// the PDF's hidden text layer incorrectly reads 2^-6 on p.589.
SymmetricLitData := function(D)
    assert D in [5,8];
    if D eq 5 then
        P<G2,J6,J10,J12> := PolynomialRing(Rationals(),[2,6,10,12]);
        I := ideal<P | 4*J12-J6^2+G2*J10>;
    else
        P<G2,H4,H6> := PolynomialRing(Rationals(),[2,4,6]);
        I := ideal<P | >;
    end if;
    citation := "Nagaoka, J. Math. Soc. Japan 35 (1983), 589-608, Theorems 1-2 and 5.1-5.2";
    return I,citation;
end function;

PublishedForms := function(M)
    F := BaseField(M); N := 1*Integers(F); D := Discriminant(Integers(F));
    assert D in [5,8];
    weights := D eq 5 select [2,6,10] else [2,4,6];
    triv := HeckeCharacterGroup(N)!1;
    G := AssociativeArray();
    for w in weights do
        E := EisensteinSeries(HMFSpace(M,N,[w,w]),triv,triv);
        c := Coefficient(E,N,F!0);
        assert c ne 0;
        G[w] := E/c;
        assert Coefficient(G[w],N,F!0) eq 1;
    end for;
    if D eq 5 then
        J6 := 67/(2^5*3^3*5^2)*(G[2]^3-G[6]);
        J10 := (412751*G[10]-5*67*2293*G[2]^2*G[6]+2^2*3*7*4231*G[2]^5)/(2^10*3^5*5^5*7);
        J12 := (J6^2-G[2]*J10)/4;
        return [* G[2],J6,J10,J12 *];
    end if;
    H4 := 11/(2^6*3^2)*(G[2]^2-G[4]);
    H6 := -5*7^2/(2^8*3^3*13)*G[2]^3
        +11*59/(2^8*3^2*5*13)*G[2]*G[4]-19^2/(2^7*3^3*5*13)*G[6];
    return [* G[2],H4,H6 *];
end function;

// R is the stored full ring, or its fixed polynomial ring with the first three
// coordinates in weights [2,6,10] for D=5 and [2,4,6] for D=8.
PublishedImages := function(D,R)
    assert D in [5,8] and Rank(R) ge 3;
    assert VariableWeights(R)[1..3] eq (D eq 5 select [2,6,10] else [2,4,6]);
    if D eq 5 then
        return [R.1,R.2,R.3,(R.2^2-R.1*R.3)/4];
    end if;
    return [R.1,R.2,R.3];
end function;
return [* SymmetricLitData,PublishedForms,PublishedImages *];
