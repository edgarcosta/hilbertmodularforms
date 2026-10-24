// van der Geer and Zagier, Invent. Math. 42 (1977), Theorems 6 and 9, pp.117-120.
// Theorem 9 is extended by eta0 = sigma2/xi0, justified by Theorem 6.
// The witness targets the freshly generated presentation used by the example.
// Equation (12), p.103: sigma1 = 0 and 2*sigma5 = sigma2*sigma3.

LitData := function(R,S)
    SourceData := function()
        Q := Rationals();
        P := PolynomialRing(Q, [2,4,6,8]);
        t:=P.1; b:=P.2; c:=P.3; d:=P.4;
        F := t^5+b*t^3-c*t^2+d*t-b*c/2;
        L := FieldOfFractions(P);
        images := [L | d/c,b,c,b^3/c,t,t^2*b^2/c,t^4*b/c,t^6/c,b/t];
        weights := [2,4,6,6,2,6,6,6,2];
        return P,F,images,weights;
    end function;

    PublishedPresentation := function()
        T := PolynomialRing(Rationals(),14,"lex");
        s:=T.1; t:=T.2; b:=T.3; c:=T.4; d:=T.5;
        a:=T.6; bb:=T.7; cc:=T.8; dd:=T.9;
        u:=T.10; v:=T.11; w:=T.12; z:=T.13; e:=T.14;
        graph := ideal<T | s*t*c-1, t^5+b*t^3-c*t^2+d*t-b*c/2,
            a*c-d,bb-b,cc-c,dd*c-b^3,u-t,
            v*c-t^2*b^2,w*c-t^4*b,z*c-t^6,e*t-b>;
        E := EliminationIdeal(graph,5);
        R := PolynomialRing(Rationals(),[2,4,6,6,2,6,6,6,2]);
        project := hom<T->R | [R|0,0,0,0,0] cat [R.i:i in [1..9]]>;
        I := ideal<R | [project(g):g in Basis(E)]>;
        P,F,images,weights := SourceData();
        for g in Basis(I) do
            value := Evaluate(g,images);
            assert Numerator(value) in ideal<P|F>;
        end for;
        return I;
    end function;

    MissingFormCertificate := function()
        // Theorem 6 gives eta0 = N/sigma3 for this quartic N with double zeros
        // at the ten P_ij. The two permutations generate its S4 stabilizer.
        P := PolynomialRing(Rationals(),4);
        xs := [P.i:i in [1..4]] cat [-&+[P.i:i in [1..4]]];
        sigma := [&+[&*[xs[i]:i in S] : S in Subsets({1..5},j)] : j in [1..5]];
        assert sigma[1] eq 0;
        t:=xs[1]; b:=sigma[2]; c:=sigma[3]; d:=sigma[4];
        surface := 2*sigma[5]-b*c;
        numerator := 2*(t^4+b*t^2-c*t+d);
        assert numerator*t-b*c eq surface;
        assert TotalDegree(numerator) eq 4;
        for pair in Subsets({1..5},2) do
            ij := Sort(Setseq(pair));
            point := [Rationals() | (i eq ij[1]) select 1 else
                ((i eq ij[2]) select -1 else 0) : i in [1..5]];
            assert Evaluate(surface,point[1..4]) eq 0;
            assert Evaluate(numerator,point[1..4]) eq 0;
            assert &and[Evaluate(Derivative(numerator,j),point[1..4]) eq 0
                : j in [1..4]];
        end for;
        for perm in [[1,3,2,4,5],[1,3,4,5,2]] do
            substitution := [xs[perm[i]]:i in [1..4]];
            assert Evaluate(numerator,substitution) eq numerator;
            assert Evaluate(c,substitution) eq c;
        end for;
        polys := [t*c,d,numerator];
        mons := Setseq(&join[Seqset(Monomials(g)):g in polys]);
        assert Rank(Matrix(Rationals(),
            [[MonomialCoefficient(g,m):m in mons]:g in polys])) eq 3;
        return true;
    end function;

    MinimalPresentation := function(I)
        R := Generic(I);
        S := PolynomialRing(Rationals(),[2,2,2,6,6]);
        a:=S.1; u:=S.2; e:=S.3; c:=S.4; z:=S.5;
        w := -z-a*u^2+u^3+u^2*e/2;
        v := -w-a*u*e+u^2*e+u*e^2/2;
        d := -v-a*e^2+u*e^2+e^3/2;
        images := [a,u*e,c,d,u,v,w,z,e];
        inverse := [R.1,R.5,R.9,R.3,R.8];
        K := ideal<S|[Evaluate(g,images):g in Basis(I)]>;
        assert &and[Evaluate(images[i],inverse)-R.i in I:i in [1..9]];
        assert &and[Evaluate(inverse[i],images) eq S.i:i in [1..5]];
        assert HilbertSeries(K) eq HilbertSeries(I);
        return K,images,inverse;
    end function;
    r1,r2,r3,r4,r5,r6,r7 := Explode([R.i : i in [1..7]]);
    s1,s2,s3,s4,s5 := Explode([S.i : i in [1..5]]);
    tau := [
    r1,
    r2,
    r3,
    -77/432000*r1^3 + 37/144000*r1^2*r2 + 401/48000*r1*r2^2 - 3643/432000*r2^3 + 217/36000*r1^2*r3 - 727/18000*r1*r2*r3 - 5963/36000*r2^2*r3 - 97/1500*r1*r3^2 - 143/1500*r2*r3^2 + 68/125*r3^3 - r4 - 6*r7,
    7/432000*r1^3 + 13/144000*r1^2*r2 - 11/48000*r1*r2^2 + 53/432000*r2^3 - 127/36000*r1^2*r3 + 157/18000*r1*r2*r3 - 187/36000*r2^2*r3 + 83/1000*r1*r3^2 - 203/1000*r2*r3^2 - 148/125*r3^3 - r5 - 2*r6 - 4*r7,
    r6,
    r7
    ];
    phi := [
    s1 + s2 + s3,
    -18*s3,
    -4/15*s1 + 64/15*s2 + 122/5*s3,
    -6408/2125*s1^3 + 5724/2125*s1^2*s2 + 266976/2125*s1*s2^2 - 266292/2125*s2^3 + 343656/2125*s1^2*s3 - 1772712/2125*s1*s2*s3 - 4791744/2125*s2^2*s3 - 5390064/2125*s1*s3^2 + 9569664/2125*s2*s3^2 + 66655872/2125*s3^3 - 497664/17*s4 + 746496/17*s5,
    153/100*s1^3 - 459/200*s1^2*s2 - 1377/20*s1*s2^2 + 13923/200*s2^3 - 5049/100*s1^2*s3 + 33507/100*s1*s2*s3 + 68391/50*s2^2*s3 + 22032/25*s1*s3^2 + 11016/25*s2*s3^2 - 66096/5*s3^3 + 16524*s4
    ];
    psi := [
    16/17*s1 - 151/612*s2 - 15/68*s3,
    1/17*s1 + 185/612*s2 + 15/68*s3,
    -1/18*s2,
    -9/157216*s1^3 + 91/628864*s1^2*s2 + 20569/33958656*s1*s2^2 - 37/19101744*s2^3 + 105/628864*s1^2*s3 + 4043/5659776*s1*s2*s3 + 2213/203751936*s2^2*s3 + 133/1257728*s1*s3^2 - 1427/7546368*s2*s3^2 - 55/628864*s3^3 + 1/16524*s5,
    9/1257728*s1^3 + 985/15092736*s1^2*s2 - 33905/407503872*s1*s2^2 - 171713/3667534848*s2^3 - 3/5030912*s1^2*s3 - 395/3773184*s1*s2*s3 - 11009/815007744*s2^2*s3 - 3/628864*s1*s3^2 + 725/20123648*s2*s3^2 + 33/20123648*s3^3 + 17/746496*s4 + 1/24786*s5
    ];
    assert MissingFormCertificate();
    published := PublishedPresentation();
    source,reduce,expand := MinimalPresentation(published);
    sourceCommon := ideal<S | [S!f : f in Basis(source)]>;
    return published,sourceCommon,reduce,tau,phi,psi;
end function;
