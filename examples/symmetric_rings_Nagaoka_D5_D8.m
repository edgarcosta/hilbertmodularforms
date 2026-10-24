// Nagaoka, J. Math. Soc. Japan 35 (1983), pp.589-608, Theorems 1, 2 and 5.1.
// Finite coefficient checks supplement his integral generation theorem.
SetNthreads(4);
SetSeed(1);
SetColumns(0);
wall := Time();
sourceData := eval Read("Verification/LiteratureEquations/NagaokaSymmetric.m");
SymmetricLitData := sourceData[1];
PublishedForms := sourceData[2];
PublishedImages := sourceData[3];
H<t> := FunctionField(Rationals());
for D in [5,8] do
    F := QuadraticField(D); N := 1*Integers(F); precision := 80;
    M := GradedRingOfHMFs(F,precision);
    assert NarrowClassNumber(M) eq 1;
    assert ideal<Integers(F) | [Automorphisms(F)[2](x) : x in Generators(N)]> eq N;
    weights := D eq 5 select [2,6,10,20] else [2,4,6,14];
    relationWeight := 2*weights[4];
    J := LoadStoredCanonicalRing(Sprintf("2.2.%o.1-1.1",D)); R := Generic(J);
    G := AssociativeArray(); loaded := true;
    for w in weights do
        // Optional checkpoints store full-ring generators at precision 80.
        directory := D eq 5 select "symmetric-subring" else "nagaoka-d5-d8";
        path := Sprintf("docs/superpowers/%o/d%o-gen-80-%o.bin",directory,D,w);
        try
            ok, forms := LoadBasis(path : Mk:=HMFSpace(M,N,[w,w]));
        catch e
            loaded := false; break;
        end try;
        assert ok; G[w] := forms;
    end for;
    if not loaded then
        data := ConstructGeneratorsAndRelations(M,N,weights[4],weights[4] : NumberOfTraceForms:=6);
        G := data[1];
    end if;
    assert Sort(Setseq(Keys(G))) eq weights;
    assert &and[#G[w] eq 1 : w in weights];
    T := ConstructWeightedPolynomialRing(G);
    flat := Sum([* SequenceToList(G[w]) : w in weights *] : empty:=[* *]);
    I := Syzygies(flat,[relationWeight]);
    I := ideal<T | [T!f : f in Basis(I)]>;
    mons := Setseq(MonomialsOfWeightedDegree(T,relationWeight));
    coeffs := CoefficientsMatrix(EvaluateMonomials(G,mons) : prec:=precision);
    known := Dimension(HMFSpace(M,N,[relationWeight,relationWeight]));
    assert Rank(coeffs) eq known;
    assert &and[Vector(Rationals(),[MonomialCoefficient(f,m) : m in mons])*coeffs eq 0 : f in Basis(I)];
    rels := AssociativeArray();
    rels[relationWeight] := [[MonomialCoefficient(f,m) : m in mons] : f in Basis(I)];
    assert CertifyAlgIndependent(G,rels,3);
    assert HilbertSeries(I) eq HilbertSeries(M,N) and HilbertSeries(I) eq HilbertSeries(J);
    phi := [R.i : i in [1..4]]; psi := [T.i : i in [1..4]];
    assert VerifyGradedIsomorphism(I,J,phi,psi);
    printf "FULL RING D=%o relation-weight=%o dimension=%o rank=%o columns=%o transport=%o inverse=%o\n",D,relationWeight,known,Rank(coeffs),Ncols(coeffs),phi,psi;
    bb := NarrowClassGroupReps(M)[1];
    indices := FunDomainRepsUpToPrec(M,bb,precision);
    printf "INDICES D=%o precision=%o bb=%o indices=%o\n",D,precision,bb,indices;
    published := PublishedForms(M);
    L,citation := SymmetricLitData(D);
    images := PublishedImages(D,R);
    for j in [1..#published] do
        f := published[j]; w := Weight(f)[1];
        space := HMFSpace(M,N,[w,w]); known := Dimension(space);
        mons := Setseq(MonomialsOfWeightedDegree(T,w));
        forms := EvaluateMonomials(G,mons);
        basis := Basis(forms);
        assert #basis eq known;
        space`Basis := basis;
        coeffs := CoefficientsMatrix(Basis(space) cat forms cat [f] : prec:=precision);
        A := RowSubmatrix(coeffs,known+1,#forms);
        assert Ncols(coeffs) eq #indices;
        assert Rank(RowSubmatrix(coeffs,1,known)) eq known and Rank(A) eq known and Rank(coeffs) eq known;
        ok,sol := IsConsistent(A,coeffs[Nrows(coeffs)]); assert ok;
        p := &+[T | sol[i]*mons[i] : i in [1..#mons]];
        assert Evaluate(p,phi)-images[j] in J;
        printf "DICTIONARY D=%o weight=%o precision=%o dimension=%o rank=%o columns=%o image=%o\n",D,w,precision,known,Rank(A),Ncols(coeffs),images[j];
        assert &and[Denominator(a) eq 1 : a in Eltseq(coeffs[Nrows(coeffs)])];
    end for;
    swapped := AssociativeArray();
    for w in weights do swapped[w] := [Swap(g) : g in G[w]]; end for;
    tau,_ := ChangeOfPresentation(G,swapped : Prec:=precision,Verify:=true);
    tau := [T!p : p in tau];
    offset := 0;
    for w in weights do
        space := HMFSpace(M,N,[w,w]); known := Dimension(space);
        assert &and[IsOne(u) : u in Values(UnitCharacters(space))];
        mons := Setseq(MonomialsOfWeightedDegree(T,w)); forms := EvaluateMonomials(G,mons);
        basis := Basis(forms); assert #basis eq known;
        space`Basis := basis;
        coeffs := CoefficientsMatrix(Basis(space) cat forms cat swapped[w] : prec:=precision);
        A := RowSubmatrix(coeffs,known+1,#forms);
        assert Ncols(coeffs) eq #indices;
        assert Rank(RowSubmatrix(coeffs,1,known)) eq known and Rank(A) eq known and Rank(coeffs) eq known;
        for j in [1..#G[w]] do
            assert Vector(Rationals(),[MonomialCoefficient(tau[offset+j],m) : m in mons])*A eq coeffs[known+#forms+j];
        end for;
        offset +:= #G[w];
        printf "SWAP RANK D=%o weight=%o dimension=%o rank=%o columns=%o\n",D,w,known,Rank(A),Ncols(coeffs);
    end for;
    storedTau := [Evaluate(Evaluate(p,tau),phi) : p in psi];
    assert VerifyGradedIsomorphism(J,J,storedTau,storedTau);
    K,inclusion,series := SymmetricSubringPresentation(J,storedTau);
    assert VerifySymmetricSubringPresentation(J,storedTau,K,inclusion);
    assert inclusion eq [R.1,R.2,R.3];
    P := Generic(K);
    fixedImages := PublishedImages(D,P);
    assert &and[Evaluate(fixedImages[i],inclusion)-images[i] in J : i in [1..#images]];
    assert VerifySymmetricSubringPresentation(K,[P.i : i in [1..Rank(P)]],L,fixedImages);
    assert VerifySymmetricSubringPresentation(J,storedTau,L,images);
    expected := D eq 5 select 1/((1-t^2)*(1-t^6)*(1-t^10)) else 1/((1-t^2)*(1-t^4)*(1-t^6));
    assert H!HilbertSeries(L) eq H!series and H!series eq expected;
    if D eq 5 then
        assert 4*images[4]-images[2]^2+images[1]*images[3] in J;
        numerator := published[2]^2-published[1]*published[3];
        row := CoefficientsMatrix([numerator] : prec:=precision);
        assert &and[Denominator(a/4) eq 1 : a in Eltseq(row)];
        bad := [images[1],images[2]/2,images[3],(images[2]^2/4-images[1]*images[3])/4];
        assert VerifySymmetricSubringPresentation(J,storedTau,L,bad);
    end if;
    diag := [RestrictionToDiagonal(f,M,N : AsCoefficients:=true) : f in published];
    qprec := Minimum([#r : r in diag]);
    Q<q> := PowerSeriesRing(Rationals());
    delta := q*(&*[Q!(1-q^n)^24 : n in [1..qprec]])+O(q^qprec);
    e4 := 1+240*&+[Q | (&+[d^3 : d in Divisors(n)])*q^n : n in [1..qprec-1]]+O(q^qprec);
    expectedDiag := D eq 5 select [e4,2*delta,Q!0,delta^2] else [e4,Q!0,delta];
    for i in [1..#diag] do
        // The trace enumerator omits zero, so obtain the constant directly.
        diag[i][1] := Coefficient(published[i],N,F!0);
        assert diag[i][1..qprec] eq [Coefficient(expectedDiag[i],n) : n in [0..qprec-1]];
    end for;
    if D eq 5 then
        badDiag := RestrictionToDiagonal(published[2]/2,M,N : AsCoefficients:=true);
        assert badDiag[1..qprec] ne [2*Coefficient(delta,n) : n in [0..qprec-1]];
        assert Coefficient(published[2]/2,N,(F!1-1/F.1)/2) eq 1/2;
        print "PASS bad J6 rescaling preserves the rational ring and fails normalization";
    end if;
    printf "NORMALIZATION D=%o integral-columns=%o diagonal-through-q^%o restrictions=%o\n",D,#indices,qprec-1,[r[1..qprec] : r in diag];
    printf "ACTION D=%o %o\nFIXED INCLUSION %o\nPUBLISHED INCLUSION %o\nSOURCE KERNEL %o\nSERIES %o\nSOURCE %o\n",D,storedTau,inclusion,images,Basis(L),series,citation;
end for;
print "PASS Nagaoka rational comparison";
print "PASS Nagaoka normalization at stated precision";
printf "RESOURCES threads=4 wall=%os memory=%oMB\n",Time(wall),GetMemoryUsage() div 1024^2;
