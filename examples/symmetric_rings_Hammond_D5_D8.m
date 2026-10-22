SetNthreads(4);
H<t> := FunctionField(Rationals());
SymmetricLitData := eval(Read("Verification/LiteratureEquations/HammondSymmetric.m")
    cat "return SymmetricLitData;");
sources, targets, maps, citation := SymmetricLitData();

for i in [1..2] do
    D := [5,8][i];
    I := sources[i]; P := Generic(I);
    J := targets[i]; R := Generic(J);
    weights := D eq 5 select [2,6,10] else [2,4,6];
    assert VariableWeights(P) eq weights;
    assert I eq ideal<P | >;
    litfile := Sprintf("Verification/LiteratureEquations/2.2.%o.1-1.1-Hirzebruch.m",D);
    LitData := eval(Read(litfile) cat "return LitData;");
    L, phi, psi, fullCitation := LitData(R,R);
    assert VerifyGradedIsomorphism(L,J,phi,psi);

    litTau := [R.1,R.2,R.3,-R.4];
    assert VerifyGradedIsomorphism(L,L,litTau,litTau);
    tau := [Evaluate(Evaluate(f,litTau),phi) : f in psi];
    assert VerifyGradedIsomorphism(J,J,tau,tau);
    K, inclusion, hs := SymmetricSubringPresentation(J,tau);
    assert VerifySymmetricSubringPresentation(J,tau,K,inclusion);
    assert VariableWeights(Generic(K)) eq weights;

    sourceToFixed := [Generic(K).j : j in [1..3]];
    fixedToSource := [P.j : j in [1..3]];
    assert VerifyGradedIsomorphism(I,K,sourceToFixed,fixedToSource);
    images := [maps[i](P.j) : j in [1..3]];
    assert images eq [Evaluate(f,inclusion) : f in sourceToFixed];
    assert &and[Evaluate(f,tau)-f in J : f in images];
    // This checks the exact graph kernel and generation of the whole fixed ring.
    assert VerifySymmetricSubringPresentation(J,tau,I,images);
    expected := 1/(&*[1-t^w : w in weights]);
    assert H!hs eq expected and H!HilbertSeries(I) eq expected;
    assert tau[4]-R.4 notin J;
    assert H!HilbertSeries(J) eq (1+t^VariableWeights(R)[4])*expected;
    printf "D=%o: zero kernel, invariant images, exact symmetric series %o\n",D,hs;
    printf "SOURCE MAP %o -> %o: %o\n",P,R,images;
    printf "SWAP %o\n",tau;
end for;
printf "%o; abstract graded generators only.\n",citation;
print "PASS Hammond D5 D8 symmetric";
