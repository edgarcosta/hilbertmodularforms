// Gundlach, J. reine angew. Math. 220 (1965), Satz 2-3, pp.122,127.
// The relations below use weighted Jacobians in place of his skew forms.
// Their normalisations are independent of his constructions on pp.142-153.
SetNthreads(4);
F<s> := QuadraticField(3);
ZF := Integers(F);
N := 1*ZF;
prec := 300;
M := GradedRingOfHMFs(F,prec);
bbs := NarrowClassGroupReps(M);
assert [LMFDBLabel(b) : b in bbs] eq ["1.1","2.1"];
assert ClassNumber(F) eq 1 and NarrowClassNumber(F) eq 2;
X := HeckeCharacterGroup(N,[1,2]);
assert #X eq 2;
chi := [c : c in Elements(X) | not IsTrivial(c)][1];
assert IsGamma1EisensteinWeight(chi,3);
one := AssociatedPrimitiveCharacter(X!1);
sign := AssociatedPrimitiveCharacter(chi);
E := AssociativeArray();
for k in [1,2,3,4,6] do
    Mk := HMFSpace(M,N,[k,k],IsOdd(k) select chi else X!1);
    E[k] := EisensteinSeries(Mk,one,IsOdd(k) select sign else one);
end for;
assert Coefficient(E[1],bbs[1],F!0) eq 0;
assert Coefficient(E[1],bbs[2],F!0) eq 1/12;
E[1] *:= 12;
for k in [2,3,4,6] do
    assert Coefficient(E[k],bbs[1],F!0) eq 1;
    assert Coefficient(E[k],bbs[2],F!0) eq 1;
end for;

H<t> := FunctionField(Rationals());
evenSeries := (1+t^14)/((1-t^2)*(1-t^4)*(1-t^6));
fullSeries := [];
for i in [1,2] do
    bb := bbs[i];
    weights := (i eq 1) select [2,3,4] else [1,4,6];
    skewWeight := &+weights+2;
    generators := [* HMF(Components(E[k])[bb]) : k in weights *];
    powers := [generators[j]^(12 div weights[j]) : j in [1..3]];
    assert AlgebraicallyIndependent(powers : IdealClassesSupport:=[bb]);
    printf "PASS component %o: independent Eisenstein triple %o\n",LMFDBLabel(bb),weights;

    // Derivative anomalies cancel in this determinant, giving weight sum(k)+2.
    // Euler derivatives in lower-set coordinates change it by a nonzero scalar.
    // They preserve exponents, so pruning retains exact convolution coefficients.
    fs := [LowerSetExpansion(Components(f)[bb]) : f in generators];
    Q := Universe(fs);
    jac := Determinant(Matrix(Q,3,3,
        [weights[j]*fs[j] : j in [1..3]] cat
        [Q.1*Derivative(f,1) : f in fs] cat
        [Q.2*Derivative(f,2) : f in fs]));
    Sk := HMFSpace(M,N,[skewWeight,skewWeight],chi);
    skew := HMF(HMFComponent(Sk,bb,jac,prec : LowerSet:=true));
    assert not IsZero(skew);
    Append(~generators,skew);
    P := PolynomialRing(Rationals(),weights cat [skewWeight]);
    relationWeight := 2*skewWeight;
    mons := [m : m in MonomialsOfWeightedDegree(P,relationWeight)
        | Exponents(m)[4] lt 2];
    forms := EvaluateMonomials(generators,mons);
    A := CoefficientsMatrix(forms : IdealClasses:=[bb]);
    gamma := CongruenceSubgroup("GL+","Gamma0",F,N,bb);
    componentSeries := H!Evaluate(HilbertSeriesVdG(gamma),t^2);
    assert componentSeries eq evenSeries;
    S<u> := PowerSeriesRing(Rationals(),relationWeight+1);
    dim := Integers()!Coefficient(S!componentSeries,relationWeight);

    // Full rank in the independently known dimension makes these coefficients
    // injective on the entire relation-weight space, including the Jacobian square.
    assert #mons eq dim and Rank(A) eq dim;
    B := CoefficientsMatrix([skew^2] : IdealClasses:=[bb]);
    polynomialRows := [j : j in [1..#mons] | Exponents(mons[j])[4] eq 0];
    A0 := Matrix([Eltseq(A[j]) : j in polynomialRows]);
    ok, sol := IsConsistent(A0,B[1]);
    assert ok;
    square := &+[P | sol[j]*mons[polynomialRows[j]] : j in [1..#polynomialRows]];
    relation := P.4^2-square;
    assert IsHomogeneous(relation) and WeightedDegree(relation) eq relationWeight;
    assert IsZero(Evaluate(relation,generators));
    factors := Factorization(square);
    assert #factors gt 0 and &and[e[2] eq 1 : e in factors];
    assert &and[Degree(e[1],4) eq 0 : e in factors];

    // A reduced branch polynomial makes this quadratic hypersurface normal.
    // Independence and nonsquareness give an injection into the modular ring.
    // Equal even series give every even form; an odd form f is integral (f^2)
    // and rational (f*g/g, g a nonzero odd generator), so normality gives f too.
    I := ideal<P | relation>;
    hs := (1+t^skewWeight)/&*[1-t^k : k in weights];
    assert H!HilbertSeries(I) eq hs;
    assert (hs+Evaluate(hs,-t))/2 eq componentSeries;
    Append(~fullSeries,hs);
    printf "PASS component %o: weights %o, relation weight %o, determination rank %o/%o at precision %o\n",
        LMFDBLabel(bb),weights cat [skewWeight],relationWeight,Rank(A),dim,prec;
    printf "RELATION %o\n",relation;
    printf "PASS component %o: squarefree branch and full Hilbert series %o\n",LMFDBLabel(bb),hs;
end for;
assert HilbertSeries(M) eq 2*evenSeries;

// Gundlach pp.133-136: nu lies in the codifferent, with numerator 2*sqrt(3)*nu.
// All ideal divisors are principal; norm signs are well-defined since units
// have norm +1. His printed kappa values fix the normalisation exactly.
bb := bbs[1];
R<a,b,c> := PolynomialRing(Rationals(),[2,3,4]);
triple := [* E[2],E[3],E[4] *];
kappas := [Rationals() | 24,36,240/23];
T<v> := PowerSeriesRing(Rationals(),5);
for j->k in [2,3,4] do
    mons := [m : m in MonomialsOfWeightedDegree(R,k)];
    A := CoefficientsMatrix(EvaluateMonomials(triple,mons) : IdealClasses:=[bb]);
    dim := Integers()!Coefficient(T!fullSeries[1],k);
    assert #mons eq dim and Rank(A) eq dim;
    checked := 0;
    for nu in FunDomainRepsUpToPrec(M,bb,prec) do
        if IsZero(nu) then
            expected := Rationals()!1;
        else
            numerator := 2*s*nu;
            assert numerator in ZF;
            nn := ideal<ZF | numerator>;
            divisorSum := Rationals()!0;
            for dd in Divisors(nn) do
                principal, mu := IsPrincipal(dd);
                assert principal;
                normSign := (Norm(mu) gt 0) select 1 else -1;
                divisorSum +:= normSign^k*Norm(dd)^(k-1);
            end for;
            expected := kappas[j]*divisorSum;
        end if;
        assert Coefficient(E[k],bb,nu) eq expected;
        checked +:= 1;
    end for;
    printf "PASS Gundlach G%o: printed divisor formula at %o indices, determination rank %o/%o at precision %o\n",
        k,checked,Rank(A),dim,prec;
end for;
print "PASS Gundlach D12 Satz 2 and 3: structural presentations on both components";
