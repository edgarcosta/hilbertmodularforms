// Compare the eta0-extended Theorem 9 with a freshly generated certified
// presentation of our ring at Gamma0((2)), not the stored file.
// Identification with the full ring of Hilbert modular forms in every weight
// also requires this quotient to be an integral domain. This is not proved here.

SetMemoryLimit(24*2^30);
SetNthreads(4); SetSeed(1);
F := QuadraticField(13); ZF := Integers(F); N := 2*ZF;
M := GradedRingOfHMFs(F,200);
assert NarrowClassNumber(M) eq 1;
sigma := Automorphisms(F)[2];
assert ideal<ZF | [sigma(x) : x in Generators(N)]> eq N;
data := ConstructGeneratorsAndRelations(M,N,6,12);
G := data[1]; rels := data[2];
R := ConstructWeightedPolynomialRing(G);
I := ConstructIdeal(R,rels);
equations := Basis(I);
assert VariableWeights(R) eq [2,2,2,6,6,6,6];
assert CertifyAlgIndependent(G,rels,3);
assert HilbertSeries(I) eq HilbertSeries(M,N);
assert &and[WeightedDegree(f) in {8,10,12} : f in equations];
print "PASS generated algebraic independence and exact full Hilbert series";
Q<q> := PowerSeriesRing(Rationals(),1);
assert Coefficient(Q!HilbertSeries(M,N),0) eq 1;
assert Rank(CoefficientsMatrix([G[2][1]^0] : prec := 200)) eq 1;
print "RANK weight=0 dimension=1 rank=1 (constants)";

S := PolynomialRing(Rationals(),[2,2,2,6,6]);
LitData := eval(Read("Verification/LiteratureEquations/2.2.13.1-4.1-vdGZagier.m") cat "return LitData;");
published,source,reduce,tau,phi,psi := LitData(R,S);
swapped := AssociativeArray();
for w in [2,6] do swapped[w] := [Swap(g) : g in G[w]]; end for;
offset := 0;
for w in [2,4,6,8,10,12] do
    space := HMFSpace(M,N,[w,w]);
    assert &and[IsOne(u) : u in Values(UnitCharacters(space))];
    known := Integers()!Trace(space,1*ZF)+EisensteinDimension(space);
    assert known eq Dimension(space);
    mons := Setseq(MonomialsOfWeightedDegree(R,w));
    forms := EvaluateMonomials(G,mons);
    extra := IsDefined(swapped,w) select swapped[w] else [];
    coeffs := CoefficientsMatrix(forms cat extra : prec := 200);
    A := RowSubmatrix(coeffs,1,#forms);
    // Full trace dimension makes coefficient comparison injective on this space.
    assert Rank(A) eq known and Rank(coeffs) eq known;
    for f in [f : f in equations | WeightedDegree(f) eq w] do
        assert Vector(BaseRing(A),[MonomialCoefficient(f,m) : m in mons])*A eq 0;
    end for;
    if IsDefined(swapped,w) then
        for j in [1..#G[w]] do
            assert Vector(BaseRing(A),[MonomialCoefficient(tau[offset+j],m) : m in mons])*A eq coeffs[#forms+j];
        end for;
        offset +:= #G[w];
    end if;
    printf "RANK weight=%o trace-dimension=%o rank=%o\n",w,known,Rank(A);
end for;
assert VerifyGradedIsomorphism(I,I,tau,tau);
print "PASS exact relation vanishing through weight 12 and geometric swap";

K,inclusion,hs := SymmetricSubringPresentation(I,tau);
assert VerifySymmetricSubringPresentation(I,tau,K,inclusion);
assert VariableWeights(Generic(K)) eq VariableWeights(S);
K := ideal<S | [S!f : f in Basis(K)]>;
assert VerifyGradedIsomorphism(source,K,phi,psi);
assert Parent(hs)!HilbertSeries(source) eq hs;
assert Parent(hs)!HilbertSeries(published) eq hs;
images := [Evaluate(f,inclusion) : f in phi];
assert &and[Evaluate(f,tau)-f in I : f in images];
assert VerifySymmetricSubringPresentation(I,tau,source,images);
publishedImages := [Evaluate(f,images) : f in reduce];
assert &and[Evaluate(f,tau)-f in I : f in publishedImages];
assert VerifySymmetricSubringPresentation(I,tau,published,publishedImages);
print "PASS eta0-extended Theorem 9: exact graph kernel, image symmetry and rational series";
