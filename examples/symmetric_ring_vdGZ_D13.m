// Theorem 7 at level one, in the stored presentation of our D=13 ring.
// The source map identifies abstract rational presentations; it does not
// identify the paper's normalized forms with the computed q-expansions.
// Geometric swap is checked after transporting freshly computed generators.

SetMemoryLimit(24*2^30);
SetNthreads(4); SetSeed(1);
SymmetricLitData := eval(Read("Verification/LiteratureEquations/2.2.13.1-1.1-vdGZagierSymmetric.m") cat "return SymmetricLitData;");
source,citation := SymmetricLitData();
P := Generic(source);
assert VariableWeights(P) eq [2,4,6,6];
assert IsHomogeneous(source) and #Basis(source) eq 1;
H<t> := FunctionField(Rationals());
expected := (1-t^12)/((1-t^2)*(1-t^4)*(1-t^6)^2);
assert H!HilbertSeries(source) eq expected;

F := QuadraticField(13); ZF := Integers(F); N := 1*ZF;
M := GradedRingOfHMFs(F,200);
assert NarrowClassNumber(M) eq 1;
sigma := Automorphisms(F)[2];
assert ideal<ZF | [sigma(x) : x in Generators(N)]> eq N;
data := ConstructGeneratorsAndRelations(M,N,8,16);
G := data[1]; rels := data[2];
R := ConstructWeightedPolynomialRing(G);
I := ConstructIdeal(R,rels);
equations := Basis(I);
assert VariableWeights(R) eq [2,4,6,6,8];
assert CertifyAlgIndependent(G,rels,3);
assert HilbertSeries(I) eq HilbertSeries(M,N);
assert Sort([WeightedDegree(f) : f in equations]) eq [12,16];

J := LoadStoredCanonicalRing("2.2.13.1-1.1"); S := Generic(J);
toStored := [S.i : i in [1..5]];
toStored[5] +:= 25/4*(S.2^2-S.1*S.4);
fromStored := [R.i : i in [1..5]];
fromStored[5] -:= 25/4*(R.2^2-R.1*R.4);
assert VerifyGradedIsomorphism(I,J,toStored,fromStored);
assert IsPrime(J);
print "PASS full-ring transport, domain and exact rational series";

swapped := AssociativeArray();
for w in Sort(Setseq(Keys(G))) do swapped[w] := [Swap(g) : g in G[w]]; end for;
tau,T := ChangeOfPresentation(G,swapped : Prec := 200, Verify := true);
tau := [R!f : f in tau];
Q<q> := PowerSeriesRing(Rationals(),1);
assert Coefficient(Q!HilbertSeries(M,N),0) eq 1;
assert Rank(CoefficientsMatrix([G[2][1]^0] : prec := 200)) eq 1;
print "RANK weight=0 dimension=1 rank=1 (constants)";
offset := 0;
for w in [2,4,6,8,10,12,14,16] do
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
    printf "RANK weight=%o trace-dimension=%o rank=%o columns=%o\n",w,known,Rank(A),Ncols(A);
end for;
// Primality and three algebraically independent HMFs make this relation
// ideal the full HMF kernel. Equality of rational series then proves generation
// in every weight.
assert VerifyGradedIsomorphism(I,I,tau,tau);
storedTau := [Evaluate(Evaluate(f,tau),toStored) : f in fromStored];
assert VerifyGradedIsomorphism(J,J,storedTau,storedTau);
print "PASS exact relation vanishing through weight 16 and geometric swap";

LitData := eval(Read("Verification/LiteratureEquations/2.2.13.1-1.1-vdGZagier.m") cat "return LitData;");
fullSource,phi,psi,fullCitation := LitData(S,S);
assert VerifyGradedIsomorphism(fullSource,J,phi,psi);
assert &and[Evaluate(phi[i],storedTau)-phi[i] in J : i in [1..4]];
assert Evaluate(phi[5],storedTau)+phi[5] in J;
K,inclusion,hs := SymmetricSubringPresentation(J,storedTau);
assert VerifySymmetricSubringPresentation(J,storedTau,K,inclusion);
assert VariableWeights(Generic(K)) eq [2,4,6,6];
assert H!hs eq expected;
images := phi[1..4];
assert VerifySymmetricSubringPresentation(J,storedTau,source,images);
printf "SOURCE %o\nINCLUSION %o\nSTORED SWAP %o\nSERIES %o\n",citation,images,storedTau,expected;
print "PASS vdGZ D13 level 1 symmetric";
