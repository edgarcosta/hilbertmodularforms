// Certify van der Geer and Zagier's Theorem 7 in the stored level-one ring.
// The rational isomorphism does not identify the paper's normalized sigma_i.
// Keep eval at top level: nested procedure eval crashes the runner.
import "Verification/SymmetricSubring.m" : is_geometric_swap;

// The transport to the stored ring assumes these seed-1 generators.
SetSeed(1);
F := QuadraticField(13);
ZF := Integers(F);
N := 1*ZF;
M := GradedRingOfHMFs(F, 200);
assert NarrowClassNumber(M) eq 1;
data := ConstructGeneratorsAndRelations(M, N, 8, 16);
G := data[1];
rels := data[2];
R := ConstructWeightedPolynomialRing(G);
I := ConstructIdeal(R, rels);
// HilbertSeries caches a Groebner basis with additional relation weights.
equations := Basis(I);
assert VariableWeights(R) eq [2, 4, 6, 6, 8];
assert CertifyAlgIndependent(G, rels, 3);
assert HilbertSeries(I) eq HilbertSeries(M, N);
assert Sort([WeightedDegree(f) : f in equations]) eq [12, 16];

J := LoadStoredCanonicalRing("2.2.13.1-1.1");
S := Generic(J);
toStored := [S.i : i in [1..5]];
toStored[5] +:= 25/4*(S.2^2 - S.1*S.4);
fromStored := [R.i : i in [1..5]];
fromStored[5] -:= 25/4*(R.2^2 - R.1*R.4);
assert VerifyGradedIsomorphism(I, J, toStored, fromStored);
// Primality and algebraic independence identify the relation kernel;
// equality of Hilbert series then proves generation in every weight.
assert IsPrime(J);

swapped := AssociativeArray();
assert not IsEmpty(Keys(G));
for w in Sort(Setseq(Keys(G))) do
  swapped[w] := [Swap(g) : g in G[w]];
end for;
tau, _ := ChangeOfPresentation(G, swapped : Prec := 200, Verify := true);
tau := [R!f : f in tau];
assert is_geometric_swap(M, N, G, I, tau, [2, 4, 6, 8, 10, 12, 14, 16], 200);
assert VerifyGradedIsomorphism(I, I, tau, tau);
storedTau := [Evaluate(Evaluate(f, tau), toStored) : f in fromStored];
assert VerifyGradedIsomorphism(J, J, storedTau, storedTau);

LitData := eval(Read("Verification/LiteratureEquations/2.2.13.1-1.1-vdGZagier.m")
    cat "return LitData;");
fullSource, phi, psi, _ := LitData(S, S);
assert VerifyGradedIsomorphism(fullSource, J, phi, psi);
symmetric_lit_data := eval(Read("Verification/LiteratureEquations/2.2.13.1-1.1-vdGZagierSymmetric.m")
    cat "return symmetric_lit_data;");
L, images, citation := symmetric_lit_data(S);
assert not IsEmpty(images);
assert images eq phi[1..4];
assert &and[Evaluate(f, storedTau) - f in J : f in images];
assert phi[5] notin J and Evaluate(phi[5], storedTau) + phi[5] in J;
assert VariableWeights(Generic(L)) eq [2, 4, 6, 6];
assert IsHomogeneous(L) and #Basis(L) eq 1;
K, inclusion, hs := SymmetricSubringPresentation(J, storedTau);
assert IsSymmetricSubringPresentation(J, storedTau, K, inclusion);
assert VariableWeights(Generic(K)) eq [2, 4, 6, 6];
H<t> := FunctionField(Rationals());
expected := (1 - t^12)/((1 - t^2)*(1 - t^4)*(1 - t^6)^2);
assert H!hs eq expected and H!HilbertSeries(L) eq expected;
assert IsSymmetricSubringPresentation(J, storedTau, L, images);
printf "D=13 level one: %o certified against the swap-fixed subring\n", citation;
