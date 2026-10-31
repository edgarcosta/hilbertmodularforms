// Certify the eta0-extended Theorem 9 against a generated level-(2) quotient.
// Theorem 6 supplies eta0. Identification with the full symmetric HMF ring
// remains conditional on this quotient being a domain, which is not proved here.
// Keep eval at top level: nested procedure eval crashes the runner.
import "Verification/SymmetricSubring.m" : is_geometric_swap;

// The stored images use the basis obtained with seed 1 and precision 200.
SetSeed(1);
F := QuadraticField(13);
N := 2*Integers(F);
M := GradedRingOfHMFs(F, 200);
assert NarrowClassNumber(M) eq 1;
data := ConstructGeneratorsAndRelations(M, N, 6, 12);
G := data[1];
rels := data[2];
R := ConstructWeightedPolynomialRing(G);
I := ConstructIdeal(R, rels);
// HilbertSeries caches a Groebner basis with additional relation weights.
equations := Basis(I);
assert not IsEmpty(equations);
assert VariableWeights(R) eq [2, 2, 2, 6, 6, 6, 6];
assert CertifyAlgIndependent(G, rels, 3);
assert HilbertSeries(I) eq HilbertSeries(M, N);
assert &and[WeightedDegree(f) in {8, 10, 12} : f in equations];
swapped := AssociativeArray();
for w in [2, 6] do
  swapped[w] := [Swap(g) : g in G[w]];
end for;
tau, _ := ChangeOfPresentation(G, swapped : Prec := 200, Verify := true);
tau := [R!f : f in tau];
assert is_geometric_swap(M, N, G, I, tau, [2, 4, 6, 8, 10, 12], 200);
assert VerifyGradedIsomorphism(I, I, tau, tau);
K, inclusion, hs := SymmetricSubringPresentation(I, tau);
assert IsSymmetricSubringPresentation(I, tau, K, inclusion);
assert VariableWeights(Generic(K)) eq [2, 2, 2, 6, 6];
symmetric_lit_data := eval(Read("Verification/LiteratureEquations/2.2.13.1-4.1-vdGZagierSymmetric.m")
    cat "return symmetric_lit_data;");
L, images, citation := symmetric_lit_data(R);
assert not IsEmpty(images);
assert &and[Evaluate(f, tau) - f in I : f in images];
assert IsSymmetricSubringPresentation(I, tau, L, images);
assert Parent(hs)!HilbertSeries(L) eq hs;

S := PolynomialRing(Rationals(), [2, 2, 2, 6, 6]);
minimal_presentation := function(I)
  R := Generic(I);
  S := PolynomialRing(Rationals(), [2, 2, 2, 6, 6]);
  a := S.1; u := S.2; e := S.3; c := S.4; z := S.5;
  w := -z - a*u^2 + u^3 + u^2*e/2;
  v := -w - a*u*e + u^2*e + u*e^2/2;
  d := -v - a*e^2 + u*e^2 + e^3/2;
  images := [a, u*e, c, d, u, v, w, z, e];
  inverse := [R.1, R.5, R.9, R.3, R.8];
  K := ideal<S | [Evaluate(g, images) : g in Basis(I)]>;
  assert &and[Evaluate(images[i], inverse) - R.i in I : i in [1..9]];
  assert &and[Evaluate(inverse[i], images) eq S.i : i in [1..5]];
  assert HilbertSeries(K) eq HilbertSeries(I);
  return K, images, inverse;
end function;
s1, s2, s3, s4, s5 := Explode([S.i : i in [1..5]]);
phi := [
  s1 + s2 + s3,
  -18*s3,
  -4/15*s1 + 64/15*s2 + 122/5*s3,
  -6408/2125*s1^3 + 5724/2125*s1^2*s2 + 266976/2125*s1*s2^2 - 266292/2125*s2^3
    + 343656/2125*s1^2*s3 - 1772712/2125*s1*s2*s3 - 4791744/2125*s2^2*s3
    - 5390064/2125*s1*s3^2 + 9569664/2125*s2*s3^2 + 66655872/2125*s3^3 - 497664/17*s4
    + 746496/17*s5,
  153/100*s1^3 - 459/200*s1^2*s2 - 1377/20*s1*s2^2 + 13923/200*s2^3 - 5049/100*s1^2*s3
    + 33507/100*s1*s2*s3 + 68391/50*s2^2*s3 + 22032/25*s1*s3^2 + 11016/25*s2*s3^2
    - 66096/5*s3^3 + 16524*s4
];
psi := [
  16/17*s1 - 151/612*s2 - 15/68*s3,
  1/17*s1 + 185/612*s2 + 15/68*s3,
  -1/18*s2,
  -9/157216*s1^3 + 91/628864*s1^2*s2 + 20569/33958656*s1*s2^2 - 37/19101744*s2^3
    + 105/628864*s1^2*s3 + 4043/5659776*s1*s2*s3 + 2213/203751936*s2^2*s3
    + 133/1257728*s1*s3^2 - 1427/7546368*s2*s3^2 - 55/628864*s3^3 + 1/16524*s5,
  9/1257728*s1^3 + 985/15092736*s1^2*s2 - 33905/407503872*s1*s2^2 - 171713/3667534848*s2^3
    - 3/5030912*s1^2*s3 - 395/3773184*s1*s2*s3 - 11009/815007744*s2^2*s3 - 3/628864*s1*s3^2
    + 725/20123648*s2*s3^2 + 33/20123648*s3^3 + 17/746496*s4 + 1/24786*s5
];
source, reduce, _ := minimal_presentation(L);
sourceCommon := ideal<S | [S!f : f in Basis(source)]>;
fixedCommon := ideal<S | [S!f : f in Basis(K)]>;
assert VerifyGradedIsomorphism(sourceCommon, fixedCommon, phi, psi);
derived := [Evaluate(f, inclusion) : f in phi];
assert [Evaluate(f, derived) : f in reduce] eq images;
printf "D=13 level (2): %o certified against the swap-fixed subring\n", citation;
