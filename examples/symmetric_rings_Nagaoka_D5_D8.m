// Nagaoka, J. Math. Soc. Japan 35 (1983), Theorems 1, 2 and 5.1.
// Finite coefficient checks supplement his integral generation theorem.
// Keep eval at top level: nested procedure eval crashes the runner.
import "Verification/SymmetricSubring.m" : is_geometric_swap;

SetSeed(1);
nagaoka_forms := function(M)
  F := BaseField(M); N := 1*Integers(F); D := Discriminant(Integers(F));
  assert D in [5, 8];
  weights := D eq 5 select [2, 6, 10] else [2, 4, 6];
  triv := HeckeCharacterGroup(N)!1;
  G := AssociativeArray();
  for w in weights do
    E := EisensteinSeries(HMFSpace(M, N, [w, w]), triv, triv);
    c := Coefficient(E, N, F!0);
    assert c ne 0;
    G[w] := E/c;
    assert Coefficient(G[w], N, F!0) eq 1;
  end for;
  if D eq 5 then
    // Nagaoka prints 2^-5 for J6; the PDF text layer reads 2^-6.
    J6 := 67/(2^5*3^3*5^2)*(G[2]^3 - G[6]);
    J10 := (412751*G[10] - 5*67*2293*G[2]^2*G[6] + 2^2*3*7*4231*G[2]^5)/(2^10*3^5*5^5*7);
    J12 := (J6^2 - G[2]*J10)/4;
    return [* G[2], J6, J10, J12 *];
  end if;
  H4 := 11/(2^6*3^2)*(G[2]^2 - G[4]);
  H6 := -5*7^2/(2^8*3^3*13)*G[2]^3
    +11*59/(2^8*3^2*5*13)*G[2]*G[4] - 19^2/(2^7*3^3*5*13)*G[6];
  return [* G[2], H4, H6 *];
end function;

H<t> := FunctionField(Rationals());
precision := 80;
for D in [5, 8] do
  file := Sprintf("Verification/LiteratureEquations/2.2.%o.1-1.1-NagaokaSymmetric.m", D);
  symmetric_lit_data := eval(Read(file) cat "return symmetric_lit_data;");
  F := QuadraticField(D);
  N := 1*Integers(F);
  M := GradedRingOfHMFs(F, precision);
  assert NarrowClassNumber(M) eq 1;
  weights := D eq 5 select [2, 6, 10, 20] else [2, 4, 6, 14];
  relationWeight := 2*weights[4];
  J := LoadStoredCanonicalRing(Sprintf("2.2.%o.1-1.1", D));
  R := Generic(J);
  data := ConstructGeneratorsAndRelations(M, N, weights[4], weights[4] :
      NumberOfTraceForms := 6);
  G := data[1];
  assert Sort(Setseq(Keys(G))) eq weights;
  assert &and[#G[w] eq 1 : w in weights];
  T := ConstructWeightedPolynomialRing(G);
  flat := Sum([* SequenceToList(G[w]) : w in weights *] : empty := [* *]);
  I := Syzygies(flat, [relationWeight]);
  I := ideal<T | [T!f : f in Basis(I)]>;
  mons := Setseq(MonomialsOfWeightedDegree(T, relationWeight));
  coeffs := CoefficientsMatrix(EvaluateMonomials(G, mons) : prec := precision);
  known := Dimension(HMFSpace(M, N, [relationWeight, relationWeight]));
  assert Rank(coeffs) eq known;
  assert &and[Vector(Rationals(), [MonomialCoefficient(f, m) : m in mons])*coeffs eq 0 :
      f in Basis(I)];
  assert not IsEmpty(Basis(I));
  rels := AssociativeArray();
  rels[relationWeight] := [[MonomialCoefficient(f, m) : m in mons] : f in Basis(I)];
  assert CertifyAlgIndependent(G, rels, 3);
  assert HilbertSeries(I) eq HilbertSeries(M, N) and HilbertSeries(I) eq HilbertSeries(J);
  phi := [R.i : i in [1..4]];
  psi := [T.i : i in [1..4]];
  assert VerifyGradedIsomorphism(I, J, phi, psi);
  bb := NarrowClassGroupReps(M)[1];
  indices := FunDomainRepsUpToPrec(M, bb, precision);
  published := nagaoka_forms(M);
  L, images, _ := symmetric_lit_data(R);
  assert not IsEmpty(published) and #published eq #images;
  for j in [1..#published] do
    f := published[j];
    w := Weight(f)[1];
    known := Dimension(HMFSpace(M, N, [w, w]));
    mons := Setseq(MonomialsOfWeightedDegree(T, w));
    forms := EvaluateMonomials(G, mons);
    coeffs := CoefficientsMatrix(forms cat [f] : prec := precision);
    A := RowSubmatrix(coeffs, 1, #forms);
    assert Ncols(coeffs) eq #indices;
    assert Rank(A) eq known and Rank(coeffs) eq known;
    ok, sol := IsConsistent(A, coeffs[Nrows(coeffs)]);
    assert ok;
    p := &+[T | sol[i]*mons[i] : i in [1..#mons]];
    assert Evaluate(p, phi) - images[j] in J;
    assert &and[Denominator(a) eq 1 : a in Eltseq(coeffs[Nrows(coeffs)])];
  end for;
  swapped := AssociativeArray();
  for w in weights do
    swapped[w] := [Swap(g) : g in G[w]];
  end for;
  tau, _ := ChangeOfPresentation(G, swapped : Prec := precision, Verify := true);
  tau := [T!p : p in tau];
  assert is_geometric_swap(M, N, G, I, tau, weights cat [relationWeight], precision);
  assert VerifyGradedIsomorphism(I, I, tau, tau);
  storedTau := [Evaluate(Evaluate(p, tau), phi) : p in psi];
  assert VerifyGradedIsomorphism(J, J, storedTau, storedTau);
  assert IsSymmetricSubringPresentation(J, storedTau, L, images);
  _, _, series := SymmetricSubringPresentation(J, storedTau);
  expected := D eq 5 select 1/((1 - t^2)*(1 - t^6)*(1 - t^10))
      else 1/((1 - t^2)*(1 - t^4)*(1 - t^6));
  assert H!HilbertSeries(L) eq H!series and H!series eq expected;
  if D eq 5 then
    assert 4*images[4] - images[2]^2 + images[1]*images[3] in J;
    numerator := published[2]^2 - published[1]*published[3];
    row := CoefficientsMatrix([numerator] : prec := precision);
    assert &and[Denominator(a/4) eq 1 : a in Eltseq(row)];
    bad := [images[1], images[2]/2, images[3], (images[2]^2/4 - images[1]*images[3])/4];
    assert IsSymmetricSubringPresentation(J, storedTau, L, bad);
  end if;
  diag := [RestrictionToDiagonal(f, M, N : AsCoefficients := true) : f in published];
  qprec := Minimum([#r : r in diag]);
  Q<q> := PowerSeriesRing(Rationals());
  delta := q*(&*[Q!(1 - q^n)^24 : n in [1..qprec]]) + O(q^qprec);
  e4 := 1 + 240*&+[Q | (&+[d^3 : d in Divisors(n)])*q^n : n in [1..qprec - 1]]
      + O(q^qprec);
  expectedDiag := D eq 5 select [e4, 2*delta, Q!0, delta^2] else [e4, Q!0, delta];
  for i in [1..#diag] do
    // The trace enumerator omits zero, so obtain the constant directly.
    diag[i][1] := Coefficient(published[i], N, F!0);
    assert diag[i][1..qprec] eq [Coefficient(expectedDiag[i], n) : n in [0..qprec - 1]];
  end for;
  if D eq 5 then
    badDiag := RestrictionToDiagonal(published[2]/2, M, N : AsCoefficients := true);
    assert badDiag[1..qprec] ne [2*Coefficient(delta, n) : n in [0..qprec - 1]];
    assert Coefficient(published[2]/2, N, (F!1 - 1/F.1)/2) eq 1/2;
  end if;
end for;
printf "Nagaoka D=5 and D=8: normalized generators identified at precision %o\n", precision;
