// van der Geer and Zagier, Invent. Math. 42 (1977), Theorems 6 and 9.
// Theorem 6 supplies eta0 = sigma2/xi0, adjoined to the Theorem 9 generators.
source_data := function()
  Q := Rationals();
  P := PolynomialRing(Q, [2, 4, 6, 8]);
  t := P.1; b := P.2; c := P.3; d := P.4;
  F := t^5 + b*t^3 - c*t^2 + d*t - b*c/2;
  L := FieldOfFractions(P);
  images := [L | d/c, b, c, b^3/c, t, t^2*b^2/c, t^4*b/c, t^6/c, b/t];
  weights := [2, 4, 6, 6, 2, 6, 6, 6, 2];
  return P, F, images, weights;
end function;

published_presentation := function()
  T := PolynomialRing(Rationals(), 14, "lex");
  s := T.1; t := T.2; b := T.3; c := T.4; d := T.5;
  a := T.6; bb := T.7; cc := T.8; dd := T.9;
  u := T.10; v := T.11; w := T.12; z := T.13; e := T.14;
  graph := ideal<T | s*t*c - 1, t^5 + b*t^3 - c*t^2 + d*t - b*c/2,
    a*c - d, bb - b, cc - c, dd*c - b^3, u - t,
    v*c - t^2*b^2, w*c - t^4*b, z*c - t^6, e*t - b>;
  E := EliminationIdeal(graph, 5);
  R := PolynomialRing(Rationals(), [2, 4, 6, 6, 2, 6, 6, 6, 2]);
  project := hom<T->R | [R | 0, 0, 0, 0, 0] cat [R.i : i in [1..9]]>;
  I := ideal<R | [project(g) : g in Basis(E)]>;
  P, F, images, _ := source_data();
  for g in Basis(I) do
    value := Evaluate(g, images);
    assert Numerator(value) in ideal<P | F>;
  end for;
  return I;
end function;

missing_form_certificate := function()
  // Theorem 6 gives eta0 = N/sigma3 for this quartic N with double zeros
  // at the ten P_ij. The two permutations generate its S4 stabilizer.
  P := PolynomialRing(Rationals(), 4);
  xs := [P.i : i in [1..4]] cat [-&+[P.i : i in [1..4]]];
  sigma := [&+[&*[xs[i] : i in S] : S in Subsets({1..5}, j)] : j in [1..5]];
  assert sigma[1] eq 0;
  t := xs[1]; b := sigma[2]; c := sigma[3]; d := sigma[4];
  surface := 2*sigma[5] - b*c;
  numerator := 2*(t^4 + b*t^2 - c*t + d);
  assert numerator*t - b*c eq surface;
  assert TotalDegree(numerator) eq 4;
  for pair in Subsets({1..5}, 2) do
    ij := Sort(Setseq(pair));
    point := [Rationals() | (i eq ij[1]) select 1 else
      ((i eq ij[2]) select - 1 else 0) : i in [1..5]];
    assert Evaluate(surface, point[1..4]) eq 0;
    assert Evaluate(numerator, point[1..4]) eq 0;
    assert &and[Evaluate(Derivative(numerator, j), point[1..4]) eq 0
: j in [1..4]];
  end for;
  for perm in [[1, 3, 2, 4, 5], [1, 3, 4, 5, 2]] do
    substitution := [xs[perm[i]] : i in [1..4]];
    assert Evaluate(numerator, substitution) eq numerator;
    assert Evaluate(c, substitution) eq c;
  end for;
  polys := [t*c, d, numerator];
  mons := Setseq(&join[Seqset(Monomials(g)) : g in polys]);
  assert Rank(Matrix(Rationals(),
    [[MonomialCoefficient(g, m) : m in mons] : g in polys])) eq 3;
  return true;
end function;


symmetric_lit_data := function(R)
  assert VariableWeights(R) eq [2, 2, 2, 6, 6, 6, 6];
  assert missing_form_certificate();
  images := [R |
    R.1 + R.2 + R.3,
    24/5*R.1*R.3 - 384/5*R.2*R.3 - 2196/5*R.3^2,
    -108/2125*R.1^3 + 1944/2125*R.1^2*R.2 - 3564/2125*R.1*R.2^2 + 1728/2125*R.2^3
        - 8424/2125*R.1^2*R.3 - 109512/2125*R.1*R.2*R.3 + 117936/2125*R.2^2*R.3
        + 493776/2125*R.1*R.3^2 + 3063744/2125*R.2*R.3^2 - 5505408/2125*R.3^3 - 746496/17*R.6,
    -29801/216000*R.1^3 + 203881/72000*R.1^2*R.2 - 561187/24000*R.1*R.2^2
        + 4468841/216000*R.2^3 + 367081/18000*R.1^2*R.3 - 2961961/9000*R.1*R.2*R.3
        + 3598441/18000*R.2^2*R.3 - 1324181/750*R.1*R.3^2 - 38539/750*R.2*R.3^2
        - 64192/125*R.3^3 + 49572*R.7,
    -18*R.3,
    459/8000*R.1^3 - 1377/8000*R.1^2*R.2 + 1377/8000*R.1*R.2^2 - 459/8000*R.2^3
        - 12257/2000*R.1^2*R.3 + 93857/1000*R.1*R.2*R.3 - 175457/2000*R.2^2*R.3
        + 294831/250*R.1*R.3^2 - 172431/250*R.2*R.3^2 - 441864/125*R.3^3 - 49572*R.7,
    -459/8000*R.1^3 + 1377/8000*R.1^2*R.2 - 1377/8000*R.1*R.2^2 + 459/8000*R.2^3
        + 1377/2000*R.1^2*R.3 - 1377/1000*R.1*R.2*R.3 + 1377/2000*R.2^2*R.3
        - 178551/250*R.1*R.3^2 + 178551/250*R.2*R.3^2 + 815184/125*R.3^3 + 49572*R.7,
    459/8000*R.1^3 - 1377/8000*R.1^2*R.2 + 1377/8000*R.1*R.2^2 - 459/8000*R.2^3
        - 1377/2000*R.1^2*R.3 + 1377/1000*R.1*R.2*R.3 - 1377/2000*R.2^2*R.3
        + 86751/250*R.1*R.3^2 - 86751/250*R.2*R.3^2 - 1090584/125*R.3^3 - 49572*R.7,
    -4/15*R.1 + 64/15*R.2 + 122/5*R.3
  ];
  citation := "van der Geer-Zagier Theorem 9 with eta0 adjoined by Theorem 6";
  return published_presentation(), images, citation;
end function;
