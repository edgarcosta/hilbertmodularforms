// The stored level-1 Hilbert modular surface for Q(sqrt41) and Elkies-Kumar's Y_-(41)
// (Algebra & Number Theory 8 (2014), Section 18) have isomorphic degree-zero function
// fields over Q. The Siegel pullbacks give Elkies-Kumar's Igusa-Clebsch map.
nthreads := GetNthreads();
SetNthreads(1);
is_zero_on, igusa_clebsch, double_cover_ideal, check_absolute_invariants,
    check_inverse_maps, check_excluded_loci, stored_generators,
    check_monomial_ranks, check_stored_relations, check_swap_is_deck,
    check_siegel_dictionary :=
  eval (Read("examples/_elkies_kumar.m") cat "return "
    cat "is_zero_on, igusa_clebsch, double_cover_ideal, check_absolute_invariants, "
    cat "check_inverse_maps, check_excluded_loci, stored_generators, "
    cat "check_monomial_ranks, check_stored_relations, check_swap_is_deck, "
    cat "check_siegel_dictionary;");
W := eval Read("Verification/ElkiesKumar/2.2.41.1-1.1.m");
J := LoadStoredCanonicalRing("2.2.41.1-1.1");
a := W`K.1;
b := W`K.2;
t := W`K.3;
DD := (a - 2)^2*b^2 + (-5 + 7*a - 4*a^2)*b + 1;
// The chart coordinates a, b, t as functions of the stored coordinates with X1 = 1.
chart := func<x | [x[7]/x[2]^2, x[6]/x[2]^2, x[4] - x[5] + x[7]]>;
Jo := double_cover_ideal(W`Z, W`branch);

// The double cover over the function field F0 of the (a, b)-plane: the quotient EE of
// F0[t] by the quadratic quad0, and the stored generators on it.
function double_cover_over_plane(Z, branch, stored)
  F0<aa, bb> := RationalFunctionField(Rationals(), 2);
  TT<tt> := PolynomialRing(F0);
  FF0 := FieldOfFractions(TT);
  quad0 := TT!(Evaluate(Z, [FF0 | aa, bb, tt])^2
    - F0!Evaluate(branch, [FF0 | aa, bb, tt]));
  EE<root> := quo<TT | quad0>;
  return [Evaluate(p, [EE | aa, bb, root]) : p in stored], quad0;
end function;

storedEE, quad0 := double_cover_over_plane(W`Z, W`branch, W`stored);
TT := Parent(quad0);
reducedPullbacks := [TT!Evaluate(p, storedEE) : p in W`pullbacks];
// Siegel pullbacks descend to the (a, b)-plane.
procedure test_siegel_pullback_descent(pullbacks)
  assert &and[Degree(p) le 0 : p in pullbacks];
end procedure;

test_siegel_pullback_descent(reducedPullbacks);
II := igusa_clebsch([W`K!Evaluate(BaseRing(TT)!p, [W`K | a, b]) : p in reducedPullbacks]);

// The stored generators on the chart satisfy J and recover a, b, t. Through the cached
// generators, six retained coordinates and their quadratic relation recover every
// stored generator, so the chart maps are mutually inverse.
procedure test_stored_chart(J, storedEE, quad0, chart, cachedInStored, reconstruction,
    retainedQuadratic)
  R := Generic(J);
  TT := Parent(quad0);
  F0 := BaseRing(TT);
  FF0 := FieldOfFractions(TT);
  EE := Universe(storedEE);
  aa := F0.1;
  bb := F0.2;
  tt := TT.1;
  for p in Basis(J) do
    assert Evaluate(p, storedEE) eq 0;
  end for;
  FR := FieldOfFractions(R);
  raw := [FR | p : p in cachedInStored];
  cu := raw[2]/R.1;
  cv := raw[7]/R.1^2;
  ct := raw[4]/R.1^2;
  ca := raw[5]/R.1^2;
  cb := raw[6]/R.1^2;
  retained := [FR | cu, 0, ct, ca, cb, cv, 0, 0, 0, 0, 0, 0];
  for i in [2..13] do
    assert is_zero_on(Evaluate(reconstruction[i - 1], retained)
      - raw[i]/R.1^(WeightedDegree(R.i) div 2), J);
  end for;
  assert Numerator(cu^2*ca + (cu^2 - cv)*cb + cu^2*cv) in J;
  nDD := R.7^2*R.6^2 - 4*R.7*R.6^2*R.2^2 + 4*R.6^2*R.2^4 - 5*R.6*R.2^6
    + 7*R.7*R.6*R.2^4 - 4*R.7^2*R.6*R.2^2 + R.2^8;
  assert nDD - R.1*R.2^3*(R.2^2 - R.7)*R.6 in J;
  assert is_zero_on(Evaluate(retainedQuadratic, [FR | cu, cv, ct, ca, cb]), J);
  d0 := (aa - 2)^2*bb^2 + (-5 + 7*aa - 4*aa^2)*bb + 1;
  u0 := (1 - aa)*bb/d0;
  v0 := u0^2*aa;
  b0 := u0^2*bb;
  a0 := u0^2*((aa - 1)*bb - aa);
  assert Evaluate(retainedQuadratic, [FF0 | u0, v0, tt, a0, b0]) eq quad0;
  assert chart(storedEE) eq [EE | aa, bb, EE.1];
end procedure;

test_stored_chart(J, storedEE, quad0, chart, W`cachedInStored, W`reconstruction,
  W`retainedQuadratic);

// The published tuple pulled back by phiFF is the modular one up to the weighted
// scale, so the absolute invariants agree.
procedure test_igusa_map(Jo, phiFF, IEK, II)
  scale := phiFF[1]^2*(4*phiFF[2] + 1)^2 - 16*phiFF[1]*phiFF[2] + 8*phiFF[1]
    + 256*phiFF[2] + 16;
  for i in [1..4] do
    assert is_zero_on(Evaluate(IEK[i], phiFF) - scale^([1, 2, 3, 5][i])*II[i], Jo);
  end for;
  check_absolute_invariants(IEK, II, phiFF, Jo);
end procedure;

test_igusa_map(Jo, W`phiFF, W`IEK, II);

// Over Q, the double cover is Elkies-Kumar's: f is not a square, the radicands differ
// by a rational square, and phiFF and psiFF are mutually inverse.
procedure test_function_fields(Jo, K, L, f, Z, branch, phiFF, psiFF, excludedEK, IEK, II,
    stored, DD)
  a := K.1;
  b := K.2;
  t := K.3;
  u := L.1;
  v := L.2;
  assert &or[IsOdd(e[2]) : e in Factorization(f)];
  assert branch/Evaluate(f, phiFF) eq ((a - 1)^3*b^3/(32*DD^2))^2;
  check_inverse_maps(Jo, f, Z, branch, phiFF, psiFF, [K | a, b, t - 2*Z]);
  check_excluded_loci(Jo,
    [K | a, b, a - 1, a - 2, b - 1, DD, II[1], II[4], Evaluate(excludedEK, phiFF)] cat phiFF
      cat stored,
    [L | u, v, u - 4, u + 4, u^2*(4*v + 1)^2 - 16*u*v + 8*u + 256*v + 16, IEK[1], IEK[4],
      excludedEK] cat psiFF);
end procedure;

test_function_fields(Jo, W`K, W`L, W`f, W`Z, W`branch, W`phiFF, W`psiFF, W`excludedEK,
  W`IEK, II, W`stored, DD);

F := QuadraticField(41);
M := GradedRingOfHMFs(F, 160);
computed := ConstructGeneratorsAndRelations(M, 1*Integers(F), 8, 16);
RG := ConstructWeightedPolynomialRing(computed[1]);
G := stored_generators(J, computed[1], RG, computed[2], W`storedInComputed);

// Forms of weights 2, 2, 4 (five), 6 (five) and 8 generate the ring with the stored
// relations.
procedure test_modular_presentation(M, G, RG, J)
  assert VariableWeights(RG) eq [2, 2, 4, 4, 4, 4, 4, 6, 6, 6, 6, 6, 8];
  check_monomial_ranks(M, G, RG, [2, 4, 6, 8, 10, 12, 14, 16]);
  check_stored_relations(M, G, J);
  assert AlgebraicallyIndependent([G[2][1]^2, G[2][1]*G[2][2], G[4][5]]);
end procedure;

test_modular_presentation(M, G, RG, J);

// Saturation transfers the domain property of the irreducible quadratic chart.
// The two chart compositions identify these localizations in every generator.
procedure test_domain(J, P, stored, DD)
  R := Generic(J);
  for p in [R | R.1, R.2, R.6, R.7, R.7 - R.2^2, 2*R.2^2 - R.7, R.6 - R.2^2] do
    assert Saturation(J, ideal<R | p>) eq J;
  end for;
  a := P.1;
  b := P.2;
  open := P!(a*b*(a - 1)*(a - 2)*(b - 1)*DD);
  for p in stored do
    den := Denominator(p);
    repeat
      common := GCD(den, open);
      den := ExactQuotient(den, common);
    until Degree(common) eq 0;
    assert Degree(den) eq 0;
  end for;
end procedure;

test_domain(J, W`P, W`stored, DD);
check_swap_is_deck(J, G, W`stored, chart, W`Z, Jo);
check_siegel_dictionary(M, G, W`pullbacks);
SetNthreads(nthreads);
