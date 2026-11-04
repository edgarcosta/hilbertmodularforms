// The stored level-1 Hilbert modular surface for Q(sqrt29) and Elkies-Kumar's Y_-(29)
// (Algebra & Number Theory 8 (2014), Section 14) have isomorphic degree-zero function
// fields over Q. The Siegel pullbacks give Elkies-Kumar's Igusa-Clebsch map.
nthreads := GetNthreads();
SetNthreads(1);
igusa_clebsch, check_stored_chart, check_absolute_invariants,
    check_inverse_maps, check_excluded_loci, generator_list, stored_generators,
    check_monomial_ranks, check_stored_relations, check_siegel_dictionary :=
  eval (Read("examples/_elkies_kumar.m") cat "return "
    cat "igusa_clebsch, check_stored_chart, check_absolute_invariants, "
    cat "check_inverse_maps, check_excluded_loci, generator_list, stored_generators, "
    cat "check_monomial_ranks, check_stored_relations, check_siegel_dictionary;");
W := eval Read("Verification/ElkiesKumar/2.2.29.1-1.1.m");
J := LoadStoredCanonicalRing("2.2.29.1-1.1");
a := W`K.1;
b := W`K.2;
t := W`K.3;
s4 := -a/b*t + (-76*a^6 + a^5 + 156*a^4*b - 17*a^3*b - 144*a^2*b^2 + a^2*b + 6*a*b^2
  + 8*b^3)/(a*(a + 4*b));
// The stored generators on the chart X1 = 1, and the chart coordinates a, b, t as
// functions of the stored ones.
stored := [W`K | 1, a, b, s4, b^2/a, a*(a^2 - b)^2/(a + 4*b), t];
chart := func<x | [x[2], x[3], x[7]]>;
Jo := ideal<W`P | W`Z^2 - W`branch>;
II := igusa_clebsch([Evaluate(p, stored) : p in W`pullbacks]);

check_stored_chart(J, Jo, W`Z, W`branch, stored, chart);
check_absolute_invariants(W`IEK, II, W`phiFF, Jo);

// Over Q, the double cover is Elkies-Kumar's: f is not a square, the radicands differ
// by a rational square, and phiFF and psiFF are mutually inverse.
procedure test_function_fields(Jo, K, L, f, Z, branch, phiFF, psiFF, excludedEK, IEK, II,
    stored)
  a := K.1;
  b := K.2;
  t := K.3;
  u := L.1;
  v := L.2;
  assert &or[IsOdd(e[2]) : e in Factorization(f)];
  assert branch/Evaluate(f, phiFF) eq (b*(a + 4*b)^3/(8*a))^2;
  check_inverse_maps(Jo, f, Z, branch, phiFF, psiFF, [K | a, b, t - 2*Z/(a*(a + 4*b))]);
  check_excluded_loci(Jo, [K | a, b, a + 4*b, a^2 - b, II[1], II[4]] cat phiFF cat stored,
    [L | u, v, 4*u - v - 1, IEK[1], IEK[4], excludedEK] cat psiFF);
end procedure;

test_function_fields(Jo, W`K, W`L, W`f, W`Z, W`branch, W`phiFF, W`psiFF, W`excludedEK,
  W`IEK, II, stored);

F := QuadraticField(29);
M := GradedRingOfHMFs(F, 160);
computed := ConstructGeneratorsAndRelations(M, 1*Integers(F), 8, 16);
RG := ConstructWeightedPolynomialRing(computed[1]);
G := stored_generators(J, computed[1], RG, computed[2], W`storedInComputed);

// Forms of weights 2, 2, 4, 6, 6, 6 and 8 generate the ring with the stored
// relations, which cut out an integral surface.
procedure test_modular_presentation(M, G, RG, J)
  assert VariableWeights(RG) eq [2, 2, 4, 6, 6, 6, 8];
  check_monomial_ranks(M, G, RG, [2, 4, 6, 8, 10, 12, 14, 16]);
  check_stored_relations(M, G, J);
  assert AlgebraicallyIndependent([G[2][1]^2, G[2][1]*G[2][2], G[4][1]]);
  assert IsPrime(J);
end procedure;

test_modular_presentation(M, G, RG, J);

// Swap fixes the generators of weights 2 and 4 and negates the weight-14 form that
// is Z on the chart.
procedure test_swap(G, RG, stored, Z)
  // Clearing the chart denominator gives the weight-14 antisymmetric form.
  n := 141*RG.2^5*RG.3 - RG.1*RG.2^4*RG.3 - 286*RG.2^3*RG.3^2 + 17*RG.1*RG.2^2*RG.3^2
    + 209*RG.2*RG.3^3 - RG.1^2*RG.2*RG.3^2 - 4*RG.1*RG.3^3;
  skewpoly := RG.2*(RG.1*RG.2 + 4*RG.3)*RG.7 + n/2;
  skew := Evaluate(skewpoly, generator_list(G));
  assert not IsZero(skew) and Swap(skew) eq (-1)*skew;
  for k in [2, 4] do
    for form in G[k] do
      assert Swap(form) eq form;
    end for;
  end for;
  assert Evaluate(skewpoly, stored) eq Z;
end procedure;

test_swap(G, RG, stored, W`Z);
check_siegel_dictionary(M, G, W`pullbacks);
SetNthreads(nthreads);
