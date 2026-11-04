// The stored level-1 Hilbert modular surface for Q(sqrt17) and Elkies-Kumar's Y_-(17)
// (Algebra & Number Theory 8 (2014), Section 10) have isomorphic degree-zero function
// fields over Q. The Siegel pullbacks give Elkies-Kumar's Igusa-Clebsch map.
nthreads := GetNthreads();
SetNthreads(1);
is_zero_on, igusa_clebsch, double_cover_ideal, check_stored_chart,
    check_absolute_invariants, check_inverse_maps, check_excluded_loci,
    stored_generators, check_monomial_ranks, check_stored_relations,
    check_swap_is_deck, check_siegel_dictionary :=
  eval (Read("examples/_elkies_kumar.m") cat "return "
    cat "is_zero_on, igusa_clebsch, double_cover_ideal, check_stored_chart, "
    cat "check_absolute_invariants, check_inverse_maps, check_excluded_loci, "
    cat "stored_generators, check_monomial_ranks, check_stored_relations, "
    cat "check_swap_is_deck, check_siegel_dictionary;");
W := eval Read("Verification/ElkiesKumar/2.2.17.1-1.1.m");
J := LoadStoredCanonicalRing("2.2.17.1-1.1");
a := W`K.1;
b := W`K.2;
t := W`K.3;
c := a*b*(4*b + 1)/(a - 1)^2;
// The stored generators on the chart X1 = 1, and the chart coordinates a, b, t as
// functions of the stored ones.
stored := [W`K | 1, a*c, c, t, b*c, a*b*c, (2 - a)*c^2 + b*c - t*b + 2*b^2*c];
chart := func<x | [x[2]/x[3], x[5]/x[3], x[4]]>;
Jo := double_cover_ideal(W`Z, W`branch);
II := igusa_clebsch([Evaluate(p, stored) : p in W`pullbacks]);

check_stored_chart(J, Jo, W`Z, W`branch, stored, chart);

// The published tuple pulled back by phiFF is the modular one up to the weighted
// scale, so the absolute invariants agree.
procedure test_igusa_map(Jo, phiFF, IEK, II)
  scale := (phiFF[1] + 1)^2 - 4*phiFF[2];
  for i in [1..4] do
    assert is_zero_on(Evaluate(IEK[i], phiFF) - scale^([1, 2, 3, 5][i])*II[i], Jo);
  end for;
  check_absolute_invariants(IEK, II, phiFF, Jo);
end procedure;

test_igusa_map(Jo, W`phiFF, W`IEK, II);

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
  assert branch/Evaluate(f, phiFF) eq (2*a^4*b*(4*b + 1)^2/(a - 1)^4)^2;
  check_inverse_maps(Jo, f, Z, branch, phiFF, psiFF, [K | a, b, t - 2*Z]);
  check_excluded_loci(Jo,
    [K | a, b, a - 1, 4*b + 1, II[1], II[4], Evaluate(excludedEK, phiFF)] cat phiFF
      cat stored,
    [L | u, v, u + 1, 2*u + 1, (u + 1)^2 - 4*v, IEK[1], IEK[4], excludedEK] cat psiFF);
end procedure;

test_function_fields(Jo, W`K, W`L, W`f, W`Z, W`branch, W`phiFF, W`psiFF, W`excludedEK,
  W`IEK, II, stored);

F := QuadraticField(17);
M := GradedRingOfHMFs(F, 80);
computed := ConstructGeneratorsAndRelations(M, 1*Integers(F), 8, 16);
RG := ConstructWeightedPolynomialRing(computed[1]);
G := stored_generators(J, computed[1], RG, computed[2], W`storedInComputed);

// Forms of weights 2, 4, 4, 6, 6, 6 and 8 generate the ring with the stored
// relations, which cut out an integral surface.
procedure test_modular_presentation(M, G, RG, J)
  assert VariableWeights(RG) eq [2, 4, 4, 6, 6, 6, 8];
  check_monomial_ranks(M, G, RG, [2, 4, 6, 8, 10, 12, 14, 16]);
  check_stored_relations(M, G, J);
  assert AlgebraicallyIndependent([G[2][1]^2, G[4][1], G[4][2]]);
  assert IsPrime(J);
end procedure;

test_modular_presentation(M, G, RG, J);
check_swap_is_deck(J, G, stored, chart, W`Z, Jo);
check_siegel_dictionary(M, G, W`pullbacks);
SetNthreads(nthreads);
