// The stored level-1 Hilbert modular surface for Q(sqrt37) and Elkies-Kumar's Y_-(37)
// (Algebra & Number Theory 8 (2014), Section 16) have isomorphic degree-zero function
// fields over Q. The Siegel pullbacks give Elkies-Kumar's Igusa-Clebsch map.
nthreads := GetNthreads();
SetNthreads(1);
igusa_clebsch, double_cover_ideal, check_stored_chart,
    check_absolute_invariants, check_inverse_maps, check_excluded_loci,
    stored_generators, check_monomial_ranks, check_stored_relations,
    check_swap_is_deck, check_siegel_dictionary :=
  eval (Read("examples/_elkies_kumar.m") cat "return "
    cat "igusa_clebsch, double_cover_ideal, check_stored_chart, "
    cat "check_absolute_invariants, check_inverse_maps, check_excluded_loci, "
    cat "stored_generators, check_monomial_ranks, check_stored_relations, "
    cat "check_swap_is_deck, check_siegel_dictionary;");
W := eval Read("Verification/ElkiesKumar/2.2.37.1-1.1.m");
J := LoadStoredCanonicalRing("2.2.37.1-1.1");
literature_data := eval Read("Verification/LiteratureEquations/2.2.37.1-1.1-Williams.m");
a := W`K.1;
b := W`K.2;
t := W`K.3;
rawImages := GradedInverseImages(Universe(W`storedInComputed), W`storedInComputed);
// The stored generators on the chart X1 = 1, and the chart coordinates a, b, t as
// functions of the stored ones.
stored := [W`K |
  1,
  a,
  (a^4 + 6/5*a^2*b + a*b - 3*b^2)/(a^2 - b),
  b,
  (-21/20*a^4 - 1/4*a^3 + 23/10*a^2*b + 1/4*a*b - 5/4*b^2)/(a^5 - 14/5*a^3*b -
    1/4*a^2*b + 2*a*b^2)*t +
    (2791/64*a^14 + 255/64*a^13 - 20019/160*a^12*b + 2659/64*a^11*b -
    101739/1600*a^10*b^2 + 45/8*a^10*b - 30291/160*a^9*b^2 + 242753/400*a^8*b^3 -
    161/32*a^8*b^2 + 41003/160*a^7*b^3 + 105/64*a^7*b^2 - 260619/320*a^6*b^4 -
    649/64*a^6*b^3 - 7533/64*a^5*b^4 - 45/32*a^5*b^3 + 64037/160*a^4*b^5 +
    85/8*a^4*b^4 - 497/64*a^3*b^5 - 1333/64*a^2*b^6 - 105/64*a^2*b^5 + 215/16*a*b^6 -
    215/8*b^7)/(a^11 + 5/16*a^10 - 121/20*a^9*b - 7/4*a^8*b + 73/5*a^7*b^2 -
    5/64*a^7*b + 7/2*a^6*b^2 - 351/20*a^5*b^3 + 5/32*a^5*b^2 - 3*a^4*b^3 +
    21/2*a^3*b^4 - 5/64*a^3*b^3 + 15/16*a^2*b^4 - 5/2*a*b^5),
  (1/4*a^4 - 1/2*a^2*b + 1/4*b^2)/(a^5 - 14/5*a^3*b - 1/4*a^2*b + 2*a*b^2)*t +
    (-351/64*a^10 + 5/16*a^9 - 203/80*a^8*b - 121/16*a^7*b + 23107/800*a^6*b^2 +
    15/64*a^6*b + 119/40*a^5*b^2 - 1093/80*a^4*b^3 - 69/32*a^4*b^2 + 179/16*a^3*b^3 -
    5/64*a^3*b^2 - 1103/64*a^2*b^4 + 65/64*a^2*b^3 - 85/16*a*b^4 + 75/8*b^5)/(a^7 +
    5/16*a^6 - 81/20*a^5*b - 9/8*a^4*b + 11/2*a^3*b^2 - 5/64*a^3*b + 15/16*a^2*b^2 -
    5/2*a*b^3),
  (-15/16*a^6 - 9/8*a^4*b - 15/16*a^3*b + 29/16*a^2*b^2 - 5/16*a*b^2 + 5/4*b^3)/(a^3 +
    5/16*a^2 - 5/4*a*b),
  (-15/16*a^9 + 7/4*a^7*b - 5/8*a^6*b + 163/40*a^5*b^2 + 13/4*a^4*b^2 - 45/4*a^3*b^3 +
    5/16*a^3*b^2 - 25/8*a^2*b^3 + 105/16*a*b^4)/(a^6 + 5/16*a^5 - 13/4*a^4*b -
    5/8*a^3*b + 7/2*a^2*b^2 + 5/16*a*b^2 - 5/4*b^3),
  (-5/16*a^5 - 3/8*a^3*b - 5/16*a^2*b + 15/16*a*b^2)/(a^2 + 5/16*a - 5/4*b),
  (1/4*a^4*b - 1/2*a^2*b^2 + 1/4*b^3)/(a^6 - 14/5*a^4*b - 1/4*a^3*b + 2*a^2*b^2)*t +
    (-5/16*a^12 + 357/64*a^10*b - 15/64*a^9*b - 2473/40*a^8*b^2 - 783/64*a^7*b^2 +
    25393/160*a^6*b^3 + 5/64*a^6*b^2 + 1407/64*a^5*b^3 - 11729/80*a^4*b^4 -
    5/16*a^4*b^3 - 517/64*a^3*b^4 + 2553/64*a^2*b^5 - 5/64*a^2*b^4 - 15/16*a*b^5 +
    35/8*b^6)/(a^8 + 5/16*a^7 - 81/20*a^6*b - 9/8*a^5*b + 11/2*a^4*b^2 - 5/64*a^4*b +
    15/16*a^3*b^2 - 5/2*a^2*b^3),
  (1/4*a^4 + 3/10*a^2*b + 1/4*a*b - 3/4*b^2)/(a^4 - 14/5*a^2*b - 1/4*a*b + 2*b^2)*t +
    (-11/64*a^14 + 5/16*a^13 - 1849/160*a^12*b - 27/8*a^11*b - 12613/1600*a^10*b^2 +
    35/64*a^10*b - 9799/320*a^9*b^2 + 178881/2000*a^8*b^3 - 217/32*a^8*b^2 +
    10799/400*a^7*b^3 + 5/32*a^7*b^2 - 23517/1600*a^6*b^4 - 5681/320*a^6*b^3 +
    18817/160*a^5*b^4 - 229/64*a^5*b^3 - 32513/160*a^4*b^5 + 159/4*a^4*b^4 -
    5/64*a^4*b^3 - 2403/16*a^3*b^5 + 45/32*a^3*b^4 + 12189/64*a^2*b^6 - 85/8*a^2*b^5 +
    2245/64*a*b^6 - 165/4*b^7)/(a^10 + 5/16*a^9 - 121/20*a^8*b - 7/4*a^7*b +
    73/5*a^6*b^2 - 5/64*a^6*b + 7/2*a^5*b^2 - 351/20*a^4*b^3 + 5/32*a^4*b^2 -
    3*a^3*b^3 + 21/2*a^2*b^4 - 5/64*a^2*b^3 + 15/16*a*b^4 - 5/2*b^5)
];

chart := func<x | [x[2], x[4], Evaluate(rawImages[11], x)]>;
Jo := double_cover_ideal(W`Z, W`branch);
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
  C2 := a^2 + 5/16*a - 5/4*b;
  C4 := a^4 - 14/5*a^2*b - 1/4*a*b + 2*b^2;
  assert &or[IsOdd(e[2]) : e in Factorization(f)];
  assert branch/Evaluate(f, phiFF) eq (25/128*(a^2 - b)^5*C4/C2)^2;
  D0 := Evaluate(Derivative(Z, 3), [K | a, b, t]);
  check_inverse_maps(Jo, f, Z, branch, phiFF, psiFF, [K | a, b, t - 2*Z/D0]);
  check_excluded_loci(Jo, [K | a, b, a^2 - b, C2, C4, II[1], II[4]] cat phiFF cat stored,
    [L | u, v, 4*u + 5*v^2 + 16*v - 4, IEK[1], IEK[4], excludedEK] cat psiFF);
end procedure;

test_function_fields(Jo, W`K, W`L, W`f, W`Z, W`branch, W`phiFF, W`psiFF, W`excludedEK,
  W`IEK, II, stored);

F := QuadraticField(37);
M := GradedRingOfHMFs(F, 160);
computed := ConstructGeneratorsAndRelations(M, 1*Integers(F), 8, 16);
RG := ConstructWeightedPolynomialRing(computed[1]);
G := stored_generators(J, computed[1], RG, computed[2], W`storedInComputed);

// Forms of weights 2, 2, 4, 4, 6, 6, 6, 6, 6, 8 and 8 generate the ring with the
// stored relations.
procedure test_modular_presentation(M, G, RG, J)
  assert VariableWeights(RG) eq [2, 2, 4, 4, 6, 6, 6, 6, 6, 8, 8];
  check_monomial_ranks(M, G, RG, [2, 4, 6, 8, 10, 12, 14, 16]);
  check_stored_relations(M, G, J);
  assert AlgebraicallyIndependent([G[2][1]^2, G[2][1]*G[2][2], G[4][2]]);
end procedure;

test_modular_presentation(M, G, RG, J);
check_swap_is_deck(J, G, stored, chart, W`Z, Jo);
check_siegel_dictionary(M, G, W`pullbacks);

// Williams' complete presentation is a ring of modular forms.
// Its even subring and this verified isomorphic presentation are domains.
procedure test_williams_domain(literature_data, J)
  R := Generic(J);
  S := PolynomialRing(Rationals(), VariableWeights(R));
  I, litPhi, litPsi := literature_data(S, R);
  assert HilbertSeries(I) eq HilbertSeries(J);
  assert VerifyGradedIsomorphism(ideal<S | MinimalBasis(I)>, ideal<R | MinimalBasis(J)>,
    litPhi, litPsi);
end procedure;

test_williams_domain(literature_data, J);
SetNthreads(nthreads);
