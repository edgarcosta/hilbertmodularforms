// The stored level-1 Hilbert modular surface for Q(sqrt13) and Elkies-Kumar's Y_-(13)
// (Algebra & Number Theory 8 (2014), Section 9) have isomorphic degree-zero function
// fields over Q. The Siegel pullbacks give Elkies-Kumar's Igusa-Clebsch map.
nthreads := GetNthreads();
SetNthreads(1);
is_zero_on, igusa_clebsch, check_absolute_invariants, check_inverse_maps,
    check_excluded_loci, stored_generators, check_monomial_ranks,
    check_stored_relations, check_siegel_dictionary :=
  eval (Read("examples/_elkies_kumar.m") cat "return "
    cat "is_zero_on, igusa_clebsch, check_absolute_invariants, check_inverse_maps, "
    cat "check_excluded_loci, stored_generators, check_monomial_ranks, "
    cat "check_stored_relations, check_siegel_dictionary;");
W := eval Read("Verification/ElkiesKumar/2.2.13.1-1.1.m");
J := LoadStoredCanonicalRing("2.2.13.1-1.1");
R := Generic(J);
LitData := eval Read("Verification/LiteratureEquations/2.2.13.1-1.1-vdGZagier.m");
I, Phi, Psi := LitData(R, R);
a := W`K.1;
b := W`K.2;
t := W`K.3;
// The stored generators on the chart, through van der Geer-Zagier's coordinates.
stored := [Evaluate(p, [W`K | 1, b, a*b, b^2/a, t]) : p in Psi];
II := igusa_clebsch([Evaluate(p, stored) : p in W`pullbacks]);

// Through van der Geer-Zagier's presentation, stored and back are mutually inverse
// between the double cover Z^2 = branch and the stored surface on the X2 chart.
procedure test_stored_chart(I, J, Phi, Psi, P, K, Z, branch, stored)
  assert VerifyGradedIsomorphism(I, J, Phi, Psi);
  Jo := ideal<P | Z^2 - branch>;
  weights := VariableWeights(Generic(J));
  normalized := [stored[i]/4^(weights[i] div 2) : i in [1..#stored]];
  for p in Basis(J) do
    assert is_zero_on(Evaluate(p, stored), Jo);
  end for;
  assert [Evaluate(Phi[3]/(Phi[1]*Phi[2]), stored), Evaluate(Phi[2]/Phi[1]^2, stored),
    Evaluate(Phi[5]/Phi[1]^4, stored)] eq [K.1, K.2, K.3];
  V<x, y, v, w> := PolynomialRing(Rationals(), 4);
  FV := FieldOfFractions(V);
  JV := ideal<V | [Evaluate(p, [V | 1, x, y, v, w]) : p in Basis(J)]>;
  back := [FV | -8*v/x, -32*x, 256*(8*w - 4*y + 57*x^2 - 57*v)];
  assert is_zero_on(Evaluate(Z^2 - branch, back), JV);
  for i in [2..5] do
    assert is_zero_on(Evaluate(normalized[i], back) - FV.(i - 1), JV);
  end for;
end procedure;

test_stored_chart(I, J, Phi, Psi, W`P, W`K, W`Z, W`branch, stored);

// The modular Igusa-Clebsch invariants have the absolute invariants of the published
// tuple, and these determine the point (g, h), so the Humbert fields agree.
procedure test_igusa_map(P, Z, branch, phiFF, IEK, II)
  check_absolute_invariants(IEK, II, phiFF, ideal<P | Z^2 - branch>);
  // Resultants isolate h and the nonzero scale in the generic invariant fiber.
  B0<g0, h0> := PolynomialRing(Rationals(), 2);
  F0 := FieldOfFractions(B0);
  IE0 := [Evaluate(p, [F0 | g0, h0, 0]) : p in IEK];
  S<hh> := PolynomialRing(F0);
  T<ll> := PolynomialRing(S);
  gg := (ll*IE0[1] - 24*hh^2 + 48*hh - 8)/32;
  IEn := [T!Evaluate(p, [FieldOfFractions(T) | gg, hh, 0]) : p in IEK];
  pp := [IEn[i] - ll^([1, 2, 3, 5][i])*IE0[i] : i in [2..4]];
  rr := [Resultant(pp[1], pp[2]), Resultant(pp[1], pp[3]), Resultant(pp[2], pp[3])];
  gcd := GCD(rr);
  gcd /:= LeadingCoefficient(gcd);
  assert gcd eq hh - h0;
  U<lu> := PolynomialRing(F0);
  pl := [U![Evaluate(c, h0) : c in Coefficients(p)] : p in pp];
  ld := GCD(pl);
  ld /:= LeadingCoefficient(ld);
  assert ld eq lu - 1;
  assert (IE0[1] - 24*h0^2 + 48*h0 - 8)/32 eq g0;
end procedure;

test_igusa_map(W`P, W`Z, W`branch, W`phiFF, W`IEK, II);

// Over Q, the double cover is Elkies-Kumar's: f is not a square, the radicands differ
// by a rational square, and phiFF and psiFF are mutually inverse.
procedure test_function_fields(P, K, L, f, Z, branch, phiFF, psiFF, excludedEK, IEK, II,
    stored)
  a := K.1;
  b := K.2;
  t := K.3;
  g := L.1;
  h := L.2;
  Jo := ideal<P | Z^2 - branch>;
  assert &or[IsOdd(e[2]) : e in Factorization(f)];
  assert branch/Evaluate(f, phiFF) eq (b^2*(4*a - b)/(8*a))^2;
  check_inverse_maps(Jo, f, Z, branch, phiFF, psiFF, [K | a, b, -t]);
  check_excluded_loci(Jo, [K | a, b, 4*a - b, II[1], II[4]] cat phiFF cat stored,
    [L | g, h, 2*g - 1, IEK[1], IEK[4], excludedEK] cat psiFF);
end procedure;

test_function_fields(W`P, W`K, W`L, W`f, W`Z, W`branch, W`phiFF, W`psiFF, W`excludedEK,
  W`IEK, II, stored);

F := QuadraticField(13);
M := GradedRingOfHMFs(F, 40);
computed := ConstructGeneratorsAndRelations(M, 1*Integers(F), 8, 16);
RG := ConstructWeightedPolynomialRing(computed[1]);
G := stored_generators(J, computed[1], RG, computed[2], W`storedInComputed);

// Forms of weights 2, 4, 6, 6 and 8 generate the ring with the stored relations,
// which cut out an integral surface.
procedure test_modular_presentation(M, G, RG, J)
  assert VariableWeights(RG) eq [2, 4, 6, 6, 8];
  check_monomial_ranks(M, G, RG, [2, 4, 6, 8, 10, 12, 16]);
  check_stored_relations(M, G, J);
  assert AlgebraicallyIndependent([G[2][1]^6, G[2][1]^4*G[4][1], G[2][1]^3*G[6][2]]);
  assert IsPrime(J);
end procedure;

test_modular_presentation(M, G, RG, J);

// Swap fixes the generators of weights 2, 4 and 6 and negates a nonzero form of
// weight 8.
procedure test_swap(G)
  skew := 8*G[8][1] - 4*G[2][1]*G[6][1] + 57*G[4][1]^2 - 57*G[2][1]*G[6][2];
  assert not IsZero(skew) and Swap(skew) eq (-1)*skew;
  for k in [2, 4, 6] do
    for form in G[k] do
      assert Swap(form) eq form;
    end for;
  end for;
end procedure;

test_swap(G);
check_siegel_dictionary(M, G, W`pullbacks);
SetNthreads(nthreads);
