// The stored level-1 Hilbert modular surface for Q(sqrt2) and Elkies-Kumar's Y_-(8)
// (Algebra & Number Theory 8 (2014), Section 7) have isomorphic degree-zero function
// fields over Q. The Siegel pullbacks give Elkies-Kumar's Igusa-Clebsch map.
nthreads := GetNthreads();
SetNthreads(1);
igusa_clebsch, check_absolute_invariants, check_inverse_maps,
    check_excluded_loci, check_monomial_ranks, check_stored_relations,
    check_siegel_dictionary :=
  eval (Read("examples/_elkies_kumar.m") cat "return "
    cat "igusa_clebsch, check_absolute_invariants, check_inverse_maps, "
    cat "check_excluded_loci, check_monomial_ranks, check_stored_relations, "
    cat "check_siegel_dictionary;");
W := eval Read("Verification/ElkiesKumar/2.2.8.1-1.1.m");
J := LoadStoredCanonicalRing("2.2.8.1-1.1");
R := Generic(J);
LitData := eval Read("Verification/LiteratureEquations/2.2.8.1-1.1-Hirzebruch.m");
I, Phi, Psi := LitData(R, R);
II := igusa_clebsch([Evaluate(p, [W`K | 1, W`K.1, W`K.2, W`K.3]) : p in W`pullbacks]);

// Through Hirzebruch's presentation, the stored surface on the X2 chart is the double
// cover Z^2 = branch.
procedure test_hirzebruch_chart(I, J, Phi, Psi, P, K, Z, branch)
  assert VerifyGradedIsomorphism(I, J, Phi, Psi);
  assert Evaluate(Phi[4], [K | 1, K.1, K.2, K.3]) eq Z/128;
  Jo := ideal<P | [Evaluate(p, [P | 1, P.1, P.2, P.3]) : p in Basis(J)]>;
  assert Jo eq ideal<P | Z^2 - branch>;
end procedure;

test_hirzebruch_chart(I, J, Phi, Psi, W`P, W`K, W`Z, W`branch);

// The modular Igusa-Clebsch invariants have the absolute invariants of the published
// tuple, and these determine the point (r, s), so the Humbert fields agree.
procedure test_igusa_map(P, Z, branch, phiFF, IEK, II)
  check_absolute_invariants(IEK, II, phiFF, ideal<P | Z^2 - branch>);
  // Equality of the three absolute invariants fixes the weighted tuple up to scale.
  // Its generic fiber is a rational point, proving equality of the Humbert fields.
  B0<r0, s0> := PolynomialRing(Rationals(), 2);
  F0 := FieldOfFractions(B0);
  IE0 := [Evaluate(p, [F0 | r0, s0, 0]) : p in IEK];
  AA<rr, ss, ll, uu> := PolynomialRing(F0, 4, "lex");
  IEn := [Evaluate(p, [FieldOfFractions(AA) | rr, ss, 0]) : p in IEK];
  weights := [1, 2, 3, 5];
  fiber := ideal<AA | [AA!Numerator(IEn[i] - ll^weights[i]*IE0[i]) : i in [1..4]]
    cat [ll*uu*rr*ss - 1]>;
  assert GroebnerBasis(fiber) eq [AA | rr - r0, ss - s0, ll - 1, uu - 1/(r0*s0)];
end procedure;

test_igusa_map(W`P, W`Z, W`branch, W`phiFF, W`IEK, II);

// Over Q, the double cover is Elkies-Kumar's: f is not a square, the radicands differ
// by a rational square, and phiFF and psiFF are mutually inverse.
procedure test_function_fields(P, K, L, f, Z, branch, phiFF, psiFF, excludedEK, IEK, II)
  a := K.1;
  b := K.2;
  t := K.3;
  r := L.1;
  s := L.2;
  Jo := ideal<P | Z^2 - branch>;
  assert &or[IsOdd(e[2]) : e in Factorization(f)];
  assert branch/Evaluate(f, phiFF) eq (b*(a + 4*b)^2/(2*a))^2;
  deck := [K | a, b, 2*a^3 + a*b + 20*a^2*b + 2*b^2 - t];
  check_inverse_maps(Jo, f, Z, branch, phiFF, psiFF, deck);
  check_excluded_loci(Jo, [K | a, b, a + 4*b, II[1], II[4]] cat phiFF,
    [L | r, s, 2*r + 1, IEK[1], IEK[4], excludedEK] cat psiFF);
end procedure;

test_function_fields(W`P, W`K, W`L, W`f, W`Z, W`branch, W`phiFF, W`psiFF, W`excludedEK,
  W`IEK, II);

F := QuadraticField(8);
M := GradedRingOfHMFs(F, 80);
computed := ConstructGeneratorsAndRelations(M, 1*Integers(F), 14, 14);
G := computed[1];
RG := ConstructWeightedPolynomialRing(G);

// Forms of weights 2, 4, 6 and 14 generate the ring with the stored relation.
procedure test_modular_presentation(M, G, RG, J)
  assert VariableWeights(RG) eq [2, 4, 6, 14];
  check_monomial_ranks(M, G, RG, [2, 4, 6, 10, 12, 14, 28]);
  check_stored_relations(M, G, J);
  assert AlgebraicallyIndependent([G[2][1]^6, G[4][1]^3, G[6][1]^2]);
end procedure;

test_modular_presentation(M, G, RG, J);

// Swap fixes the generators of weights 2, 4 and 6 and negates a nonzero form of
// weight 14.
procedure test_swap(G)
  skew := 2*G[2][1]*G[4][1]^3 + G[2][1]^2*G[4][1]*G[6][1] + 20*G[4][1]^2*G[6][1]
    + 2*G[2][1]*G[6][1]^2 - 2*G[14][1];
  assert not IsZero(skew) and Swap(skew) eq (-1)*skew;
  for k in [2, 4, 6] do
    assert Swap(G[k][1]) eq G[k][1];
  end for;
end procedure;

test_swap(G);

// The Siegel pullbacks are computed at precision 40, from generators that agree with
// G to that precision.
procedure test_siegel_dictionary(M, G, pullbacks)
  F := BaseField(M);
  ZF := Integers(F);
  bb := NarrowClassRepresentative(M, Different(ZF)^-1);
  Mlo := GradedRingOfHMFs(F, 40);
  Glo := ConstructGeneratorsAndRelations(Mlo, 1*ZF, 14, 14)[1];
  for k in [2, 4, 6, 14] do
    for nu in FunDomainRepsUpToPrec(Mlo, bb, 40) do
      assert Coefficient(G[k][1], bb, nu : InFunDomain := true)
        eq Coefficient(Glo[k][1], bb, nu : InFunDomain := true);
    end for;
  end for;
  check_monomial_ranks(Mlo, Glo, ConstructWeightedPolynomialRing(Glo), [4, 6, 10, 12]);
  check_siegel_dictionary(Mlo, Glo, pullbacks);
end procedure;

test_siegel_dictionary(M, G, W`pullbacks);
SetNthreads(nthreads);
