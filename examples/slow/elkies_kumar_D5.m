// The stored level-1 Hilbert modular surface for Q(sqrt5) and Elkies-Kumar's Y_-(5)
// (Algebra & Number Theory 8 (2014), Section 6) have isomorphic degree-zero function
// fields over Q. The Siegel pullbacks give Elkies-Kumar's Igusa-Clebsch map.
nthreads := GetNthreads();
SetNthreads(1);
absolute_invariants, igusa_clebsch, check_absolute_invariants,
    check_inverse_maps, check_excluded_loci, check_monomial_ranks,
    check_stored_relations, check_siegel_dictionary :=
  eval (Read("examples/_elkies_kumar.m") cat "return "
    cat "absolute_invariants, igusa_clebsch, check_absolute_invariants, "
    cat "check_inverse_maps, check_excluded_loci, check_monomial_ranks, "
    cat "check_stored_relations, check_siegel_dictionary;");
W := eval Read("Verification/ElkiesKumar/2.2.5.1-1.1.m");
J := LoadStoredCanonicalRing("2.2.5.1-1.1");
R := Generic(J);
LitData := eval Read("Verification/LiteratureEquations/2.2.5.1-1.1-Hirzebruch.m");
I, Phi, Psi := LitData(R, R);
II := igusa_clebsch([Evaluate(p, [W`K | 1, W`K.1, W`K.2, W`K.3]) : p in W`pullbacks]);

// Elkies-Kumar's rational inverse of the Humbert map: the point (g, h) from the
// absolute invariants j, and the two denominators it divides by.
function humbert_inverse(j)
  r := j[2]/j[1];
  s := j[3]/j[1];
  AA := 6*s - 2*r;
  den := 7776 - 2*j[1]*AA*r;
  k := (1944 - j[1]*(AA^2 + 4*r^3))/den;
  return [k/(1 - 4*k), (AA - r*k)/(1 - 4*k)^3], [den, 1 - 4*k];
end function;

// Through Hirzebruch's presentation, the stored surface on the X2 chart is the double
// cover Z^2 = branch.
procedure test_hirzebruch_chart(I, J, Phi, Psi, P, K, Z, branch)
  assert VerifyGradedIsomorphism(I, J, Phi, Psi);
  assert Evaluate(Phi[4], [K | 1, K.1, K.2, K.3]) eq Z;
  Jo := ideal<P | [Evaluate(p, [P | 1, P.1, P.2, P.3]) : p in Basis(J)]>;
  assert Jo eq ideal<P | Z^2 - branch>;
end procedure;

test_hirzebruch_chart(I, J, Phi, Psi, W`P, W`K, W`Z, W`branch);

// The modular Igusa-Clebsch invariants have the absolute invariants of the published
// tuple, and these recover the point (g, h), so the Humbert fields agree.
procedure test_igusa_map(P, K, L, Z, branch, phiFF, IEK, II)
  a := K.1;
  b := K.2;
  g := L.1;
  h := L.2;
  assert II eq [K | 24*a^2/b - 16, 4, 32*a^2/b - 24 + 2304*a, 4096*b];
  assert IEK eq [L | 24*g + 6, 9*g^2, 81*g^3 + 18*g^2 + 36*h, 4*h^2];
  check_absolute_invariants(IEK, II, phiFF, ideal<P | Z^2 - branch>);
  assert humbert_inverse(absolute_invariants(IEK)) eq [g, h];
end procedure;

test_igusa_map(W`P, W`K, W`L, W`Z, W`branch, W`phiFF, W`IEK, II);

// Over Q, the double cover is Elkies-Kumar's: f is not a square, the radicands differ
// by a rational square, and phiFF and psiFF are mutually inverse.
procedure test_function_fields(P, K, L, f, Z, branch, phiFF, psiFF, excludedEK, IEK, II)
  a := K.1;
  b := K.2;
  t := K.3;
  Jo := ideal<P | Z^2 - branch>;
  assert &or[IsOdd(e[2]) : e in Factorization(f)];
  assert Evaluate(f, phiFF)*(2^23*a^5/b)^2 eq branch;
  deck := [K | a, b, (a^3 - a*b + 52*b^2)/4 - t];
  check_inverse_maps(Jo, f, Z, branch, phiFF, psiFF, deck);
  _, poles := humbert_inverse(absolute_invariants(IEK));
  check_excluded_loci(Jo, [K | a, b, II[1], II[4]] cat phiFF,
    [L | L.1, L.2, IEK[1], IEK[4], excludedEK] cat poles cat psiFF);
end procedure;

test_function_fields(W`P, W`K, W`L, W`f, W`Z, W`branch, W`phiFF, W`psiFF, W`excludedEK,
  W`IEK, II);

F := QuadraticField(5);
M := GradedRingOfHMFs(F, 80);
computed := ConstructGeneratorsAndRelations(M, 1*Integers(F), 20, 20);
G := computed[1];
RG := ConstructWeightedPolynomialRing(G);

// Forms of weights 2, 6, 10 and 20 generate the ring with the stored relation.
procedure test_modular_presentation(M, G, RG, J)
  assert VariableWeights(RG) eq [2, 6, 10, 20];
  check_monomial_ranks(M, G, RG, [2, 4, 6, 10, 12, 20, 40]);
  check_stored_relations(M, G, J);
  assert AlgebraicallyIndependent([G[2][1]^6, G[6][1]^2, G[2][1]*G[10][1]]);
end procedure;

test_modular_presentation(M, G, RG, J);

// Swap fixes the generators of weights 2, 6 and 10 and negates a nonzero form of
// weight 20.
procedure test_swap(G)
  skew := G[2][1]*G[6][1]^3 - G[2][1]^2*G[6][1]*G[10][1] - 8*G[20][1]
    + 52*G[10][1]^2;
  assert not IsZero(skew) and Swap(skew) eq (-1)*skew;
  for k in [2, 6, 10] do
    assert Swap(G[k][1]) eq G[k][1];
  end for;
end procedure;

test_swap(G);

// The Siegel pullbacks are computed at precision 20, from generators that agree with
// G to that precision. No pullback needs the missing weight-20 generator.
procedure test_siegel_dictionary(M, G, pullbacks)
  F := BaseField(M);
  ZF := Integers(F);
  bb := NarrowClassRepresentative(M, Different(ZF)^-1);
  Mlo := GradedRingOfHMFs(F, 20);
  Glo := ConstructGeneratorsAndRelations(Mlo, 1*ZF, 10, 12)[1];
  Rlo := ConstructWeightedPolynomialRing(Glo);
  for k in [2, 6, 10] do
    for nu in FunDomainRepsUpToPrec(Mlo, bb, 20) do
      assert Coefficient(G[k][1], bb, nu : InFunDomain := true)
        eq Coefficient(Glo[k][1], bb, nu : InFunDomain := true);
    end for;
  end for;
  check_monomial_ranks(Mlo, Glo, Rlo, [4, 6, 10, 12]);
  check_siegel_dictionary(Mlo, Glo,
    [Evaluate(p, [Rlo | Rlo.1, Rlo.2, Rlo.3, 0]) : p in pullbacks]);
end procedure;

test_siegel_dictionary(M, G, W`pullbacks);
SetNthreads(nthreads);
