// Examples select these routines with eval and an appended return statement.
// CI skips this support file because its name starts with an underscore.

// The record each witness file Verification/ElkiesKumar/2.2.D.1-1.1.m returns.
// P and K are the ring and function field of the chart a, b, t, where the stored
// surface is Z^2 = branch. Q and L are those of Elkies-Kumar's model z^2 = f.
// Witnesses for D >= 13 set storedInComputed; only D = 41 sets the four after it.
witness_format := recformat<P, K, Q, L, f, Z, branch, phiFF, psiFF, pullbacks,
  excludedEK, IEK, storedInComputed, stored, cachedInStored, reconstruction,
  retainedQuadratic>;

// I must be prime so nonzero denominators are invertible in its function field.
is_zero_on := func<x, I | Numerator(x) in I and not Denominator(x) in I>;
is_unit_on := func<x, I | not Numerator(x) in I and not Denominator(x) in I>;

// The Igusa-Clebsch invariants [I2, I4, I6, I10] from the values of psi4, psi6, chi10
// and chi12, with the conversion of Mestre/Qsqrt3.m.
igusa_clebsch := func<s | [-24*s[4]/s[3], 4*s[1], -8*s[2]/3 - 32*s[1]*s[4]/s[3],
  -2^14*s[3]]>;

absolute_invariants := func<v | [v[1]^5/v[4], v[1]^3*v[2]/v[4], v[1]^2*v[3]/v[4]]>;

// The published Igusa-Clebsch tuple IEK pulled back by phiFF has the absolute
// invariants of II on the double cover Jo.
procedure check_absolute_invariants(IEK, II, phiFF, Jo)
  published := absolute_invariants(IEK);
  modular := absolute_invariants(II);
  for i in [1..3] do
    assert is_zero_on(Evaluate(published[i], phiFF) - modular[i], Jo);
  end for;
end procedure;

// phiFF and psiFF are mutually inverse rational maps between the double cover Jo
// (Z^2 = B over the chart) and Elkies-Kumar's z^2 = f. The deck transformation deck
// fixes Z^2 - B and negates the third coordinate of phiFF.
procedure check_inverse_maps(Jo, f, Z, B, phiFF, psiFF, deck)
  K := Universe(phiFF);
  L := Universe(psiFF);
  Q := Parent(f);
  JE := ideal<Q | Q.3^2 - f>;
  assert Numerator(Evaluate(Q.3^2 - f, phiFF)) in Jo;
  assert Numerator(Evaluate(Z^2 - B, psiFF)) in JE;
  for i in [1..3] do
    assert is_zero_on(Evaluate(psiFF[i], phiFF) - K.i, Jo);
    assert is_zero_on(Evaluate(phiFF[i], psiFF) - L.i, JE);
  end for;
  assert Evaluate(Z^2 - B, deck) eq Z^2 - B;
  assert [Evaluate(p, deck) : p in phiFF] eq [phiFF[1], phiFF[2], -phiFF[3]];
end procedure;

// The excluded loci are proper closed subsets: each function in onChart is a unit on
// the double cover Jo, and each function in onTarget is nonzero.
procedure check_excluded_loci(Jo, onChart, onTarget)
  for p in onChart do
    assert is_unit_on(p, Jo);
  end for;
  for p in onTarget do
    assert p ne 0;
  end for;
end procedure;

// This order must agree with ConstructWeightedPolynomialRing(G).
function generator_list(G)
  gens := [* *];
  for k in Sort(Setseq(Keys(G))) do
    for form in G[k] do
      Append(~gens, form);
    end for;
  end for;
  return gens;
end function;

// coordinateMap carries the stored generators into the recomputed ring.
// Verify the presentation before evaluating it on modular forms.
function stored_generators(J, G, RG, relations, coordinateMap)
  coordinateMap := [RG | RG!p : p in coordinateMap];
  assert VerifyGradedIsomorphism(J, ConstructIdeal(RG, relations), coordinateMap,
    GradedInverseImages(RG, coordinateMap));
  gens := generator_list(G);
  stored := AssociativeArray();
  for p in coordinateMap do
    k := WeightedDegree(p);
    if not IsDefined(stored, k) then
      stored[k] := [];
    end if;
    Append(~stored[k], Evaluate(p, gens));
  end for;
  return stored;
end function;

// For each k in weights, the weight-k monomials in G have rank dim M_k on the
// q-expansions of M. So they span M_k, and the precision of M separates its forms.
procedure check_monomial_ranks(M, G, RG, weights)
  for k in weights do
    monomials := [m : m in MonomialsOfWeightedDegree(RG, k)];
    rank := Rank(CoefficientsMatrix(EvaluateMonomials(G, monomials)));
    assert rank eq Dimension(HMFSpace(M, [k, k]));
  end for;
end procedure;

// G satisfies the stored relations J, which have the Hilbert series of the trace
// formula.
procedure check_stored_relations(M, G, J)
  gens := generator_list(G);
  for p in Basis(J) do
    assert IsZero(Evaluate(p, gens));
  end for;
  assert HilbertSeriesSanityCheck(M, 1*Integers(BaseField(M)), [J]);
end procedure;

// A norm -1 unit makes the determinant-unit quotient trivial, so the minus
// parts omitted by UniversalIgusa vanish. The inverse different lies in the
// principal narrow class, the component supporting G.
procedure check_siegel_dictionary(M, G, pullbacks)
  F := BaseField(M);
  ZF := Integers(F);
  U, unitmap := UnitGroup(F);
  assert ClassNumber(F) eq 1 and Norm(unitmap(U.2)) eq -1;
  assert NarrowClassRepresentative(M, Different(ZF)^-1) eq 1*ZF;
  psi4, psi6, _, _, chi10, chi12 := UniversalIgusa(M);
  gens := generator_list(G);
  for i -> form in [* psi4, psi6, chi10, chi12 *] do
    assert IsZero(form - Evaluate(pullbacks[i], gens));
  end for;
end procedure;
