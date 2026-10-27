// Q(sqrt(5), i) has class number 1 and unit index 4 in this normalization.
// Scaling the discriminant changes the conductor and the embedding count.
procedure test_field_embedding_counts()
  F := QuadraticField(5);
  ZF := Integers(F);
  // Each case is <D, level, diamond ideal, expected count>. The fourth case repeats the first,
  // so its count comes from the cache.
  cases := [* <ZF!(-4), 1*ZF, 1*ZF, 1/4>, <ZF!(-16), 1*ZF, 1*ZF, 5/4>,
    <ZF!(-16), 1*ZF, 2*ZF, 1/4>, <ZF!(-4), 1*ZF, 1*ZF, 1/4>, <ZF!(-4), 1*ZF, 2*ZF, 0>,
    <ZF!(-4), ideal<ZF | 1>, 1*ZF, 1/4> *];
  for i in [1..#cases] do
    D, level, diamond_ideal, expected := Explode(cases[i]);
    count := EmbeddingNumberOverUnitIndex(F, D, level, diamond_ideal);
    error if count ne expected, Sprintf("embedding count %o, expected %o: case %o, D %o, " cat
      "level norm %o, diamond ideal norm %o", count, expected, i, D, Norm(level),
      Norm(diamond_ideal));
  end for;
end procedure;

procedure test_embedding_discriminant_domain()
  F := QuadraticField(5);
  ZF := Integers(F);
  for D in [ZF!1, ZF!(-1)] do
    rejected := false;
    try
      _ := EmbeddingNumberOverUnitIndex(F, D, 1*ZF, 1*ZF);
    catch err
      rejected := "D must be" in Sprint(err);
    end try;
    error if not rejected, Sprintf("EmbeddingNumberOverUnitIndex did not reject D = %o", D);
  end for;
end procedure;

// A zero diamond ideal and a level in the non-maximal order Z[sqrt(5)] are both rejected.
procedure test_embedding_ideal_domain()
  F := QuadraticField(5);
  ZF := Integers(F);
  rejected_inputs := [* <1*ZF, 0*ZF, "diamond_ideal must be">,
    <ideal<EquationOrder(F) | 2>, 1*ZF, "level must be"> *];
  for rejected_input in rejected_inputs do
    level, diamond_ideal, message := Explode(rejected_input);
    rejected := false;
    try
      _ := EmbeddingNumberOverUnitIndex(F, ZF!(-4), level, diamond_ideal);
    catch err
      rejected := message in Sprint(err);
    end try;
    error if not rejected, "EmbeddingNumberOverUnitIndex did not report: " cat message;
  end for;
end procedure;

test_field_embedding_counts();
test_embedding_discriminant_domain();
test_embedding_ideal_domain();

// Changing expansion precision preserves trace dimensions.
procedure test_trace_counts_across_parents(F)
  ZF := Integers(F);
  pp := Factorization(2*ZF)[1][1];
  for prec in [1, 2] do
    M := GradedRingOfHMFs(F, prec);
    for NN in [1*ZF, pp, pp^2] do
      for k in [2, 6] do
        Mk := HMFSpace(M, NN, [k, k]);
        expected := CuspDimension(Mk : version := "builtin");
        correction := CorrectionFactor(Mk, 1*ZF);
        error if TraceProduct(Mk, 1*ZF, 1*ZF) + correction ne expected,
          Sprintf("trace and builtin dimensions differ: field discriminant %o, prec %o, " cat
            "level norm %o, weight %o", Discriminant(ZF), prec, Norm(NN), k);
      end for;
    end for;
  end for;
end procedure;

// T((4)) and P((2)) share discriminants but restrict conductor divisors differently.
procedure test_trace_counts_for_diamond_ideal()
  F := QuadraticField(5);
  ZF := Integers(F);
  M := GradedRingOfHMFs(F, 1);
  Mk := HMFSpace(M, 1*ZF, [6, 6]);
  // S_6(1) is one-dimensional and the builtin T((2)) acts on it by 20, so
  // T((4)) = T((2))^2 - 4^5 has trace 20^2 - 4^5 = -624.
  hecke_trace := TraceProduct(Mk, 4*ZF, 1*ZF);
  error if hecke_trace ne -624, Sprintf("trace of T((4)) is %o, expected -624", hecke_trace);
  expected := CuspDimension(Mk : version := "builtin");
  diamond_trace := TraceProduct(Mk, 1*ZF, 2*ZF);
  error if diamond_trace ne expected,
    Sprintf("trace of P((2)) is %o, expected the builtin dimension %o", diamond_trace, expected);
end procedure;

for d in [3, 5, 13] do
  test_trace_counts_across_parents(QuadraticField(d));
end for;
test_trace_counts_for_diamond_ideal();

// Precomputed traces retain the builtin dimensions at prime-power levels.
procedure test_precomputed_trace_counts()
  F := QuadraticField(5);
  ZF := Integers(F);
  M := GradedRingOfHMFs(F, 1);
  HMFTracePrecomputation(M, [1*ZF] : SaveAndLoad := false);
  pp := Factorization(2*ZF)[1][1];
  for NN in [1*ZF, pp, pp^2] do
    Mk := HMFSpace(M, NN, [6, 6]);
    error if Trace(Mk, 1*ZF : precomp := true) ne CuspDimension(Mk : version := "builtin"),
      Sprintf("precomputed trace and builtin dimension differ: field discriminant %o, " cat
        "level norm %o", Discriminant(ZF), Norm(NN));
  end for;
end procedure;

test_precomputed_trace_counts();
