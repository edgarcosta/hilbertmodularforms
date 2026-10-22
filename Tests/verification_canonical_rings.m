// Stored-series checks do not rerun q-expansion relation evaluations.
SetNthreads(1);

// === Q(sqrt(5)), level 1 [disc=5, label 2.2.5.1-1.1] ===
printf "Verifying Q(sqrt(5)) level 1...";
I := eval (Read("Verification/CanonicalRingEquations/2.2.5.1-1.1-gl-0.m") cat "return Ideal(S);");
F5 := LMFDBField("2.2.5.1"); ZF5 := Integers(F5);
M5 := GradedRingOfHMFs(F5, 1);
assert HilbertSeriesSanityCheck(M5, 1*ZF5, [I]);
printf "PASSED\n";


// === Q(sqrt(5)), level 4.1 [disc=5, label 2.2.5.1-4.1] ===
printf "Verifying Q(sqrt(5)) level 4.1...";
I := eval (Read("Verification/CanonicalRingEquations/2.2.5.1-4.1-gl-0.m") cat "return Ideal(S);");
NN5_4 := LMFDBIdeal(F5, "4.1");
assert HilbertSeriesSanityCheck(M5, NN5_4, [I]);
printf "PASSED\n";


// === Q(sqrt(5)), level 5.1 [disc=5, label 2.2.5.1-5.1] ===
printf "Verifying Q(sqrt(5)) level 5.1...";
I := eval (Read("Verification/CanonicalRingEquations/2.2.5.1-5.1-gl-0.m") cat "return Ideal(S);");
NN5_5 := LMFDBIdeal(F5, "5.1");
assert HilbertSeriesSanityCheck(M5, NN5_5, [I]);
printf "PASSED\n";


// === Q(sqrt(5)), level 31.2 [disc=5, label 2.2.5.1-31.2] ===
printf "Verifying Q(sqrt(5)) level 31.2...";
I := eval (Read("Verification/CanonicalRingEquations/2.2.5.1-31.2-gl-0.m") cat "return Ideal(S);");
NN5_31 := LMFDBIdeal(F5, "31.2");
assert HilbertSeriesSanityCheck(M5, NN5_31, [I]);
printf "PASSED\n";


// === Q(sqrt(2)), level 1 [disc=8, label 2.2.8.1-1.1] ===
printf "Verifying Q(sqrt(2)) level 1...";
I := eval (Read("Verification/CanonicalRingEquations/2.2.8.1-1.1-gl-0.m") cat "return Ideal(S);");
F2 := LMFDBField("2.2.8.1"); ZF2 := Integers(F2);
M8 := GradedRingOfHMFs(F2, 1);
assert HilbertSeriesSanityCheck(M8, 1*ZF2, [I]);
printf "PASSED\n";


// === Q(sqrt(2)), level 2.1 [disc=8, label 2.2.8.1-2.1] ===
printf "Verifying Q(sqrt(2)) level 2.1...";
I := eval (Read("Verification/CanonicalRingEquations/2.2.8.1-2.1-gl-0.m") cat "return Ideal(S);");
NN8_2 := LMFDBIdeal(F2, "2.1");
assert HilbertSeriesSanityCheck(M8, NN8_2, [I]);
printf "PASSED\n";


// === Q(sqrt(13)), level 1 [disc=13, label 2.2.13.1-1.1] ===
printf "Verifying Q(sqrt(13)) level 1...";
I13_ref := eval (Read("Verification/CanonicalRingEquations/2.2.13.1-1.1-gl-0.m") cat "return Ideal(S);");
F13 := LMFDBField("2.2.13.1"); ZF13 := Integers(F13);
M13 := GradedRingOfHMFs(F13, 1);
assert HilbertSeriesSanityCheck(M13, 1*ZF13, [I13_ref]);
printf "PASSED\n";


// === Q(sqrt(13)), level 3.1 [disc=13, label 2.2.13.1-3.1] ===
printf "Verifying Q(sqrt(13)) level 3.1...";
I := eval (Read("Verification/CanonicalRingEquations/2.2.13.1-3.1-gl-0.m") cat "return Ideal(S);");
NN13_3 := LMFDBIdeal(F13, "3.1");
assert HilbertSeriesSanityCheck(M13, NN13_3, [I]);
printf "PASSED\n";


// === Q(sqrt(13)), level 4.1 [disc=13, label 2.2.13.1-4.1] ===
printf "Verifying Q(sqrt(13)) level 4.1...";
I := eval (Read("Verification/CanonicalRingEquations/2.2.13.1-4.1-gl-0.m") cat "return Ideal(S);");
NN13_4 := LMFDBIdeal(F13, "4.1");
assert HilbertSeriesSanityCheck(M13, NN13_4, [I]);
printf "PASSED\n";


// === Q(sqrt(17)), level 1 [disc=17, label 2.2.17.1-1.1] ===
printf "Verifying Q(sqrt(17)) level 1...";
I := eval (Read("Verification/CanonicalRingEquations/2.2.17.1-1.1-gl-0.m") cat "return Ideal(S);");
F17 := LMFDBField("2.2.17.1"); ZF17 := Integers(F17);
M17 := GradedRingOfHMFs(F17, 1);
assert HilbertSeriesSanityCheck(M17, 1*ZF17, [I]);
printf "PASSED\n";


// === Q(sqrt(29)), level 1 [disc=29, label 2.2.29.1-1.1] ===
printf "Verifying Q(sqrt(29)) level 1...";
I := eval (Read("Verification/CanonicalRingEquations/2.2.29.1-1.1-gl-0.m") cat "return Ideal(S);");
F29 := LMFDBField("2.2.29.1"); ZF29 := Integers(F29);
M29 := GradedRingOfHMFs(F29, 1);
assert HilbertSeriesSanityCheck(M29, 1*ZF29, [I]);
printf "PASSED\n";


// === Q(sqrt(37)), level 1 [disc=37, label 2.2.37.1-1.1] ===
printf "Verifying Q(sqrt(37)) level 1...";
I := eval (Read("Verification/CanonicalRingEquations/2.2.37.1-1.1-gl-0.m") cat "return Ideal(S);");
F37 := LMFDBField("2.2.37.1"); ZF37 := Integers(F37);
M37 := GradedRingOfHMFs(F37, 1);
assert HilbertSeriesSanityCheck(M37, 1*ZF37, [I]);
printf "PASSED\n";


// === Q(sqrt(41)), level 1 [disc=41, label 2.2.41.1-1.1] ===
printf "Verifying Q(sqrt(41)) level 1...";
I := eval (Read("Verification/CanonicalRingEquations/2.2.41.1-1.1-gl-0.m") cat "return Ideal(S);");
F41 := LMFDBField("2.2.41.1"); ZF41 := Integers(F41);
M41 := GradedRingOfHMFs(F41, 1);
assert HilbertSeriesSanityCheck(M41, 1*ZF41, [I]);
printf "PASSED\n";


// The literal expectations retain the stored variable order, including D=12.
Q<t> := FunctionField(Rationals());
stored_cases := [
  <12, ["1.1", "2.1"], [[2, 14, 4, 6], [2, 14, 4, 6]],
    [(-t^12+t^10-t^8+t^6-t^4+t^2-1)/(t^10-2*t^8+t^6-t^4+2*t^2-1),
     (-t^12+t^10-t^8+t^6-t^4+t^2-1)/(t^10-2*t^8+t^6-t^4+2*t^2-1)], "SCRAMBLED">,
  <21, ["1.1", "3.1"], [[2, 4, 6, 6, 8], [2, 4, 4, 6, 10]],
    [(-t^12+t^10-t^8-t^4+t^2-1)/(t^10-2*t^8+t^6-t^4+2*t^2-1),
     (-t^12+t^10-2*t^8+2*t^6-2*t^4+t^2-1)/(t^10-2*t^8+t^6-t^4+2*t^2-1)], "PASS">,
  <24, ["1.1", "2.1"], [[2, 4, 4, 6, 6, 8, 10], [2, 2, 4, 10]],
    [(-t^8+2*t^6-3*t^4+2*t^2-1)/(t^6-3*t^4+3*t^2-1),
     (-t^8+t^6-t^4+t^2-1)/(t^6-3*t^4+3*t^2-1)], "PASS">,
  <28, ["1.1", "3.1"], [[2, 4, 4, 6, 6, 6, 8], [2, 2, 4, 6, 8]],
    [(-t^12+t^10-2*t^8-2*t^4+t^2-1)/(t^10-2*t^8+t^6-t^4+2*t^2-1),
     (-t^12-t^8-t^4-1)/(t^10-2*t^8+t^6-t^4+2*t^2-1)], "PASS">
];
for entry in stored_cases do
  D, labels, weights, singleton_series, verdict := Explode(entry);
  label := Sprintf("2.2.%o.1-1.1", D);
  components := LoadStoredCanonicalRings(label);
  assert [c[1] : c in components] eq labels;
  assert not (Generic(components[1][2]) cmpeq Generic(components[2][2]));
  guards := [];
  for i in [1..#components] do
    I := components[i][2];
    R := Generic(I);
    assert VariableWeights(R) eq weights[i];
    eqns := Basis(I);
    assert forall{f : f in eqns | Parent(f) cmpeq R};
    guard := &and[MonomialCoefficient(f, R.j) eq 0 : f in eqns, j in [1..#weights[i]]];
    if #eqns eq 1 then
      _, top := Max(weights[i]);
      guard := guard and Degree(eqns[1], top) ge 2;
      if D eq 12 then
        assert top eq 2 and Degree(eqns[1], top) eq 1;
      end if;
    end if;
    ordered := &and[weights[i][j] le weights[i][j+1] : j in [1..#weights[i]-1]];
    Append(~guards, ordered and guard);
  end for;
  sane, report := VerifyCanonicalRingComponents(label, components);
  assert sane and #report eq 3;
  assert [row[1] : row in report] eq labels cat ["all"];
  expected := singleton_series cat [&+singleton_series];
  for i in [1..#report] do
    row := report[i];
    assert row[2] and Q!row[3] eq expected[i] and Q!row[4] eq expected[i];
    assert Parent(row[3]) cmpeq Parent(report[1][3]);
    assert Parent(row[4]) cmpeq Parent(report[1][3]);
  end for;
  stored_certified := sane and &and guards;
  assert guards eq (D eq 12 select [false, false] else [true, true]);
  assert stored_certified eq (verdict eq "PASS");
  if D in {21, 24} then
    assert stored_certified and singleton_series[1] ne singleton_series[2];
    swapped := [<labels[1], components[2][2]>, <labels[2], components[1][2]>];
    swapped_sane, swapped_report := VerifyCanonicalRingComponents(label, swapped);
    assert not swapped_sane;
    assert [row[2] : row in swapped_report] eq [false, false, true];
    assert swapped_report[3] eq report[3];
  end if;
  if verdict eq "SCRAMBLED" then
    assert not stored_certified;
    printf "UNVERIFIED D=%o SCRAMBLED; singleton/full series pass\n", D;
  else
    printf "PASS stored-series D=%o components=%o\n", D, #components;
  end if;
end for;
missing := false;
try
  _ := Read("Verification/CanonicalRingEquations/2.2.33.1-1.1-gl-0.m");
catch e
  missing := true;
end try;
assert missing;
print "UNVERIFIED D=33 MISSING";

// === Cross-check: run HilbertModularVariety on Q(sqrt(13)) ===
// Verify the output matches the stored reference equations
printf "Cross-checking HilbertModularVariety output vs reference for Q(sqrt(13))...";
comp_data, schemes, certified := HilbertModularVariety(F13, 1*ZF13 : MaxB := 30);
assert certified;
assert #schemes eq 1;
assert Dimension(schemes[1]) eq 2;
// The Hilbert series of the HilbertModularVariety output should match the reference
assert HilbertSeriesSanityCheck(M13, 1*ZF13, schemes);
// Also verify it matches the stored reference
assert HilbertSeries(Ideal(schemes[1])) eq HilbertSeries(I13_ref);
printf "PASSED\n";
