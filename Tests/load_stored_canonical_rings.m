// Check stored presentations, the single-component wrapper and malformed sources.
SetNthreads(1);

// Magma 2.30-1 crashes on reference-source evals inside procedures evaluated by run_tests.m.
cases := [
  <"2.2.21.1-1.1", ["1.1", "3.1"], [[2, 4, 6, 6, 8], [2, 4, 4, 6, 10]]>
];
reference_ideals := [];
for entry in cases do
  label, labels, weights := Explode(entry);
  source := Read("Verification/CanonicalRingEquations/" cat label cat "-gl-0.m");
  ideals := [];
  for i in [1..#labels] do
    prefix := source;
    if i lt #labels then
      stop := Position(source, "// component with label " cat labels[i + 1]);
      prefix := source[1..stop - 1];
    end if;
    Append(~ideals, eval (prefix cat "\nreturn ideal< R | eqns >;"));
  end for;
  Append(~reference_ideals, ideals);
end for;

// The stored labels, weights, parents and coefficients agree with the source.
procedure test_stored_files(cases, reference_ideals)
  assert #cases gt 0;
  for n in [1..#cases] do
    label, labels, weights := Explode(cases[n]);
    components := LoadStoredCanonicalRings(label);
    assert Type(components) eq SeqEnum;
    assert [c[1] : c in components] eq labels;
    assert not (Generic(components[1][2]) cmpeq Generic(components[2][2]));
    for i in [1..#labels] do
      expected := reference_ideals[n][i];
      I := components[i][2];
      R := Generic(I);
      assert Type(I) eq RngMPol;
      assert VariableWeights(R) eq weights[i];
      assert BaseRing(R) cmpeq Rationals();
      assert forall{g : g in Basis(I) | Parent(g) cmpeq R};
      assert Basis(I) eq [Evaluate(g, [R.j : j in [1..Rank(R)]]) : g in Basis(expected)];
    end for;
  end for;
end procedure;

// The single-component wrapper returns the sole ideal and rejects a two-component file.
procedure test_single_component_wrapper()
  I := LoadStoredCanonicalRing("2.2.13.1-1.1");
  assert Type(I) eq RngMPol;
  assert VariableWeights(Generic(I)) eq [2, 4, 6, 6, 8];
  R := Generic(I);
  expected := LoadStoredCanonicalRings("2.2.13.1-1.1")[1][2];
  assert Basis(I) eq [Evaluate(g, [R.j : j in [1..Rank(R)]]) : g in Basis(expected)];
  rejected := false;
  try
    _ := LoadStoredCanonicalRing("2.2.12.1-1.1");
  catch e
    rejected := "single-component" in Sprint(e);
  end try;
  assert rejected;
end procedure;

function load_error(label, file)
  message := "";
  try
    _ := LoadStoredCanonicalRings(label : SourceFile := file);
  catch e
    message := Sprint(e);
  end try;
  return message;
end function;

// Each malformed source passed as SourceFile fails with the filename and the reason, and a
// well-formed one loads.
procedure test_malformed_sources()
  label := "2.2.13.1-1.1";
  block := "// component with label 1.1\n" cat
    "// Hilbert modular variety with label 2.2.13.1-1.1-1.1-gl-0\n" cat
    "R<x, y> := PolynomialRing(Rationals(), [2, 4]);\n" cat
    "A := Proj(R);\neqns := [y - 3/2*x^2];\nS :=\n Scheme(A, eqns);\n";
  second := "// component with label 2.1\n" cat
    "// Hilbert modular variety with label 2.2.13.1-1.1-2.1-gl-0\n" cat
    "R<u, v> := PolynomialRing(Rationals(), [2, 6]);\n";
  fixtures := [
    <block cat second, "incomplete component 2.1">,
    <block cat block, "duplicate component label 1.1">,
    <"// component with label 1.1\n" cat
      "// Hilbert modular variety with label 2.2.24.1-1.1-1.1-gl-0\n" cat
      "R<x> := PolynomialRing(Rationals(), [2]);\nA := Proj(R);\n" cat
      "eqns := [x];\nS := Scheme(A, eqns);\n", "conflicting variety metadata for component 1.1">,
    <block cat "S := Scheme(A, eqns);\n", "extra statement after component 1.1 scheme">,
    <block cat "// component with label 2.1\n" cat
      "// Hilbert modular variety with label 2.2.13.1-1.1-2.1-gl-0\n" cat
      "S := Scheme(A, eqns);\n", "incomplete scheme for component 2.1">,
    <"// level has label 2.1\n" cat block, "conflicting level metadata">
  ];
  file := TemporaryFile();
  errors := [];
  assert #fixtures gt 0;
  for fixture in fixtures do
    Write(file, fixture[1] : Overwrite := true);
    Append(~errors, load_error(label, file));
  end for;
  Write(file, block : Overwrite := true);
  components := LoadStoredCanonicalRings(label : SourceFile := file);
  Remove(file);
  for i in [1..#fixtures] do
    assert Sprintf("%o: %o", file, fixtures[i][2]) in errors[i];
  end for;
  assert #components eq 1 and components[1][1] eq "1.1";
  I := components[1][2];
  R := Generic(I);
  assert VariableWeights(R) eq [2, 4];
  assert Basis(I) eq [R.2 - 3/2*R.1^2];
end procedure;

test_stored_files(cases, reference_ideals);
test_single_component_wrapper();
test_malformed_sources();
