SetNthreads(1);

cases := [
  <"2.2.12.1-1.1", ["1.1", "2.1"], [[2,14,4,6], [2,14,4,6]]>,
  <"2.2.21.1-1.1", ["1.1", "3.1"], [[2,4,6,6,8], [2,4,4,6,10]]>,
  <"2.2.24.1-1.1", ["1.1", "2.1"], [[2,4,4,6,6,8,10], [2,2,4,10]]>,
  <"2.2.13.1-1.1", ["1.1"], [[2,4,6,6,8]]>
];
for entry in cases do
  label, labels, weights := Explode(entry);
  components := LoadStoredCanonicalRings(label);
  assert Type(components) eq SeqEnum;
  assert [c[1] : c in components] eq labels;
  if #components eq 2 then
    assert not (Generic(components[1][2]) cmpeq Generic(components[2][2]));
  end if;
  source := Read("Verification/CanonicalRingEquations/" cat label cat "-gl-0.m");
  for i in [1..#labels] do
    prefix := source;
    if i lt #labels then
      stop := Position(source, "// component with label " cat labels[i+1]);
      prefix := source[1..stop-1];
    end if;
    expected := eval (prefix cat "\nreturn ideal< R | eqns >;");
    I := components[i][2];
    R := Generic(I);
    assert Type(I) eq RngMPol;
    assert VariableWeights(R) eq weights[i];
    assert BaseRing(R) cmpeq Rationals();
    assert forall{g : g in Basis(I) | Parent(g) cmpeq R};
    assert Basis(I) eq [Evaluate(g, [R.j : j in [1..Rank(R)]]) : g in Basis(expected)];
  end for;
end for;

I := LoadStoredCanonicalRing("2.2.13.1-1.1");
assert Type(I) eq RngMPol;
assert VariableWeights(Generic(I)) eq [2,4,6,6,8];
rejected := false;
try
  _ := LoadStoredCanonicalRing("2.2.12.1-1.1");
catch e
  rejected := "single-component" in Sprint(e);
end try;
assert rejected;

root := GetCurrentDirectory();
label := "2.2.13.1-1.1";
block := "// component with label 1.1\n" cat
  "// Hilbert modular variety with label 2.2.13.1-1.1-1.1-gl-0\n" cat
  "R<x,y> := PolynomialRing(Rationals(), [2,4]);\n" cat
  "A := Proj(R);\neqns := [y - 3/2*x^2];\nS :=\n Scheme(A, eqns);\n";
second := "// component with label 2.1\n" cat
  "// Hilbert modular variety with label 2.2.13.1-1.1-2.1-gl-0\n" cat
  "R<u,v> := PolynomialRing(Rationals(), [2,6]);\n";
fixtures := [
  <block cat second, "incomplete component 2.1">,
  <block cat block, "duplicate component label 1.1">,
  <"// component with label 1.1\n" cat
    "// Hilbert modular variety with label 2.2.24.1-1.1-1.1-gl-0\n" cat
    "R<x> := PolynomialRing(Rationals(), [2]);\nA := Proj(R);\n" cat
    "eqns := [x];\nS := Scheme(A,eqns);\n", "conflicting variety metadata for component 1.1">,
  <block cat "S := Scheme(A,eqns);\n", "extra statement after component 1.1 scheme">,
  <block cat "// component with label 2.1\n" cat
    "// Hilbert modular variety with label 2.2.13.1-1.1-2.1-gl-0\n" cat
    "S := Scheme(A,eqns);\n", "incomplete scheme for component 2.1">,
  <"// level has label 2.1\n" cat block, "conflicting level metadata">
];
fixture_root := Split(Pipe("mktemp -d", ""), "\n")[1];
try
  System("mkdir -p '" cat fixture_root cat "/Verification/CanonicalRingEquations'");
  ChangeDirectory(fixture_root);
  file := "Verification/CanonicalRingEquations/" cat label cat "-gl-0.m";
  for fixture in fixtures do
    handle := Open(file, "w");
    Puts(handle, fixture[1]);
    Flush(handle);
    delete handle;
    rejected := false;
    try
      _ := LoadStoredCanonicalRings(label);
    catch e
      diagnostic := Split(Sprint(e), "\n");
      rejected := diagnostic[#diagnostic] eq
        Sprintf("Runtime error in 'LoadStoredCanonicalRings': %o: %o", file, fixture[2]);
    end try;
    assert rejected;
  end for;
  handle := Open(file, "w");
  Puts(handle, block);
  Flush(handle);
  delete handle;
  components := LoadStoredCanonicalRings(label);
  assert #components eq 1 and components[1][1] eq "1.1";
  I := components[1][2];
  R := Generic(I);
  assert VariableWeights(R) eq [2,4];
  assert Basis(I) eq [R.2 - 3/2*R.1^2];
catch e
  ChangeDirectory(root);
  System("rm -rf '" cat fixture_root cat "'");
  error e;
end try;
ChangeDirectory(root);
System("rm -rf '" cat fixture_root cat "'");
print "PASS component loader";
