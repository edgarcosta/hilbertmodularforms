SetNthreads(1);

label := "2.2.60.1-1.1";
F := LMFDBField("2.2.60.1");
M := GradedRingOfHMFs(F, 1);
labels := [LMFDBLabel(bb) : bb in NarrowClassGroupReps(M)];
assert #labels eq 4 and #Seqset(labels) eq 4;
blocks := [Sprintf(
  "// component with label %o\n" cat
  "// Hilbert modular variety with label %o-%o-gl-0\n" cat
  "R<x,y> := PolynomialRing(Rationals(), [2,%o]);\n" cat
  "A := Proj(R);\neqns := [y - %o*x^%o];\nS := Scheme(A, eqns);\n",
  labels[i], label, labels[i], 2*i+2, i, i+1) : i in [1..4]];

root := GetCurrentDirectory();
fixture_root := Split(Pipe("mktemp -d", ""), "\n")[1];
try
  System("mkdir -p '" cat fixture_root cat "/Verification/CanonicalRingEquations'");
  ChangeDirectory(fixture_root);
  file := "Verification/CanonicalRingEquations/" cat label cat "-gl-0.m";
  Write(file, &cat blocks : Overwrite:=true);
  components := LoadStoredCanonicalRings(label);
  assert [c[1] : c in components] eq labels;
  for i in [1..4] do
    I := components[i][2];
    R := Generic(I);
    assert VariableWeights(R) eq [2, 2*i+2];
    assert Basis(I) eq [R.2 - i*R.1^(i+1)];
    for j in [1..i-1] do
      assert not (R cmpeq Generic(components[j][2]));
    end for;
  end for;
  print "PASS four distinct component labels and stored presentations", labels;

  // Synthetic polynomial rings exercise coverage without computing modular forms.
  sane, report := VerifyCanonicalRingComponents(label, components);
  assert not sane and #report eq 5;
  assert [row[1] : row in report] eq labels cat ["all"];
  t := Parent(report[1][4]).1;
  assert &and[row[4] eq 1/(1-t^2) : row in report[1..4]];
  assert report[5][4] eq 4/(1-t^2);
  assert report[5][3] eq &+[row[3] : row in report[1..4]];
  reversed_sane, reversed_report := VerifyCanonicalRingComponents(label, Reverse(components));
  assert not reversed_sane;
  assert reversed_report eq Reverse(report[1..4]) cat [report[5]];
  print "PASS four singleton series and combined report";

  Write(file, &cat blocks[1..3] : Overwrite:=true);
  missing := LoadStoredCanonicalRings(label);
  assert [c[1] : c in missing] eq labels[1..3];
  for entry in [
    <missing, "exactly one component per narrow ideal class">,
    <components[1..3] cat [components[1]], "Duplicate component label">
  ] do
    rejected := false;
    try
      _ := VerifyCanonicalRingComponents(label, entry[1]);
    catch e
      rejected := entry[2] in Sprint(e);
    end try;
    assert rejected;
  end for;
  Write(file, &cat blocks[1..3] cat blocks[1] : Overwrite:=true);
  rejected := false;
  try
    _ := LoadStoredCanonicalRings(label);
  catch e
    rejected := "duplicate component label" in Sprint(e);
  end try;
  assert rejected;
  print "PASS missing and duplicate components rejected";
catch e
  ChangeDirectory(root);
  System("rm -rf '" cat fixture_root cat "'");
  error e;
end try;
ChangeDirectory(root);
System("rm -rf '" cat fixture_root cat "'");
print "PASS four-component contract";
