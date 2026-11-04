// Check four labeled components using synthetic weighted hypersurfaces.
SetNthreads(1);

// Synthetic hypersurfaces use the four narrow-class labels of Q(sqrt(15))
// without requiring modular-form basis computations.
function four_component_blocks()
  labels := ["1.1", "2.1", "3.1", "6.1"];
  blocks := [Sprintf(
    "// component with label %o\n" cat
    "// Hilbert modular variety with label 2.2.60.1-1.1-%o-gl-0\n" cat
    "R<x, y> := PolynomialRing(Rationals(), [2, %o]);\n" cat
    "A := Proj(R);\neqns := [y - %o*x^%o];\nS := Scheme(A, eqns);\n",
    labels[i], labels[i], 2*i + 2, i, i + 1) : i in [1..4]];
  return labels, blocks;
end function;

function load_source(source)
  file := TemporaryFile();
  Write(file, source : Overwrite := true);
  components := [];
  message := "";
  try
    components := LoadStoredCanonicalRings("2.2.60.1-1.1" : SourceFile := file);
  catch e
    message := Sprint(e);
  end try;
  Remove(file);
  return components, message;
end function;

// Four narrow classes load as four labelled components, each in its own polynomial ring.
procedure test_four_labels_and_parents()
  labels, blocks := four_component_blocks();
  assert #labels eq 4 and #Seqset(labels) eq 4;
  components, message := load_source(&cat blocks);
  assert message eq "";
  assert [c[1] : c in components] eq labels;
  for i in [1..4] do
    I := components[i][2];
    R := Generic(I);
    assert VariableWeights(R) eq [2, 2*i + 2];
    assert Basis(I) eq [R.2 - i*R.1^(i + 1)];
    for j in [1..i - 1] do
      assert not (R cmpeq Generic(components[j][2]));
    end for;
  end for;
end procedure;

// The synthetic component series force a false verdict while preserving report order.
procedure test_four_singleton_series()
  labels, blocks := four_component_blocks();
  components := load_source(&cat blocks);
  sane, report := VerifyCanonicalRingComponents("2.2.60.1-1.1", components);
  assert not sane and #report eq 5;
  assert [row[1] : row in report] eq labels cat ["all"];
  t := Parent(report[1][4]).1;
  assert &and[row[4] eq 1/(1 - t^2) : row in report[1..4]];
  assert report[5][4] eq 4/(1 - t^2);
  assert report[5][3] eq &+[row[3] : row in report[1..4]];
  reversed_sane, reversed_report :=
    VerifyCanonicalRingComponents("2.2.60.1-1.1", Reverse(components));
  assert not reversed_sane;
  assert reversed_report eq Reverse(report[1..4]) cat [report[5]];
end procedure;

test_four_labels_and_parents();
test_four_singleton_series();
