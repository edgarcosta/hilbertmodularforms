SetNthreads(1);

label := "2.2.24.1-1.1";
components := LoadStoredCanonicalRings(label);
sane, report := VerifyCanonicalRingComponents(label, components);
assert sane;
assert #report eq 3;
assert [row[1] : row in report] eq ["1.1", "2.1", "all"];
Q<t> := FunctionField(Rationals());
expected := [
  (-t^8+2*t^6-3*t^4+2*t^2-1)/(t^6-3*t^4+3*t^2-1),
  (1+t^10)/((1-t^2)^2*(1-t^4))
];
assert expected[1] ne expected[2];
for i in [1..3] do
  row := report[i];
  assert #row eq 4 and row[2];
  assert row[3] eq (i le 2 select expected[i] else &+expected);
  assert row[3] eq row[4];
  assert Parent(row[3]) cmpeq Parent(report[1][3]);
  assert Parent(row[4]) cmpeq Parent(report[1][3]);
end for;

sane, reversed := VerifyCanonicalRingComponents(label, Reverse(components));
assert sane;
assert reversed eq [report[2], report[1], report[3]];
swapped := [<components[1][1], components[2][2]>,
            <components[2][1], components[1][2]>];
sane, swapped_report := VerifyCanonicalRingComponents(label, swapped);
assert not sane;
assert #swapped_report eq 3;
for i in [1..2] do
  assert not swapped_report[i][2];
  assert swapped_report[i][3] eq expected[i];
  assert swapped_report[i][4] eq expected[3-i];
end for;
assert swapped_report[3] eq report[3];
print "PASS unequal-series baseline, order reversal and swapped ideals";

I := components[2][2];
R := Generic(I);
assert not (R.1 in I);
corrupted := [components[1], <components[2][1], I + ideal<R | R.1>>];
sane, corrupted_report := VerifyCanonicalRingComponents(label, corrupted);
assert not sane and #corrupted_report eq 3;
assert corrupted_report[1] eq report[1];
assert not corrupted_report[2][2] and not corrupted_report[3][2];
assert corrupted_report[2][3] eq report[2][3];
assert corrupted_report[2][4] ne corrupted_report[2][3];
assert corrupted_report[3][4] eq corrupted_report[1][4] + corrupted_report[2][4];
print "PASS added homogeneous relation changes singleton and combined series";

// The norm-four ideal is in the principal narrow class, but is a different ideal.
relabeled := [<"4.1", components[1][2]>, components[2]];
sane, relabeled_report := VerifyCanonicalRingComponents(label, relabeled);
assert sane and relabeled_report[1][1] eq "4.1";
assert relabeled_report[1][3] eq report[1][3];
bad_inputs := [
  <[], "exactly one component per narrow ideal class">,
  <components[1..1], "exactly one component per narrow ideal class">,
  <[components[1], components[1]], "Duplicate component label">,
  <[components[1], <"999.999", components[2][2]>], "Unknown component label">,
  <[components[1], <"4.1", components[2][2]>], "same narrow ideal class">
];
for entry in bad_inputs do
  rejected := false;
  try
    _ := VerifyCanonicalRingComponents(label, entry[1]);
  catch e
    rejected := entry[2] in Sprint(e);
  end try;
  assert rejected;
end for;
print "PASS missing, duplicate, unknown and same-class labels rejected";

for other_label in ["2.2.13.1-1.1", "2.2.21.1-1.1"] do
  other_components := LoadStoredCanonicalRings(other_label);
  sane, other_report := VerifyCanonicalRingComponents(other_label, other_components);
  assert sane and #other_report eq #other_components + 1;
  assert [row[1] : row in other_report] eq
    [c[1] : c in other_components] cat ["all"];
end for;
print "PASS one component and nonprincipal component label 3.1";
print "PASS component Hilbert series";
