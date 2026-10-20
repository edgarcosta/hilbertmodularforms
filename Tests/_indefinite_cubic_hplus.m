// test-time: ~10-45 min (variable) -- QUARANTINED: excluded from CI (leading "_")
//
// Targeted regression guard for the narrow class number > 1 fixes in
// ModFrmHil/level.m (robust H^1 lift via the quotient map, and an in-order
// element of norm -1 for the plus involution).
//
// The disc-1556 cubic (h+ = 2) at weight 4 is the documented field where the
// indefinite algorithm used to nondeterministically assert (see the comment in
// Tests/cubic_dimension_battery.m). Reproducing the failure requires BOTH h+ > 1
// AND a fundamental domain complex enough for the field-valued H^1 to be large
// (here the cuspidal dimension is 90); smaller h+ > 1 fields (e.g. disc 229) do
// not trip it. The failure is nondeterministic (it depends on the randomly
// constructed ideal-class orders and the quaternion-algebra presentation), so we
// run several fresh computations; before the fix this failed in roughly a third
// to two thirds of runs.
//
// This is slow and its runtime is highly variable (the splitting field chosen
// for the weight representation can be degree 12, 24, or 48 depending on the
// random presentation -- see the note on Splittings), which is why it is
// quarantined out of CI. Run it manually after touching the h+ > 1 indefinite
// path:  magma filename:=Tests/_indefinite_cubic_hplus.m exitsignal:='' run_tests.m

R<x> := PolynomialRing(Rationals());

for iter in [1..5] do
  F := NumberField(x^3 - 2*x^2 - 8*x - 2); // disc 1556, h+ = 2
  ZF := Integers(F);
  assert NarrowClassNumber(F) eq 2;
  M := HilbertCuspForms(F, 1*ZF, [4, 4, 4]);
  assert not IsDefinite(M);
  assert Dimension(M) eq 90;
end for;
