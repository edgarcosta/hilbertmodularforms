// test-time: ~25s
//
// High-level (ModFrmHilD) interface to the indefinite algorithm: forcing the
// backend via SetAlgorithm / SetQuaternionOrder (the "force the quaternion
// backend/order" feature) must route through ModFrmHil/level.m and agree with
// the default computation, and the guards must hold.
//
// We use a cubic field, where the indefinite algebra has discriminant 1 (no
// ramified finite primes), so the forced order is valid for the full cuspidal
// space that HilbertCuspForms(Mk::ModFrmHilD) builds. (Forcing a *ramified*
// indefinite order -- mandatory over an even-degree field -- is only valid for
// the new subspace, and is covered at the ModFrmHil layer in
// indefinite_quadratic_hplus.m.)

SetSeed(1);

R<x> := PolynomialRing(Rationals());
F := NumberField(x^3 - x^2 - 2*x + 1); // disc 49, h+ = 1
ZF := Integers(F);
assert NarrowClassNumber(F) eq 1;

prec := 50;
N := 1*ZF;
k := [4, 4, 4];

// default backend (indefinite is the default over an odd-degree field)
Mdef := GradedRingOfHMFs(F, prec);
MFdef := HilbertCuspForms(HMFSpace(Mdef, N, k));
ddef := Dimension(MFdef);
assert not IsDefinite(MFdef);
Odef := QuaternionOrder(MFdef);

// SetAlgorithm("Indefinite") routes through the indefinite backend
Malg := GradedRingOfHMFs(F, prec);
Mk_alg := HMFSpace(Malg, N, k);
SetAlgorithm(Mk_alg, "Indefinite");
MFalg := HilbertCuspForms(Mk_alg);
assert not IsDefinite(MFalg);
assert Dimension(MFalg) eq ddef;

// SetQuaternionOrder forces a specific (indefinite) order
Mqo := GradedRingOfHMFs(F, prec);
Mk_qo := HMFSpace(Mqo, N, k);
SetQuaternionOrder(Mk_qo, Odef);
MFqo := HilbertCuspForms(Mk_qo);
assert not IsDefinite(MFqo);
assert Dimension(MFqo) eq ddef;

// Guard 1: setting the backend after the space is computed must fail.
ok := false;
try
  SetQuaternionOrder(Mk_qo, Odef);
catch e
  ok := true;
end try;
assert ok;

// Guard 2: SetAlgorithm only accepts a valid algorithm name.
Mbad := GradedRingOfHMFs(F, prec);
Mk_bad := HMFSpace(Mbad, N, k);
ok := false;
try
  SetAlgorithm(Mk_bad, "Bogus");
catch e
  ok := true;
end try;
assert ok;
