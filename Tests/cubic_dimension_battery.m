// test-time: ~4 min. Thorough validation of the degree > 2 trace-formula dimension fix.
// Runs in parallel with Tests/cubic_trace_dimension.m (the focused regression), which
// carries the full diagnosis. The fix rewires the nonprecomp local optimal-embedding count
// in ModFrmHilD/Trace/Trace.m to the Hijikata closed form OptimalEmbeddings already used by
// the precomp path.
//
// This file deliberately does NOT cross-check against builtin HilbertCuspForms: that backend
// is flaky for some of these fields (e.g. the disc-1556 narrow-class-number-2 cubic at weight
// 4 nondeterministically returns 90 or fails an internal assertion in ModFrmHil/level.m).
// Instead it uses the deterministic invariant nonprecomp == precomp together with dimensions
// pinned to values verified against builtin on the (stable) runs where builtin succeeded.

Pb<xb> := PolynomialRing(Rationals());

// (1) Unification invariant (nonprecomp == precomp AND integer) across cubic and quartic
//     fields at levels (1) and (2), with a few weight-2/4 level-(2) dimensions pinned to
//     their verified builtin values. Combined with the separately verified precomp == builtin
//     (see the reviews / scratch), this gives nonprecomp == builtin everywhere.
//     <defining poly, degree, [<k, verified cusp dim at level (2)>]>
battery := [*
  <xb^3 - xb^2 - 2*xb + 1,        3, [<2, 0>, <4, 4>]>,   // Q(zeta_7)^+ (disc 49, order-7)
  <xb^3 - 3*xb - 1,               3, [<2, 1>, <4, 7>]>,   // Q(zeta_9)^+ (disc 81, order-9)
  <xb^3 - xb^2 - 3*xb + 1,        3, [<2, 1>, <4, 28>]>,  // non-Galois cubic (disc 148)
  <xb^3 - xb^2 - 4*xb - 1,        3, [<2, 1>, <4, 21>]>,  // cyclic cubic (disc 169)
  <xb^4 - xb^3 - 3*xb^2 + xb + 1, 4, [<2, 1>, <4, 24>]>   // totally real quartic (disc 725)
*];
for spec in battery do
  Fb := NumberField(spec[1]); ZFb := Integers(Fb); degb := spec[2];
  Rb := GradedRingOfHMFs(Fb, 1);
  HMFTracePrecomputation(Rb, [1*ZFb] : SaveAndLoad := false);
  exp2 := AssociativeArray();
  for pr in spec[3] do exp2[pr[1]] := pr[2]; end for;
  weightsb := (degb eq 3) select [2, 4, 6, 8] else [2, 4];
  for NNb in [1*ZFb, 2*ZFb] do
    for kb in weightsb do
      Mkb := HMFSpace(Rb, NNb, [kb : ib in [1..degb]]);
      tfb := Trace(Mkb, 1*ZFb : precomp := false);
      tpb := Trace(Mkb, 1*ZFb : precomp := true);
      assert tfb eq tpb;                          // the two implementations are now unified
      assert Denominator(Rationals()!tfb) eq 1;   // and integer-valued
      if NNb eq 2*ZFb and IsDefined(exp2, kb) then
        assert Rationals()!tfb eq exp2[kb];       // pinned to the verified builtin value
      end if;
    end for;
  end for;
end for;

// (2) Hecke traces (mm != 1): nonprecomp == precomp for cubics whose *dimensions* were
//     already correct before the fix. The old local miscount also affected general CM orders
//     appearing for mm != 1 at their 2-inert prime, so these are non-vacuous.
for polh in [* xb^3 - 3*xb - 1, xb^3 - xb^2 - 4*xb - 1 *] do  // Q(zeta_9)^+, cyclic169
  Fh := NumberField(polh); ZFh := Integers(Fh);
  Rh := GradedRingOfHMFs(Fh, 1);
  mmsh := [];
  for ph in [3, 5, 7] do
    for prh in [th[1] : th in Factorization(ph*ZFh)] do
      if Norm(prh) le 60 then Append(~mmsh, prh); end if;
    end for;
  end for;
  mmsh := mmsh[1..Min(3, #mmsh)];
  HMFTracePrecomputation(Rh, [1*ZFh] cat mmsh : SaveAndLoad := false);
  for mmh in mmsh do
    for kh in [2, 4] do
      Mkh := HMFSpace(Rh, 2*ZFh, [kh, kh, kh]);
      assert Trace(Mkh, mmh : precomp := false) eq Trace(Mkh, mmh : precomp := true);
    end for;
  end for;
end for;

// (3) The local optimal-embedding number is residue-degree agnostic. At an even inert prime
//     that splits in the CM extension, the optimal embedding number is 1 + A = 2 regardless
//     of the residue field; this is exactly the value the old hardcoded polynomial (Phi_3
//     mod 2) failed to produce over odd-degree residue fields. Checked at residue degrees
//     3 (q = 8) and 5 (q = 32).
F7 := NumberField(xb^3 - xb^2 - 2*xb + 1);
pp8 := Factorization(2*Integers(F7))[1][1];
assert Norm(pp8) eq 8;
assert OptimalEmbeddings(1, 0, 0, 1, pp8) eq 2;
F11 := NumberField(xb^5 + xb^4 - 4*xb^3 - 3*xb^2 + 3*xb + 1); // Q(zeta_11)^+, 2 inert
pp32 := Factorization(2*Integers(F11))[1][1];
assert Norm(pp32) eq 32;
assert OptimalEmbeddings(1, 0, 0, 1, pp32) eq 2;

// (4) Narrow class number > 1 cubic (disc 1556, h+ = 2): the two trace paths agree and are
//     integer-valued, and the dimensions verified against builtin (on runs where builtin did
//     not crash) are pinned. This exercises the narrow-class-group averaging with the degree
//     fallback removed.
Fnc := NumberField(xb^3 - 2*xb^2 - 8*xb - 2); ZFnc := Integers(Fnc);
assert Discriminant(ZFnc) eq 1556;
assert NarrowClassNumber(Fnc) eq 2;
Rnc := GradedRingOfHMFs(Fnc, 1);
HMFTracePrecomputation(Rnc, [1*ZFnc] : SaveAndLoad := false);
verified := AssociativeArray();
verified[<1, 2>] := 0; verified[<1, 4>] := 90; verified[<8, 2>] := 34; // <Norm(NN), k> -> cusp dim
for NNnc in [1*ZFnc, 2*ZFnc] do
  for knc in [2, 4] do
    Mknc := HMFSpace(Rnc, NNnc, [knc, knc, knc]);
    tf := Rationals()!Trace(Mknc, 1*ZFnc : precomp := false);
    tp := Rationals()!Trace(Mknc, 1*ZFnc : precomp := true);
    assert tf eq tp;
    assert Denominator(tf) eq 1;
    key := <Norm(NNnc), knc>;
    if IsDefined(verified, key) then assert tf eq verified[key]; end if;
  end for;
end for;
