# Canonical Ring Equations

Thanks for helping verify these stored canonical rings.
The files contain equations for Hilbert modular surfaces, exported by
`WriteCanonicalRingComputationToFile` (see `ModFrmHilD/CanonicalRing/IO.m`).
Each narrow-class component defines a weighted projective scheme `S`.
A later component overwrites `S`, so load all components with the plural API.

## Loading and checking components

Run from the checkout root after attaching the package:

```magma
AttachSpec("spec");
label := "2.2.24.1-1.1";
components := LoadStoredCanonicalRings(label);
sane, report := VerifyCanonicalRingComponents(label, components);
```

`LoadStoredCanonicalRings(label::MonStgElt) -> SeqEnum` returns
`[<component_label, ideal>, ...]` in file order, including a length-one sequence
for a single component. Each ideal retains its stored polynomial parent, weights,
and coefficients. The loader reads trusted Magma source from
`Verification/CanonicalRingEquations/<label>-gl-0.m`.
It requires unique component labels, matching field/level/group metadata and
one complete scheme per component.

`LoadStoredCanonicalRing(label::MonStgElt) -> RngMPol` is the compatibility
wrapper for single-component files. It returns the sole ideal and rejects
files with multiple components.

`VerifyCanonicalRingComponents(label::MonStgElt, components::SeqEnum)
-> BoolElt, SeqEnum` requires exactly one homogeneous ideal per narrow ideal
class. It resolves each label to its actual ideal class, regardless of input order.
Labels need not be consecutive: D=21 and D=28 use `1.1` and `3.1`.
Missing, duplicate, unknown, and repeated-class entries raise errors.
Another ideal label representing the same class is accepted if coverage remains
complete and distinct.

The report contains `<label, sane, H_trace, H_test>` rows in input order,
followed by an `"all"` row. The boolean is true exactly when every row agrees.
Each singleton series has constant 1; the full sum has constant `h+`, the narrow
class number. Compare each ideal with its own singleton trace series and the
sum with the full-support series, without dividing by `h+`.
Reordering intact pairs preserves the result. Swapping ideals between labels
is detected when their singleton series differ; equal series cannot detect a
swap, as in D=12.

## Evidence kinds

- **stored-series:** the installed source SHA256 matches a complete ordered
  recheck, and fresh singleton/full Hilbert-series comparisons agree.
  Weights must be nondecreasing and applicable linear-generator guards must
  hold. This certifies components under the stored-data contract.
  Historical q-expansion relation evaluations and algebraic-independence
  certificates are unavailable; these checks do not recreate them.
- **generated:** a new export retains relation evaluations on generator
  q-expansions in exact exported order and an algebraic-independence certificate.
  Independent reload checks complete class coverage, structure, and all series.
  Records retain source/output hashes, backend, precision, bounds, and resources.
- **literature-isomorphism:** `VerifyGradedIsomorphism` checks a stored witness
  and its inverse for the selected component and literature ring.
  This is separate from series certification. An unsuccessful witness search
  is inconclusive.

The component verifier checks series, not generator order or equation provenance.
The ordered recheck records variable weights, relation degrees in each variable,
applicable linear-generator guards, labels, singleton/full series and source SHA256.
For a single relation, the recheck requires degree at least two in the
top-weight variable. This is a structural guard used by the recheck.
Mixed linear terms in a multi-relation ideal alone do not establish elimination.
Both D=12 components have weights `[2,14,4,6]` and a hypersurface relation linear
in the weight-14 variable. They remain `UNVERIFIED` / `SCRAMBLED` despite matching
series. Regeneration is pending. Failed, scrambled or missing data require
regeneration; incomplete rechecks remain pending.
A passing ordered stored file can receive stored-series certification without
regeneration or historical exporter certificates.

### Current h+=2 evidence (2026-10-22)

| D | Labels | Evidence | Source SHA256 |
|---|---|---|---|
| 12 | 1.1, 2.1 | UNVERIFIED: SCRAMBLED; regeneration pending | `6a2111010443229a9670575e582ba1caf6a875b8f8904174daeb192417f0e637` |
| 21 | 1.1, 3.1 | stored-series | `de7d3cd63616e713b49ccfc4d7100115088e47933c61d202ec3e38e7a7fa6cd7` |
| 24 | 1.1, 2.1 | stored-series | `2551928b334e82d6101cea8ed6136d40d88142b82a65c7809978c2ef5f072bd6` |
| 28 | 1.1, 3.1 | stored-series | `705c8e5e516784e237cfb6982b18bba6b4f84babc74d84a04981966f9c3fe885` |
| 33 | 1.1, 2.1 | generated | `ac28bf14a5620836f8e89ea6c6faa9217f983916b4c10029047f6eec409dd669` |

The Hilbert-series failure claims in the historical `STALE` headers and
`// Sanity check failed!` lines predate the Hilbert-series fix for h+>1 and are inaccurate.
The old comparison omitted component constants. The equation files remain
unchanged because literature data on another branch bind their SHA256 hashes.
The ordered recheck determines their current status; D=12's structural failure
still requires regeneration.

No literature-isomorphism certificate for D=12/21/24/28/33 is supplied here.
D=12 and D=24 literature examples remain pending until their witness
continuations are integrated. Those continuations adopt the plural loader,
check every component's series, and verify the witness only on the component
matching the literature's group and action.
D=21, D=28 and D=33 have no level-1 literature witness here.

## Reusing the local batch bundle

The in-tree regression [Tests/verification_canonical_rings.m](../../Tests/verification_canonical_rings.m)
repeats the ordered recheck: variable order, structural guards and singleton/full
series for D=12/21/24/28/33, plus unequal-series swaps for D=21/24/28/33.
Run it from the checkout root:

```sh
magma -b filename:=Tests/verification_canonical_rings.m exitsignal:='' run_tests.m
```

The `docs/superpowers/level1-d100/` bundle is local scratch and is not shipped
with the repository. It records field outcomes; its `RUN.md` explains how to
prepare runs, set generation budgets and reuse data.
The bundle and `docs/superpowers/multi-component/recheck-ordered.json` are excluded
from git. Copy them separately to use the following command in another checkout.
With those artifacts present, run from the checkout root:

```sh
python3 docs/superpowers/level1-d100/batch.py verify --D 24 \
  --input Verification/CanonicalRingEquations/2.2.24.1-1.1-gl-0.m \
  --evidence stored --recheck docs/superpowers/multi-component/recheck-ordered.json
```

Stored mode requires a complete passing recheck for the exact input SHA256,
then reloads every component and compares fresh structure and series.
It records `verification_kind=stored-series` under `runs/<D>/<attempt>/record.json`.
Generated mode (`--evidence generated`, the default) requires exporter
certificates and rejects stale/failed headers.
Use it for newly generated candidates. Stored evidence cannot replace exporter
certificates or resume a generation run.
Both modes stage inputs without editing the equation store and retain reload
logs and hashes. The bundle records these results itself.

## File status

### Current (sanity check passes)

| File | Field | Level | Components |
|------|-------|-------|------------|
| `2.2.5.1-1.1-gl-0.m` | Q(sqrt(5)) | 1 | 1 |
| `2.2.5.1-4.1-gl-0.m` | Q(sqrt(5)) | 4.1 | 1 |
| `2.2.5.1-5.1-gl-0.m` | Q(sqrt(5)) | 5.1 | 1 |
| `2.2.8.1-1.1-gl-0.m` | Q(sqrt(2)) | 1 | 1 |
| `2.2.8.1-2.1-gl-0.m` | Q(sqrt(2)) | 2.1 | 1 |
| `2.2.13.1-1.1-gl-0.m` | Q(sqrt(13)) | 1 | 1 |
| `2.2.13.1-3.1-gl-0.m` | Q(sqrt(13)) | 3.1 | 1 |
| `2.2.13.1-4.1-gl-0.m` | Q(sqrt(13)) | 4.1 | 1 |
| `2.2.17.1-1.1-gl-0.m` | Q(sqrt(17)) | 1 | 1 |
| `2.2.21.1-1.1-gl-0.m` | Q(sqrt(21)) | 1 | 2 (1.1, 3.1): stored equations passed each component's Hilbert-series check and the variable-order check. The equations were not regenerated or re-derived; the historical STALE header remains. Historical regeneration: >4h / 50 GB. |
| `2.2.24.1-1.1-gl-0.m` | Q(sqrt(6)) | 1 | 2 (1.1, 2.1): stored equations passed each component's Hilbert-series check and the variable-order check. The equations were not regenerated or re-derived; the historical STALE header remains. Historical regeneration blocker: precompute.m:1064. |
| `2.2.28.1-1.1-gl-0.m` | Q(sqrt(7)) | 1 | 2 (1.1, 3.1): stored equations passed each component's Hilbert-series check and the variable-order check. The equations were not regenerated or re-derived; the historical STALE header remains. Historical regeneration blocker: precompute.m:1064. |
| `2.2.29.1-1.1-gl-0.m` | Q(sqrt(29)) | 1 | 1 |
| `2.2.33.1-1.1-gl-0.m` | Q(sqrt(33)) | 1 | 2 (1.1, 2.1): generated; relation evaluations and algebraic independence checked by the exporter. Independent reload passes variable order and singleton/full series. |
| `2.2.37.1-1.1-gl-0.m` | Q(sqrt(37)) | 1 | 1 |
| `2.2.41.1-1.1-gl-0.m` | Q(sqrt(41)) | 1 | 1 |

### Stale (needs regeneration)

D=12's singleton and full series match after the h+>1 Hilbert-series fix,
but its variable order is scrambled, as described in the h+=2 evidence table above.
Regeneration is pending on a machine with enough memory; earlier runs exceeded
four hours with 64 GB of memory.

| File | Field | Level | h+ | Issue |
|------|-------|-------|----|-------|
| `2.2.12.1-1.1-gl-0.m` | Q(sqrt(3)) | 1 | 2 | stale; regen runs >4h / 64 GB |
