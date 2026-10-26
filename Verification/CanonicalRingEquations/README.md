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

- **stored-series:** The in-tree regression checks component labels, stored
  variable weights, structural guards, and singleton/full Hilbert series.
  This checks the stored presentation's structure and dimensions.
  It does not evaluate relations on generator q-expansions or prove
  algebraic independence.
- **generated:** The stored file records the exporter's algebraic-independence
  and Hilbert-series results in comments.
  The exporter in `ModFrmHilD/CanonicalRing/IO.m` also evaluates relations on
  generator q-expansions before writing equations.
  Reloading the equations cannot repeat those evaluations: the equation files
  contain neither the generator q-expansions nor the independence certificates.
- **literature-isomorphism:** `VerifyGradedIsomorphism` checks a witness and
  its inverse for the selected component and literature ring.
  An unsuccessful witness search is inconclusive.

The component verifier checks Hilbert series.
The regression adds checks for nondecreasing variable weights and the absence
of bare linear generator terms in the stored relations.
For a single relation, it also requires degree at least two in the
variable of greatest weight.
These structural guards do not establish that the equations define the
claimed modular forms.
Mixed linear terms in a multi-relation ideal alone do not establish elimination.

### Current h+=2 evidence

For each discriminant D, the file is `2.2.<D>.1-1.1-gl-0.m` in this directory.
The evidence column describes checks in
[Tests/verification_canonical_rings.m](../../Tests/verification_canonical_rings.m)
and comments in the stored files.
The hashes identify the exact equation files described here.

| D | Labels | Evidence a reader can check | Source SHA256 |
|---|---|---|---|
| 12 | 1.1, 2.1 | UNVERIFIED / SCRAMBLED: the regression expects matching singleton/full series, but both components fail the structural guards. Both have weights `[2,14,4,6]` and a relation linear in the weight-14 variable. | `6a2111010443229a9670575e582ba1caf6a875b8f8904174daeb192417f0e637` |
| 21 | 1.1, 3.1 | stored-series: The regression checks both components' weights, structural guards, and singleton/full series. Swapping the ideals between labels fails the singleton comparisons. The file retains a historical STALE header. | `de7d3cd63616e713b49ccfc4d7100115088e47933c61d202ec3e38e7a7fa6cd7` |
| 24 | 1.1, 2.1 | stored-series: The regression checks both components' weights, structural guards, and singleton/full series. Swapping the ideals between labels fails the singleton comparisons. The file retains a historical STALE header. | `2551928b334e82d6101cea8ed6136d40d88142b82a65c7809978c2ef5f072bd6` |
| 28 | 1.1, 3.1 | stored-series: The regression checks both components' weights, structural guards, and singleton/full series. Swapping the ideals between labels fails the singleton comparisons. The file retains a historical STALE header. | `705c8e5e516784e237cfb6982b18bba6b4f84babc74d84a04981966f9c3fe885` |
| 33 | 1.1, 2.1 | generated: The file records algebraic independence verified and Hilbert series agreeing. The regression checks both components' weights, structural guards, singleton/full series, and rejection of swapped ideals. | `ac28bf14a5620836f8e89ea6c6faa9217f983916b4c10029047f6eec409dd669` |

The historical `STALE` headers and `// Sanity check failed!` comments record
comparisons made before the h+>1 Hilbert-series fix.
The regression expects matching series for all five fields, including D=12.
D=12 remains unverified because its stored presentation fails the structural guards.

No literature-isomorphism witness for D=12/21/24/28/33 is supplied here.

## Reproducing the stored checks

Run the in-tree regression from the checkout root:

```sh
magma -b filename:=Tests/verification_canonical_rings.m exitsignal:='' run_tests.m
```

It checks the stored variable order, structural guards and singleton/full
series for D=12/21/24/28/33, plus unequal-series swaps for D=21/24/28/33.
Its expected output includes `UNVERIFIED D=12 SCRAMBLED; singleton/full series pass`
and `PASS stored-series D=<D> components=2` for D=21/24/28/33.
Those lines describe stored-data checks, including for the generated D=33 file.
The test also checks the single-component files and recomputes the D=13
level-1 ring with `HilbertModularVariety`.

To compare the equation files with the hashes above, run from the checkout root:

```sh
sha256sum Verification/CanonicalRingEquations/2.2.12.1-1.1-gl-0.m \
  Verification/CanonicalRingEquations/2.2.21.1-1.1-gl-0.m \
  Verification/CanonicalRingEquations/2.2.24.1-1.1-gl-0.m \
  Verification/CanonicalRingEquations/2.2.28.1-1.1-gl-0.m \
  Verification/CanonicalRingEquations/2.2.33.1-1.1-gl-0.m
```

A matching hash identifies the stored source; it does not certify the equations.

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
| `2.2.21.1-1.1-gl-0.m` | Q(sqrt(21)) | 1 | 2 (1.1, 3.1); stored-series checks listed above; historical STALE header. |
| `2.2.24.1-1.1-gl-0.m` | Q(sqrt(6)) | 1 | 2 (1.1, 2.1); stored-series checks listed above; historical STALE header. |
| `2.2.28.1-1.1-gl-0.m` | Q(sqrt(7)) | 1 | 2 (1.1, 3.1); stored-series checks listed above; historical STALE header. |
| `2.2.29.1-1.1-gl-0.m` | Q(sqrt(29)) | 1 | 1 |
| `2.2.33.1-1.1-gl-0.m` | Q(sqrt(33)) | 1 | 2 (1.1, 2.1); exporter results recorded in file comments; stored-series checks listed above. |
| `2.2.37.1-1.1-gl-0.m` | Q(sqrt(37)) | 1 | 1 |
| `2.2.41.1-1.1-gl-0.m` | Q(sqrt(41)) | 1 | 1 |

### Stale (needs regeneration)

D=12's singleton and full series match after the h+>1 Hilbert-series fix,
but its variable order is scrambled, as described in the h+=2 evidence table above.
The stored header records a failed historical series check and a regeneration
blocker at `precompute.m:1064`; the regression checks the structural failure.

| File | Field | Level | h+ | Issue |
|------|-------|-------|----|-------|
| `2.2.12.1-1.1-gl-0.m` | Q(sqrt(3)) | 1 | 2 | UNVERIFIED / SCRAMBLED; structural guards fail |
