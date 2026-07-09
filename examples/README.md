# Worked examples

Self-contained scripts for the examples in the papers, run in CI exactly like
`Tests/` (the runner and Makefile walk `examples/` too). Heavy cases that exceed
a CI runner live in `examples/slow/` and are skipped by CI; run them manually with
`magma -b filename:=examples/slow/<file>.m exitsignal:='' run_tests.m`.

## Computing with Fourier expansions of Hilbert modular forms

| Paper section | Example | File | Status |
|---|---|---|---|
| Modular curve X0(11) | X0(11) model is an elliptic curve of conductor 11 | `modular_curve_X0_11.m` | CI |
| Igusa invariants | Igusa invariants for Q(sqrt 12) and Q(sqrt 21) | `igusa_invariants.m` | CI |
| Hilbert modular threefolds | cyclic cubic field Q(zeta_7 + zeta_7^-1): trace-formula dimensions (builtin-confirmed through weight 8), Eisenstein + split-prime trace-form model at full precision, exact dependence of the third trace form, sound Jacobian threefold certificate, and relation ideal certified zero through degree 16 (degree 26 in slow/); the formerly displayed degree-16 equations are refuted, with witness pinned in `Tests/cyclic_cubic_threefold_regression.m` | `cyclic_cubic_threefold.m` | CI |
| Hilbert modular threefolds | cyclic cubic relation hunt at precisions 450 and 700: unconditional relation-freeness of the 7-generator model through degree 26, phantom-kernel table (spurious relations at the truncation frontier at every precision), free-count vs dimension table through degree 40 | `slow/cyclic_cubic_threefold_certify.m` | slow (CI-skipped) |
| Hilbert modular threefolds | D=49 level (2) weight 4 defect-to-q-expansion bridge, both cusps: full four-row vanishing matrix via the Fricke involution, rank 4, surviving dimension 2, witnessing the arXiv:2501.15719 positive Kodaira-dimension row | `d49_level2_defect_bridge.m` | CI |
| D=5 | Q(sqrt 5) canonical ring vs Gundlach/Hirzebruch, deterministic witness map | `canonical_ring_Qsqrt5.m` | CI |
| D=8 | Q(sqrt 8) canonical ring vs Hirzebruch double cover (rational sign c^2 = -C), deterministic witness map | `canonical_ring_Qsqrt2.m` | CI |
| D=13 | Q(sqrt 13) canonical ring vs van der Geer-Zagier, deterministic witness map | `canonical_ring_Qsqrt13.m` | CI |
| heavy cases (D=12,21,24,28,33 are h+=2; D=41 is heavy level-1) | end-to-end recompute | `slow/Surface_Qsqrt*.m`, `slow/GradedRing_Qsqrt*.m` | slow (CI-skipped) |

## numerical-invariants paper (LuCaNT)

| Example | File | Status |
|---|---|---|
| Examples 1-4: surface invariants by label | `numerical_surface_invariants.m` | CI |

## X_0(p31) over Q(sqrt 5): a properly elliptic surface with K3 invariants

The prime `p31` above 31 (norm 31, LMFDB `31.2`). The minimal smooth model `Y`
has the numerical invariants of a K3 (`chi=2`, `p_g=1`, `q=0`, `K^2=0`, `e=24`)
yet `kappa(Y)=1`. See the accompanying note `WorkInProgress/X0p31_Qsqrt5.tex`.

| Result | File | Status |
|---|---|---|
| `P_1=1`, `P_2=2`, and the exact `m=2` (multiplicity) certificate --- `M_4 = Sym^2 M_2`, conic-pencil discriminant `l1*l2^2`, rank-1 member `Omega^2` --- hence `kappa=1` and `P_n = 1 + floor(n/2)` | `X0p31_plurigenera.m` | CI |
| Singular-fibre configuration `I_6 + 2 I_4 + I_2 + 8 I_1 + _2I_0`, proved unconditionally over Q: exact `j(t0)` at 72 fibres, exact interpolation of `j(t)=N/D`, and factorization of `D` over Q (height-free, `~1h`) | `slow/X0p31_elliptic_fibres.m` | slow (CI-skipped) |

## Paper Pointer Snippets

Repath the existing Igusa comments in the paper source:

    % For verification of the above formulas, see examples/igusa_invariants.m
    % Code that verifies the above is in examples/igusa_invariants.m

New pointer, after the X0(11) model:

    % Verified in examples/modular_curve_X0_11.m (model is an elliptic curve of conductor 11, isomorphic to X_0(11)).

Canonical-ring worked examples (each certifies our stored ring is graded-isomorphic
over Q to the literature equations, via a stored witness map in
`Verification/LiteratureEquations/` checked deterministically by `VerifyGradedIsomorphism`):

    % Verified in examples/canonical_ring_Qsqrt5.m  (our canonical ring is graded-isomorphic over Q to Hirzebruch's, via a stored witness map).
    % Verified in examples/canonical_ring_Qsqrt2.m  (D=8; Hirzebruch's double cover, rational sign c^2 = -C).
    % Verified in examples/canonical_ring_Qsqrt13.m (van der Geer and Zagier).

All three canonical-ring examples run green in CI; the D=5 stored `CanonicalRingEquations/`
file was regenerated with the sorted-generator-order fix in this branch.
