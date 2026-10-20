# Handoff: order > 2 nebentypus for the definite method

Status as of this branch (`def-nonpar-integrate`): **order-2 (quadratic) paritious
nebentypus works and is stable**; **order > 2 is diagnosed but not yet working**. This
doc records the precise findings so the remaining (deep) work can be picked up later.

All experiments below are over `F = Q(sqrt5)`, level `N = 14*ZF = (2)(7)`, with an
**order-3** Hecke character `chi` (conductor `(7)`, norm 49), parallel weights `[2,2]`
and `[4,4]`, computed via the **definite** method.

## What already works and is committed

- Order-2 paritious nebentypus: `par_wt_neb_def`, `old_quad_neb_def`, `forms_new_at_d`,
  `p1_gl2_coset_reps`, `def_vs_indef_neb` all pass, deterministically (checked `old_quad`
  gives `#Sk = 4` across 6 seeds).
- **Bug A (fixed, commit `730bf38`):** `Dimension(M : UseFormula)` used the
  `DefiniteClassNumber` formula for every parallel-weight-2 space, but that formula ignores
  the Dirichlet character and is only valid for trivial nebentypus (it returned 5 instead of
  the true 3 for `S_[2,2](14, chi)`). Now gated to trivial character; nebentypus reads the
  dimension off the (character-twisted) basis matrix.
- **Bug B1 field-forcing (fixed, commit `88679db`):** `SetRationalBasis` forced
  `hecke_matrix_field := Rationals()` for every weight-2 space; an order>2 nebentypus has its
  Hecke algebra over `Q(zeta_d)`, so this is now gated on `Order(chi) le 2`.
- **PR #535 absorbed (commit `d313de0`):** `Components.m` StrongCoerces unit-character values
  before multiplying; `IsStrongCoercible` no longer blindly trusts the `L!x` fast path. Fixes
  the "Arguments are not compatible" / "hom: element not in codomain" coercion symptom on the
  Hecke-stability / coefficient path.

## Confirmed facts about the Eisenstein subspace (verified empirically)

- **No Eisenstein series at nontrivial nebentypus** (parallel wt 2, Gamma_0(N)): the
  `(Np+1)`-eigenspace of the big Hecke operators is 0 for order-3 chars. So the raw definite
  space is already cuspidal for nebentypus; the existing "no removal" (`else`) branch is
  correct. (Reason: Eisenstein <-> a narrow class char `eta` with `eta o nrd` matching chi on
  `\hat{O}^x`, but `nrd(\hat{O}^x)` is trivial under any narrow class char, forcing chi trivial.)
- **`dim Eisenstein = #NarrowClassGroup`** at trivial character: verified `raw - cusp = #Cl`
  on Q(sqrt10) (h+=2) and Q(sqrt15) (h+=4).

## Confirmed facts about the coefficient field

- The Hecke **characteristic polynomial is defined over `Q(zeta_d)`** (verified: for
  `S(14, chi order 3)` the charpoly coefficients strong-coerce into `Q(zeta_3)` at both [2,2]
  and [4,4]; factor degrees over the big field are [1,1] and [9,9]). So
  `minimal_hecke_matrix_field = Q(zeta_d)` is the correct minimal field: for parallel weight
  the weight-preserving automorphisms fix `F' = Q`, so minimal `= compositum(Q, Q(zeta_d)) =
  Q(zeta_d)` (cf. `DefaultCoefficientRing` in `ModFrmHilD/Space.m`). The eigenforms themselves
  may have coefficients in a larger field; it's the matrices/algebra that live over `Q(zeta_d)`.

## The two remaining blockers

### Blocker 1 (weight 2, order > 2): nondeterminism in `hecke_algebra`

After Bug A + B1, the coefficient field is correct, but `NewCuspFormBasis` for
`S_[2,2](14, chi order 3)` is **nondeterministic** (depends on the Magma seed). Across 10
seeds: ~5 succeed but with **inconsistent dimension (sometimes #=2, sometimes #=3)**, and the
rest crash with either "Eigenform: the space M is not an irreducible module" or "hom: element
is not in the codomain of the map".

Root cause: `hecke_algebra` (`ModFrmHil/hecke.m`) finds the Hecke-algebra dimension and a
cyclic vector via a **random mod-P reduction** (`reduction_mod_random_large_split_prime`,
`dimension_lower_bound`). How the random prime `P` splits in `Q(zeta_d)` changes the reduction,
so the computed dimension/decomposition is unreliable over a cyclotomic coefficient field.
The direct `NewformDecomposition` on a freshly-built `S` (via `HilbertCuspForms(F,N,chi,k)`)
DID split cleanly into irreducible pieces in one probe, which is consistent with "it works for
some random choices and not others."

OPEN QUESTION for you (you flagged it): **is the true dimension 2 or 3?** The two order-3
chars at N=14 gave rawdims 2 and 3 in one experiment; the nondeterminism muddies which is
correct for this specific char. Determining the true cusp dimension (e.g. via the def-vs-indef
new-at-pp oracle, or a reliable computation) is the first step.

Likely fix direction: make the reduction prime `P` split-compatible with `Q(zeta_d)` (choose
`P` that splits completely in `Q(zeta_d)`, or reduce the `Q(zeta_d)`-structure correctly), so
`dimension_lower_bound` is deterministic and correct. Entry points:
`ModFrmHil/hecke.m: hecke_algebra`, `reduction_mod_random_large_split_prime`,
`dimension_lower_bound`, `reduction`.

### Blocker 2 (weight > 2, order > 2): `rational_basis` doesn't rotate to `Q(zeta_d)`

Separate from Blocker 1. At weight > 2 the big field is `weight_base_field (x) Q(zeta_d)`
(degree 8 in the [4,4] example), and the raw Hecke matrix entries genuinely live there —
they are only *conjugate* (not entry-wise equal) to a `Q(zeta_d)`-form (confirmed: a failing
entry has minpoly degree 8 with 0 roots in `Q(zeta_3)`). `rational_basis`
(`ModFrmHil/hecke.m`) spins a cyclic vector but does not produce a `Q(zeta_d)`-rational basis,
so the descent `change_hecke_matrix_ring(deg 8 -> Q(zeta_d))` fails ("hecke_matrix_field
seems to be wrong").

Why order-2 and nonparallel-trivial work but this doesn't: in those cases the raw matrices are
*already* entry-wise in the minimal field (order-2 entries are rational; nonparallel-trivial
land in the minimal field naturally), so the early-return in `SetRationalBasis` just coerces.
Order>2 nebentypus is the first case that genuinely needs a *rotation* to the minimal field,
which no current code path performs.

Two candidate fixes:
1. Rationalize `rational_basis` to the minimal field (classical rational-form-over-minimal-
   field): choose a `Q(zeta_d)`-rational cyclic vector / rotate so the spun matrices land over
   `Q(zeta_d)`. Keeps matrices small (performant) but edits core shared machinery.
2. Keep matrices over the big field and teach `Eigenform` (`ModFrmHil/finitefield.m`) to
   factor the (reducible-over-big-field) charpoly over `Q(zeta_d)` to extract newform orbits,
   instead of requiring irreducibility over the current field. Avoids rewriting
   `rational_basis` but leaves matrices over a bigger field.

Blocker 2 is gated behind Blocker 1 (the random-reduction nondeterminism bites first).

## How to reproduce

```
load "config.m";
F := QuadraticField(5); ZF := Integers(F);
Mgr := GradedRingOfHMFs(F, 100);
N := 14*ZF; H := HeckeCharacterGroup(N,[1,2]);
chi := [c : c in Elements(H) | Order(c) eq 3][1];  // order 3, conductor (7)
// weight 2 (Blocker 1 -- try several SetSeed(s) to see nondeterminism):
B := CuspFormBasis(HMFSpace(Mgr, N, [2,2], chi));
// weight 4 (Blocker 2 -- descent failure):
B := CuspFormBasis(HMFSpace(Mgr, N, [4,4], chi));
```
