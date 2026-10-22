# Coefficient fields, Hecke-matrix fields, and coercion in ModFrmHil / ModFrmHilD

A field guide to the number-field plumbing around Hilbert modular forms in this repo, written
after long debugging sessions on the descent-to-minimal-field, nebentypus-coercion, and
eigenbasis-optimization performance work. It focuses on **ModFrmHil** (`hecke_field.m`, `hecke.m`,
`finitefield.m`, `diamond.m`, `weight_rep.m`) with the relevant **ModFrmHilD** bits (`FldExt.m`,
`Components.m`, `Space.m`) where they interact.

This is the single canonical reference for this subsystem; it supersedes the former
`NONPARITIOUS_COERCION_HANDOFF.md` and `PERF_COERCION_HANDOFF.md` (folded in here). The
`BUG_cubic_paritious_nonparallel.md` / `BUG_nonparallel_findings.md` files are separate historical
investigation logs, not reference material.

If you remember one thing: **most of the bugs in this area are the same bug** — two number fields
that are *abstractly isomorphic but are different Magma objects*, or the *wrong Galois conjugate*
getting chosen when coercing between fields. `StrongCoerce` exists to pin the conjugate, but it has
sharp edges (below), so the code is **parity-gated**: paritious weights pin via marked archimedean
places, nonparitious weights pin via the hand-built embedding. That gate is deliberate and correct,
not a wart — see §5.

---

## 0. The one cross-cutting problem

Magma does **not** auto-coerce between two independently-constructed number fields, even when:
- they have the **same defining polynomial**, or
- one is abstractly a subfield of the other.

You get either `Runtime error in '!': Arguments are not compatible`, or
`Runtime error: Arguments are not compatible` (for `*`/`+`), or — worse — a *silent* wrong answer
where `L!x` or `Roots` picks a different Galois conjugate than you meant.

Almost every symptom in this subsystem (`FldNumElt[FldRat]` incompatibility,
`hecke_matrix_field seems to be wrong`, products "escaping" the target space, `Compositum`
"must be normal") is a manifestation of this. Keep it front of mind.

---

## 1. StrongCoerce and marked places (ModFrmHilD/FldExt.m)

`StrongCoerce(L, x)` is the project's "correct" coercion. It does **not** trust Magma's `!`.
Instead it:
1. takes `MinimalPolynomial(x)`,
2. finds its roots in `L`,
3. picks the root whose value at `MarkedEmbedding(L)` numerically matches `x`'s value at
   `MarkedEmbedding(Parent(x))` (see `IsStrongCoercible`).

`MarkedEmbedding(K)` (FldExt.m) is a *distinguished infinite place* of `K`, **defaulting to
`InfinitePlaces(K)[1]`**, cached on `K`MarkedEmbedding`. The whole point is that whenever we pick
"the" embedding of a field we pick the same one, so conjugate choices are consistent across
independently-built fields.

**Consequences / gotchas:**
- StrongCoerce is only as good as the two marked places. If a field's marked place isn't the one
  the rest of the computation assumes, StrongCoerce silently returns the **wrong conjugate** — this
  is exactly the nonparitious issue (§5).
- StrongCoerce is **slow** relative to `@@ emb` or `!`: it computes `Roots` over `L` **per element**.
  On big fields (e.g. the degree-12 `K(√z)` nonparitious field) and large matrices this is a real
  performance problem. Prefer a precomputed embedding in hot paths — see §3 and §6.
- **The element cache is now an `AssociativeArray`** keyed by the element `x` (value: short list of
  `<L, r>` pairs matched by `IsIdentical` on `L`). It used to be a flat `[* <L,x,r> *]` list scanned
  linearly on every call — O(n²) over a descent that coerces n distinct elements, and it grew
  without bound. The AssociativeArray makes lookup O(1); semantics are unchanged (distinct
  conjugates key separately; distinct field objects sharing a defining poly still disambiguated by
  `IsIdentical`). This was part of the PR #533 performance fix (§6).
- `IsStrongCoercible` had a **fast-path bug**: "if `K` and `L` share a defining polynomial and are
  isomorphic, `return true, L!x`" — but `L!x` still throws for independently-constructed isomorphic
  fields. Fixed (PR #535) by only trusting `L!x` when it succeeds, else falling through to
  root-matching. If you see StrongCoerce itself throwing `in '!'`, this is why.

---

## 2. The field hierarchy in ModFrmHil

For a space `M` (non-parallel weight), three fields matter, biggest to smallest:

1. **`weight_base_field`** (`M`weight_base_field`, set in `hecke_field.m` `WeightRepresentation`):
   the big field `K` over which the weight representation / splitting is defined. Absolute,
   optimized, contains the Galois closure of the base field `F` and the splitting data of the
   quaternion algebra. Raw Hecke operators are born here (or over `K(√z)`, §5).

2. **`hecke_matrix_field(M)`** (`hecke_field.m`): the field the Hecke matrices "currently" live
   over. For **paritious** weight this is just `weight_base_field`. For **nonparitious** weight it
   is the quadratic extension `K(√z)` (§5).

3. **`minimal_hecke_matrix_field(M)`** (`hecke_field.m`): the *smallest* field the Hecke matrices
   can be descended to — a subfield of `Kgal = F`SplittingField[1]` fixed by the subgroup of `Gal`
   stabilizing the weight. This is what `M`hecke_matrix_field` becomes after `SetRationalBasis`, and
   what the operators are stored over for performance.

The **descent** (big → minimal) is where the subtlety lives.

### The embeddings that make descent work
- `M`splitting_field_emb_weight_base_field` : `Fspl -> weight_base_field` (set in
  `WeightRepresentation`).
- `M`minimal_hecke_field_emb` : `minimal_hecke_matrix_field -> (big field)` (set in
  `minimal_hecke_matrix_field`, as `splitting_field_emb_weight_base_field * emb_fixed`, where
  `emb_fixed` comes from `IsSubfield(H, Kgal)`).
- `M`strong_descent_embs` : an `Assoc` cache of marked-place-consistent embeddings used by the
  paritious descent (§3).

`SetRationalBasis` (`hecke.m`) does the descent: computes `H := minimal_hecke_matrix_field(M)`, sets
`M`hecke_matrix_field := H`, and coerces every cached Hecke matrix/charpoly down via
`change_hecke_matrix_ring` / `change_hecke_polynomial_ring`.

---

## 3. The descent coercion: `change_hecke_matrix_ring` (hecke.m)

Called from `operator()` (`diamond.m`) and `SetRationalBasis` to push a Hecke matrix `T` from its
current (big) ring into `H` (minimal). It is **parity-gated**:

```
if is_paritious(Weight(M)) then
    // build the marked-place-consistent embedding ONCE and descend by preimage:
    emb := strong_descent_emb(M, H, BaseRing(T));   // = hom<H -> K | StrongCoerce(K, H.1)>, cached
    return [ x @@ emb : x in Eltseq(T) ];           // + per-element-StrongCoerce + CanChangeRing fallbacks
else (nonparitious)
    return [ x @@ M`minimal_hecke_field_emb : x in Eltseq(T) ]   // the stored embedding's preimage
```

**Why parity-gated, and why it is not a style choice:**
- For **paritious** multi-orbit spaces, the plain `x @@ minimal_hecke_field_emb` path picks an
  **arbitrary** Galois conjugate (the `IsSubfield`-derived `emb` is an arbitrary conjugate),
  producing **non-commuting** descended operators on the harder cases. Pinning the conjugate via the
  marked places (StrongCoerce) fixes it. (Empirically: at `f9fcfcc2` plain `@@emb` passes the
  quadratic product test but **fails** the cubic one.)
- For **nonparitious** spaces, StrongCoerce picks the **wrong** conjugate (§5 — the k₀ place), while
  `x @@ minimal_hecke_field_emb` is correct. StrongCoerce is also ~20× slower there.

**Performance note (how the paritious branch is written):** the conjugate pinning *was* a
per-element `StrongCoerce` (each call does `Roots` over the target field and populates the element
cache). That is what ballooned memory (§6). The current code builds the marked-place embedding
**once** from the generator — `strong_descent_emb = hom<H -> K | StrongCoerce(K, H.1)>` — and
descends with the cheap preimage `x @@ emb`. This is **mathematically identical** to per-element
`StrongCoerce(H, x)` for descent-path elements (a field hom is determined by the generator image and
preserves the marked evaluation), but does the expensive root/marked-match **once** and never
touches the element cache.

`change_hecke_polynomial_ring` mirrors this exactly for charpolys.

---

## 4. Newform-component anchoring and the up-coercion (finitefield.m)

`NewformDecomposition` in **`finitefield.m`** is the *active* copy (it shadows the one in
`hecke.m`). For each Hecke-irreducible orbit component `N` of a space `M`, it builds `N`'s basis and
anchors `N` to an ambient space. The headline "nonparallel-weight products escape the target cusp
space" bug lived here.

### The bug, and the two ways it has been fixed
The component basis `kmat` is over the (descended) component field; to restrict the raw ambient's
Hecke operators to `N` you must coerce `kmat` **up** to the raw field. Doing this with plain
`ChangeRing` picks an **arbitrary conjugate** → for multi-orbit `M` the component operators come out
**non-commuting** → `GaloisDescent` trace assembly produces a non-Hecke-stable eigenbasis →
products escape.

- **`6f2c1507`'s fix (anchor to M):** set `N`Ambient := M` (the immediate *descended* space) instead
  of the raw top ambient `MA`, so `operator(N)` restricts `M`'s small, already-descended, already-
  commuting operators and the up-coercion of `kmat` is sidestepped entirely. Correct, but it makes
  `operator(N,p)` recurse through `operator(M,p)` — a `dim(MA)→dim(M)` restriction through `M`'s
  large-entry inverse **every prime** (~18 s/prime on the norm-391 (2,4) space; see §6). It also
  regressed nonparitious (`nonparitious_cubic` 102 s → >5 min).

- **Current fix (anchor to MA + parity-gated up-coercion):** anchor `N` back to the raw ambient `MA`
  (cheap `dim(MA)→dim(N)` restriction per prime) and do the up-coercion of `kmat` *correctly*, gated
  on the **same `is_paritious` predicate as the descent (§3)**:
  ```
  if is_paritious(Weight(M)) then
     kmat_up := strong_up_matrix(BaseRing(A), kmat);   // hom<K->L | StrongCoerce(L,K.1)>, forward
  else
     kmat_up := ChangeRing(kmat, BaseRing(A));          // nonparitious: see §5
  end if;
  ```
  `strong_up_matrix` is the *forward* of the same marked-place embedding the paritious descent
  inverts with `@@`, so up and down are mutually inverse and multi-orbit operators stay commuting.
  For nonparitious, plain `ChangeRing` is correct (it carries the k₀-anchored convention, §5) and
  object-compatible with the target field; StrongCoerce would pick the wrong √z square class.

**Matching the gate on both sides is the point:** the up-coercion (here) and the down-descent (§3)
branch on the *identical* `is_paritious(Weight(M))` predicate, so they always use mutually-inverse
embeddings. That is what keeps the operators commuting.

**When is `M` a proper subspace (so any of this matters)?** When `M` carries
`basis_matrix_wrt_ambient`: (a) **oldforms present** (`NewSubspace` is a proper subspace of the full
new⊕old cuspidal space), and/or (b) a **nontrivial Hecke-character subspace** (only when the narrow
class number is > 1; `HeckeCharacterSubspace` returns `M` unchanged for trivial class group).

---

## 5. The nonparitious field `K(√z)`, the involution, and the k₀ place

This is the asymmetry that forces the parity gate. It is **indefinite-method-only**: the ±/√z
machinery lives in `basis_of_plus_subspace`, which is only reached from the
`not IsDefinite(M) and ambient` branch of `basis_matrix` (`hecke.m`). The definite method uses
`BasisMatrixDefinite` and never builds `K(√z)`.

### Where the square root comes from (walk-through)
1. The weight rep is `Wk = ⊗_i (Sym^{n_i} ⊗ det^{m_i}) ⊗ χ`, `n_i = k_i−2`, `m_i = (k₀−k_i)/2`
   (`weight_rep.m` `m_from_k`, `weight_map_arch`).
2. **Paritious** ⇒ all `k_i` same parity ⇒ `k₀−k_i` even ⇒ `m_i ∈ ℤ`. `det^{m_i}` is an honest
   polynomial; no roots; everything over `weight_base_field`.
3. **Nonparitious** ⇒ `m_i` half-integral ⇒ `det^{m_i}` wants `√det`. The determinant of the Hecke
   operator at `p` is (a totally positive generator `π` of) `p`, so `det^{(k₀−k_i)/2}` would
   introduce **`√π` for every prime `p`**. To avoid a field with `√π` for all `p`, `m_from_k`
   **returns `[0,…,0]` for nonparitious** — it drops the det twist from the weight rep and handles
   it downstream (its own comment: "so as to avoid dealing with square roots").
4. The one place the twist cannot be dropped is **complex conjugation**: the involution
   `T = hecke_matrix_auto(…, "Infinity", …)` is the action of `μ = ElementOfNormMinusOne(O)`. With
   the twist, `T` is an involution (eigenvalues ±1). Without it, `T`'s eigenvalue is scaled by the
   omitted twist value at `μ`: `det(μ)^{m_i} = Norm(μ)^{(k₀−k_i)/2} = eps^{(k₀−k_i)/2}`, which
   across the places gives `±√z` with `z = ∏_i σ_i(eps)^{k₀−k_i}` (`get_image_of_eps_nonparit`,
   `eps = Norm(ElementOfNormMinusOne(O))`). The code asserts `eig² = embs[1](z^{-1})`.

So dropping the twist trades "`√π` at every prime" for **a single `√z` concentrated at `μ`**, and
that one `√z` is unavoidable because it *is* the ± split. Hence `hecke_matrix_field = K(√z)`
(`ext<K | x² − embs[1](z)>`), and `basis_of_plus_subspace` cuts
`V± = Ker(T ∓ eig)`, `eig = √(z^{-1})`.

### The indexing is self-consistent — k₀ need not be the first place
Probed on `(2,2,3)` over Q(ζ₇)⁺: `k₀` is at **weight index 3**, the split place is index 3, and
`eps` is **negative there** (`eps(v₃) ≈ −0.247`; the other two places positive). This is *fine* and
needs **no re-sorting of the weight**:
- `z = ∏_i σ_i(eps)^{k₀−k_i}` has exponent `k₀−k_i = 0` at the split place, so **the split place
  drops out of `z` automatically**, wherever it sits. (Here `z = σ₁(eps)·σ₂(eps)`, the two
  non-split places.)
- `embs[1] = WeightBaseEmbeddings[1]` is the **base/marked evaluation embedding**, *not* the split
  place. The `σ_i` from `AutsOfKReppingEmbeddingsOfF` are defined *relative to it*
  (`v_i = v_0 ∘ σ_i`), so `embs[i] = embs[1] ∘ σ_i` and therefore
  `embs[1](z) = ∏_i embs[i](eps)^{k₀−k_i} = eig²`. That is why, empirically, **only** `embs[1]`
  satisfies `eig² = embs[i](z^{-1})` — not because it is the split place, but because `z` is written
  relative to it. "Fixing" it to use the actual split place (embs[3]) would give the *wrong* value.
- Also: the det-twist exponent `m_i` is 0 at the split place too, so the split place never had a
  twist to omit; `√z` comes from the **non-split** places' omitted twists. The negative-norm split
  place is *why there is a nontrivial involution at all*, not what `z`'s square class is built from.

### Does the ± sign choice matter? (It is consistency, not the sign.)
Probed: for primes over 2 and 13, the Hecke operators `T_p` have **identical characteristic
polynomials on `V₊` and `V₋`** (and each is its own `√z↦−√z` conjugate). So:
- **Which ± subspace you take does not change the forms or eigenvalues** — the two are isomorphic
  Hecke modules (the classical modular-symbols ± picture). `basis_of_plus_subspace` commits to
  `V₊ = Ker(T − eig)` as `M`basis_matrix`.
- What *must* be consistent is the **√z square class across all operators in a computation**. A
  *globally* consistent choice (even the "wrong" one) is fine — flipping `√z` uniformly just
  σ-conjugates every operator, preserving commuting and charpolys. An *inconsistent* choice (some
  operators with `+√z`, some with `−√z`) makes them non-commuting → products escape. This is exactly
  why the descent (§3) and up-coercion (§4) must agree on the conjugate.

### `9b754f1` (the embs[1] pinning) is correct
`9b754f1` builds `K(√z)` **once** via `embs[1](z)` (not Magma's natural `F→K` coercion, which
disagreed with the splitting embedding in Magma 2.29-8) and asserts `eig² = embs[1](z^{-1})`. This
supplies exactly the consistency above: one `K(√z)` object, one `√z`, self-checked against the
operator's actual `eig`. The descent (`@@ minimal_hecke_field_emb`) and the nonparitious up-coercion
(`ChangeRing` into that same `K(√z)` object) both preserve it. Confirmation it holds end-to-end:
`nonparitious_cubic` passes (products land), which *requires* the descended multi-orbit operators to
commute.

**One latent caveat (not a bug here):** `eig := Rep(Eigenvalues(T))[1]` fixes the sign only *within*
a run. If `Rep` is not deterministic across runs, two separate computations of the "same" space
could pick opposite signs — harmless within one `CuspFormBasis` (self-consistent), but a possible
source of *cross-run* mismatch when comparing/combining forms from different runs. `9b754f1` pins the
*field's* `√z`, not `eig`'s sign, so it does not address that. (Smells related to the CM-(1,2)
cross-run nondeterminism seen on the definite-nebentypus branch.)

### We do NOT need to unify the gate
There *is* a tidier end state — set `MarkedEmbedding` of the nonparitious fields to the k₀/split
place so StrongCoerce resolves the right conjugate and a single coercion works for both parities,
dropping the gate. It is a weight-rep-construction change (derive the place from
`WeightBaseEmbeddings`, mind that `MarkedEmbedding` is global to the field object, and the `√z`
square-class is already Magma-version-sensitive). **It is not necessary.** The parity gate is
lightweight, correct, and a fine permanent solution; the nonparitious branch using `@@ emb` /
`ChangeRing` instead of StrongCoerce is deliberate. Do not "just use StrongCoerce everywhere" to
chase uniformity — see §9.

---

## 6. Performance: the PR #533 (eigenbasis-opt) regression and its fix

PR #533 (`eigenbasis-optimizations`, merge `253ab5e9`) made every weight-`(2,k)` cusp-basis
computation balloon to **6–11 GB and "not finish"**, and ~3× slower even when it finished. (The
headline dim-54 `(2,4)`/Q(√2)/norm-391/prec-80 basis: pre-eigopt `f9fcfcc2` does it in **~214 s**;
the "49 s" quoted in the original slowdown report was wrong.)

**Three compounding causes** (two in the same commit `6f2c1507`, plus the PR #530 cache):
1. **PR #530's StrongCoerce element cache was an O(n²) flat list** (§1). Tolerable alone.
2. **`6f2c1507` routed paritious descent through per-element `StrongCoerce`** (§3) → millions of
   calls into that cache → the 6–11 GB balloon (dominant cause).
3. **`6f2c1507`'s `anchor_to_M`** (§4) → per-prime `dim(MA)→dim(M)` restriction through `M`'s
   ~145-bit-entry inverse (~18 s/prime × ~21 primes).

**The fix (this branch, 4 files, all correctness-preserving):**
- `FldExt.m`: StrongCoerce cache → `AssociativeArray` (fixes 1).
- `hecke.m`: paritious descent builds the marked-place embedding once and uses `@@` (fixes 2);
  nonparitious descent unchanged.
- `finitefield.m`: replace `anchor_to_M` with raw-ambient anchoring + parity-gated up-coercion
  (fixes 3); also drops paritious `multiplication_escape_cubic` from 172 s → 36 s.
- `hecke_field.m`: one attribute declaration (`strong_descent_embs`).

Result: dim-54 `(2,4)` prec-80 goes from 6–11 GB / stalls to **207 s / ~76 MB**, matching pre-eigopt
while keeping every correctness test green (all `multiplication_escape_*`, `nonparitious_cubic`,
`eigenbasis*`, `strong_coercion`, the `Bug*` battery, etc.). `Bug143` is a flaky timing-ratio
assertion (passes uncontended); `hecke_matrix.m` is ~3.5 min on 2.29-8 on master too;
`base-change.m` is a pre-existing weight-1 precision failure.

---

## 7. DefaultCoefficientRing and the ModFrmHilD side (Space.m, Components.m)

`DefaultCoefficientRing(Mk)` (`Space.m`) = `SafeCompositum(NebCharField, UnitCharField)` — it
**does** include the nebentypus field. Every form-creation path is supposed to put coefficients
here, to avoid cross-field coercion. So a coercion error building a form is almost never "make the
ring bigger" — it is "coerce the value into the existing ring object" (object identity, §0).

Two concrete bugs fixed here (PR #535):
- `Components.m` `Coefficient` and `HMFGetLowerSetFromExpansion` did `a * Evaluate(uc, eps)` —
  multiplying a Fourier coefficient by a unit-character value in the separately-built
  `UnitCharField` object. Even though `UnitCharField ⊆ DefaultCoefficientRing` abstractly, Magma's
  `*` refuses the two distinct objects. Fix: `a * StrongCoerce(Parent(a), Evaluate(uc, eps))`.
  (`uc` is a `GrpCharUnitTotElt` on the totally positive unit group; `Evaluate(uc, x)` expects `x`
  in `TotallyPositiveUnitsGroup(F)`.)
- Fixing the multiply then exposed the `IsStrongCoercible` `L!x` fast-path bug (§1). Both fixes are
  needed together for an order-4-nebentypus weight-1 computation.

### `SafeCompositum` (FldExt.m, PR #534)
`StrongAdd`/`StrongMultiply` build a common field via iterated `SafeCompositum`. Magma's
`Compositum` requires at least one field normal; `SafeCompositum` now falls back to `CompositeFields`
and takes the maximal-degree compositum when neither is normal.

---

## 8. definite vs indefinite backend — and the nonparitious scope

Whether a space uses the **definite** or **indefinite** quaternion algorithm is *not* determined by
parity, and it does not change the §3 descent gate (which really is about parity). But it matters for
two things:

- **`definite.m` hard-asserts a trivial Dirichlet character** (`assert M`DirichletCharacter cmpeq 1`),
  so any space with a nontrivial Dirichlet-restriction nebentypus must go through the **indefinite**
  method. `SetAlgorithm` / `SetQuaternionOrder` (ModFrmHilD/Space.m) and the `force_indefinite`
  propagation (`diamond.m`, `Newforms.m`) exist for this. Routing an odd-degree space to definite vs
  indefinite is conditional (roughly: on a prime exactly dividing the level that is coprime to the
  nebentypus conductor); **do not assume a given `(k,χ)` "is" definite or indefinite without
  checking `IsDefinite`.**

- **The §5 `K(√z)` / ±-involution machinery is indefinite-only.** So the `(2,2,3)+χ` cubic test is
  *indefinite* (verified `IsDefinite=false`) and is the one nonparitious case the suite exercises —
  which is why the nonparitious descent/up-coercion branches are what it stresses. A genuine
  **definite-nonparitious** space has no `√z`, so StrongCoerce would likely be fine there; but the
  parity gate keys on `is_paritious`, *not* backend, so it would route definite-nonparitious to the
  `@@ emb` / `ChangeRing` branch. **No current test exercises definite-nonparitious**, so that path
  is unvalidated here — revisit (and add a test) if/when definite-with-nebentypus lands. A separate
  agent owns the definite-nebentypus work.

---

## 9. Things that look right but are wrong (so you don't repeat them)

- **"Just use StrongCoerce everywhere in `change_hecke_matrix_ring` / `strong_up_matrix`."** Breaks
  nonparitious (wrong conjugate, §5) and is ~20× slower there. Hence the parity gate.
- **"Just use `@@ emb` everywhere."** Breaks paritious multi-orbit (non-commuting operators, §3): the
  `IsSubfield`-derived `emb` is an arbitrary conjugate (fails the cubic product test at `f9fcfcc2`).
- **"Make `minimal_hecke_field_emb` marked-consistent (build `emb_fixed` via StrongCoerce)."** Fixes
  paritious but *breaks* nonparitious — the nonparitious matrices embed the minimal field via the
  k₀-anchored (non-marked) convention, so their correct `emb` is the non-marked `IsSubfield` one.
- **"Keep `anchor_to_M` for the multi-orbit fix."** Correct but pathologically slow (§4, §6): per-
  prime restriction through the newspace's large-entry inverse. Anchor to the raw ambient and do the
  up-coercion with the parity-matched conjugate instead.
- **"Re-sort the weight / use the split place (embs[3]) to build `√z`."** Unnecessary and wrong (§5):
  `z`'s formula self-selects the split place via the zero exponent, and `embs[1]` is the base
  evaluation embedding the `σ_i` are defined against.
- **`StrongMultiply([* a, v *])` to fix an `a * v` multiply in Components.m.** Wrong: it builds a
  *fresh compositum* object; use `StrongCoerce` into the *existing* coefficient ring instead.
- **"The coefficient ring is too small for order-4 nebentypus."** No — `DefaultCoefficientRing`
  already contains the nebentypus field (§7). It's object identity, not size.
- **`DetachSpec`/`AttachSpec` repeatedly in one interactive Magma session.** Corrupts Magma's
  intrinsic table. Restart the process for a fresh compile.

---

## 10. Symptom → likely cause cheat sheet

| Symptom | Likely cause |
|---|---|
| `Arguments are not compatible: FldNumElt; FldNumElt/FldQuadElt` on `*`/`+` | two isomorphic-but-distinct fields met; StrongCoerce one into the other's object (§0) |
| `Runtime error in '!'` inside `StrongCoerce` | `IsStrongCoercible` `L!x` fast path (§1) |
| `Compositum: ... must be normal` | `SafeCompositum` with two non-normal fields (§7) |
| `hecke_matrix_field seems to be wrong!` | `change_hecke_matrix_ring` fell through to `CanChangeRing` and it failed — conjugate/field mismatch in descent (§3) |
| products "escape" the target cusp space (multi-orbit) | up-coercion / descent conjugate mismatch (§3, §4) |
| non-commuting Hecke operators | the above — descent/up-coercion picked incoherent conjugates |
| wrong Galois conjugate but no error | `MarkedEmbedding` not the place the construction assumes (§5), or `L!x`/`Roots` default conjugate |
| weight-(2,k) basis uses 6–11 GB / doesn't finish | the PR #533 regression (§6) — should be fixed on this branch |
| nonparitious result differs across otherwise-identical runs | `eig` sign non-determinism (§5 caveat) |

---

## 11. Pointers
- `ModFrmHil/hecke_field.m` — `hecke_matrix_field` (nonparitious `K(√z)`), `minimal_hecke_matrix_field`,
  `splitting_field_embedding_to_weight_field`, `WeightRepresentation`.
- `ModFrmHil/hecke.m` — `strong_descent_emb`, `change_hecke_matrix_ring` / `_polynomial_ring`,
  `get_image_of_eps_nonparit`, `basis_of_plus_subspace`, `SetRationalBasis`.
- `ModFrmHil/weight_rep.m` — `m_from_k` (det-twist exponents; `[0,…]` for nonparitious),
  `weight_map_arch`, `Splittings`, `WeightBaseEmbeddings`.
- `ModFrmHil/finitefield.m` — `NewformDecomposition` (active copy; component loop + `strong_up_matrix`).
- `ModFrmHil/diamond.m` — `operator` (descent call), `HeckeCharacterSubspace`.
- `ModFrmHil/definite.m` — DirichletCharacter asserts, `BasisMatrixDefinite`.
- `ModFrmHilD/FldExt.m` — `MarkedEmbedding`, `IsStrongCoercible`/`StrongCoerce`, `SafeCompositum`,
  `StrongAdd`/`StrongMultiply`, `AutsOfKReppingEmbeddingsOfF`.
- `ModFrmHilD/Space.m` — `DefaultCoefficientRing`, `SetAlgorithm`/`SetQuaternionOrder`.
- `ModFrmHilD/Components.m` — `Coefficient`, `HMFGetLowerSetFromExpansion`, `HMFConstructExpansion`.

Related PRs (edgarcosta/hilbertmodularforms): #530 (StrongCoerce root-matching + cache), #533
(multi-orbit descent + parity-gated coercion + eigenbasis opt), #534 (SafeCompositum non-normal),
#535 (nebentypus coefficient coercion). Commit `9b754f1` (nonparitious `√z` via the weight-rep
marked embedding, Magma 2.29-8); `6f2c1507` (the multi-orbit fix this branch reworks for perf).
