# hilbertmodularforms

A [Magma](http://magma.maths.usyd.edu.au/magma/) package for computing with Hilbert modular forms over totally real number fields, and with Hilbert modular surfaces. It extends Magma's built-in `ModFrmHil` with q-expansion bases, surface invariants, Hirzebruch–Zagier divisors, and canonical rings.

## Papers

This package accompanies two papers:

- *Computing with Fourier expansions of Hilbert modular forms* (in preparation).
- *A database of basic numerical invariants of Hilbert modular surfaces*, LuCaNT proceedings; arXiv:[2301.10302](https://arxiv.org/abs/2301.10302).

## Loading the package

Requires Magma. Attach the package via its top-level `spec` file:

```magma
AttachSpec("spec");
```

A convenience file `config.m` is also provided, which attaches the spec and sets a few sensible defaults (e.g. `SetClassGroupBounds("GRH")`).

## Tests

Tests live in `Tests/` and are run via the included `Makefile`:

```bash
make check                  # run all tests in parallel (uses all CPU cores)
make check/<testfile.m>     # run a single test
make debug/<testfile.m>     # run a single test with debug-on-error
make clean                  # clear cached precomputed data
```

Each test file is a Magma script that uses `assert`. Individual tests can also be run directly:

```bash
magma -b filename:=Tests/<testfile.m> exitsignal:='' run_tests.m
```

## Source code

Brief explanations of each top-level directory.

### ModFrmHil

Patches and extensions to Magma's built-in [Hilbert modular forms](http://magma.maths.usyd.edu.au/magma/handbook/hilbert_modular_forms) implementation (Hecke and diamond operators, the definite case, precomputation hooks).

### ModFrmHilD

The core of the package — the `D` stands for *Dartmouth*, where the project originated. The type hierarchy is

```
ModFrmHilDGRng  >  ModFrmHilD  >  ModFrmHilDElt  >  ModFrmHilDEltComp
```

with subdirectories for form creation (`Creation/` — Eisenstein, theta, base change, dihedral, trace forms), canonical rings (`CanonicalRing/`), and trace formula data (`Trace/`).

### HilbertSeries

Formulas for Hilbert series of Hilbert modular surfaces.

### Verification

Code to verify computed equations against equations in the literature.

### spec files

Package specification files; see the Magma [handbook section on packages](http://magma.maths.usyd.edu.au/magma/handbook/text/24#181).

## Examples and work in progress

- `examples/` holds the paper's worked examples that run in CI (the X0(11) modular curve, Igusa invariants, the cyclic cubic threefold example with syzygy-computed equations, numerical surface invariants), each a self-contained script; `examples/slow/` holds the heavy cases CI skips. The canonical-ring witness examples are listed as pending in `examples/README.md`.
- `WorkInProgress/` contains demonstrations and exploratory scripts that may or may not currently run end-to-end.

## Scripts and data

Scripts in `scripts/` generate data for [hilbertmodularsurfacesdata](https://github.com/edgarcosta/hilbertmodularsurfacesdata), which in turn feeds [https://alpha.lmfdb.xyz/HilbertModularSurface/Q/](https://alpha.lmfdb.xyz/HilbertModularSurface/Q/). Each script documents its calling convention at the top of the file. For example:

```bash
magma -b D:=13 ambient:=SL gamma:=Gamma0 scripts/generate_hs.m
```

For parallel runs across many discriminants we use GNU Parallel, e.g.:

```bash
A=GL; G=Gamma0; t=hs
parallel -j 64 magma -b D:={} ambient:=$A gamma:=$G scripts/generate_${t}.m ::: {1..3000}
```

## License

BSD 3-Clause. See [`LICENSE`](LICENSE).

## Authors

- [Eran Assaf](https://math.dartmouth.edu/~eassaf/)
- [Angelica Babei](https://angelicababei.com/)
- [Ben Breen](http://www.benbreenmath.com/)
- [Sara Chari](https://www.bates.edu/mathematics/faculty-profile/sara-l-chari/)
- [Edgar Costa](https://edgarcosta.org)
- [Juanita Duque-Rosero](https://math.dartmouth.edu/~jduque/)
- [Aleksander Horawa](https://people.maths.ox.ac.uk/horawa/)
- [Jean Kieffer](https://scholar.harvard.edu/kieffer)
- [Avinash Kulkarni](https://math.dartmouth.edu/~akulkarn/)
- [Grant Molnar](https://www.grantmolnar.com/)
- [Abhijit Mudigonda](https://cs.uchicago.edu/people/abhijit-mudigonda/)
- [Michael Musty](https://michaelmusty.github.io/)
- [Sam Schiavone](https://math.mit.edu/~sschiavo/)
- [Shikhin Sethi](https://www.math.princeton.edu/people/shikhin-sethi)
- [Samuel Tripp](https://samueltripp.github.io/)
- [John Voight](http://www.math.dartmouth.edu/~jvoight/)
