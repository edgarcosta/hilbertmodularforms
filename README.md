# hilbertmodularforms

Implementation to compute graded rings of Hilbert modular forms in [Magma](http://magma.maths.usyd.edu.au/magma/).

## Source code

Explanations about the Magma source code in each directory.

### ModFrmHil

This project builds on the [current Hilbert modular form implementation](http://magma.maths.usyd.edu.au/magma/handbook/hilbert_modular_forms) in Magma.
The source code in ModFrmHil connects this work to the current implementation.

### ModFrmHilD

The `ModFrmHilD` class represents the additional functionality we are adding to `ModFrmHil`.
The `D` in this name stands for _Dartmouth_ where this project originated.

### HilbertSeries

Source code to compute formulas for Hilbert series of Hilbert modular surfaces.

### spec and sig files

Package specification files, or `spec` files, help organize imports in various places.
Package specification documentation: [http://magma.maths.usyd.edu.au/magma/handbook/text/24#181](http://magma.maths.usyd.edu.au/magma/handbook/text/24#181).

`.sig` files contain signature information for Magma package files. See [http://magma.maths.usyd.edu.au/magma/handbook/text/24#164](http://magma.maths.usyd.edu.au/magma/handbook/text/24#164).

## Tests

Example computations that are run during CI via `run_tests.m`.
These examples can also be executed individually using

```{shell}
magma Tests/filename.m
```

## Examples

These files are similar to files in Tests, but not run during CI.

## scripts

Scripts should include calling information in a comment at the top of the file. For example, we can run `generate_hs.m` using the following command.

```{shell}
magma -b D:=13 ambient:=SL gamma:=Gamma0 scripts/generate_kposs.m
```

These scripts are then used to generate data for [https://github.com/edgarcosta/hilbertmodularsurfacesdata](https://github.com/edgarcosta/hilbertmodularsurfacesdata) which ultimately ends up on [https://teal.lmfdb.xyz/HilbertModularSurface/Q/](https://teal.lmfdb.xyz/HilbertModularSurface/Q/). These can be run using the following command.

```{shell}
A=GL;G=Gamma0;t=kposs;name=${A}_${G}_lt3000_cut5000_${t}; time parallel --joblog data/joblog/${name}.txt --results data/results/${name} --eta -j 64 magma -b cut:=5000 D:={} ambient:=$A gamma:=$G scripts/generate_${t}.m ::: {1..3000} > data/${name}.txt
```

TODO: explain how to call `counts_and_timings.m`

## Verification

This is unfinished work to verify computed equations against equations in the literature.

## WorkInProgress

Examples that may or may not run successfully, but have code or comments that may be useful or informative.
Once a file has been polished and appropriate for public consumption it can be moved to Examples or Tests.

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
