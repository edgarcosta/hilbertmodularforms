/***************************************************************
* Diagonal restrictions of CM / dihedral parallel-weight-1
* Hilbert modular forms, and the classical nebentypus of the
* restriction.
*
* RestrictionToDiagonal of a weight-[1,...,1] form over a
* degree-n field is a classical form of weight n. Its classical
* nebentypus is the Dirichlet character psi(m) = chi(m*ZF),
* where chi is the Hilbert nebentypus. When psi is nontrivial
* -- which is forced whenever the classical weight n is odd --
* the restriction does NOT live in M_n(Gamma0(N)) with trivial
* character, and the (pre-fix) code that always built
* ModularForms(Gamma0(N), n) crashed with
*   "The series does not define a modular form in the space".
* These tests exercise both the trivial and the nontrivial
* nebentypus cases, and check the ModFrmElt returned by the
* non-AsCoefficients path agrees with the raw coefficients.
***************************************************************/

printf "Testing diagonal restriction nebentypus...";

// helper: truncated raw coefficients of the restriction to the
// trivial component, and the classical ModFrmElt, cross-checked.
RestrInfo := function(f, M, ZF, len)
  cf := RestrictionToDiagonal(f, M, 1*ZF : AsCoefficients := true);
  trunc := cf[1 .. Min(#cf, len)];
  g := RestrictionToDiagonal(f, M, 1*ZF);   // must not crash
  qe := qExpansion(g, Min(#cf, len) + 1);
  match := &and[Coefficient(qe, i-1) eq cf[i] : i in [1 .. Min(#cf, len)]];
  return trunc, match, &+Weight(f);
end function;

// collect the nonzero restriction coefficient-vectors (length `len`)
// over every weight-compatible character at level NN.
NonzeroRestrictions := function(M, ZF, NN, k, len)
  out := [];
  H := HeckeCharacterGroup(NN, [1 .. Degree(NumberField(ZF))]);
  for chi in [c : c in Elements(H) | IsCompatibleWeight(c, k)] do
    Mk := HMFSpace(M, NN, k, chi);
    for f in DihedralBasis(Mk) do
      cf := RestrictionToDiagonal(f, M, 1*ZF : AsCoefficients := true);
      if &and[IsZero(c) : c in cf] then continue; end if;
      trunc, match, wt := RestrInfo(f, M, ZF, len);
      assert match;          // non-AsCoefficients path agrees with raw coeffs
      Append(~out, <trunc, wt>);
    end for;
  end for;
  return out;
end function;

//////////////////// 1. Q(sqrt5), parallel weight [1,1] ////////////////////
// Classical weight 2. These CM/dihedral forms have rational integer
// restriction coefficients. (Their classical nebentypus is trivial, so
// they also exercise the trivial branch of the fix.)

F := QuadraticField(5);
ZF := Integers(F);
M := GradedRingOfHMFs(F, 200);

r19 := NonzeroRestrictions(M, ZF, 19*ZF, [1,1], 6);
assert exists{t : t in r19 | t[1] eq [0, 2, 0, -4, -4, 6] and t[2] eq 2};

r23 := NonzeroRestrictions(M, ZF, 23*ZF, [1,1], 6);
assert exists{t : t in r23 | t[1] eq [0, 2, 0, -2, -2, 0] and t[2] eq 2};

//////////////////// 2. Cubic field of discriminant 49 ////////////////////
// Parallel weight [1,1,1] -> classical weight 3 (ODD), so the classical
// nebentypus is necessarily nontrivial. Pre-fix, the non-AsCoefficients
// path crashed here; RestrInfo asserts it now returns a ModFrmElt whose
// q-expansion matches the raw coefficients.

R<x> := PolynomialRing(Rationals());
Fc := NumberField(x^3 - 6*x^2 + 5*x - 1);
ZFc := Integers(Fc);
assert Discriminant(ZFc) eq 49;
Mc := GradedRingOfHMFs(Fc, 200);

r19c := NonzeroRestrictions(Mc, ZFc, 19*ZFc, [1,1,1], 5);
assert exists{t : t in r19c | t[1] eq [0, 3, 3, -3, -3] and t[2] eq 3};

printf "Success!\n";
