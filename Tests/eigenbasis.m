// test-time: ~30s
// Tests Eigenbasis on paritious newform spaces. For each returned form we check
// that the eigenbasis spans the cusp space and that each form is a genuine
// simultaneous Hecke eigenform to full precision: the eigenvalue of T_pp matches
// the coefficient a_pp (including at primes of norm beyond P, i.e. beyond the
// operators used to diagonalize), and the coefficients are multiplicative up to
// the precision. The latter two catch the failure mode where a degenerate
// "eigenbasis" agrees with a true eigenform only out to a small norm.
//
// Also checks that a space containing oldforms is rejected (rather than silently
// returning a non-eigenbasis) when only good primes are used: degeneracy-map
// oldforms share every good-prime eigenvalue, so coprime_only:=false (which adds
// the bad primes) is needed to separate them.

R<x> := PolynomialRing(Rationals());

procedure check_eigenforms(Mk, eigs)
  M := Parent(Mk);
  F := BaseField(Mk);
  ZF := Integers(F);
  N := Level(Mk);
  prec := Precision(M);

  Sk := CuspFormBasis(Mk);
  assert #eigs eq #Sk;
  assert #LinearDependence(Sk cat eigs) eq #Sk;

  primes := PrimesUpTo(prec, F : coprime_to:=N);
  for f in eigs do
    ff := DivideByFirstNonzeroIdlCoeff(f);

    // genuine eigenform: T_pp ff = a_pp ff, including primes of norm beyond P
    for pp in primes do
      if Norm(pp)^2 le prec then
        ld := LinearDependence([ff, HeckeOperator(ff, pp)]);
        assert #ld eq 1;
        assert -ld[1][1] / ld[1][2] eq Coefficient(ff, pp);
      end if;
    end for;

    // full-precision genuineness: a_pp * a_qq = a_{pp*qq} up to prec
    for pp in primes do
      for qq in primes do
        if Norm(pp) lt Norm(qq) and Norm(pp * qq) le prec and GCD(pp, qq) eq 1*ZF then
          assert Coefficient(ff, pp * qq) eq Coefficient(ff, pp) * Coefficient(ff, qq);
        end if;
      end for;
    end for;
  end for;
end procedure;

/****** Q(sqrt5): one-dimensional (n=1 shortcut) and two-dimensional ******/
F := QuadraticField(5);
ZF := Integers(F);
M := GradedRingOfHMFs(F, 100);

Mk := HMFSpace(M, Factorization(31*ZF)[1][1], [2, 2]);
check_eigenforms(Mk, Eigenbasis(Mk, CuspFormBasis(Mk)));

Mk := HMFSpace(M, Factorization(41*ZF)[1][1], [2, 4]);
check_eigenforms(Mk, Eigenbasis(Mk, CuspFormBasis(Mk)));

/****** Q(sqrt13): good primes alone cannot separate an oldform-containing space ******/
F := QuadraticField(13);
ZF := Integers(F);
M := GradedRingOfHMFs(F, 100);
Mk := HMFSpace(M, 2*ZF, [4, 6]);
Sk := CuspFormBasis(Mk);

separated := true;
try
  _ := Eigenbasis(Mk, Sk);
catch e
  separated := false;
end try;
assert not separated;
