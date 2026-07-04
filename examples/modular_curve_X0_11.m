// Full verification of the X_0(11) worked example (dimension one) from the
// accompanying paper: the graded ring M(Gamma_0(11)) = Q[E2, f2, E4]/(R8).
// Each scenario pins one displayed claim of that example.  Runs in a few
// seconds on base Magma (no package intrinsics needed here).
Q := Rationals();

// Weight-2 basis convention used throughout and in the paper:
// Basis(ModularForms(11,2))[1] = E2 (constant term 1), [2] = f2 (the cusp form).
function X011Weight2Basis(prec)
  B := Basis(ModularForms(11, 2));
  return qExpansion(B[1], prec), qExpansion(B[2], prec);
end function;

// The paper reports Hilb_{M(Gamma)}(T) = 1 + 2T^2/(1-T^2)^2, computed from
// dimension formulas.  Check the closed form against dim M_k for even k, the
// independent oracle being Magma's dimension of ModularForms(11,k).
procedure test_X011_hilbert_series()
  St<T> := PowerSeriesRing(Q, 22);
  hilb := 1 + 2*T^2/(1-T^2)^2;
  assert Coefficient(hilb, 0) eq 1;              // M_0 = constants
  for k in [2..20 by 2] do
    assert Dimension(ModularForms(11, k)) eq Coefficient(hilb, k);
  end for;
end procedure;

// In weight 8 the nine monomials in E2, f2, E4 span an 8-dimensional space
// (dim M_8 = 8), so there is a unique relation up to scalar.  Check that the
// paper's R8 is that relation: it vanishes on the q-expansions and the relation
// space is one-dimensional.  The q-expansions are the independent oracle.
procedure test_X011_weight8_relation()
  prec := 40;
  E2, f2 := X011Weight2Basis(prec);
  E4 := qExpansion(Basis(ModularForms(11, 4))[1], prec);
  R8 := E2^4 + 240*E2^3*f2 + 2592*E2^2*f2^2 + 8640*E2*f2^3 + 9216*f2^4
        - 122*E2^2*E4 - 240*E2*f2*E4 + 288*f2^2*E4 + 121*E4^2;
  assert IsWeaklyZero(R8);

  P<a,b,c> := PolynomialRing(Q, [2,2,4]);
  mons := MonomialsOfWeightedDegree(P, 8);
  assert #mons eq 9;
  wt8 := [Evaluate(m, [E2, f2, E4]) : m in mons];
  M := Matrix([[Coefficient(g, i) : i in [0..20]] : g in wt8]);
  assert Dimension(Kernel(M)) eq 1;
end procedure;

// With S := Q[E2, f2, E4]/(R8), the paper asserts Hilb_S = Hilb_{M(Gamma)}.
// Over the weighted ring [2,2,4] this Hilbert series is (1+t^4)/(1-t^2)^2,
// matching the T-series above with t = T.
procedure test_X011_graded_ring_hilbert_series()
  R<E2, f2, E4> := PolynomialRing(Q, [2,2,4]);
  R8 := E2^4 + 240*E2^3*f2 + 2592*E2^2*f2^2 + 8640*E2*f2^3 + 9216*f2^4
        - 122*E2^2*E4 - 240*E2*f2*E4 + 288*f2^2*E4 + 121*E4^2;
  FF<t> := FunctionField(Q);
  assert HilbertSeries(ideal<R | R8>) eq (1 + t^4)/(1 - t^2)^2;
end procedure;

// The subring criterion is applied to {f2, E2}: on U = {E2 != 0} the map is
// z |-> f2/E2, and the Jacobian is nonvanishing at the cusp.  f2 is the cusp
// form, so f2/E2 vanishes at the cusp (constant term 0) and its derivative has
// constant term 1 != 0.  Pin the exact displayed q-expansions and the
// non-vanishing at the cusp; the two series must satisfy d/dq.
procedure test_X011_qexpansion_derivative()
  prec := 15;
  E2, f2 := X011Weight2Basis(prec);
  assert Coefficient(E2, 0) eq 1;               // E2 is not a cusp form
  assert Coefficient(f2, 0) eq 0;               // f2 is the cusp form
  g := f2/E2;
  assert [Coefficient(g, i) : i in [0..9]]
         eq [0, 1, -2, -13, 14, 169, 2, -2042, -2040, 22606];
  gp := Derivative(g);
  assert [Coefficient(gp, i) : i in [0..8]]
         eq [1, -4, -39, 56, 845, 12, -14294, -16320, 203454];
  assert Coefficient(gp, 0) ne 0;               // Jacobian nonvanishing at the cusp
end procedure;

// The model embeds via the Veronese into ordinary projective space and defines
// an elliptic curve of conductor 11, isomorphic to X_0(11).
procedure test_X011_equation()
  R<E2, f2, E4> := PolynomialRing(Q, [2,2,4]);
  PR := ProjectiveSpace(R);
  R8 := E2^4 + 240*E2^3*f2+2592*E2^2*f2^2+8640*E2*f2^3+9216*f2^4-122*E2^2*E4-240*E2*f2*E4+288*f2^2*E4+121*E4^2;
  S := Scheme(PR, R8);
  M := MonomialsOfWeightedDegree(R, 4);
  PN<[z]> := ProjectiveSpace(Q, #M - 1);
  // construct the Veronese embedding into regular projective space
  // so that Magma will be able to do something with it
  nu := map< PR -> PN | [m : m in M] >;
  C := Curve(S);
  C_prime := nu(C);
  pt := C_prime![1,0,0,1];
  E := EllipticCurve(C_prime, pt);
  assert Conductor(E) eq 11;
  X011 := X0NQuotient(11, []);
  assert IsIsomorphic(X011, E);
end procedure;

test_X011_hilbert_series();
test_X011_weight8_relation();
test_X011_graded_ring_hilbert_series();
test_X011_qexpansion_derivative();
test_X011_equation();
