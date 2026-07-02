// D=49, level (2), weight 4 defect-to-q-expansion bridge, both cusps.
//
// This is a companion to the positive Kodaira-dimension row
// for K = Q(zeta_7)^+ and level (2) in arXiv:2501.15719.  It computes
// the q=2 cusp-defect coefficient ideals via the defect algorithm, maps
// the conditions at BOTH cusps of Gamma_0((2)) to ModFrmHilD coefficient
// keys, builds the full four-row vanishing matrix on a basis of M_4, and
// checks its rank is 4, so the surviving dimension 2 attains the paper's
// dim M_4 - defect bound and witnesses Kodaira dimension >= 1.
//
// The infinity cusp contributes the constant term and the coefficient at
// nu_1 = (w^2-w+1)/7, which generates the codifferent.  The zero cusp has
// Knoller type ((2), O_{F,+}^x); with W = [[0,-1],[2,0]] = sigma*diag(2,1)
// and the unitary slash (determinant power k/2), the coefficient identity
// c_nu(f|W) = Norm((2))^(k/2) * b_{nu/2}, where b is the sigma-normalized
// zero-cusp expansion of f, turns the two zero-cusp conditions into the
// SAME two coefficient keys evaluated on f|W.
//
// Runs in CI (about 2 minutes); run it directly with:
//   magma -b filename:=examples/d49_level2_defect_bridge.m exitsignal:='' run_tests.m
//
// In an attached Magma session, set BuildBasis := false before loading this
// file to skip the slow basis computation and only print/check the index
// bridge.  Set NativeALCrossCheck := true to additionally verify the
// Atkin-Lehner signs against the native (quaternionic) operator.

if not assigned BuildBasis then
  BuildBasis := true;
elif Type(BuildBasis) eq MonStgElt then
  BuildBasis := not (BuildBasis in {"false", "False", "0", ""});
end if;

if not assigned NativeALCrossCheck then
  NativeALCrossCheck := false;
elif Type(NativeALCrossCheck) eq MonStgElt then
  NativeALCrossCheck := not (NativeALCrossCheck in {"false", "False", "0", ""});
end if;

function CompareIdealLabels(a, b)
  la := LMFDBLabel(a);
  lb := LMFDBLabel(b);
  if la lt lb then
    return -1;
  elif la eq lb then
    return 0;
  else
    return 1;
  end if;
end function;

function IdealLabelOrZero(I)
  if IsZero(I) then
    return "0";
  end if;
  return LMFDBLabel(I);
end function;

function DefectCoefficientIdealsForPrincipalCusp(F, q)
  ZF := Integers(F);
  dd := Different(ZF);
  codiff := dd^-1;

  // Positive trace < q implies every real embedding is in (0, q), so this
  // hypercube contains all elements needed by Algorithm defect for M = O_F.
  Mbox := GradedRingOfHMFs(F, 10);
  RR := RealField();
  candidates := ElementsInAHyperCube(Mbox, codiff,
      [RR | 0 : i in [1..Degree(F)]], [RR | q : i in [1..Degree(F)]]);
  ts := [t : t in candidates | t ne 0 and IsTotallyPositive(t) and Trace(t) lt q];

  ideals := {};
  for t in ts do
    I := ideal<ZF | t*dd>;
    for J in Divisors(I) do
      if IsNarrowlyPrincipal(I * J^-1) then
        Include(~ideals, J);
      end if;
    end for;
  end for;

  return Sort(SetToSequence(ideals), CompareIdealLabels), ts;
end function;

function InfinityDefectIndexData(M, ideals)
  F := BaseField(M);
  ZF := Integers(F);
  zero := 0*ZF;
  data := [* *];

  bb0 := NarrowClassGroupReps(M)[1];
  Append(~data, <bb0, F!0, zero, [0 : i in [1..Degree(F)]]>);

  for J in ideals do
    bb := IdealToNarrowClassRep(M, J);
    nu := IdealToRep(M, J);
    p := M`FunDomainReps[bb][nu];
    exp := M`FunDomainRepsOfPrec[bb][p][nu];
    assert Norm(J) le Precision(M);
    Append(~data, <bb, nu, J, exp>);
  end for;

  return data;
end function;

function InfinityDefectMatrix(forms, data)
  return Matrix([[Coefficient(f, item[1], item[2]) : f in forms] : item in data]);
end function;

// The Fricke involution W on the adapted basis [E1, E2, A, B, H1, H2] in
// column convention (column j = coordinates of basis[j]|W).  Level-1 forms
// satisfy f|sigma = f, so f|W = Norm((2))^(k/2) f(2z) = 64 f(2z); hence the
// Eisenstein and oldform pairs are swapped with scalars 64 and 1/64, and the
// newforms are scaled by their Atkin-Lehner signs.  W^2 = I holds for any
// swap pair (c, 1/c), so it cannot certify the scalars; they come from the
// coefficient identity above.
function UnitaryFrickeMatrix(epsA, epsB)
  Q := Rationals();
  return Matrix(Q, [
      [0, 1/64, 0,    0,    0,  0   ],
      [64, 0,   0,    0,    0,  0   ],
      [0,  0,   epsA, 0,    0,  0   ],
      [0,  0,   0,    epsB, 0,  0   ],
      [0,  0,   0,    0,    0,  1/64],
      [0,  0,   0,    0,    64, 0   ]]);
end function;

procedure CheckD49Level2SecondCuspBridge(M, Mk, data)
  Q := Rationals();
  F := BaseField(M);
  ZF := Integers(F);
  N := Level(Mk);
  dd := Different(ZF);

  // The same two coefficient keys as the infinity half: (bb, 0) and (bb, nu1).
  assert #data eq 2;
  L0 := func<f | Q!Coefficient(f, data[1][1], data[1][2])>;
  L1 := func<f | Q!Coefficient(f, data[2][1], data[2][2])>;
  nu1 := data[2][2];

  // nu1 generates the codifferent, and the raw zero-cusp index nu1/2 lies in
  // ((2)*dd)^-1 but not in dd^-1; rescaling by the totally positive generator
  // 2 maps it back onto the stored index nu1.
  assert nu1 * dd eq 1*ZF;
  assert Trace(nu1) eq 1;
  assert IsIntegral(nu1/2 * (N*dd));
  assert not IsIntegral(nu1/2 * dd);
  assert Norm(N) le Precision(M);
  assert Norm(3*ZF) le Precision(M);

  // Adapted basis, each pair oriented structurally rather than by position.
  EB := EisensteinBasis(Mk);
  assert #EB eq 2;
  if L1(EB[1]) eq 0 then
    E1 := EB[2]; E2 := EB[1];
  else
    E1 := EB[1]; E2 := EB[2];
  end if;
  assert L0(E1) eq 1 and L0(E2) eq 1;
  assert L1(E1) eq 1680/79 and L1(E2) eq 0;
  // E2 is the degeneracy image E1(2z): ideal coefficients shift by (2).
  assert Coefficient(E2, 2*ZF) eq Coefficient(E1, 1*ZF);

  Mk1 := HMFSpace(M, 1*ZF, Weight(Mk));
  hbasis := CuspFormBasis(Mk1);
  assert #hbasis eq 1;
  old := Inclusion(hbasis[1], Mk);
  assert #old eq 2;
  if L1(old[1]) eq 0 then
    H1 := old[2]; H2 := old[1];
  else
    H1 := old[1]; H2 := old[2];
  end if;
  assert L0(H1) eq 0 and L0(H2) eq 0;
  assert L1(H1) eq 1 and L1(H2) eq 0;
  assert Coefficient(H2, 2*ZF) eq Coefficient(H1, 1*ZF);

  // Smoke block: the Eisenstein and oldform columns alone already force
  // rank 4, for any Atkin-Lehner signs on the newforms.
  W4 := Matrix(Q, [[0,1/64,0,0],[64,0,0,0],[0,0,0,1/64],[0,0,64,0]]);
  assert W4^2 eq IdentityMatrix(Q, 4);
  four := [E1, E2, H1, H2];
  Erows4 := Matrix(Q, [[L0(f) : f in four], [L1(f) : f in four]]);
  D4 := VerticalJoin(Erows4, Erows4*W4);
  expected4 := Matrix(Q, [
      [1,       1,       0, 0   ],
      [1680/79, 0,       1, 0   ],
      [64,      1/64,    0, 0   ],
      [0,       105/316, 0, 1/64]]);
  assert D4 eq expected4;
  assert Rank(D4) eq 4;
  printf "Eisenstein+oldform smoke block has rank %o\n", Rank(D4);

  // The two rational newforms, normalized by a_(1) = 1.  For a newform at
  // the prime level (2), the U_(2) eigenvalue a_(2) satisfies
  // a_(2) = -eps * Norm((2))^(k/2-1) = -8 eps for the Atkin-Lehner sign eps,
  // so a_(2)^2 = 64 certifies both the eigenform property and the package
  // normalization before we trust the sign.
  NB := NewCuspFormBasis(Mk);
  assert #NB eq 2;
  news := [];
  for X0 in NB do
    a1 := Coefficient(X0, 1*ZF);
    assert a1 ne 0;
    X := (1/a1) * X0;
    a3 := Q!Coefficient(X, 3*ZF);
    a2 := Q!Coefficient(X, 2*ZF);
    assert a3 in {280, 80};
    assert a2^2 eq 64;
    eps := -a2/8;
    printf "Newform with T_(3) eigenvalue %o has Atkin-Lehner sign %o\n", a3, eps;
    Append(~news, <a3, eps, X>);
  end for;
  assert {n[1] : n in news} eq {280, 80};
  Sort(~news, func<u, v | v[1] - u[1]>);
  epsA := news[1][2];
  epsB := news[2][2];
  A := news[1][3];
  B := news[2][3];

  forms := [E1, E2, A, B, H1, H2];
  assert Rank(CoefficientsMatrix(forms)) eq 6;

  W := UnitaryFrickeMatrix(epsA, epsB);
  assert W^2 eq IdentityMatrix(Q, 6);

  Erows := Matrix(Q, [[L0(f) : f in forms], [L1(f) : f in forms]]);
  assert Erows eq Matrix(Q, [[1, 1, 0, 0, 0, 0], [1680/79, 0, 1, 1, 1, 0]]);
  assert Rank(Erows) eq 2;
  EW := Erows * W;
  assert EW eq Matrix(Q, [[64, 1/64, 0, 0, 0, 0],
                          [0, 105/316, epsA, epsB, 0, 1/64]]);
  D := VerticalJoin(Erows, EW);
  printf "Full two-cusp defect matrix on [E1, E2, A, B, H1, H2]:\n%o\n", D;
  printf "Rank %o, surviving dimension %o\n", Rank(D), Ncols(D) - Rank(D);
  assert Rank(D) eq 4;
  assert Dimension(Mk) - Rank(D) eq 2;

  if NativeALCrossCheck then
    printf "Cross-checking Atkin-Lehner signs against the native operator\n";
    S := HilbertCuspForms(Mk);
    Wraw := AtkinLehnerOperator(S, N);
    K := BaseRing(Wraw);
    assert Wraw^2 eq 64*IdentityMatrix(K, 4);
    P3 := Factorization(3*ZF)[1][1];
    T3 := HeckeOperator(S, P3);
    assert Wraw*T3 eq T3*Wraw;
    for n in news do
      // Left kernel: row vectors v with v*(T3 - a3) = 0, so v*T3 = a3*v.
      V := Kernel(T3 - n[1]*IdentityMatrix(K, 4));
      assert Dimension(V) eq 1;
      v := V.1;
      vW := v*Wraw;
      s := vW[i]/v[i] where i is Min([j : j in [1..4] | v[j] ne 0]);
      assert vW eq s*v;
      assert s in {K!8, K!-8};
      assert K!(8*n[2]) eq s;
    end for;
    printf "Native Atkin-Lehner signs match\n";
  end if;
end procedure;

procedure CheckD49Level2Weight4DefectBridge()
  Q := Rationals();
  R<x> := PolynomialRing(Q);
  F<w> := NumberField(x^3 - x^2 - 2*x + 1);
  ZF := Integers(F);
  assert Discriminant(ZF) eq 49;

  q := 2;
  defect_ideals, trace_terms := DefectCoefficientIdealsForPrincipalCusp(F, q);
  assert #defect_ideals + 1 eq 2;
  assert defect_ideals eq [1*ZF];

  printf "Trace<%o codifferent representatives: %o\n", q, [F!t : t in trace_terms];
  printf "Nonzero defect coefficient ideals: %o\n", [LMFDBLabel(J) : J in defect_ideals];

  M := GradedRingOfHMFs(F, 100);
  N := 2*ZF;
  Mk := HMFSpace(M, N, [4,4,4]);

  // arXiv:2501.15719 Table positive-kod uses dim M_4 = 6 and total defect 4.
  assert NumberOfCusps(Mk) eq 2;
  assert EisensteinDimension(Mk) eq 2;
  assert CuspDimension(Mk : version := "builtin") eq 4;
  assert Dimension(Mk) eq 6;

  data := InfinityDefectIndexData(M, defect_ideals);
  printf "Infinity-cusp ModFrmHilD indices:\n";
  for item in data do
    bb, nu, J, exp := Explode(item);
    printf "  bb=%o ideal=%o nu=%o exponent=%o\n", LMFDBLabel(bb), IdealLabelOrZero(J), nu, exp;
  end for;

  if BuildBasis then
    printf "Building basis for D=49 level (2) weight 4 at precision %o\n", Precision(M);
    time B := Basis(Mk);
    assert #B eq Dimension(Mk);

    mat := InfinityDefectMatrix(B, data);
    printf "Infinity-cusp defect matrix has %o rows, %o columns, rank %o\n",
        Nrows(mat), Ncols(mat), Rank(mat);
    assert Nrows(mat) eq 2;
    assert Ncols(mat) eq 6;
    assert Rank(mat) eq 2;

    CheckD49Level2SecondCuspBridge(M, Mk, data);
  else
    printf "Skipping basis and matrix check because BuildBasis=false\n";
  end if;
end procedure;

CheckD49Level2Weight4DefectBridge();
