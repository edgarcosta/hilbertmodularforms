// D=49, level (2), weight 4 defect-to-q-expansion bridge.
//
// This is a companion to the positive Kodaira-dimension row
// for K = Q(zeta_7)^+ and level (2) in arXiv:2501.15719.  It computes
// the q=2 cusp-defect coefficient ideals via the defect algorithm, maps
// the infinity-cusp conditions to ModFrmHilD coefficient keys, and checks
// the corresponding rank on a weight-4 q-expansion basis.
//
// Runs in CI (about 1 minute); run it directly with:
//   magma -b filename:=examples/d49_level2_defect_bridge.m exitsignal:='' run_tests.m
//
// In an attached Magma session, set BuildBasis := false before loading this
// file to skip the slow basis computation and only print/check the index bridge.

if not assigned BuildBasis then
  BuildBasis := true;
elif Type(BuildBasis) eq MonStgElt then
  BuildBasis := not (BuildBasis in {"false", "False", "0", ""});
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
  else
    printf "Skipping basis and matrix check because BuildBasis=false\n";
  end if;
end procedure;

CheckD49Level2Weight4DefectBridge();
