function Igusa(M)
  psi := AssociativeArray();
  // psi_j are the pullbacks of the Siegel-Eisenstein forms
  for j in [4,6,10,12] do
    psi[j] := AssociativeArray(['+','-']);
    psi[j]['+'], psi[j]['-'] := SiegelEisensteinPullback(M, [j,j]);
  end for;
  psi4psi6 := AssociativeArray();
  psi4psi6['+'] := psi[4]['+']*psi[6]['+'] + psi[4]['-']*psi[6]['-'];
  psi4psi6['-'] := psi[4]['+']*psi[6]['-'] + psi[4]['-']*psi[6]['+'];
  chi10const := -43867/(2^12*3^5*5^2*7^1*53^1);
  chi10 := AssociativeArray();
  chi10['+'] := chi10const*(psi4psi6['+']-psi[10]['+']);
  chi10['-'] := chi10const*(psi4psi6['-']-psi[10]['-']);
  chi12const := 131*593/(2^13*3^7*5^3*7^2*337^1);
  psi4_3 := AssociativeArray();
  psi4_3['+'] := psi[4]['+']^3 + 3*psi[4]['+']*psi[4]['-']^2;
  psi4_3['-'] := psi[4]['-']^3 + 3*psi[4]['-']*psi[4]['+']^2;
  psi6_2 := AssociativeArray();
  psi6_2['+'] := psi[6]['+']^2 + psi[6]['-']^2;
  psi6_2['-'] := 2*psi[6]['+']*psi[6]['-'];
  chi12 := AssociativeArray();
  chi12['+'] := chi12const*(3^2*7^2*psi4_3['+']+2^1*5^3*psi6_2['+']-691*psi[12]['+']);
  chi12['-'] := chi12const*(3^2*7^2*psi4_3['-']+2^1*5^3*psi6_2['-']-691*psi[12]['-']);
  return psi[4], psi[6], chi10, chi12;
end function;

function gens_and_rels(D, B, num_gens, num_rels)
  F := QuadraticField(D);
  ZF := Integers(F);
  prec := ComputePrecisionFromHilbertSeries(1*ZF, 2*B);
  M := GradedRingOfHMFs(F, prec);
  bb := NarrowClassRepresentative(M, Different(ZF)^(-1));
  R := ApproximateGradedRing(M, 1*ZF, B : IdealClassesSupport := [bb]);
  gens := R[1];
  rels := R[2];
  assert Keys(gens) eq Keys(num_gens);
  assert Keys(rels) eq Keys(num_rels);
  max_num := Maximum([n : n in num_gens]);
  vars := [AssociativeArray() : i in [1..max_num]];
  for j in [1..max_num] do
    for k in Keys(gens) do
      assert #gens[k] eq num_gens[k];
      if IsDefined(gens[k], j) then
        vars[j][k] := gens[k][j];
      end if;
    end for;
  end for;
  max_num := IsEmpty(Keys(num_rels)) select 0 else Maximum([n : n in num_rels]);
  R := [AssociativeArray() : i in [1..max_num]];
  for j in [1..max_num] do
    for k in Keys(rels) do
      assert #rels[k] eq num_rels[k];
      R[j][k] := rels[k][j];
    end for;
  end for;
  return vars, R, M;
end function;

// This should be changed once we fix HilbertModularVariety
procedure test_Igusa_Qsqrt12()
  num_gens := AssociativeArray([2,4,6]);
  for d in [2,4,6] do num_gens[d] := 1; end for;
  num_rels := AssociativeArray();
  vars, R, M := gens_and_rels(12, 6, num_gens, num_rels);
  x := vars[1];
  psi4, psi6, chi10, chi12 := Igusa(M);
  assert psi4['+'] eq 1/4*x[2]^2 + 72*x[4];
  assert psi6['+'] eq 1/8*x[2]^3 - 162*x[2]*x[4] - 1728*x[6];
  assert psi4['-']^2 eq 7200*x[2]*x[6];
  assert psi4['-']*psi6['-'] eq -7560*x[2]^2*x[6];
  assert chi10['+'] eq -1/8*x[4]*x[6];
  assert chi12['+'] eq 1/8*x[4]^3-1/24*x[2]*x[4]*x[6]+x[6]^2;
  assert psi4['-']*chi10['-'] eq 15/2*x[2]*x[6]^2;
  assert psi4['-']*chi12['-'] eq -15/2*x[2]*x[4]^2*x[6]+5/2*x[2]^2*x[6]^2;
  return;
end procedure;

procedure test_Igusa_Qsqrt21()
  num_gens := AssociativeArray([2,4,6,10]);
  for d in [2,6,10] do num_gens[d] := 1; end for;
  num_gens[4] := 2;
  num_rels := AssociativeArray([8,20]);
  for d in [8,20] do num_rels[d] := 1; end for;
  vars, R, M := gens_and_rels(21, 10, num_gens, num_rels);
  x := vars[1];
  y := vars[2];
  R8 := -4*x[4]^2+x[2]^2*y[4]-56*x[4]*y[4]-196*y[4]^2+8*x[2]*x[6];
  assert IsZero(R8);
  R20 := 11/18*x[4]*y[4]^4+9/2*y[4]^5+x[2]*y[4]^3*x[6]+3/2*x[4]*y[4]*x[6]^2+21*y[4]^2*x[6]^2+1/36*x[2]*x[6]^3-1/36*x[2]*y[4]^2*x[10]-1/18*x[4]*x[6]*x[10]-17/9*y[4]*x[6]*x[10]+1/18*x[10]^2;
  assert IsZero(R20);
  psi4, psi6, chi10, chi12 := Igusa(M);
  assert psi4['+'] eq 1/4*x[2]^2+96*x[4]+816*y[4];
  assert psi6['+'] eq 1/8*x[2]^3-144*x[2]*x[4]-2736*x[2]*y[4]-1728*x[6];
  assert chi10['+'] eq -1/16*x[2]*y[4]^2-1/4*y[4]*x[6];
  assert chi12['+'] eq 1/96*x[2]^2*y[4]^2+1/2*x[4]*y[4]^2+9/2*y[4]^3+7/24*x[2]*y[4]*x[6]+x[6]^2;
  assert psi4['-']^2 eq 3600*x[2]^2*y[4];
  assert psi4['-']*psi6['-'] eq -3780*x[2]^3*y[4]-181440*x[2]*x[4]*y[4]-1270080*x[2]*y[4]^2;
  assert psi4['-']*chi10['-'] eq 15/2*x[2]*x[4]*y[4]^2+105/2*x[2]*y[4]^3;
  assert psi4['-']*chi12['-'] eq -5/4*x[2]^2*x[4]*y[4]^2-95/4*x[2]^2*y[4]^3-30*x[2]*x[4]*y[4]*x[6]-210*x[2]*y[4]^2*x[6];
  return;
end procedure;

test_Igusa_Qsqrt12();
test_Igusa_Qsqrt21();
