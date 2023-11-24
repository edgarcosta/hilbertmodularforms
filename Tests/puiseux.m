F := QuadraticField(5);
ZF := Integers(F);
prec := 20;
M := GradedRingOfHMFs(F, prec);
M22 := HMFSpace(M, 7*ZF, [2,2]);
K1 := Rationals();
K2 := SplittingField(F);

// construct HMFSerPuis rings
R := cHMFSerPuis(M, K1);
S := cHMFSerPuis(M, K2);;

// test compositum
T := Compositum(R, S);
assert S eq T;

bb := 1*ZF;
reps := FunDomainReps(M)[bb];
true_coeffs := [];

// test "monomial-by-monomial" construction 
f_ser := RngSerPuisZero(R);
for nu in reps do
  a := Random(K1, 10);
  Append(~true_coeffs, a);
  f_ser +:= RngSerPuisMonomial(R, nu, a);
end for;
f := cHMFSerPuisElt(M22, bb, f_ser);

// test coefficient access
fourier_coeffs := [];
for nu in reps do
  Append(~fourier_coeffs, Coefficient(f, F!nu));
end for;
assert true_coeffs eq fourier_coeffs;

// test "monomial-by-monomial" construction
// over a larger field
g_ser := RngSerPuisZero(S);
for nu in reps do
  g_ser +:= RngSerPuisMonomial(S, nu, Random(K2, 10));
end for;
g := cHMFSerPuisElt(M22, bb, g_ser : coeff_ring := K2);

// test coercion
f_S := S!f;
f_R := R!f_S;
assert f eq f_R;

S22 := CuspFormBasis(M22);
E22 := EisensteinBasis(M22);
f_cmp := Components(S22[1])[bb];
g_cmp := Components(E22[1])[bb];
h_cmp := f_cmp / g_cmp;

iden := HMFSerPuisIdentity(M22, bb);
f_true_coeffs := Coefficients(f_cmp); 
g_true_coeffs := Coefficients(g_cmp);

f := cHMFSerPuisElt(M22, bb, f_true_coeffs);
g := cHMFSerPuisElt(M22, bb, g_true_coeffs);

function test(f, reps, true_coeffs)
  // f::HMFSerPuisElt
  // reps::SeqEnum[FldElt]
  // true_coeffs::SeqEnum[FldElt] 
  for i in [1 .. #reps] do
    assert Coefficient(f, reps[i]) eq true_coeffs[i];
  end for;
  return "";
end function;

// test arithmetic operations

first_ten_reps := [reps[i] : i in [1 .. 10]];

true_coeffs := [ 0, 1, 0, -4, 5, -3, -3, -4, 0, 0 ];
test(f, first_ten_reps, true_coeffs);

true_coeffs := [ 1, 120, 600, 720, 1200, 1440, 1440, 2520, 2400, 2400 ];
test(g, first_ten_reps, true_coeffs);

h := f + g;
true_coeffs := [ 1, 121, 600, 716, 1205, 1437, 1437, 2516, 2400, 2400 ];
test(h, first_ten_reps, true_coeffs);

h := 3 * f;
true_coeffs := [ 0, 3, 0, -12, 15, -9, -9, -12, 0, 0 ];
test(h, first_ten_reps, true_coeffs);

h := f * g;
true_coeffs := [ 0, 1, 120, 236, 845, 837, 837, 2276, 1080, 1080 ];
test(h, first_ten_reps, true_coeffs);

h := f^2;
true_coeffs := [ 0, 0, 1, 2, 2, -8, -8, -6, 4, 4 ];
test(h, first_ten_reps, true_coeffs);

h := f / g;
true_coeffs := [ 0, 1, -120, -244, 13565, 42357, 42357, -1499884, -6466680, -6466680 ];
test(h, first_ten_reps, true_coeffs);

assert g / g eq HMFSerPuisIdentity(M22, bb);
assert g * g^-1 eq HMFSerPuisIdentity(M22, bb);
assert f - f eq HMFSerPuisZero(M22, bb);
