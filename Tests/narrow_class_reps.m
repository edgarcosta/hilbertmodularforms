printf "Testing deterministic narrow class reps ...";
// generated with
/*
for D in [1..100] do
  K, _ := Polredabs(QuadraticField(D));
  if Degree(K) ne 2 or #NarrowClassGroup(K) eq 1 then
    continue;
  end if;
  M := GradedRingOfHMFs(K, 2);
  Sprintf("A[Polynomial(%o)] := %m", Sprint(Coefficients(DefiningPolynomial(K))), [LMFDBLabel(elt) : elt in NarrowClassGroupReps(M)]);
end for;
*/

A := AssociativeArray();

A[Polynomial([ -3, 0, 1 ])] := [ Strings() | "1.1", "2.1" ];
A[Polynomial([ -6, 0, 1 ])] := [ Strings() | "1.1", "2.1" ];
A[Polynomial([ -7, 0, 1 ])] := [ Strings() | "1.1", "3.1" ];
A[Polynomial([ -10, 0, 1 ])] := [ Strings() | "1.1", "2.1" ];
A[Polynomial([ -11, 0, 1 ])] := [ Strings() | "1.1", "2.1" ];
A[Polynomial([ -3, 0, 1 ])] := [ Strings() | "1.1", "2.1" ];
A[Polynomial([ -14, 0, 1 ])] := [ Strings() | "1.1", "5.1" ];
A[Polynomial([ -15, 0, 1 ])] := [ Strings() | "1.1", "2.1", "6.1", "3.1" ];
A[Polynomial([ -19, 0, 1 ])] := [ Strings() | "1.1", "2.1" ];
A[Polynomial([ -5, -1, 1 ])] := [ Strings() | "1.1", "3.1" ];
A[Polynomial([ -22, 0, 1 ])] := [ Strings() | "1.1", "2.1" ];
A[Polynomial([ -23, 0, 1 ])] := [ Strings() | "1.1", "7.1" ];
A[Polynomial([ -6, 0, 1 ])] := [ Strings() | "1.1", "2.1" ];
A[Polynomial([ -26, 0, 1 ])] := [ Strings() | "1.1", "2.1" ];
A[Polynomial([ -3, 0, 1 ])] := [ Strings() | "1.1", "2.1" ];
A[Polynomial([ -7, 0, 1 ])] := [ Strings() | "1.1", "3.1" ];
A[Polynomial([ -30, 0, 1 ])] := [ Strings() | "1.1", "2.1", "5.1", "7.1" ];
A[Polynomial([ -31, 0, 1 ])] := [ Strings() | "1.1", "3.1" ];
A[Polynomial([ -8, -1, 1 ])] := [ Strings() | "1.1", "2.1" ];
A[Polynomial([ -34, 0, 1 ])] := [ Strings() | "1.1", "3.1", "9.1", "3.2" ];
A[Polynomial([ -35, 0, 1 ])] := [ Strings() | "1.1", "2.1", "10.1", "5.1" ];
A[Polynomial([ -38, 0, 1 ])] := [ Strings() | "1.1", "2.1" ];
A[Polynomial([ -39, 0, 1 ])] := [ Strings() | "1.1", "2.1", "3.1", "6.1" ];
A[Polynomial([ -10, 0, 1 ])] := [ Strings() | "1.1", "2.1" ];
A[Polynomial([ -42, 0, 1 ])] := [ Strings() | "1.1", "2.1", "6.1", "3.1" ];
A[Polynomial([ -43, 0, 1 ])] := [ Strings() | "1.1", "2.1" ];
A[Polynomial([ -11, 0, 1 ])] := [ Strings() | "1.1", "2.1" ];
A[Polynomial([ -46, 0, 1 ])] := [ Strings() | "1.1", "5.1" ];
A[Polynomial([ -47, 0, 1 ])] := [ Strings() | "1.1", "11.1" ];
A[Polynomial([ -3, 0, 1 ])] := [ Strings() | "1.1", "2.1" ];
A[Polynomial([ -51, 0, 1 ])] := [ Strings() | "1.1", "3.1", "2.1", "5.1" ];
A[Polynomial([ -6, 0, 1 ])] := [ Strings() | "1.1", "2.1" ];
A[Polynomial([ -55, 0, 1 ])] := [ Strings() | "1.1", "2.1", "6.1", "3.1" ];
A[Polynomial([ -14, 0, 1 ])] := [ Strings() | "1.1", "5.1" ];
A[Polynomial([ -14, -1, 1 ])] := [ Strings() | "1.1", "2.1" ];
A[Polynomial([ -58, 0, 1 ])] := [ Strings() | "1.1", "2.1" ];
A[Polynomial([ -59, 0, 1 ])] := [ Strings() | "1.1", "2.1" ];
A[Polynomial([ -15, 0, 1 ])] := [ Strings() | "1.1", "2.1", "6.1", "3.1" ];
A[Polynomial([ -62, 0, 1 ])] := [ Strings() | "1.1", "13.1" ];
A[Polynomial([ -7, 0, 1 ])] := [ Strings() | "1.1", "3.1" ];
A[Polynomial([ -16, -1, 1 ])] := [ Strings() | "1.1", "2.1" ];
A[Polynomial([ -66, 0, 1 ])] := [ Strings() | "1.1", "3.1", "2.1", "6.1" ];
A[Polynomial([ -67, 0, 1 ])] := [ Strings() | "1.1", "2.1" ];
A[Polynomial([ -17, -1, 1 ])] := [ Strings() | "1.1", "5.1" ];
A[Polynomial([ -70, 0, 1 ])] := [ Strings() | "1.1", "2.1", "5.1", "3.1" ];
A[Polynomial([ -71, 0, 1 ])] := [ Strings() | "1.1", "7.1" ];
A[Polynomial([ -74, 0, 1 ])] := [ Strings() | "1.1", "2.1" ];
A[Polynomial([ -3, 0, 1 ])] := [ Strings() | "1.1", "2.1" ];
A[Polynomial([ -19, 0, 1 ])] := [ Strings() | "1.1", "2.1" ];
A[Polynomial([ -19, -1, 1 ])] := [ Strings() | "1.1", "7.1" ];
A[Polynomial([ -78, 0, 1 ])] := [ Strings() | "1.1", "2.1", "14.1", "7.1" ];
A[Polynomial([ -79, 0, 1 ])] := [ Strings() | "1.1", "3.1", "5.1", "15.1", "5.2", "3.2" ];
A[Polynomial([ -82, 0, 1 ])] := [ Strings() | "1.1", "3.2", "2.1", "3.1" ];
A[Polynomial([ -83, 0, 1 ])] := [ Strings() | "1.1", "2.1" ];
A[Polynomial([ -5, -1, 1 ])] := [ Strings() | "1.1", "3.1" ];
A[Polynomial([ -21, -1, 1 ])] := [ Strings() | "1.1", "3.1" ];
A[Polynomial([ -86, 0, 1 ])] := [ Strings() | "1.1", "2.1" ];
A[Polynomial([ -87, 0, 1 ])] := [ Strings() | "1.1", "2.1", "6.1", "3.1" ];
A[Polynomial([ -22, 0, 1 ])] := [ Strings() | "1.1", "2.1" ];
A[Polynomial([ -10, 0, 1 ])] := [ Strings() | "1.1", "2.1" ];
A[Polynomial([ -91, 0, 1 ])] := [ Strings() | "1.1", "2.1", "3.1", "5.1" ];
A[Polynomial([ -23, 0, 1 ])] := [ Strings() | "1.1", "7.1" ];
A[Polynomial([ -23, -1, 1 ])] := [ Strings() | "1.1", "3.1" ];
A[Polynomial([ -94, 0, 1 ])] := [ Strings() | "1.1", "5.1" ];
A[Polynomial([ -95, 0, 1 ])] := [ Strings() | "1.1", "2.1", "14.1", "7.1" ];
A[Polynomial([ -6, 0, 1 ])] := [ Strings() | "1.1", "2.1" ];
A[Polynomial([ -11, 0, 1 ])] := [ Strings() | "1.1", "2.1" ];


for f->v in A do
  M := GradedRingOfHMFs(NumberField(f), 0);
  assert v eq [LMFDBLabel(elt) : elt in NarrowClassGroupReps(M)];
end for;
