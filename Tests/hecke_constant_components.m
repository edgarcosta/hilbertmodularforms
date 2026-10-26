SetNthreads(1);

F := QuadraticField(229);
ZF := Integers(F);
M := GradedRingOfHMFs(F, 30);
Mk := HMFSpace(M, 1*ZF, [2,2]);
H := HeckeCharacterGroup(1*ZF);
eta := AssociatedPrimitiveCharacter(H.1);
assert Order(eta) eq 3;
E := EisensteinSeries(Mk, eta, eta^-1);
pp := Decomposition(ZF, 3)[1][1];
assert Norm(pp) eq 3;

T := HeckeOperator(E, pp);
lambda := Coefficient(E, pp) / Coefficient(E, 1*ZF);
bbs := NarrowClassGroupReps(M);
assert #bbs eq 3;

// Classes of order two conceal the direction of the component shift.
positive_equal := &and[Coefficient(T, nn) eq lambda*Coefficient(E, nn)
  : nn in Ideals(M) | not IsZero(nn) and Norm(nn) le Precision(T)];
constant_equal := [Coefficient(T, bb, F!0) eq lambda*Coefficient(E, bb, F!0)
  : bb in bbs];
print "Positive coefficients satisfy the eigenvalue equation:", positive_equal;
print "Component constants satisfying the eigenvalue equation:",
  #[equal : equal in constant_equal | equal];
assert positive_equal;
assert &and constant_equal;
