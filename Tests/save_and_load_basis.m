function test(Mk, basis, correct_prefix)
  prefix := SaveFilePrefix(Mk);
  assert prefix eq correct_prefix;

  filename := prefix cat ".m";
  SaveBasis(filename, basis);
  basis_load := LoadBasis(filename, Mk);
  if not basis eq basis_load then
    print "------------- Original basis -------------";
    print basis;
    print "------------- Loaded basis -------------";
    print basis_load;
  end if;

  assert basis eq basis_load;
  return "";
end function;

print "thing 1";
F := QuadraticField(5);
ZF := Integers(F);
prec := 50;
M := GradedRingOfHMFs(F, prec);
N := 14*ZF;
M22 := HMFSpace(M, N, [2, 2]);
S22 := CuspFormBasis(M22);
correct_prefix := "2.5-196.1-2.2-0";
test(M22, S22, correct_prefix);

print "thing 2";
N := 50*ZF;
H := HeckeCharacterGroup(N, [1, 2]);
chi := H.1^2*H.2;
M11chi := HMFSpace(M, N, [1, 1], chi);
E11chi := EisensteinBasis(M11chi);
correct_prefix := "2.5-2500.1-1.1-2.1";
test(M11chi, E11chi, correct_prefix);

print "thing 3";
N := 7*ZF;
M24 := HMFSpace(M, N, [2, 4]);
S24 := CuspFormBasis(M24);
correct_prefix := "2.5-49.1-2.4-0";
test(M24, S24, correct_prefix);

/*
print "thing 4";
R<x> := PolynomialRing(Rationals());
K<a> := NumberField(x^3 - x^2 - 2*x + 1);
ZK := Integers(K);
prec := 50;
M := GradedRingOfHMFs(K, prec);
N := 11*ZK;
k := [2, 2, 2];
M222 := HMFSpace(M, N, [2, 2, 2]);
S222 := CuspFormBasis(M222);
correct_prefix := "3.49-1331.1-2.2.2-0";
test(M222, S222, correct_prefix);
*/
