PREC := 50;

procedure test(Mk, basis, correct_prefix)
  prefix := SaveFilePrefix(Mk);
  if not prefix eq correct_prefix then
    print "prefix is", prefix;
    print "but it should be", correct_prefix;
  end if;
  assert prefix eq correct_prefix;

  save_dir := "./Precomputations/";
  filepath := save_dir cat prefix cat "_test";
  SaveBasis(filepath, basis);
  b, basis_load := LoadBasis(filepath, Mk);
  assert b;
  if not basis eq basis_load then
    print "------------- Original basis -------------";
    print basis;
    print "------------- Loaded basis -------------";
    print basis_load;
  end if;

  assert basis eq basis_load;
  basis_load_2 := LoadBasis(filepath);
  assert #basis eq #basis_load_2;

  F := BaseField(Mk);
  K := BaseField(Parent(basis_load_2[1]));
  ZK := Integers(K);
  for i in [1 .. #basis] do
    f := basis[i];
    g := basis_load_2[i];
    for pp in PrimesUpTo(PREC, F) do
      assert Coefficient(f, pp) eq Coefficient(g, ZK!!pp);
    end for;
  end for;
end procedure;

print "thing 1";
F := QuadraticField(5);
ZF := Integers(F);
prec := PREC;
M := GradedRingOfHMFs(F, prec);
N := 14*ZF;
M22 := HMFSpace(M, N, [2, 2]);
S22 := CuspFormBasis(M22);
correct_prefix := "-5.0.1=196.1=2.2=0_50";
test(M22, S22, correct_prefix);

print "thing 2";
N := 50*ZF;
H := HeckeCharacterGroup(N, [1, 2]);
chi := H.1^2*H.2;
M11chi := HMFSpace(M, N, [1, 1], chi);
E11chi := EisensteinBasis(M11chi);
correct_prefix := "-5.0.1=2500.1=1.1=2.1_50";
test(M11chi, E11chi, correct_prefix);


print "thing 3";
N := 7*ZF;
M24 := HMFSpace(M, N, [2, 4]);
S24 := CuspFormBasis(M24);
correct_prefix := "-5.0.1=49.1=2.4=0_50";
test(M24, S24, correct_prefix);

// uncomment once cubic field stuff works without errors
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
correct_prefix := "1.-2.-1.1=1331.1=2.2.2=0_50";
test(M222, S222, correct_prefix);
*/
