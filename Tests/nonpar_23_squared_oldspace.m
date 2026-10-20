// Same flavor of test as nonpar_23_squared.m (a weight [2,3] quadratic
// nebentypus space squares into weight [4,6]), but at a level with a
// genuinely nontrivial old subspace, to check that the degeneracy
// operators / OldCuspFormBasis machinery works correctly for nonparitious
// weight with nontrivial nebentypus.
//
// The character has conductor equal to the prime above 23; extending the
// level by the (small, ramified) prime above 2 introduces an oldspace.

F := QuadraticField(2);
ZF := Integers(F);
M := GradedRingOfHMFs(F, 200);

p23 := Factorization(23*ZF)[1][1];
p2 := Factorization(2*ZF)[1][1];
N := p23*p2;

H0 := HeckeCharacterGroup(p23, [1, 2]);
chi0 := 0;
for i in [1..Ngens(H0)] do
  if Order(H0.i) eq 2 then
    chi0 := H0.i;
  end if;
end for;
assert chi0 cmpne 0;

n := Degree(F);
chi := Extend(chi0, N, [1..n]);
assert Order(chi) eq 2;

// The base (conductor) level space -- these forms should show up as
// oldforms once we go up to level N.
Mk0 := HMFSpace(M, p23, [2, 3], chi0);
Sk0 := CuspFormBasis(Mk0);
assert #Sk0 eq 2;

Mk := HMFSpace(M, N, [2, 3], chi);
NewSk := NewCuspFormBasis(Mk);
OldSk := OldCuspFormBasis(Mk);
assert #NewSk eq 2;
assert #OldSk eq 4;

Sk := CuspFormBasis(Mk);
assert #Sk eq #NewSk + #OldSk;
assert #LinearDependence(Sk) eq 0;

// Check the level-p23 forms actually embed inside the oldspace at level N.
Sk0_incl := [Inclusion(f, Mk, p2) : f in Sk0];
assert #LinearDependence(Sk0_incl) eq 0;
assert #Intersection(Sk0_incl, OldSk) eq #Sk0_incl;

// Same squaring check as nonpar_23_squared.m, now at a level with a
// nontrivial old subspace.
M46 := HMFSpace(M, N, [4, 6]);
S46 := CuspFormBasis(M46);
assert #S46 eq 45;
assert #LinearDependence(S46) eq 0;

f := Sk[1];
assert #Intersection([f^2], S46) eq 1;
