// Test for Eisenstein series computation over cubic fields
// This test verifies the fix for issue #472 where hardcoded [1,2] 
// was causing failures for fields of degree greater than 2

printf "Testing Eisenstein series over cubic field... ";

Q := Rationals();
nf := ext<Q|Polynomial([4,-5,-1,1])>; // cubic field
M := GradedRingOfHMFs(nf, 100);
ps := PrimesUpTo(100, nf);
hmf2_2 := HMFSpace(M, ps[1], [2,2,2], Identity(HeckeCharacterGroup(ps[1], [1..3])));
es := EisensteinBasis(hmf2_2);
assert #es eq 2;

printf "Success!\n";