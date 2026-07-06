AttachSpec("spec");

F := QuadraticField(2);
ZF := Integers(F);
pp := Factorization(2*ZF)[1][1];

// We can just compute the spaces at low precision to be fast!
prec := 30;
M := GradedRingOfHMFs(F, prec);

Mk2 := HMFSpace(M, pp, [2,2]);
B2 := Basis(Mk2);
assert #B2 eq 2;

Mk4 := HMFSpace(M, pp, [4,4]);
B4 := Basis(Mk4);
assert #B4 eq 4;

// We know the weight 4 generator is the one that doesn't come from weight 2.
// We can just construct an associative array of generators and relations.
Gens := AssociativeArray();
Gens[2] := B2;
// In CanonicalRing, ApproximateGradedRing computes the relations, but we just need
// to test CandidateAlgIndependentElements.
// Since CandidateAlgIndependentElements only requires Gens and Relations up to degree 4.
// There are no relations up to degree 4.
Relations := AssociativeArray();
Relations[2] := [];
Relations[4] := [];

// Wait, the weight 4 generator in CanonicalRing is computed by finding the complement
// of the monomials from weight 2. We can just use the basis B4 directly!
// But wait, the polynomials in Gens[4] are just the new generators. 
// For this test, it doesn't matter if we use the exact new generator, any element not in the span of B2^2 works.
// We can just use B4[4] as the new generator! (Or find one).
// Let's just use B4 as if it were the new generators.
// Actually, CandidateAlgIndependentElements just needs SOME forms.
// Let's do it exactly as CandidateAlgIndependentElements expects:
// Gens[2] = [g2a, g2b]
// Gens[4] = [g4]
// But how do we find g4? We just need ANY form in B4 that is independent of B2^2.
mons := [B2[1]^2, B2[1]*B2[2], B2[2]^2];
V_mons := CoefficientsMatrix(mons : prec:=prec);
for f in B4 do
    V_f := CoefficientsMatrix([f] : prec:=prec);
    if Rank(VerticalJoin(V_mons, V_f)) eq 4 then
        Gens[4] := [f];
        break;
    end if;
end for;
assert IsDefined(Gens, 4);

// Now test CandidateAlgIndependentElements!
// Before the fix, it would pick the first 3 linearly independent monomials of degree 4.
// The monomials of degree 4 are Gens[2]^2 and Gens[4].
// If we run CandidateAlgIndependentElements, it should return an algebraically independent triple (certified=true).
candidates, certified := CandidateAlgIndependentElements(Gens, Relations, 3 : IdealClassesSupport := [1*ZF]);
assert certified;

printf "CandidateAlgIndependentElements regression test PASSED\n";
exit;
