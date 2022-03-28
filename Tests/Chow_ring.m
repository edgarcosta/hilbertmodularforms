printf "Testing the computation of the Chow Ring for QQ(sqrt(13))...";

// Basic tests.
K := QuadraticField(13);
G := CongruenceSubgroup(K);
R := ChowRing(G);

gens := Generators(R);
reso := ResolutionCycles(R);
resokeys := Keys(reso);

assert GeneratorInfo(R.1) eq "Canonical";
assert #[p : p in resokeys | p`SingularityType eq "Quotient"] eq 6;

shouldbethis := {* <3, 1, -1>^^2, <3, 1, 1>^^2, <2, 1, 1>^^2 *};
assert {p`SingularityInfo : p in resokeys | p`SingularityType eq "Quotient"} eq shouldbethis;

// Test for a crash.
for g in gens do
    info_list := GeneratorInfo(g);
end for;

// Test level.
K := QuadraticField(13);
ZK := MaximalOrder(K);
G := CongruenceSubgroup(K, 2*ZK);
R := ChowRing(G);

reso := ResolutionCycles(R);
resokeys := Keys(reso);

assert #[p : p in resokeys | p`SingularityType eq "Quotient"] eq 0;

// All tests passed.
return true;
