es := AssociativeArray();
ds := [13,17,29,37,41,53,61,73,89,97,101,109,113,137,149,157,173,181,193,197,229,233,241,257,269,277,281,293,313,317,337,349,353,373,389,397,401,409,421,433,449,457,461];
e_vals := [15,16,28,29,30,40,41,43,52,53,60,61,60,68,78,77,86,85,103,94,97,114,133,116,112,133,142,120,161,126,185,143,148,175,162,153,194,225,175,225,216,247,174];
assert #e_vals eq #ds;
for i in [1..#ds] do
    es[ds[i]] := e_vals[i];
end for;

printf "Testing Euler number of level 1, discriminant... D=";
for d in ds do
    printf "%o ", d;
    // at the moment the code still fails when the class group is
    // not a 2-group
    F := QuadraticField(d);
    if IsPowerOf(NarrowClassNumber(F),2) then
	G := Gamma0(F, 1*Integers(F));
	assert EulerNumber(G) eq es[d];
    end if;
end for;
