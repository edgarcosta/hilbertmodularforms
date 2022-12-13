printf "Testing Example 1 in [vdG] p. 92...";
D := 13;
F := QuadraticField(D);
ZF := Integers(F);
N := 1*ZF;
b := 1*ZF;
mults := AssociativeArray();
mults[1] := [1,0,0];
mults[3] := [0,1,1];
mults[4] := [1,0,0];
mults[9] := [3,1,1];
mults[12] := [0,1,1];
mults[13] := [0,1,1];
mults[29] := [0,3,3];
mults[36] := [3,1,1];

assert &and[HZCuspIntersection(F,t,N,b) eq [mults[t]] : t in Keys(mults)];
    
