procedure testHZ(D, bs, mults)
    F := QuadraticField(D);
    ZF := Integers(F);
    N := 1*ZF;
    for b in bs do
        print [HZCuspIntersection(F,t,N,b)
		       : t in Keys(mults[b])];
        print [mults[b][t] 
		       : t in Keys(mults[b])];
	    assert &and[HZCuspIntersection(F,t,N,b) eq mults[b][t] 
		        : t in Keys(mults[b])];
    end for;
end procedure;

Ds := [13,60];
bs := AssociativeArray(Ds);
bs[13] := [1*Integers(QuadraticField(13))];
F := QuadraticField(60);
cl_plus_F, cl_plus_map := NarrowClassGroup(F);
bs[60] := [cl_plus_map(x) : x in cl_plus_F];

mults := AssociativeArray(Ds);
for D in Ds do
    mults[D] := AssociativeArray(bs[D]);
    for b in bs[D] do
	mults[D][b] := AssociativeArray();
    end for;
end for;

b := bs[13][1];
mults[13][b][1] := [[1,0,0]];
mults[13][b][3] := [[0,1,1]];
mults[13][b][4] := [[1,0,0]];
mults[13][b][9] := [[3,1,1]];
mults[13][b][12] := [[0,1,1]];
mults[13][b][13] := [[0,1,1]];
mults[13][b][29] := [[0,3,3]];
mults[13][b][36] := [[3,1,1]];

b := bs[60][1];
mults[60][b][1] := [[1],[1]];
mults[60][b][10] := [[2],[2]];

b := bs[60][2];
mults[60][b][2] := [[0,1],[0,1]];
mults[60][b][17] := [[2,2],[2,2]];

b := bs[60][3];
mults[60][b][6] := [[1,0,0,0,0,0],[1,0,0,0,0,0]];
mults[60][b][11] := [[0,1,0,0,0,1],[0,1,0,0,0,1]];
mults[60][b][14] := [[0,0,1,0,1,0],[0,0,1,0,1,0]];
mults[60][b][15] := [[0,0,0,1,0,0],[0,0,0,1,0,0]];
mults[60][b][35] := [[2,1,0,0,0,1],[2,1,0,0,0,1]];
mults[60][b][51] := [[0,1,1,0,1,1],[0,1,1,0,1,1]];
mults[60][b][59] := [[0,0,1,2,1,0],[0,0,1,2,1,0]];

b := bs[60][4];
mults[60][b][3] := [[0,1,0],[0,1,0]];
mults[60][b][7] := [[1,0,1],[1,0,1]];
mults[60][b][22] := [[1,2,1],[1,2,1]];
mults[60][b][30] := [[1,0,1],[1,0,1]];
		       
printf "Testing Example 1 in [vdG] p. 92...";
testHZ(13, bs[13], mults[13]);
    
printf "Tesing Example 2 in [vdG] p.93...";
// Note that vdG is doing the Hurwitz-Maass extension,
// which is a Z/2-extension of our group

testHZ(60, bs[60], mults[60]);



