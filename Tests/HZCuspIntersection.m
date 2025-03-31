procedure testHZ(D, bs, mults)
    F := QuadraticField(D);
    ZF<z> := Integers(F);
    N := 1*ZF;
    for b in bs do
	Gamma := CongruenceSubgroup("SL", "Gamma0", F, N, b);
        for t in Keys(mults[b]) do
            results:= HZCuspIntersection(Gamma, t);
            for i->res in results do
                pass := false;
                // assert CanonicalCyclicShift(res) eq CanonicalCyclicShift(mults[b][t][i]);
		if res ne mults[b][t][i] then
		    printf "res = %o, mults[%o][%o][%o] = %o", res, IdealOneLine(b), t, i, mults[b][t][i];
		    assert false;
		end if;
            end for;
        end for;
    end for;
end procedure;

procedure testHZComponents(D, bs, mults)
    F := QuadraticField(D);
    ZF<z> := Integers(F);
    N := 1*ZF;
    for b in bs do
	Gamma := CongruenceSubgroup("SL", "Gamma0", F, N, b);
        for t in Keys(mults[b]) do
            results := HZCuspIntersection(Gamma, t);
	    results_by_comp := HZCuspIntersectionComponents(Gamma, t);

	    ncusps := #results[1];
	    sum_res_by_comp := [ [&+[comp[i] : comp in res]
				  : i in [1..ncusps]] : res in results_by_comp];
	    assert sum_res_by_comp eq results;
        end for;
    end for;
end procedure;

Ds := [13, 60];
bs := AssociativeArray(Ds);
for d in Ds do
    ZF<z> := Integers(QuadraticField(d));
    cl_plus_F, cl_plus_map := NarrowClassGroup(ZF);
    bs[d] := [cl_plus_map(x) : x in cl_plus_F];
end for;


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
mults[60][b][2] := [[1,0],[1,0]];
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
mults[60][b][3] := [[1,0,0],[1,0,0]];
mults[60][b][7] := [[0,1,1],[0,1,1]];
mults[60][b][22] := [[2,1,1],[2,1,1]];
mults[60][b][30] := [[0,1,1],[0,1,1]];

printf "\n\tTesting Example 1 in [vdG] p. 92...";
testHZ(13, bs[13], mults[13]);
print "Success!";

printf "\tTesting Example 2 in [vdG] p.93...";
// Note that vdG is doing the Hurwitz-Maass extension,
// which is a Z/2-extension of our group

testHZ(60, bs[60], mults[60]);
print "Success!";


testHZComponents(13, bs[13], mults[13]);

testHZComponents(60, bs[60], mults[60]);
