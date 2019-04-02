intrinsic UniversalIgusa(i::RngIntElt, prec::RngIntElt) -> any
{Computes the IgusaClebsch invariants for QQ(sqrt(i)), using specified precision}


_<x>:=PolynomialRing(Rationals());
F := NumberField(x^2-i);
M := HMFSpace(F, prec);



r2 := 1;
r4 := 1;
r6 := 1;
r10 := 1;

SiegEis4 := SiegelEisensteinPullback(M,4);
SiegEis6 := SiegelEisensteinPullback(M,6);
SiegEis10 := SiegelEisensteinPullback(M,10);
SiegEis12 := SiegelEisensteinPullback(M,12);

Chi10 := -43867/(2^12*3^5*5^2*7^1*53^1)*(SiegEis4*SiegEis6-SiegEis10);
Chi12Const := 131*593/(2^13*3^7*5^3*7^2*337^1);
Chi12Form := (3^2*7^2*SiegEis4^3+2^1*5^3*SiegEis6^2-691*SiegEis12);
Chi12 := Chi12Const*Chi12Form;

/*
I2 := -2^3*3^1*Chi12/Chi10;
I4 := 2^2*SiegEis4;
I6 := -2^3/3*SiegEis6 - 2^5*SiegEis4*Chi12/Chi10;
I10 := -2^14*Chi10;

Cl, mp := NarrowClassGroup(F);
reps := [mp(g):g in Cl];

g, r := ConstructGeneratorsAndRelations(M,reps[1],2,maxgenwt);
g, r := Relations(M,g,r,maxrelwt);

if not IsDefined(g,2) then g[2] := []; end if;
if not IsDefined(g,4) then g[4] := []; end if;
if not IsDefined(g,6) then g[6] := []; end if;
if not IsDefined(g,10) then g[10] := []; end if;

g2 := g;
g4 := g;
g6 := g;
g10 := g;

Append(~g2[2],I2);
Append(~g4[4],I4);
Append(~g6[6],I6);
Append(~g10[10],I10);


/*
g2[2] = Append(g2[2],I2);
g4[4] = Append(g4[4],I4);
g6[6] = Append(g6[6],I6);
g10[10] = Append(g10[10],I10);
*/
/*
_, r2 := Relations(M,g2,AssociativeArray(),2);
_, r4 := Relations(M,g4,AssociativeArray(),4);
_, r6 := Relations(M,g6,AssociativeArray(),6);
_, r10 := Relations(M,g10,AssociativeArray(),10);
*/

return SiegEis4,SiegEis6,SiegEis10,Chi10,Chi12;

end intrinsic;
