
load "config.m";

SetDebugOnError(true);
MaxDiscr := 1000;
MaxLevelNorm := 1000;

count := 0;

for D:=1 to MaxDiscr do
	F := QuadraticField(D);
	if Degree(F) eq 1 then continue; end if;
	
	printf "Now trying %o\n", F;
	ZF := Integers(F);
	Pl := InfinitePlaces(F);
	
	NCl, _ := NarrowClassGroup(F);
	Ns := IdealsUpTo(MaxLevelNorm, F);
	
	printf "%o levels, %o components\n", #Ns, #NCl;
	count +:= #Ns * #NCl;
	/* for N in Ns do */
	/* 	printf "Trying level %o\n", N; */
	/* 	m := ClassGroupPrimeRepresentatives(ZF, N, Pl); */
	/* 	for x in Domain(m) do */
	/* 		bb := m(x); */
	/* 		cs := Cusps(N, bb); //Gamma0 */
	/* 		//print cs; */
	/* 		for c in cs do */
	/* 			a, b := Explode(Eltseq(c[3])); */
	/* 			a, b := NormalizeCusp(F, a, b, N); */
	/* 			L, n := CuspResolutionIntersections(F, bb, N, a, b); //Gamma0; */
	/* 			//printf "Cusp %o: %o x %o\n", c, L, n; */
	/* 		end for; */
	/* 	end for; */
	/* end for; */
end for;
				
printf "Total count %o\n", count;
