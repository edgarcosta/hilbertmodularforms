
load "config.m";

SetDebugOnError(true);
MaxDiscr := 1000;
MaxLevelNorm := 1000;

for D:=1 to MaxDiscr do
	F := QuadraticField(D);
	if Degree(F) eq 1 then continue; end if;
	printf "Now trying %o\n", F;
	
	NCl, m := NarrowClassGroup(F);	
	Ns := IdealsUpTo(MaxLevelNorm, F);
	bbs := [];
	for b in NCl do
		Append(~bbs, m(b));
	end for;
	printf "%o levels, %o components\n", #Ns, #bbs;
	for N in Ns do
		printf "Trying level %o\n", N;
		for bb in bbs do
			cs := Cusps(N, bb); //Gamma0
			//print cs;
			for c in cs do
				a, b := Explode(Eltseq(c[3]));
				a, b := NormalizeCusp(F, a, b, N);
				L, n := CuspResolutionIntersections(F, bb, N, a, b); //Gamma0;
				//printf "Cusp %o: %o x %o\n", c, L, n;
			end for;
		end for;
	end for;
end for;
				
