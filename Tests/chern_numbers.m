// Chern numbers tests

// We compare our results with the table in the back of van der Geer.

// Entries in the table consist of
// Discriminant, sign of fundamental unit, genus (component), <2,1,1> singularities,
// <3,1,1> singularities, <3, 1, -1> singularities, number of cuspidal resoluton cycles,
// euler number (c2), Arithmetic genus, First chern number of the minimal model,
// picard number.

dot := -100;
unk := -100; // Unlisted value.

EULER_NUM_INDEX := 8;
ARITH_GENUS_INDEX := 9;


vdgTable := [*
    [* 5	, -1,     [1],  2, 1, 1,  1, 14, 1, dot,  12 *],
    [* 8	, -1,     [1],  2, 1, 1,  2, 15, 1, dot,  13 *],
    [* 12	,  1,   [1,1],  3, 2, 0,  2, 16, 1, dot,  14 *],
    [* 12	,  1, [-1,-1],  3, 0, 2,  4, 16, 1, dot,  14 *],
    [* 13	, -1,     [1],  2, 2, 2,  3, 15, 1, dot,  13 *],
    [* 17	, -1,     [1],  4, 1, 1,  5, 16, 1, dot,  14 *],
    [* 21	,  1,   [1,1],  4, 4, 1,  2, 18, 1, dot,  14 *],
    [* 21	,  1, [-1,-1],  4, 1, 4,  6, 25, 2,   0, unk *],
    [* 24	,  1,   [1,1],  6, 3, 0,  4, 19, 1, dot, unk *],
    [* 24	,  1, [-1,-1],  6, 0, 3,  8, 26, 2,   0, unk *],
    [* 28	,  1,   [1,1],  4, 2, 2,  4, 20, 1, dot, unk *],
    [* 28	,  1, [-1,-1],  4, 2, 2, 10, 26, 2,   0, unk *],
    [* 29	, -1,     [1],  6, 3, 3,  5, 28, 2,   0,  23 *],
    [* 33	,  1,   [1,1],  4, 3, 0,  8, 21, 1, dot, unk *],
    [* 33	,  1, [-1,-1],  4, 0, 3, 12, 28, 2,   0, unk *],
    [* 37	, -1,     [1],  2, 4, 4,  7, 29, 2,   0,  24 *],
    [* 40	, -1,   [1,1],  6, 2, 2, 12, 32, 2,   0, unk *],
    [* 40	, -1, [-1,-1],  6, 2, 2,  8, 28, 2,   0, unk *],
    [* 41	, -1,     [1],  8, 1, 1, 11, 30, 2,   0,  25 *],
    [* 44	,  1,   [1,1], 10, 2, 2,  6, 32, 2,   0, unk *],
    [* 44	,  1, [-1,-1], 10, 2, 2, 12, 38, 3,   0, unk *],
    [* 53	, -1,     [1],  6, 5, 5,  7, 40, 3,   0,  32 *]
 *];

// Check data entry.
assert #{#entry : entry in vdgTable} eq 1;

function Find(disc, signs)
    for entry in vdgTable do
	if entry[1] eq disc and entry[3] eq signs then
	    return entry;
	end if;
    end for;
    error "Entry not found in table.", disc, signs;
end function;

function CorrectChernValues(entry)
    e := entry[EULER_NUM_INDEX];
    return 12 * entry[ARITH_GENUS_INDEX] - e, e;
end function;

quadraticFields := Setseq({QuadraticField(D) : D in [2..53] | IsSquarefree(D)});
Sort(~quadraticFields, func<x,y | Discriminant(x) - Discriminant(y)>);
quadraticFields := [K : K in quadraticFields | Discriminant(K) le 53];

for K in quadraticFields do

    // Extract components
    cg, mp := NarrowClassGroup(K);

    for b in cg do
	disc := Discriminant(K);

	if disc in [12] then continue; end if;

	if b eq Identity(cg) then
	    signs := [1 : i in [1..#cg]];
	else
	    signs := [-1 : i in [1..#cg]];
	end if;

	entry := Find(disc, signs);

	// Compute the correct chern number.
	c1, c2 := CorrectChernValues(entry);


	// Now compute the HMS
	ZK := MaximalOrder(K);
	B := mp(b);
	G := CongruenceSubgroup(K, 1*ZK, B);

	a, c := ChernNumbers(ChowRing(G));
	boo := a eq c1 and c eq c2;
	if not boo then
	    error "Values not equal:", disc, signs,  [c1, c2], [a, c];
	end if;
    end for;

end for;
