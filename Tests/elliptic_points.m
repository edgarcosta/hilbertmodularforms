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
A2_INDEX := 4;
A3PLUS_INDEX  := 5;
A3MINUS_INDEX := 6;


//FIXME use vanderGeerTable
vdgTable := [*
    [* 5  , -1,     [1],  2, 1, 1,  1, 14, 1, dot,  12 *],
    [* 8  , -1,     [1],  2, 1, 1,  2, 15, 1, dot,  13 *],
    [* 12 ,  1,   [1,1],  3, 2, 0,  2, 16, 1, dot,  14 *],
    [* 12 ,  1, [-1,-1],  3, 0, 2,  4, 16, 1, dot,  14 *],
    [* 13 , -1,     [1],  2, 2, 2,  3, 15, 1, dot,  13 *],
    [* 17 , -1,     [1],  4, 1, 1,  5, 16, 1, dot,  14 *],
    [* 21 ,  1,   [1,1],  4, 4, 1,  2, 18, 1, dot,  14 *],
    [* 21 ,  1, [-1,-1],  4, 1, 4,  6, 25, 2,   0, unk *],
    [* 24 ,  1,   [1,1],  6, 3, 0,  4, 19, 1, dot, unk *],
    [* 24 ,  1, [-1,-1],  6, 0, 3,  8, 26, 2,   0, unk *],
    [* 28 ,  1,   [1,1],  4, 2, 2,  4, 20, 1, dot, unk *],
    [* 28 ,  1, [-1,-1],  4, 2, 2, 10, 26, 2,   0, unk *],
    [* 29 , -1,     [1],  6, 3, 3,  5, 28, 2,   0,  23 *],
    [* 33 ,  1,   [1,1],  4, 3, 0,  8, 21, 1, dot, unk *],
    [* 33 ,  1, [-1,-1],  4, 0, 3, 12, 28, 2,   0, unk *],
    [* 37 , -1,     [1],  2, 4, 4,  7, 29, 2,   0,  24 *],
    [* 40 , -1,   [1,1],  6, 2, 2, 12, 32, 2,   0, unk *],
    [* 40 , -1, [-1,-1],  6, 2, 2,  8, 28, 2,   0, unk *],
    [* 41 , -1,     [1],  8, 1, 1, 11, 30, 2,   0,  25 *],
    [* 44 ,  1,   [1,1], 10, 2, 2,  6, 32, 2,   0, unk *],
    [* 44 ,  1, [-1,-1], 10, 2, 2, 12, 38, 3,   0, unk *],
    [* 53 , -1,     [1],  6, 5, 5,  7, 40, 3,   0,  32 *]
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

function CorrectEllipticPointCounts(entry)
    a2  := entry[A2_INDEX];
    a31 := entry[A3PLUS_INDEX];
    a32 := entry[A3MINUS_INDEX];
    return a2, a31, a32;
end function;

quadraticFields := Setseq({QuadraticField(D) : D in [2..53] | IsSquarefree(D)});
Sort(~quadraticFields, func<x,y | Discriminant(x) - Discriminant(y)>);
quadraticFields := [K : K in quadraticFields | Discriminant(K) le 53];

//print "Testing elliptic points data for disc=";
for K in quadraticFields do
    // Extract components
    cg, mp := NarrowClassGroup(K);

    disc := Discriminant(K);
//    if disc in [8, 12] then continue; end if;
    // printf "%o,", disc;

    // randomizing since otherwise it takes too long
    bs := [Random(cg) : i in [1..2]];
    for b in bs do
    
  if b eq Identity(cg) then
      signs := [1 : i in [1..#cg]];
  else
      signs := [-1 : i in [1..#cg]];
  end if;

  entry := Find(disc, signs);

        // Compute the numbers of elliptic points in the table.
  a2, a3p, a3m := CorrectEllipticPointCounts(entry);

  // Now compute the HMS
  ZK := MaximalOrder(K);
  B := mp(b);
  G_SL := CongruenceSubgroup("SL", "Gamma0", K, 1*ZK, B);
  G_GL := CongruenceSubgroup("GL+", "Gamma0", K, 1*ZK, B);

  A := CountEllipticPoints(G_SL);
        boo := (A[2][[1,1]] eq a2) and (A[3][[1,1]] eq a3p) and
         (A[3][[2,1]] eq a3m);
  if not boo then
      error "Values not equal:", disc, signs;
  end if;

        // Also check if the number of elliptic points are integers in the GL+ case.
        A := CountEllipticPoints(G_GL);
        assert &and [&and[count in Integers() : count in counts] : counts in A];

        // Also do an integrality check for levels.
	// randomizing since otherwise it takes too long
	Ns := [Random([1..13]) : i in [1..2]];
	for N in Ns do
        // for N in [1..13] do
	    printf "[%o; %o; %o],", Discriminant(ZK), N, IdealOneLine(B);
            G0N_SL := CongruenceSubgroup("SL", "Gamma0", K, N*ZK, B);
      G0N_GL := CongruenceSubgroup("GL+", "Gamma0", K, N*ZK, B);
            A := CountEllipticPoints(G0N_SL);
      assert &and [&and[count in Integers() : count in counts] :
       counts in A];
            A := CountEllipticPoints(G0N_GL);
            assert &and [&and[count in Integers() : count in counts] :
       counts in A];
        end for;
    end for;
end for;

// Print newline.
print "";

