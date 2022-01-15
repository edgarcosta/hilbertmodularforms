// Warning - currently only testing trivial weight and character
dim_list := AssociativeArray();
/*
Generated with
foo.m:
// This is an arbitrary bound (the maximal discriminant in the first file in Nipp's database)
B := 457; 
fund_discs := [d : d in [1..B] | IsFundamentalDiscriminant(d)];
for d in fund_discs do
  dims := [];
  max_n := Floor(Sqrt(B/d));
  for n in [1..max_n] do
      // This function belongs to the package ModFrmAlg of AlgebraicModularForms
      total, cusp := getHilbertDims(d,n);
      Append(~dims, [total, cusp]);
  end for;
  dim_list[d] := dims;
end for;
strs := [Sprintf("dim_list[%o] := %o;\n", k, dim_list[k]) : k in Sort(SetToSequence(Keys(dim_list)))];
output_str := &cat strs;
fprintf "hilbertmodularforms/Tests/character_subspace.m", "%o", output_str;
*/

dim_list[5] := [
[ 1, 0 ],
[ 1, 0 ],
[ 1, 0 ],
[ 0, 0 ],
[ 0, 0 ],
[ 2, 1 ],
[ 2, 1 ],
[ 0, 0 ],
[ 0, 0 ]
];
dim_list[8] := [
[ 1, 0 ],
[ 0, 0 ],
[ 2, 1 ],
[ 0, 0 ],
[ 3, 2 ],
[ 0, 0 ],
[ 4, 3 ]
];
dim_list[12] := [
[ 2, 0 ],
[ 0, 0 ],
[ 0, 0 ],
[ 0, 0 ],
[ 6, 4 ],
[ 0, 0 ]
];
dim_list[13] := [
[ 1, 0 ],
[ 2, 1 ],
[ 2, 1 ],
[ 0, 0 ],
[ 4, 3 ]
];
dim_list[17] := [
[ 1, 0 ],
[ 2, 1 ],
[ 3, 2 ],
[ 0, 0 ],
[ 6, 5 ]
];
dim_list[21] := [
[ 2, 0 ],
[ 4, 2 ],
[ 0, 0 ],
[ 0, 0 ]
];
dim_list[24] := [
[ 3, 1 ],
[ 0, 0 ],
[ 0, 0 ],
[ 0, 0 ]
];
dim_list[28] := [
[ 3, 1 ],
[ 0, 0 ],
[ 6, 4 ],
[ 0, 0 ]
];
dim_list[29] := [
[ 2, 1 ],
[ 4, 3 ],
[ 5, 4 ]
];
dim_list[33] := [
[ 3, 1 ],
[ 4, 2 ],
[ 0, 0 ]
];
dim_list[37] := [
[ 2, 1 ],
[ 5, 4 ],
[ 4, 3 ]
];
dim_list[40] := [
[ 4, 2 ],
[ 0, 0 ],
[ 8, 6 ]
];
dim_list[41] := [
[ 2, 1 ],
[ 3, 2 ],
[ 9, 8 ]
];
dim_list[44] := [
[ 4, 2 ],
[ 0, 0 ],
[ 12, 10 ]
];
dim_list[53] := [
[ 3, 2 ],
[ 7, 6 ]
];
dim_list[56] := [
[ 5, 3 ],
[ 0, 0 ]
];
dim_list[57] := [
[ 4, 2 ],
[ 6, 4 ]
];
dim_list[60] := [
[ 8, 4 ],
[ 0, 0 ]
];
dim_list[61] := [
[ 3, 2 ],
[ 8, 7 ]
];
dim_list[65] := [
[ 4, 2 ],
[ 6, 4 ]
];
dim_list[69] := [
[ 5, 3 ],
[ 12, 10 ]
];
dim_list[73] := [
[ 3, 2 ],
[ 5, 4 ]
];
dim_list[76] := [
[ 6, 4 ],
[ 0, 0 ]
];
dim_list[77] := [
[ 5, 3 ],
[ 12, 10 ]
];
dim_list[85] := [
[ 6, 4 ],
[ 14, 12 ]
];
dim_list[88] := [
[ 7, 5 ],
[ 0, 0 ]
];
dim_list[89] := [
[ 4, 3 ],
[ 5, 4 ]
];
dim_list[92] := [
[ 7, 5 ],
[ 0, 0 ]
];
dim_list[93] := [
[ 6, 4 ],
[ 16, 14 ]
];
dim_list[97] := [
[ 4, 3 ],
[ 6, 5 ]
];
dim_list[101] := [
[ 5, 4 ],
[ 13, 12 ]
];
dim_list[104] := [
[ 8, 6 ],
[ 0, 0 ]
];
dim_list[105] := [
[ 12, 8 ],
[ 12, 8 ]
];
dim_list[109] := [
[ 5, 4 ],
[ 16, 15 ]
];
dim_list[113] := [
[ 5, 4 ],
[ 8, 7 ]
];
dim_list[120] := [
[ 14, 10 ]
];
dim_list[124] := [
[ 9, 7 ]
];
dim_list[129] := [
[ 8, 6 ]
];
dim_list[133] := [
[ 7, 5 ]
];
dim_list[136] := [
[ 10, 8 ]
];
dim_list[137] := [
[ 6, 5 ]
];
dim_list[140] := [
[ 14, 10 ]
];
dim_list[141] := [
[ 9, 7 ]
];
dim_list[145] := [
[ 10, 8 ]
];
dim_list[149] := [
[ 7, 6 ]
];
dim_list[152] := [
[ 11, 9 ]
];
dim_list[156] := [
[ 16, 12 ]
];
dim_list[157] := [
[ 7, 6 ]
];
dim_list[161] := [
[ 11, 9 ]
];
dim_list[165] := [
[ 14, 10 ]
];
dim_list[168] := [
[ 18, 14 ]
];
dim_list[172] := [
[ 12, 10 ]
];
dim_list[173] := [
[ 8, 7 ]
];
dim_list[177] := [
[ 13, 11 ]
];
dim_list[181] := [
[ 8, 7 ]
];
dim_list[184] := [
[ 13, 11 ]
];
dim_list[185] := [
[ 10, 8 ]
];
dim_list[188] := [
[ 13, 11 ]
];
dim_list[193] := [
[ 10, 9 ]
];
dim_list[197] := [
[ 9, 8 ]
];
dim_list[201] := [
[ 12, 10 ]
];
dim_list[204] := [
[ 20, 16 ]
];
dim_list[205] := [
[ 14, 12 ]
];
dim_list[209] := [
[ 15, 13 ]
];
dim_list[213] := [
[ 13, 11 ]
];
dim_list[217] := [
[ 15, 13 ]
];
dim_list[220] := [
[ 22, 18 ]
];
dim_list[221] := [
[ 12, 10 ]
];
dim_list[229] := [
[ 10, 9 ]
];
dim_list[232] := [
[ 16, 14 ]
];
dim_list[233] := [
[ 12, 11 ]
];
dim_list[236] := [
[ 16, 14 ]
];
dim_list[237] := [
[ 14, 12 ]
];
dim_list[241] := [
[ 14, 13 ]
];
dim_list[248] := [
[ 17, 15 ]
];
dim_list[249] := [
[ 19, 17 ]
];
dim_list[253] := [
[ 15, 13 ]
];
dim_list[257] := [
[ 13, 12 ]
];
dim_list[264] := [
[ 26, 22 ]
];
dim_list[265] := [
[ 18, 16 ]
];
dim_list[268] := [
[ 18, 16 ]
];
dim_list[269] := [
[ 12, 11 ]
];
dim_list[273] := [
[ 24, 20 ]
];
dim_list[277] := [
[ 14, 13 ]
];
dim_list[280] := [
[ 28, 24 ]
];
dim_list[281] := [
[ 16, 15 ]
];
dim_list[284] := [
[ 19, 17 ]
];
dim_list[285] := [
[ 22, 18 ]
];
dim_list[293] := [
[ 13, 12 ]
];
dim_list[296] := [
[ 20, 18 ]
];
dim_list[301] := [
[ 15, 13 ]
];
dim_list[305] := [
[ 20, 18 ]
];
dim_list[309] := [
[ 18, 16 ]
];
dim_list[312] := [
[ 30, 26 ]
];
dim_list[313] := [
[ 19, 18 ]
];
dim_list[316] := [
[ 23, 21 ]
];
dim_list[317] := [
[ 14, 13 ]
];
dim_list[321] := [
[ 25, 23 ]
];
dim_list[328] := [
[ 24, 22 ]
];
dim_list[329] := [
[ 25, 23 ]
];
dim_list[332] := [
[ 22, 20 ]
];
dim_list[337] := [
[ 22, 21 ]
];
dim_list[341] := [
[ 19, 17 ]
];
dim_list[344] := [
[ 23, 21 ]
];
dim_list[345] := [
[ 34, 30 ]
];
dim_list[348] := [
[ 32, 28 ]
];
dim_list[349] := [
[ 17, 16 ]
];
dim_list[353] := [
[ 19, 18 ]
];
dim_list[357] := [
[ 28, 24 ]
];
dim_list[364] := [
[ 34, 30 ]
];
dim_list[365] := [
[ 20, 18 ]
];
dim_list[373] := [
[ 20, 19 ]
];
dim_list[376] := [
[ 29, 27 ]
];
dim_list[377] := [
[ 24, 22 ]
];
dim_list[380] := [
[ 34, 30 ]
];
dim_list[381] := [
[ 22, 20 ]
];
dim_list[385] := [
[ 42, 38 ]
];
dim_list[389] := [
[ 19, 18 ]
];
dim_list[393] := [
[ 33, 31 ]
];
dim_list[397] := [
[ 19, 18 ]
];
dim_list[401] := [
[ 25, 24 ]
];
dim_list[408] := [
[ 38, 34 ]
];
dim_list[409] := [
[ 29, 28 ]
];
dim_list[412] := [
[ 31, 29 ]
];
dim_list[413] := [
[ 23, 21 ]
];
dim_list[417] := [
[ 32, 30 ]
];
dim_list[421] := [
[ 22, 21 ]
];
dim_list[424] := [
[ 32, 30 ]
];
dim_list[428] := [
[ 28, 26 ]
];
dim_list[429] := [
[ 34, 30 ]
];
dim_list[433] := [
[ 30, 29 ]
];
dim_list[437] := [
[ 23, 21 ]
];
dim_list[440] := [
[ 38, 34 ]
];
dim_list[444] := [
[ 40, 36 ]
];
dim_list[445] := [
[ 30, 28 ]
];
dim_list[449] := [
[ 29, 28 ]
];
dim_list[453] := [
[ 26, 24 ]
];
dim_list[456] := [
[ 44, 40 ]
];
dim_list[457] := [
[ 33, 32 ]
];


// This function test that we have the correct dimension
// for the new subspace of Hilbert modular forms of trivial character
// and weight, for a quadratic field of discriminant d, with level n*Z_K.
// It does so by considering the oriented genera of quaternary
// quadratic forms.
// We restrict to trivial level and weight because
// we don't have access here to the algebraic modular form package
// which can compute those for arbitrary level and weight.
// update : instead of computing on the spot, we just compare to a
// value from a precomputed list.
// This is the computation for d,n - 
// &+[Dimension(OrthogonalModularForms(g[1] : Special))-1
// : g in QuaternaryQuadraticLattices(d*n^2)]
procedure testHeckeCharacterSubspace(d,n, dim_list)

    K := QuadraticField(d);
    D := Discriminant(K);
    
    // Verify that we have the precomputed values
    assert D in Keys(dim_list);
    assert n in [1..#dim_list[D]];
    
    // This is currently only worked out for GCD(D,n) eq 1 and n square free
    // (The theorem transferring orthogonal modular forms to Hilbert modular forms)
    // We have precomputed the other ones as well, but the map is no longer an isomorphism
    assert GCD(D,n) eq 1 and IsSquarefree(n);
    
    if Type(K) eq FldRat then
	K := QNF();
    end if;
    Z_K := Integers(K);
    N := ideal<Z_K|n>;

    // to igure out which space we should be looking at, we have to understtand the
    // ramification of the quaternion algebra B_K
    // We assumed that disc(B) and K are relatively prime, so
    // the primes ramifying in B are precisely the ones dividing n.
    // Such a prime (i.e. the primes above it) is also ramified in B_K iff its is split in K.
    
    new_level := &*([1] cat [p : p in PrimeDivisors(n) | IsSplit(p, Z_K)]);
    prec := 1;
    R := GradedRingOfHMFs(K, prec);
    hmf := HMFSpace(R, N, [2,2]);
    // !! TODO - we should implement a new-subspace intrinsic for HMFSpaces
    // That would make the following easier.
    // dim_hmf := Dimension(hmf);
    // dim_cusp := CuspDimension(hmf);
    hcf := NewSubspace(hmf, new_level * Z_K);
    dim_cusp := Dimension(hcf);

    // This is not true, since Eisenstein series do not surject in JL
    // assert dim_hmf eq dim_list[D][n][1];
    assert dim_cusp eq dim_list[D][n][2];
    
end procedure;

// we run tests for 5 of the keys
num_tests := 5;

fund_discs := Keys(dim_list);
B := Maximum(fund_discs);
ds := [Random(fund_discs) : i in [1..num_tests]];
ns := [[n : n in [1..Floor(Sqrt(B/d))] | GCD(d,n) eq 1 and IsSquarefree(n)] : d in ds];

printf "Checking dimensions at d=";
for i->d in ds do
    printf "%o ", d;
    printf "n=";
    for n in ns[i] do
	printf "%o ", n;
	testHeckeCharacterSubspace(d,n, dim_list);
    end for;
    printf "\n";
end for;
return true;
