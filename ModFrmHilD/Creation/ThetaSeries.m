//Theta series

intrinsic QuadraticZ(F::FldNum, M::AlgMatElt) -> AlgMatElt
	{Input: F a otally real field, M the Gram Matrix for quadratic form
	Output: the Gram matrix for the trace form over Z
  }

	ZF<w>:=Integers(F);
	B:=Basis(ZF);
	n:=#B;
	d:=Nrows(M);
	Blocks:=[];
	for j:= 1 to d do
		for i:=1 to d do
			Tr_ij:=ZeroMatrix(RationalField(),n, n );
			for p:= 1 to n do
				for q:=1 to n do
					Tr_ij[p][q]:=Trace(M[i][j]*B[p]*B[q]);
				end for;
			end for;
			Append(~Blocks, Tr_ij);
		end for;
	end for;
	return BlockMatrix(d,d, Blocks);
end intrinsic;


intrinsic ThetaCoefficient(M::ModFrmHilDGRng, v::RngOrdElt, L::Lat, GM::AlgMatElt) -> FldNumElt
  {given v a totally positive element in a totally real field and M the Gram matrix of a quadratic form (should be equal to (1/2)*inner product matrix with respect to the standard basis, outputs the coefficient in the theta series for v}
  K := BaseField(M);
  //force matrix over field
  GM := Matrix(K, GM);
	BasisK := Basis(K);
	ZK<w> := Integers(K);
	B := Basis(ZK);
	n := #B;
	t := Trace(v);
  assert Dimension(L) mod n eq 0;
	d := Integers() ! (Dimension(L)/n);

  //Preimages of Trace(v) in expanded  Z-lattice
	S := ShortVectors(L, t, t);
	num_sols := #S;
  if num_sols eq 0 then
    return 0;
  end if;
  //Coefficients of linear combinations in basis elements of  of  preimages of Trace(v) by quadratic trace form
	PreimTr:= ZeroMatrix(K, num_sols, d);
	for k:=1 to num_sols do
		for i:=0 to (d-1) do
			elt:=0;
			for j:= (i*n+1) to (i+1)*n do
				if (j mod n) ne 0 then
					elt +:= S[k][1][j]*B[j mod n];
				else
          elt +:= S[k][1][j]*B[n];
				end if;
			end for;
			PreimTr[k][i+1]:=elt;
		end for;
	end for;

  pgm := PreimTr * GM;
  r_v := 0;
	for i:=1 to num_sols do
    //number of preimages of v inside initial lattice; also the Fourier coefficient for element v
    if DotProduct(pgm[i],PreimTr[i])  eq v then
      r_v +:= 2;
    end if;
	end for;
	return r_v;
end intrinsic;


//FIXME, this is a multiple of the level
intrinsic Level(K::FldNum, GM::AlgMatElt) -> RngOrdElt
  {given a Gram Matrix returns the level of the Theta series associated to the Gram matrix}
  // return ideal<Integers(K)| 4*Determinant(GM)>;
  L := NumberFieldLatticeWithGram(GM);
  return ideal<Integers(K)|(1/2*Norm(L))^(-1)*(1/2*Norm(Dual(L)))^(-1)>;
end intrinsic;

intrinsic ThetaSeries(M::ModFrmHilDGRng, GM::AlgMatElt) -> ModFrmHilDElt
  {generates the Theta series associated to the gram matrix of the quadratic form in the space GM}
  assert NumberOfRows(GM) mod 2 eq 0;
  K := BaseField(M);
  ZK := Integers(K);

  //checking that the level of Theta divides the level of M

  L := LatticeWithGram(QuadraticZ(K, GM));

  reps := IdealsByNarrowClassGroup(M);
  K := BaseField(M);
  ZK := IntegerRing(K);
  coeffs := AssociativeArray();
  //we are assuming class number = 1
  for bb in Keys(reps) do
    coeffs[bb] := AssociativeArray();
    for nu in Keys(reps[bb]) do
      coeffs[bb][nu] := ThetaCoefficient(M, ZK!nu, L, GM);
    end for;
  end for;
  w := Integers()! (NumberOfRows(GM)/2);
  weight := [w : i in [1..Degree(K)]];
  return HMF(HMFSpace(M, Level(K, GM), weight), coeffs);
end intrinsic;
