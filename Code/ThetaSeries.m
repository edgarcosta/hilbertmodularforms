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


intrinsic ThetaCoefficient(v::RngOrdElt, L::Lat, GM::AlgMatElt) -> FldNumElt
  {given v a totally positive element in a totally real field and M the Gram matrix of a quadratic form, outputs the coefficient in the theta series for v}
  K := Parent(v);
	d:=Dimension(L);
	BasisK:=Basis(K);
	ZK<w>:=Integers(K);
	B:=Basis(ZK);
	n:=#B;
	t:=Trace(v);
  print t;
  //Preimages of Trace(v) in expanded  Z-lattice
	S:=ShortVectors(L, t, t);
	num_sols := #S;
  //Coefficients of linear combinations in basis elements of  of  preimages of Trace(v) by quadratic trace form
	PreimTr:= ZeroMatrix(K, num_sols, d);
	for k:=1 to num_sols do
		for i:=0 to (d-1) do
			elt:=0;
			for j:= (i*n+1) to (i+1)*n do
				if (j mod n) ne 0 then
					elt+:=S[k][1][j]*B[j mod n];
				else elt+:=S[k][1][j]*B[n];
				end if;
			end for;
			PreimTr[k][i+1]:=elt;
		end for;
	end for;
	checkmult:=[]; // preimages of Trace(v) in ZF-lattice
	for i:=1 to num_sols do
    // 
		Append(~checkmult, DotProduct(PreimTr[i]*GM, PreimTr[i]));
	end for;
	r_v:=0; //number of preimages of v inside initial lattice; also the Fourier coefficient for element v
	for i:=1 to #checkmult do
		if checkmult[i] eq v then
			r_v+:=2;
		end if;
	end for;
	return r_v;
end intrinsic;



intrinsic ThetaSeries(M::ModFrmHilD, GM::AlgMatElt) -> ModFrmHilDElt
  {generates the Theta series associated to the gram matrix of the quadratic form in the space GM}
  K := BaseField(M);
  ZK := Integers(K);
  levelGM := ideal<ZK|Determinant(GM)>;
  //checking that the level of Theta divides the level of M
  assert Level(M) subset levelGM;


  L := LatticeWithGram(QuadraticZ(K, GM));


  rep := Representatives(M);
  K := BaseField(M);
  ZK := IntegerRing(K);
  coeffs := [ZK!0 :  nu in rep];
  //we are assuming class number = 1
  for i := 2 to #rep do
    coeffs[i] := ThetaCoefficient(rep[i], L, GM);
  end for;
  coeffs[1] := ZK ! 1;
  w := NumberOfRows(GM)/2;
  weight := [w : i in [1..Degree(K)]];
  return HMF(M, weight, coeffs);
end intrinsic;
