//Theta series

intrinsic QuadraticZ(F::FldNum, M::AlgMatElt) -> AlgMatElt
	{Input: F a totally real field, M the Gram Matrix for quadratic form
	Output: the Gram matrix for the trace form over ZZ}

	ZF:=Integers(F);
	B:=Basis(ZF);
	n:=#B;
	d:=Nrows(M);
	Blocks:=[];
	for j:= 1 to d do
		for i:=1 to d do
      Tr_ij:=[[Trace(M[i][j]*B[p]*B[q]): q in [1..n]]: p in [1..n]];
			Tr_ij:=Matrix(Tr_ij);
			Append(~Blocks, Tr_ij);
		end for;
	end for;
	return BlockMatrix(d,d, Blocks);
end intrinsic;


intrinsic ThetaCoefficient(M::ModFrmHilDGRng, v::FldQuadElt,  GM::AlgMatElt) -> FldNumElt
  { inputs: M a graded ring,
            v a totally positive element in a totally real field,
            GM the Gram matrix of a quadratic form (should be equal to (1/2)*inner product matrix with respect to the standard basis),
    output: the coefficient in the theta series for v}
  K := BaseField(M);
  //force matrix over field
  GM := Matrix(K, GM);
  assert Nrows(GM) mod 2 eq 0; //half weight not implemented yet
  L:=LatticeWithGram(QuadraticZ(K, GM)); // L is the ZZ-lattice of the map Tr(Q(v)) where Q is the quadratic form with Gram matrix GM
	BasisK := Basis(K);
	ZK := Integers(K);
	B := Basis(ZK);
	n := #B;
	t := Trace(v);
  if not IsTotallyPositive(t) then print([t, v]);
  end if;
	d := Integers() ! (Dimension(L)/n);

  //Preimages of Trace(v) as vectors over ZZ
	S := ShortVectors(L, t, t);
	num_sols := #S;
  if num_sols eq 0 then
    return 0;
  end if;
	PreimTr:= ZeroMatrix(K, num_sols, d);   //convert from vectors over ZZ to vectors over ZK
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
    if DotProduct(pgm[i],PreimTr[i])  eq v then //check which vectors in the preimage of Tr(v) are also in the preimage of
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
  {generates the Theta series associated to the Gram matrix of the quadratic form in the space GM}
  assert NumberOfRows(GM) mod 2 eq 0;
  K := BaseField(M);
  ZK := Integers(K);
  print("Warning: something is fishy with ThetaCoefficient perhaps related with the change from bb to bbp");

  //checking that the level of Theta divides the level of M

  reps := NarrowClassGroupReps(M);
  K := BaseField(M);
  ZK := IntegerRing(K);
  discriminant := Discriminant(ZK);
  if discriminant mod 4 eq 0 then
    diffGen:=2*K.1;
  else
    diffGen:=K.1;
  end if;
  coeffs := AssociativeArray();
  eps:=FundamentalUnit(ZK);
  if RealEmbeddings(eps)[1] gt 0 then 
    epsrootd:=FundamentalUnit(ZK)/diffGen;
  else
    epsrootd:=-FundamentalUnit(ZK)/diffGen;
  end if;
  require NarrowClassNumber(K) eq 1: "Theta Series only impliemented with narrow class number one";
  for bb in reps do
    coeffs[bb] := AssociativeArray();
    for nu in ShintaniRepsUpToTrace(M, bb, Precision(M)) do
      if IsZero(nu) then
        coeffs[bb][nu] := 1;
      else
        if not IsTotallyPositive(nu/epsrootd)  then print([nu, epsrootd, nu/epsrootd, K.1, K.1^2]);
        end if;
        coeffs[bb][nu] := ThetaCoefficient(M, nu/epsrootd, GM);
      end if;
    end for;
  end for;
  w := Integers()! (NumberOfRows(GM)/2);
  weight := [w : i in [1..Degree(K)]];
  return HMF(HMFSpace(M, Level(K, GM), weight), coeffs);
end intrinsic;
