//Theta series
/* TODO:  I'm here. Edgar
intrinsic coefficient_v := function(v, K, M)
	//Input: v a totally positive element, K totally real field containing v, 
	// M the Gram matrix of a quadratic form
	//Output: the coefficient in the theta series for v
	d:=Nrows(M);
	BasisK:=Basis(K);
		if DefiningPolynomial(K) eq DefiningPolynomial(Rationals()) then
		 ZK<w>:=IntegerRing();
	else 
		 ZK<w>:=Integers(K);
	end if;
	B:=Basis(ZK);
	n:=#B;
	t:=Trace(v);
	L1:=LatticeWithGram(QuadraticZ(K, M)); //Z-lattice corresponding to quadratic (trace) form over Z
	S:=ShortVectors(L1, t,t); //Preimages of Trace(v) in expanded  Z-lattice
	num_sols := #S;
	PreimTr:= ZeroMatrix(K, num_sols, d); //Coefficients of linear combinations in basis elements of  of  preimages of Trace(v) by quadratic trace form 
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
		Append(~checkmult, DotProduct(PreimTr[i]*M, PreimTr[i]));
	end for;
	r_v:=0; //number of preimages of v inside initial lattice; also the Fourier coefficient for element v
	for i:=1 to #checkmult do
		if checkmult[i] eq v then
			r_v+:=2;
		end if;
	end for;
	return r_v;
end intrinsic;



intrinsic ThetaSeries(M::ModFrmHilD, GM::ModMatFldElt) -> ModFrmHilDElt
  {generates the Theta series associated to the gram matrix of the quadratic form in the space M}
  //FIXME assert that level of Theta divides the level of M
  rep := Representatives(M);
  K := BaseField(M);
  ZK := IntegerRing(K);
  coeffs := [ZK!0 | for nu in rep];
  for i := 1 to #rep do
    coeffs[i] := theta_coefficient(rep[i], K, GM);
  end for;
  //we are assuming class number = 1
  coeffs[1] := ZK ! 1;
  w := NumberOfRows(GM)/2;
  weight := [w : i in [1..Degree(K)];
  retuns HMF(M, weight, coeffs);
end intrinsic;
*/
