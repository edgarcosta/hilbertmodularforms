//TODO add optional flag to limit the number of coefficients
intrinsic CoefficientsMatrix(list::SeqEnum[ModFrmHilDElt]) -> AlgMatElt
  {returns a matrix with the coefficients of each modular form in each row}
  return Matrix( [ Coefficients(elt) : elt in list] );
end intrinsic;



intrinsic LinearDependence(list::SeqEnum[SeqEnum] ) -> SeqEnum[RngIntElt]
  {finds a small non-trivial integral linear combination between components of v. If none can be found return 0.}
  M := Matrix( [ elt : elt in list] );
  B := Basis(Kernel(M));
  if #B ne 0 then
    Mat := Matrix(LLL(Basis(Kernel(M))));
    return [Eltseq(i) : i in Rows(Mat)];
  else
    return [];
  end if;
end intrinsic;

//TODO add optional flag to limit the number of coefficients
//TODO make outputs to be of the same type

intrinsic LinearDependence(list::SeqEnum[ModFrmHilDElt] ) -> SeqEnum[RngIntElt]
  {finds a small non-trivial integral linear combination between components of v. If none can be found return 0.}
  return LinearDependence([ Coefficients(elt) : elt in list] );
end intrinsic;

//EchelonBasis
