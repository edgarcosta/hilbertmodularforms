
//TODO add optional flag to limit the number of coefficients
intrinsic CoefficientsMatrix(list::SeqEnum[ModFrmHilDElt]) -> AlgMatElt
  {returns a matrix with the coefficients of each modular form in each row}
  return Matrix( [ Coefficients(elt) : elt in list] );
end intrinsic;

//TODO add optional flag to limit the number of coefficients
intrinsic LinearDependence(list::SeqEnum[ModFrmHilDElt] ) -> SeqEnum[RngIntElt]
  {finds a small non-trivial integral linear combination between components of v. If none can be found return the empty vector.}
  M := Matrix( [ Coefficients(elt) : elt in list] );
  B := Basis(Kernel(M));
  if #B ne 0 then
    return Matrix(LLL(Basis(Kernel(M))));
  else
    return 0;
  end if;
end intrinsic;

//EchelonBasis
