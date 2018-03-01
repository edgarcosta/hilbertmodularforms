
//TODO add optional flag to limit the number of coefficients
intrinsic LinearDepedence(list::SeqEnum[ModFrmHilDElt] ) -> SeqEnum[RngIntElt]
  {finds a small non-trivial integral linear combination between components of v. If none can be found return an empty vector.}
  M := Matrix( [ Coefficients(elt) : elt in list] );
  return LLL(Basis(Kernel(M)));;
end intrinsic;

//EchelonBasis
