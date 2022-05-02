// Generic Linear algebra
intrinsic PivotColumns(A::Mtrx: is_echelonized:=false) -> SeqEnum[RngIntElt]
  {Return the pivot column positions of the matrix A}
  if not is_echelonized then
    A := EchelonForm(A);
  end if;
  r := Rank(A);
  return Sort(SetToSequence({ PivotColumn(A, i) : i in [1..r] }));
end intrinsic;

intrinsic PivotRows(A::Mtrx) -> SeqEnum[RngIntElt]
  {Return the pivot row positions for the matrix A, which are a topmost
  subset of the rows that span the row space and are linearly
  independent}
  return PivotColumns(Transpose(A) : is_echelonized:=false);
end intrinsic;



intrinsic Columns(X::Mtrx, Q::[RngIntElt]) -> []
  {The columns given by Q of X as a sequence};
    return Transpose(X)[Q];
end intrinsic;

intrinsic Columns(X::Mtrx) -> []
  {The columns of matrix X as a sequence}
    return Columns(X, [1..Ncols(X)]);
end intrinsic;





////////// ModFrmHilDElt: Linear Algebra  //////////

intrinsic CoefficientsMatrix(list::SeqEnum[ModFrmHilDElt] : IdealClasses:=false, prec:=false ) -> AlgMatElt
  {returns a matrix with the coefficients of each modular form in each row}
  // assuring that all the forms have the same coefficient ring
  list := ChangeToCompositumOfCoefficientFields(list);

  M := GradedRing(list[1]);
  // The ideal classes from which we are taking the coefficients.
  if IdealClasses cmpeq false then
    bbs := NarrowClassGroupReps(M); // Default is all ideals classes
  else
    bbs := IdealClasses;
  end if;
  require #bbs gt 0: "at least on ideal class must be specified";

  if prec cmpeq false then
    prec := Min([Precision(Components(f)[bb]): f in list, bb in bbs]);
  end if;

  mat := Matrix([
    &cat[
      &cat[Eltseq(Coefficients(Components(f)[bb])[nu]) : nu in ShintaniRepsUpToTrace(M, bb, prec)]
      : bb in bbs]
    : f in list]);
  nus := &cat[ShintaniRepsUpToTrace(M, bb, prec) : bb in bbs];
  return mat, nus;
end intrinsic;

intrinsic ShortLinearDependence(M::Mtrx) -> SeqEnum[RngIntElt]
  {
    finds a small non-trivial integral linear combination between components of v.
    If none can be found return 0.
  }
  // in case M is defined over the rationals
  M := ChangeRing(Denominator(M)*M, Integers());
  B := Basis(Kernel(M));
  if #B ne 0 then return [Eltseq(i) : i in Rows(Matrix(LLL(B)))]; else return []; end if;
end intrinsic;



//TODO add optional flag to limit the number of coefficients
intrinsic LinearDependence(list::SeqEnum[ModFrmHilDElt] : IdealClasses:=false, prec:=false ) -> SeqEnum[RngIntElt]
  {Finds any linear relations between the forms (returns 0 if none are found).
    The optional parameter IdealClasses can be specified to look at the relations over a subset of narrow class reps }
  if IsNull(list) then return list; end if;

  // The ideal classes from which we are taking the coefficients.
  if not IdealClasses cmpeq false then
    // ie, we will be looking at relations that makes the forms vanish on these components
    if #IdealClasses eq 0 then
      // the empty sum is zero
      return IdentityMatrix(Integers(), #list);
    end if;
  end if;
  return ShortLinearDependence(CoefficientsMatrix(list : IdealClasses:=IdealClasses, prec:=prec));
end intrinsic;



intrinsic ComplementBasis(
  Wbasis::SeqEnum[ModFrmHilDElt],
  Vbasis::SeqEnum[ModFrmHilDElt]
  :
  Alg := "WeightedLLL"
  )-> SeqEnum[ModFrmHilDElt]
  {Given bases for spaces W < V, return a basis for the complement of W in V}

  VCoeffMatrix, nus1 := CoefficientsMatrix(Vbasis);
  WCoeffMatrix, nus2 := CoefficientsMatrix(Wbasis);
  assert nus1 eq nus2;

  AlgOpts := ["Standard", "LLL", "WeightedLLL", "HNF", "Orthogonal"];
  require Alg in AlgOpts: "the optional parameter must be one of the following %o\n", AlgOpts;
  V := VectorSpaceWithBasis(VCoeffMatrix);
  W := sub<V | Rows(WCoeffMatrix)>;
  if (Alg eq "Standard") then
    WExtendedCoeffBasis := ExtendBasis(W, V);
  elif (Alg eq "LLL") then
    WExtendedCoeffBasis := ExtendBasis(W, V);
    B := WExtendedCoeffBasis[Dimension(W) + 1 .. Dimension(V)];
    if #B ne 0 then
        WExtendedCoeffBasis := Basis(W) cat Rows(Matrix(LLL(B)));
    else
        WExtendedCoeffBasis := Basis(W);
    end if;
    assert #WExtendedCoeffBasis eq Dimension(V);
  elif (Alg eq "WeightedLLL") then
    WExtendedCoeffBasis := ExtendBasis(W, V);
    B := WExtendedCoeffBasis[Dimension(W) + 1 .. Dimension(V)];
    if #B ne 0 then
        // wt := [Floor(Degree(B[1])/Sqrt(n)) : n in [1..Degree(B[1])]];
        traces := [Max(1, Trace(nu)): nu in nus1];
        max_trace := Max(traces);
        wt := [Floor(max_trace/t) : t in traces];
        WExtendedCoeffBasis := Basis(W) cat Rows(LLL(Matrix(B) : Weight := wt));
    else
        WExtendedCoeffBasis := Basis(W);
    end if;
    assert #WExtendedCoeffBasis eq Dimension(V);
  elif (Alg eq "HNF") then
    WExtendedCoeffBasis := ExtendBasis(W, V);
    B := WExtendedCoeffBasis[Dimension(W)+1..Dimension(V)];
    denom := Denominator(Matrix(B));
    intmat := ChangeRing(denom * Matrix(B), Integers());
    WExtendedCoeffBasis := Basis(W) cat Rows(ChangeRing(HermiteForm(intmat), Rationals())/denom);
  elif (Alg eq "Orthogonal") then
    coeffs_W := Solution(Matrix(Basis(V)), Matrix(Basis(W)));
    coeffs_W := ChangeRing(Matrix([Denominator(v)*v : v in Rows(coeffs_W)]), Integers());
    W_perp := Matrix(Basis(Kernel(Transpose(coeffs_W))));
    basis_V := ChangeRing(Matrix([Denominator(v)*v : v in Basis(V)]), Integers());
    WExtendedCoeffBasis := Basis(W) cat Rows(W_perp * basis_V);
  end if;

  WComplementBasis := WExtendedCoeffBasis[Dimension(W) + 1..Dimension(V)];
  sol := Solution(VCoeffMatrix, WComplementBasis);
  return [ &+[elt[i]*Vbasis[i] : i in [1..#Vbasis]] : elt in sol];
end intrinsic;

intrinsic ComplementBasis(Wbasis::SeqEnum[ModFrmHilDElt] : Alg := "WeightedLLL"
  )-> SeqEnum[ModFrmHilDElt]
  {Given bases for a space W contained within a space `V` of Hilbert Modular Surfaces, 
  (i.e., `V := Parent(Wbasis[1])`), return a basis for the complement of W in V}
  return ComplementBasis(Wbasis, Parent(Wbasis[1]) : Alg:=Alg);
end intrinsic;

intrinsic ComplementBasis(Wbasis::SeqEnum[ModFrmHilDElt], V::ModFrmHilD : Alg := "WeightedLLL"
  )-> SeqEnum[ModFrmHilDElt]
  {Given bases for a space W contained within a space `V` of Hilbert Modular Surfaces, 
  return a basis for the complement of W in V}
  return ComplementBasis(Wbasis, Basis(V) : Alg:=Alg);
end intrinsic;
