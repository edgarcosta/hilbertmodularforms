// Generic Linear algebra
intrinsic PivotColumns(A::Mtrx: is_echelonized:=false, rank:=false) -> SeqEnum[RngIntElt]
  {Return the pivot column positions of the matrix A}
  if Type(BaseRing(A)) in [RngInt, FldRat] then
    if rank cmpeq false then
      rank := Rank(A);
    end if;
    d := Denominator(A);
    AZ := Matrix(Integers(), d*A);
    p := 1;
    while true do
      p := NextPrime(p);
      if d mod p ne 0 then
        Ap := Matrix(GF(p), AZ);
        if Rank(Ap) eq rank then
          return $$(Ap : rank:=rank);
        end if;
      end if;
    end while;
  elif not is_echelonized then
    A := EchelonForm(A);
  end if;
  if rank cmpeq false then
    rank := Rank(A);
  end if;
  return Sort(SetToSequence({ PivotColumn(A, i) : i in [1..rank] }));
end intrinsic;

intrinsic PivotRows(A::Mtrx) -> SeqEnum[RngIntElt]
  {Return the pivot row positions for the matrix A, which are a topmost
  subset of the rows that span the row space and are linearly
  independent}
  return PivotColumns(Transpose(A) : is_echelonized:=false);
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
  require #bbs gt 0: "at least one ideal class must be specified";
  // make it a SeqEnum
  bbs := [bb : bb in bbs];

  if prec cmpeq false then
    prec := Min([Precision(Components(f)[bb]): f in list, bb in bbs]);
  end if;

  nus := [FunDomainRepsUpToPrec(M, bb, prec) : bb in bbs];

  mat := Matrix([&cat[[Coefficient(Components(f)[bb], nu : InFunDomain := true)
                       : nu in nus[i]] : i->bb in bbs] : f in list]);
  assert Ncols(mat) eq &+[#elt : elt in nus];
  assert Nrows(mat) eq #list;
  return mat, nus, bbs;
end intrinsic;


intrinsic ShortLinearDependence(M::Mtrx) -> SeqEnum[RngIntElt]
  {
    finds a small non-trivial integral linear combination between components of v.
    If none can be found return 0.
  }
  // in case M is defined over the rationals
  if CanChangeRing(M, Rationals()) then
    M := ChangeRing(Denominator(M)*M, Integers());
  end if;
  
  B := Basis(Kernel(M));

  if #B eq 0 then
    return [];
  elif CanChangeRing(M, Rationals()) then
    kernel_basis_vectors := Rows(Matrix(LLL(B)));
  else 
    kernel_basis_vectors := B;
  end if;
  // return a SeqEnum of SeqEnums instead of a SeqEnum of vectors
  return [Eltseq(v) : v in kernel_basis_vectors];
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


intrinsic Basis(generators::SeqEnum[ModFrmHilDElt]) -> SeqEnum[ModFrmHilDElt]
  {returns Basis for the vector space spanned by the inputted forms}
  if #generators eq 0 then return generators; end if;
  M := GradedRing(generators[1]);
  bbs := NarrowClassGroupReps(M);
  prec := Min([Precision(Components(f)[bb]): f in generators, bb in bbs]);
  C, nus, bbs := CoefficientsMatrix(generators : prec:=prec);
  E := EchelonForm(C);
  r := Rank(E);
  Mk := Parent(generators[1]);
  return [Mk | HMF(Mk, Eltseq(row), nus, bbs : prec:=prec) : row in Rows(E)[1..r] ];
end intrinsic;

intrinsic Intersection(V::SeqEnum[ModFrmHilDElt], W::SeqEnum[ModFrmHilDElt]) -> SeqEnum[ModFrmHilDElt]
  {}
  // assumes that V and W are actually bases, but doesn't check this 
  // to avoid a slowdown. TODO abhijitm can probably handle better
  if #V eq 0 or #W eq 0 then
    return [];
  end if;

  lindep := LinearDependence(V cat W);
  intersection := [];
  for v in lindep do
    f := Normalize(&+[v[i]*V[i] : i in [1 .. #V]]);
    Append(~intersection, f);
  end for;
  return intersection;
end intrinsic;


intrinsic ComplementBasis(
  Wbasis::SeqEnum[ModFrmHilDElt],
  Vbasis::SeqEnum[ModFrmHilDElt]
  :
  Alg := "WeightedLLL"
  )-> SeqEnum[ModFrmHilDElt]
  {Given bases for spaces W < V, return a basis for the complement of W in V}

  if #Wbasis eq 0 then return Vbasis; end if;
  require Parent(Wbasis[1]) eq Parent(Vbasis[1]) : "Forms not in the same space";
  Mk := Parent(Wbasis[1]);
  R := CoefficientRing(Wbasis[1]);
  require &and[R eq CoefficientRing(elt) : elt in Vbasis cat Wbasis] : "we expect the forms to have the same coefficient ring";
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
  return [Mk |  &+[elt[i]*Vbasis[i] : i in [1..#Vbasis]] : elt in sol];
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
