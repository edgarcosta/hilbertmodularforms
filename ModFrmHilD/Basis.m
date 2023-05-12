///////////////////////////////////////////////////
//                                               //
//               Basis for M_k(N)                //
//                                               //
///////////////////////////////////////////////////

//Auxiliary function to handle the optional parameters for Basis calls
function SubBasis(basis, IdealClassesSupport, GaloisInvariant)
  if IsNull(basis) or #basis eq 0 then return basis; end if;
  Mk := Parent(basis[1]);
  // handle optional argument IdealClassesSupport
  if IdealClassesSupport cmpeq false then
    IdealClassesSupport := SequenceToSet(NarrowClassGroupReps(Parent(Mk))); // Default is all ideals classes
  else
    IdealClassesSupport := SequenceToSet(IdealClassesSupport); // Optionally we may specify a subset of ideal classes
  end if;
  IdealClassesSupportComplement := Setseq(SequenceToSet(NarrowClassGroupReps(Parent(Mk))) diff IdealClassesSupport);

  if #IdealClassesSupportComplement eq 0 then // in this case LinearDependence will return the identity matrix
    basis := basis;
  else
    B := basis;
    relations := LinearDependence(B : IdealClasses:=IdealClassesSupportComplement);
    // basis is only supported over IdealClassesSupport
    basis := [ &+[rel[i]*B[i] : i in [1..#B]] : rel in relations];
  end if;

  // handle optional argument GaloisInvariant
  if GaloisInvariant then
    InvariantGenerators := [1/2*(b + Swap(b)) : b in basis];
    coeffs := CoefficientsMatrix(basis : IdealClasses:=IdealClassesSupport);
    basis := [basis[i] : i in PivotRows(coeffs)];
  end if;
  return basis;
end function;

// Currently calls the Newforms and Eisenstein series from Creations folder

//  idea: if known basis for Mk use Hecke to extract basis for Sk
intrinsic CuspFormBasis(
  Mk::ModFrmHilD
  :
  IdealClassesSupport:=false,
  GaloisInvariant:=false,
  GaloisDescent:=true
  ) -> SeqEnum[ModFrmHilDElt]
  {returns a basis for cuspspace of M of weight k}

  require #SequenceToSet(Weight(Mk)) eq 1: "We only support parallel weight.";

  // we only cache GaloisDescent basis
  if not assigned Mk`CuspFormBasis or not GaloisDescent then
    require CuspDimension(Mk) lt NumberOfCoefficients(Parent(Mk)) : "Dimension of the space too large for the current precision";
    N := Level(Mk);
    k := Weight(Mk);

    if k[1] ge 2 then
      cusp_forms := [Mk | ];
      for i->dd in Divisors(N) do
        Mkdd := HMFSpace(Parent(Mk), dd, k);
        cusp_forms cat:= CuspForms(Mkdd, Mk : GaloisDescent:=GaloisDescent);
        vprint HilbertModularForms: i, Norm(dd), "#cusp_forms =", #cusp_forms;
        require &and[not IsZero(f) : f in cusp_forms] : "insufficient precision: a cusp form of level form seems to be zero";
      end for;
      dim := 0;
      if #cusp_forms gt 0 then
        dim := &+[Degree(CoefficientRing(f)) : f in cusp_forms];
      end if;
      require CuspDimension(Mk) eq dim : Sprintf("CuspDimension(Mk) = %o != %o = dim(forms)", CuspDimension(Mk), dim);
      if GaloisDescent then
        Mk`CuspFormBasis := cusp_forms;
      end if;
    else
      // FIXME not passing arguments
      Mk`CuspFormBasis := Weight1CuspBasis(Mk);
      cusp_forms := Mk`CuspFormBasis;
    end if;
  else
    cusp_forms := Mk`CuspFormBasis;
  end if;
  return SubBasis(cusp_forms, IdealClassesSupport, GaloisInvariant);
end intrinsic;


intrinsic EisensteinBasis(
  Mk::ModFrmHilD
  :
  IdealClassesSupport:=false,
  GaloisInvariant:=false
  ) -> SeqEnum[ModFrmHilDElt]
  { return a basis for the complement to the cuspspace of Mk }
  if not assigned Mk`EisensteinBasis then
    require EisensteinDimension(Mk) lt NumberOfCoefficients(Parent(Mk)) : "Dimension of the space too large for the current precision";
    pairs := EisensteinAdmissibleCharacterPairs(Mk);
    eisensteinbasis := [Mk | ] cat &cat[EisensteinInclusions(Mk, p[1], p[2]) : p in pairs];
    Mk`EisensteinBasis := [Mk | ] cat &cat[GaloisOrbitDescent(f) : f in eisensteinbasis];
    require #Mk`EisensteinBasis eq EisensteinDimension(Mk) : "#Mk`EisensteinBasis = %o != %o = EisensteinDimension(Mk)", #Mk`EisensteinBasis, EisensteinDimension(Mk);
  end if;

  // this handles the optional parameters
  return SubBasis(Mk`EisensteinBasis, IdealClassesSupport, GaloisInvariant);
end intrinsic;




intrinsic Basis(
  Mk::ModFrmHilD
  :
  IdealClassesSupport:=false,
  GaloisInvariant:=false,
  UseKnown:=true,
  UseTraceForms:=true
  ) -> SeqEnum[ModFrmHilDElt]
  { returns a Basis for the space }
  if not assigned Mk`Basis then
    require Dimension(Mk) lt NumberOfCoefficients(Parent(Mk)) : Sprintf("insufficient precision: number of coefficients = %o < %o = ambient dimension", NumberOfCoefficients(Parent(Mk)), Dimension(Mk)) ;
    k := Weight(Mk);
    require #SequenceToSet(Weight(Mk)) eq 1: "We only support parallel weight.";
    vprintf HilbertModularForms: "Computing basis for space of parallel weight %o with precision %o\n", Weight(Mk)[1], Precision(Parent(Mk));
    //Eisenstein Series
    res := EisensteinBasis(Mk);

    shortcut := UseKnown or UseTraceForms;
    if #res lt Dimension(Mk) and shortcut and k[1] ge 2 then
      divisors := Divisors(Level(Mk));
      vprint HilbertModularForms: "#Eisenstein forms =", #res;
      if UseKnown then
        res cat:= Mk`KnownForms;
        vprint HilbertModularForms: "#Mk`KnownForms =", #Mk`KnownForms;
      end if;
      if UseTraceForms then //these should come for free
        trace_forms := [Mk | Trace(Mk, elt) : elt in Parent(Mk)`PrecomputationforTraceIdeals];
        res cat:= trace_forms;
        vprint HilbertModularForms: "#trace_forms =", #trace_forms;
      end if;
      res := Basis(res);
      vprint HilbertModularForms: "#res =", #res;
      if #res eq Dimension(Mk) then
        divisors := []; //we are done
      end if;
      for i->dd in divisors do
        Mkdd := HMFSpace(Parent(Mk), dd, k);
        cusp_forms := CuspForms(Mkdd, Mk : GaloisDescent:=true);
        vprint HilbertModularForms: i, Norm(dd), "#cusp_forms =", #cusp_forms;
        require &and[not IsZero(f) : f in cusp_forms] : "insufficient precision: a cusp form of seems to be zero";
        res cat:= cusp_forms;
        res := Basis(res);
        vprint HilbertModularForms: i, Norm(dd), "#res =", #res;
        if #res eq Dimension(Mk) then
          break dd;
        end if;
      end for;

      require Dimension(Mk) eq #res : Sprintf("CuspDimension(Mk) = %o != %o = dim(forms)", Dimension(Mk), #res);
    else
      res cat:= CuspFormBasis(Mk);
    end if;
    Mk`Basis := res;
  end if;

  // this handles the optional parameters
  return SubBasis(Mk`Basis, IdealClassesSupport, GaloisInvariant);
end intrinsic;

intrinsic GaloisInvariantBasis(Mk::ModFrmHilD) -> SeqEnum[ModFrmHilDElt]
  {returns a basis for the Galois invariant subspace}

  B := Basis(Mk);
  InvariantGenerators:=[];
  for x in B do
    Append(~InvariantGenerators, 1/2*(x+Swap(x)));
  end for;
  InvariantBasis:=[];
  for x in InvariantGenerators do
    if #LinearDependence(InvariantBasis cat [x]) eq 0 then
      Append(~InvariantBasis, x);
    end if;
  end for;
  return InvariantBasis;
end intrinsic;

intrinsic ComponentBasis(Mk::ModFrmHilD) -> SeqEnum[ModFrmHilDElt]
  {returns a Basis for Mk of forms that are only supported on one component}
  bbs := NarrowClassGroupReps(Parent(Mk));
  return &cat[Basis(Mk: IdealClassesSupport := [bb]) : bb in bbs];
end intrinsic;

intrinsic SpecifiedComponentBasis(Mk::ModFrmHilD, bb::RngOrdIdl) -> SeqEnum[ModFrmHilDElt]
  {returns a basis of forms that are only supported on a specified component bb}
  return Basis(Mk: IdealClassesSupport := [bb]);
end intrinsic;
