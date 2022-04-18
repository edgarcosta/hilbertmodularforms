freeze;

//////////////////////////////////////////////////////////////////////////////
//
// Predicates for Quaternion Algebras
// February 2006, John Voight
//
//////////////////////////////////////////////////////////////////////////////

declare attributes AlgQuat: is_definite;

//-------------
//
// Basic predicates for quaternion algebras over number fields.
//
//-------------

intrinsic IsTotallyComplex(F::FldAlg) -> BoolElt
  {Returns true iff F is totally complex.}

  return forall{v : v in InfinitePlaces(F) | IsComplex(v)};
end intrinsic;


intrinsic IsTotallyReal(F::FldAlg) -> BoolElt
  {Returns true iff F is totally real.}

  return forall{v : v in InfinitePlaces(F) | IsReal(v)};
end intrinsic;

intrinsic IsIndefinite(K::AlgQuat) -> BoolElt
   {True if and only if K is split at one or more infinity places}
  return not IsDefinite(K);
end intrinsic;

intrinsic IsDefinite(A::AlgQuat[FldAlg]) -> BoolElt
  {Returns true iff A is a definite quaternion algebra (over a totally real number field).  
   Here definite means that all infinite places are ramified in A.}

  if assigned A`is_definite then 
    return A`is_definite; 
  end if;

  F := BaseField(A);
  if not IsTotallyReal(F) then
    A`is_definite := false;
  else
    _, a := IsScalar((A.1-Trace(A.1)/2)^2);
    _, b := IsScalar((A.2-Trace(A.2)/2)^2);
    S := [v : v in RealPlaces(F) | Real(Evaluate(a,v)) lt 0 and 
                                   Real(Evaluate(b,v)) lt 0];
    A`is_definite := #S eq Degree(F);
  end if;
  return A`is_definite;
end intrinsic;

//-------------
//
// Basic functions for quaternion algebras over number fields.
//
//-------------

intrinsic Denominator(alpha::AlgQuatElt[FldAlg]) -> RngIntElt
  {}

  return Lcm([Denominator(x) : x in Eltseq(alpha)]);
end intrinsic;

intrinsic QuaternionicComplement(alpha::AlgQuatElt) -> AlgQuatElt
  {Given an element alpha, returns a nonzero element beta of trace
   zero such that B(alpha,beta) = 0, where B is the canonical
   bilinear form on A.}

  A := Parent(alpha);
  // Compute beta such that Trace(beta) = 0 = Trace(alpha*beta) = -Trace(alpha*Conjugate(beta))
  return A ! Kernel(Matrix([ [ Trace(b), Trace(alpha*b) ] : b in Basis(A) ])).1;
end intrinsic;
