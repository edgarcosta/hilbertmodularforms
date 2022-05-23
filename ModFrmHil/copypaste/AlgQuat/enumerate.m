freeze;

//////////////////////////////////////////////////////////////////////////////
//
// Enumerative Algorithms for Quadratic Forms and Quaternion Algebras
// April 2006, John Voight
//
//////////////////////////////////////////////////////////////////////////////

import "../AlgAss/enum.m": TraceFormsOnQBasis;

debug := false;

//-------------
//
// Enumeration of elements in a Z_F-lattice inside a definite
// quaternion algebra.
//
//-------------

function QsFromCholesky(M);
  // Assumes that M is symmetric
  m := Ncols(M);
  Q := MatrixRing(BaseRing(M), m)!0;
  for i := 1 to m do
    for j := i to m do
      Q[i,j] := M[i,j];
    end for;
  end for;
  for i := 1 to m-1 do
    for j := i+1 to m do
      Q[j,i] := Q[i,j];
      Q[i,j] /:= Q[i,i];
    end for;
    for k := i+1 to m do
      for l := k to m do
        Q[k,l] -:= Q[k,i]*Q[i,l];
      end for;
    end for;
  end for;

  return Q;
end function;

// Enumerate the elements in the lattice represented by the pseudomatrix
// P with norm bounded by the sequence B, with the algebra A.
function EnumerateInternal(P, A, B);
  F := BaseField(A);
  Z_F := MaximalOrder(F);
  Foo := InfinitePlaces(F);
  n := Degree(F);

  // Lattices don't like denominators, so scale the generators (and 
  // the ideals, proportionally) to guarantee integral coefficient ideals
  RR := Parent(Evaluate(F.1,Foo[1]));
  eps := 10^(-Precision(RR)/2);
  B := [RR | B[i] + eps : i in [1..n]];
  Pbasis := [A!b : b in Basis(P)];
  I := CoefficientIdeals(P);
  den := [Denominator(I[i]) : i in [1..4]];
  I := [I[i]*den[i] : i in [1..4]];
  Pbasis := [Pbasis[i]/den[i] : i in [1..4]];

  // Matrices representing the positive definite quadratic norm forms 
  // for each real place.
  M := [ MatrixRing(RR,4)![Evaluate(Norm(x+y)-Norm(x)-Norm(y),v)/2 : x,y in Pbasis] : 
         v in Foo];

  // Initial LLL step does not seem to work over Z_F, so ignore.
  // Compute the Cholesky decomposition; see [FinkePohst].
  Q := [QsFromCholesky(M[i]) : i in [1..n]];

  // The final (4th) coordinate is immediately bounded in a box, which
  // we enumerate.
  // Remember that the lattice vectors are with respect to the basis of
  // the ideal!
  L := MinkowskiLattice(Z_F!!I[4]);
  Lbasis := Basis(Z_F!!I[4]);
  V := LatticeVectorsInBox(L, [Sqrt(B[i]/Q[i][4,4]) : i in [1..n]]);
  V := [&+[Eltseq(v)[j]*Lbasis[j] : j in [1..n]] : v in V];

  // Store the valuations and new upper bounds for each found vector
  newV := [];
  zeros := [RR | 0 : i in [1..n]];
  for x in V do
    x4 := Z_F!Eltseq(x);
    Append(~newV, <[0,0,0,x4], [zeros : i in [1..3]] cat 
                               [[Evaluate(F!x4,v) : v in Foo]], B>);
  end for;
  V := newV;

  for k := 3 to 1 by -1 do
    newV := [];
    L := MinkowskiLattice(Z_F!!I[k]);
    Lbasis := Basis(Z_F!!I[k]);
    for i := 1 to #V do
      // print k, i, #V, #newV;
      v := V[i];
      x := v[2];
      T := v[3];
      Bv := [];

      // Using the Cholesky decomposition, compute new upper bounds for the
      // kth coordinate; this is a modified version of the Fincke-Pohst
      // algorithm, [FinckePohst]
      for j := 1 to n do
        qx := 0;
        for l := k+2 to 4 do
          qx +:= Q[j][k+1,l]*x[l][j];
        end for;
        T[j] -:= Q[j][k+1,k+1]*(x[k+1][j] + qx)^2;

        if T[j] lt 0 then
          // Allow a generous error (square root of the precision).
          if Abs(T[j]) lt eps then
            T[j] := 0;
          else
            continue i;
          end if;
        end if;
        qx := &+[Q[j][k,l]*x[l][j] : l in [k+1..4]];
        rtj := Sqrt(T[j]/Q[j][k,k]);
        Bv[j] := Max(Abs(rtj-qx),Abs(-rtj-qx));
        if Abs(Bv[j]) lt eps then
          Bv[j] := eps;
        end if;
      end for;

      // Enumerate lattice vectors
      xks := LatticeVectorsInBox(L, Bv);
      xks := [&+[Eltseq(xk)[j]*Lbasis[j] : j in [1..n]] : xk in xks];

      for xk in xks do
        newv := v;
        newv[1][k] := xk;
        newv[2][k] := [Evaluate(F!xk,v) : v in Foo];
        newv[3] := T;
        Append(~newV, newv);

        // Since both v and -v will always appear, we choose one sign
        // arbitrarily, no need to keep track of both!
        if xk ne 0 and not &and[v[1][l] eq 0 : l in [k+1..4]] then
          newv[1][k] *:= -1;
          newv[2][k] := [-n : n in newv[2][k]];
          Append(~newV, newv);
        end if;
      end for;
    end for;
    V := newV;
  end for;

  // Final check, should not be necessary, but nevertheless inexpensive
  S := [ A!&+[v[1][i]*Pbasis[i] : i in [1..4]] : v in V];
  S := [ s : s in S | &and[Evaluate(Norm(s),Foo[i]) le B[i] : i in [1..n]]];
  return S;
end function;

intrinsic Enumerate(I::AlgAssVOrdIdl[RngOrd], B::SeqEnum[RngElt]) -> SeqEnum
  {Lists all elements x in I such that v[i](Norm(x)) <= B[i] for
   v the real embeddings.}

  O := Order(I);
  A := Algebra(O);
  require IsDefinite(A) : 
    "The ideal must be contained in a definite quaternion algebra";
  P := PseudoMatrix(I);

  BI := Basis(I);
  M := Matrix([A!BI[i] : i in [1..4]]);
  P := PseudoMatrix(CoefficientIdeals(P), M);

  S := EnumerateInternal(P, A, B);
  return [O!s : s in S];
end intrinsic;

intrinsic Enumerate(O::AlgAssVOrd[RngOrd], B::SeqEnum[RngElt]) -> SeqEnum
  {Lists all elements x of O such that v[i](Norm(x)) <= B[i] for
   v the real embeddings.}

  A := Algebra(O);
  require IsDefinite(A) : "The order must be a definite quaternion order";
  S := EnumerateInternal(PseudoMatrix(O), A, B);
  return [O!s : s in S];
end intrinsic;

intrinsic LatticeVectorsInBox(L::Lat, B::SeqEnum[FldReElt]) -> SeqEnum
  {Returns the set of linear combinations of the basis of L giving vectors v
   such that |v[i]| <= B[i].}

  LL, T := LLL(L);
  LLbasis := Basis(LL);
  d := Dimension(L);
  Minv := Matrix(Basis(LL))^(-1);

  // This gives upper bounds for the size of the coefficients
  eps := 10^(-Precision(B[1])/2);
  Bs := [];
  RR := BaseRing(L);
  for nu in CartesianPower([-1,1],d-1) do
    Append(~Bs, Eltseq(Matrix(RR,1,d,[B[1]] cat [nu[i]*B[i+1] : i in [1..d-1]])*Minv));
  end for;
  C := [ Floor(Max([Abs(Bs[i][j]) : i in [1..#Bs]])+eps) : j in [1..d] ];
  a := [0 : i in [1..d]];

  function Increment(aa);
    d := #aa;
    if d eq 1 or aa[d] lt C[d] then
      aa[d] +:= 1;
      return aa;
    else
      return ($$)(aa[1..d-1]) cat [-C[d]];
    end if;
  end function;

  foundVecs := [];

  while a[1] le C[1] do
    v := &+[ a[i]*LLbasis[i] : i in [1..d]];
    if &and[ Abs(v[i]) le B[i]+eps : i in [1..d]] then
      Append(~foundVecs, Matrix(Integers(),1,d,a)*T);
    end if;
    a := Increment(a);
  end while;

  return foundVecs;
end intrinsic;

//-------------
//
// (Free) Z-bases.
//
//-------------

/*
function ZBasisInternal(P, A);
  PI := CoefficientIdeals(P);
  B := [A!b : b in Basis(P)];
  E := [];
  for i := 1 to 4 do
    E cat:= [x*B[i] : x in Basis(PI[i])];
  end for;
  return E;
end function;
*/

intrinsic ZBasis(O::AlgAssVOrd[RngOrd]) -> SeqEnum
  {A basis for the order O as a free Z-module}

  return ZBasis(PseudoMatrix(O), Algebra(O));
end intrinsic;

intrinsic ZBasis(I::AlgAssVOrdIdl[RngOrd]) -> SeqEnum
  {A basis for the ideal I as a free Z-module}

  // this used to sometimes return elements of the order, D
  // rather than elements of Algebra(O).  I'm changing it 
  // to always be Algebra(O)                   --- SRD

  //return ZBasisInternal(PseudoMatrix(I), Order(I));

  O := Order(I);
  zb := ZBasis(PseudoMatrix(I), O);
  if Universe(zb) cmpne Algebra(O) then
    assert Universe(zb) cmpeq O;
    ChangeUniverse(~zb, Algebra(O));
  end if;
  return zb;
end intrinsic;

/*
intrinsic ZBasis(P::PMat, A::AlgAss) -> SeqEnum
  {Returns a Z-basis of the Z-module inside A corresponding to the pseudomatrix P.}

  return ZBasisInternal(P, A);
end intrinsic;
*/

//-------------
//
// Reduced bases.
//
//-------------

// Requires the base field to be totally real; reduces the coefficients
// with respect to the standard basis of A.

function ReducedBasisInternal(P, A : return_new_basis:=true, q0 := 0, w := []); 
  if Type(P) eq SeqEnum then
    Pbasis := P;
  else
    if BaseField(A) cmpeq Rationals() then
      Pbasis := ZBasis(P);
    else
      Pbasis := ZBasis(P, A);
    end if;
  end if;
  m := #Pbasis;

  if IsDefinite(A) then
    //Pbmat := Matrix([ &cat [Flat(a) : a in Eltseq(b)] : b in Pbasis ]);
    Pbmat := Matrix([ Flat(b) : b in Pbasis ]);
    M := 1/2 * Pbmat * TraceFormsOnQBasis(A) * Transpose(Pbmat);
    /* Obvious but slow way, because mult for matrices over FldNum is slow
    // GramMatrixofAlgebra gives the norm form A x A -> BaseField(A)
    Pbmat := Matrix([ Eltseq(b) : b in Pbasis ]); 
    PbasisGram := Pbmat * GramMatrixofAlgebra(A) * Transpose(Pbmat);
    Mold := 1/2 * Matrix( Rationals(), m, [ Trace(x): x in Eltseq(PbasisGram)]);
    assert Mold eq M; */

    L, T := LLL(LatticeWithGram(M : CheckPositive:=debug));
  elif IsTotallyReal(BaseField(A)) then
    if BaseField(A) cmpeq Rationals() then
      S := [];
    else
      _, S := Discriminant(A);
    end if;
    if #S eq Degree(BaseField(A))-1 then
      prec0 := 20*Degree(BaseField(A));
      prec := prec0;
      while true do 
        if q0 cmpeq 0 then
          // don't set this as the default because then it gets executed in all cases
          q0 := UnitDisc(:Precision := prec)!0; 
        elif Parent(q0)`prec lt prec then
          q0 := UnitDisc(:Precision := prec)!ComplexValue(q0);           
        end if;
        M := DefiniteGramMatrix(Pbasis : q := q0, w := w);
        try
          b := IsPositiveDefinite(M);
        catch e
          assert "efinite" in e`Object;  // "cannot determine definiteness"
          b := false;
        end try;
        if b then
          break;
        end if;
        prec +:= prec0;
        vprintf Quaternion: "QuaternionAlgebra: increasing precision to %o\n", prec;
      end while;
      L, T := LLL(LatticeWithGram(M));
      // TO DO: do we still get 'not positive definite' errors from LatticeWithGram ?
    else
      Foo := RealPlaces(BaseField(A));

      M := Matrix([[Evaluate(Pb[i],v) : i in [1..4], v in Foo] : Pb in Pbasis]);
      L, T := LLL(LatticeWithBasis(M));
    end if;
  else
    T := IdentityMatrix(BaseField(A), m);
    L := StandardLattice(m);
  end if;

  underlyingPbasis := Pbasis;
  if return_new_basis or debug then 
    Pbasis := [ &+[Pbasis[j]*T[i,j] : j in [1..m]] : i in [1..m]];
  end if;

  if debug and IsDefinite(A) then
    assert &and[ Trace(Norm(Pbasis[i])) eq Norm(L.i) : i in [1..m]];
    assert [Trace(Norm(x+y)-Norm(x)-Norm(y))/2 : x,y in Pbasis]
           eq Eltseq(GramMatrix(L));
    assert [Trace(Norm(x+y)-Norm(x)-Norm(y))/2 : x,y in underlyingPbasis]
           eq Eltseq(InnerProductMatrix(L));  // tautology 
  end if;
  
  if return_new_basis then 
    return Pbasis, L, underlyingPbasis;
  else 
    return L, underlyingPbasis; 
  end if;
end function;

intrinsic ReducedBasis(O::AlgAssVOrd[RngOrd]) -> SeqEnum, Lat
  {For an order O over a totally real field, if O is totally definite
   then a Z-basis for O is returned which is LLL-reduced with
   respect to the quadratic form Trace(Norm(x)), else with respect to 
   the coefficients in the standard basis of A.}

  require Type(Algebra(O)) eq AlgQuat : 
    "Function only implemented for quaternion algebras";
  require IsTotallyReal(FieldOfFractions(BaseRing(O))) : 
    "O must be an order of a totally real number ring";

  red_basis, L := ReducedBasisInternal(PseudoMatrix(O), Algebra(O));
  red_basis := ChangeUniverse(red_basis, O);

  return red_basis, L;
end intrinsic;

intrinsic ReducedBasis(I::AlgAssVOrdIdl[RngOrd]) -> SeqEnum
  {Reduced basis of I.}

  O := Order(I);
  A := Algebra(O);
  require Type(A) eq AlgQuat : 
    "Function only implemented for quaternion algebras";
  require IsTotallyReal(FieldOfFractions(BaseRing(O))) : 
    "O must be an order of a totally real number ring";

  return ReducedBasisInternal(PseudoMatrix(I, A), A);
end intrinsic;

//-------------
//
// Enumeration of elements in a Z_F-lattice of a definite quaternion
// algebra with respect to the underlying Z-lattice.
//
//-------------

intrinsic Enumerate(O::AlgAssVOrd[RngOrd], B1::RngElt, B2::RngElt) -> SeqEnum
  {The sequence of elements x in O (up to sign) such that 
   Trace(Norm(x)) in [A..B], where O is a definite quaternion order.}

  //Pbasis, L := ReducedBasis(O);
  L, Pbasis := ReducedBasisInternal(PseudoMatrix(O), Algebra(O) 
                                   : return_new_basis:=false);
  m := #Pbasis;
  S := ShortVectors(L, B1, B2);
  ans := [ &+[ S[i][1][j]*Pbasis[j] : j in [1..m] ] : i in [1..#S] ];
  //ans := [ &+[ Coordinates(S[i][1])[j]*Pbasis[j] : j in [1..m] ] : i in [1..#S] ];
  
  if debug then 
    assert &and[ Trace(Norm(ans[i])) eq S[i][2] : i in [1..#S] ];
  end if;
  return ans;
end intrinsic;

intrinsic Enumerate(O::AlgAssVOrd[RngOrd], B::RngElt) -> SeqEnum
  {The sequence of elements x in O (up to sign) such that 
   Trace(Norm(x)) <= B, where O is a definite quaternion order.}

  //Pbasis, L := ReducedBasis(O);
  L, Pbasis := ReducedBasisInternal(PseudoMatrix(O), Algebra(O) 
                                   : return_new_basis:=false);
  m := #Pbasis;
  S := ShortVectors(L, B);
  ans := [ &+[ S[i][1][j]*Pbasis[j] : j in [1..m] ] : i in [1..#S] ];
  //ans := [ &+[ Coordinates(S[i][1])[j]*Pbasis[j] : j in [1..m] ] : i in [1..#S] ];
  
  if debug then 
    assert &and[ Trace(Norm(ans[i])) eq S[i][2] : i in [1..#S] ];
  end if;
  return ans;
end intrinsic;

function EnumerateInternalFromBasis(Pbasis, A, B : exact:=false);
  m := #Pbasis;
  L := ReducedBasisInternal(Pbasis, A : return_new_basis:=false); 
  // The basis of the ambient vector space of L corresponds to Pbasis
  S := exact select ShortVectors(L, B, B)
              else  ShortVectors(L, B);
  ans := [ &+[ S[i][1][j]*Pbasis[j] : j in [1..m] ] : i in [1..#S] ];
  
  if debug then 
    assert &and[ Trace(Norm(ans[i])) eq S[i][2] : i in [1..#S] ];
  end if;
  return ans;
end function;

function EnumerativeSearchUntilSuccess(Bp, Np : increment:=1)
  L := StandardLattice(#Bp);
  low := 1; 
  high := increment;
  P := ShortVectorsProcess(L, low, high);
  while true do
    v := NextVector(P);
    if IsZero(v) then
      low +:= increment; 
      high +:= increment;
      P := ShortVectorsProcess(L, low, high);
      continue;
    end if;
    v := Eltseq(v);
    nu := &+[v[i]*Bp[i] : i in [1..#Bp]];
    Nnu := Abs(Norm(Norm(nu)));
    if Nnu eq Np then
      return nu;
    end if;
  end while;
end function;

function enumerate_z(X, a, b)
  L:= LatticeWithGram(GramMatrix(X));
  if a cmpeq 0 then
    if b eq 0 then return [ L ! 0 ]; end if;
    S:= ShortVectors(L, 2*b);
    return [ L ! 0] cat [s[1]: s in S]; // cat [-s[1]: s in S];
  end if;
  S:= ShortVectors(L, 2*a, 2*b);
  return [s[1]: s in S]; // cat [-s[1]: s in S];
end function;

intrinsic Enumerate(O::AlgQuatOrd[RngInt], A::RngIntElt, B::RngIntElt) -> SeqEnum
{Enumerates all elements in the order O with reduced norm in [A..B] or [0..B].}
  require IsDefinite(Algebra(O)) : "The algebra must be definite.";
  require A ge 0 and B ge 0 and A le B : "The boundaries must satisfy 0 <= A <= B";
  S:= enumerate_z(O, A, B);
  return [ O | Eltseq(s) : s in S ];
end intrinsic;

intrinsic Enumerate(O::AlgQuatOrd[RngInt], B::RngIntElt) -> SeqEnum
{"} // "
  return Enumerate(O, 0, B);
end intrinsic;

intrinsic Enumerate(I::AlgQuatOrdIdl[RngInt], A::RngElt, B::RngElt) -> SeqEnum
{Enumerates all elements in the ideal I with reduced norm in [A..B] or [0..B].}
  require IsDefinite(Algebra(I)) : "The algebra must be definite";
  require A ge 0 and B ge 0 and A le B : "The boundaries must satisfy 0 <= A <= B";
  require {Type(A), Type(B)} subset {RngIntElt, FldRatElt} : "A and B must be integers or rationals.";
  S:= enumerate_z(I, A, B);
  BB:= Basis(I);
  return [ &+[BB[i] * s[i] : i in [1..4]] : s in S ];
end intrinsic;

intrinsic Enumerate(I::AlgQuatOrdIdl[RngInt], B::RngElt) -> SeqEnum
{"} // "
  return Enumerate(I, 0, B);
end intrinsic;


//-------------
//
// Bibliography
//
//-------------

/*

[FinckePohst] 
U. Fincke and M. Pohst, Improved methods for calculating vectors of short length in a lattice, including a complexity analysis, Math. Comp. 44 (1985), no. 170, 463--471.

*/
