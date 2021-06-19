

intrinsic ComputeMiddleM1(r::SeqEnum[FldRatElt]) -> FldRatElt
{We are constricted by 4m_1m_2 >= m^2. This function computes the
    value of m_1 that maximizes 4m_1m_2-m^2}
return Round((4*r[1]+2*r[3]*r[4])/(2*r[4]*r[4]-8*r[2]));
end intrinsic;

intrinsic SatisfiesRules(T::SeqEnum[FldRatElt]) -> boolean
{Having computed some candidate quadratic form, this function ensures it is
    actually integral, with first and last entry >=0}
if IsIntegral(T[1]) and IsIntegral(T[2]) and IsIntegral(T[3]) and (T[1] ge 0) and (T[3] ge 0) then
return true, [Integers()!T[1],Integers()!T[2],Integers()!T[3]];
end if;
return false, T;
end intrinsic;

intrinsic MultLaw(basis::SeqEnum, basechange::AlgMatElt) -> any
{Computes coefficients of e_1^2, e_1e_2, and e_2^2 in terms of e_1 and e_2}

e1 := basis[1];
e2 := basis[2];


//print(e1*e1);
//print(Eltseq(e1*e1));
e11 := Transpose(Matrix(Rationals(),[Eltseq(e1*e1)]));
e12 := Transpose(Matrix(Rationals(),[Eltseq(e1*e2)]));
e22 := Transpose(Matrix(Rationals(),[Eltseq(e2*e2)]));

a := Transpose(basechange^(-1)*e11);
b := Transpose(basechange^(-1)*e12);
c := Transpose(basechange^(-1)*e22);

return [a,b,c];
end intrinsic;


intrinsic MultLawV2(basis::SeqEnum) -> any
{Computes coefficients of e_1^2, e_1e_2, and e_2^2 in terms of e_1 and e_2}

e1 := basis[1];
e2 := basis[2];

return [e1^2,e1*e2,e2^2];
end intrinsic;

intrinsic Constraint(m1::RngIntElt, r::SeqEnum[FldRatElt]) -> any
{This computes the value of 4*m_1m_2-m^2}
out := (4*r[2] - r[4]*r[4])*m1*m1 + (4*r[1]+2*r[3]*r[4])*m1 - r[3]*r[3];
return out;
end intrinsic;

intrinsic SiegelMatrix(m1::RngIntElt, r::SeqEnum[FldRatElt]) -> any
{Given m_1 and r information, computes m, and m_2}
out := [0/1,0/1,0/1];
out[1] := m1;
out[2] := r[3] - r[4]*m1;
out[3] := r[1] + r[2]*m1;

return out;
end intrinsic;


intrinsic Coeff(basis::SeqEnum, elt::RngOrdElt, siegelWeight::RngIntElt, basechange:: AlgMatElt) -> any
{Given a fractional ideal classrep representing a class in the narrow class group,
    an element in that classrep, and a siegel weight, computes the coefficient
    of the pullback of the siegel eisenstein form of that weight at that elt}
verbose := false;



multlaw := MultLaw(basis, basechange);
a := Eltseq(multlaw[1]); b := Eltseq(multlaw[2]); c := Eltseq(multlaw[3]);

e1 := basis[1];
e2 := basis[2];
t := Transpose(Matrix(Rationals(),[Eltseq(elt)]));
t := Eltseq(Transpose(basechange^(-1)*t));
r := [0/1,0/1,0/1,0/1];


// These are the coefficients that allow us to compute m_2, m
// given a value for m_1. Depends on what in the 'multiplication
// law' is zero.
r[1] := (b[2]*t[1]-b[1]*t[2])/(c[1]*b[2]-c[2]*b[1]);
r[2] := (a[2]*b[1]-a[1]*b[2])/(c[1]*b[2]-c[2]*b[1]);
if (b[1] ne 0) then
	r[3] := (t[1]-c[1]*r[1])/b[1];
  r[4] := (a[1]-c[1]*r[2])/b[1];
else
  r[3] := (t[2]-c[2]*r[1])/b[2];
  r[4] := (a[2]+c[2]*r[2])/b[2];
end if;

// Add the intial value if it is positive and satisfies constraints
m1 := ComputeMiddleM1(r);
coeff := 0;
if (Constraint(m1, r) ge 0) then
	T := SiegelMatrix(m1, r);
  sat, newT := SatisfiesRules(T);
  if sat then
    newcoeff := SiegelCoeff(siegelWeight,newT[1],newT[2],newT[3]);
    if verbose then
      print newT, elt, newcoeff;
    end if;
    coeff +:= newcoeff;   
  end if;
end if;

// Work out from the central value until you are no longer positive
width := 2;
while(Constraint(m1,r) ge 0) do
	m1 := m1 - 1;

  if (Constraint(m1,r) ge 0) then
		T:=SiegelMatrix(m1,r);
    sat, newT := SatisfiesRules(T);
    if sat then
      newcoeff := SiegelCoeff(siegelWeight,newT[1],newT[2],newT[3]);
      if verbose then
        print newT, elt, newcoeff;
      end if;
      coeff +:= newcoeff; 
    end if;
  end if;

  if (Constraint(m1+width, r) ge 0) then
		T:= SiegelMatrix(m1+width,r);
    sat, newT := SatisfiesRules(T);
    if sat then
      newcoeff := SiegelCoeff(siegelWeight,newT[1],newT[2],newT[3]);
      if verbose then
        print newT, elt, newcoeff;
      end if;
      coeff +:= newcoeff; 
    end if;
  end if;
  width := width + 2;
end while;

return coeff;
end intrinsic;


intrinsic CoeffV2(basis::SeqEnum, elt::RngOrdElt, siegelWeight::RngIntElt) -> any
{Given a fractional ideal classrep representing a class in the narrow class group,
    an element in that classrep, and a siegel weight, computes the coefficient
    of the pullback of the siegel eisenstein form of that weight at that elt}
verbose := false;

e1 := basis[1];
e2 := basis[2];
a := e1^2; b := e1*e2; c := e2^2;


t := elt;

r := [0/1,0/1,0/1,0/1];


// These are the coefficients that allow us to compute m_2, m
// given a value for m_1. Depends on what in the 'multiplication
// law' is zero.
r[1] := (b[2]*t[1]-b[1]*t[2])/(c[1]*b[2]-c[2]*b[1]);
r[2] := (a[2]*b[1]-a[1]*b[2])/(c[1]*b[2]-c[2]*b[1]);
if (b[1] ne 0) then
  r[3] := (t[1]-c[1]*r[1])/b[1];
  r[4] := (a[1]-c[1]*r[2])/b[1];
else
  r[3] := (t[2]-c[2]*r[1])/b[2];
  r[4] := (a[2]+c[2]*r[2])/b[2];
end if;

// Add the intial value if it is positive and satisfies constraints
m1 := ComputeMiddleM1(r);
coeff := 0;
if (Constraint(m1, r) ge 0) then
  T := SiegelMatrix(m1, r);
  sat, newT := SatisfiesRules(T);
  if sat then
    newcoeff := SiegelCoeff(siegelWeight,newT[1],newT[2],newT[3]);
    if verbose then
      print newT, elt, newcoeff;
    end if;
    coeff +:= newcoeff;   
  end if;
end if;

// Work out from the central value until you are no longer positive
width := 2;
while(Constraint(m1,r) ge 0) do
  m1 := m1 - 1;

  if (Constraint(m1,r) ge 0) then
    T:=SiegelMatrix(m1,r);
    sat, newT := SatisfiesRules(T);
    if sat then
      newcoeff := SiegelCoeff(siegelWeight,newT[1],newT[2],newT[3]);
      if verbose then
        print newT, elt, newcoeff;
      end if;
      coeff +:= newcoeff; 
    end if;
  end if;

  if (Constraint(m1+width, r) ge 0) then
    T:= SiegelMatrix(m1+width,r);
    sat, newT := SatisfiesRules(T);
    if sat then
      newcoeff := SiegelCoeff(siegelWeight,newT[1],newT[2],newT[3]);
      if verbose then
        print newT, elt, newcoeff;
      end if;
      coeff +:= newcoeff; 
    end if;
  end if;
  width := width + 2;
end while;

return coeff;
end intrinsic;



// FIXME documentation string
intrinsic SiegelEisensteinPullback(M::ModFrmHilDGRng, Weight::RngIntElt) -> any
{Does Something}
  F := BaseField(M);
  ZF:=Integers(F);
  prec := Precision(M);
  Cl, mp := NarrowClassGroup(F);
  reps := [mp(g):g in Cl];
  WeightVector := [ Weight : i in [1..Degree(F)]];

  max := #reps;
  // Once we can do higher class number get rid of this max = 1;

  coeffs := AssociativeArray();
  for i := 1 to max do
    bb:=reps[i];
    basbb:=Basis(bb);
    basechange := MatrixAlgebra(Rationals(),2)!Transpose(BasisMatrix(bb));
         print(basbb);
    repcoeffs := AssociativeArray();
    numcoeffs := #ShintaniReps(M)[bb];
    elts := ShintaniReps(M)[bb];
    for j := 1 to numcoeffs do
      repcoeffs[ShintaniRepresentativeToIdeal(M, bb,elts[j])]:=Coeff(basbb,elts[j],Weight, basechange);
    end for;
    coeffs[bb]:=repcoeffs;
  end for;

  A := HMF(HMFSpace(M, WeightVector), coeffs);
  return A;
end intrinsic;


// FIXME documentation string
intrinsic SiegelEisensteinPullbackV2(M::ModFrmHilDGRng, Weight::RngIntElt) -> any
{Does Something}
  F := BaseField(M);
  coeffs := AssociativeArray();
  bb:=1*Integers(F);
  basbb:=Basis(bb);
  repcoeffs := AssociativeArray();
  elts := ShintaniReps(M)[bb];
  for j := 1 to #elts do
    repcoeffs[ShintaniRepresentativeToIdeal(M, bb,elts[j])]:=CoeffV2(basbb,elts[j],Weight);
  end for;
  coeffs[bb]:=repcoeffs;
  A := HMF(HMFSpace(M, [ Weight : i in [1..Degree(F)]]), CompleteCoeffsZeros(M, coeffs));
  return A;
end intrinsic;


intrinsic UniversalIgusa(M::ModFrmHilDGRng) -> any
{Computes the IgusaClebsch invariants for QQ(sqrt(i)), using specified precision}

SiegEis4 := SiegelEisensteinPullback(M,4);
SiegEis6 := SiegelEisensteinPullback(M,6);
SiegEis10 := SiegelEisensteinPullback(M,10);
SiegEis12 := SiegelEisensteinPullback(M,12);


Chi10 := -43867/(2^12*3^5*5^2*7^1*53^1)*(SiegEis4*SiegEis6-SiegEis10);
Chi12Const := 131*593/(2^13*3^7*5^3*7^2*337^1);
Chi12Form := (3^2*7^2*SiegEis4*SiegEis4*SiegEis4+2^1*5^3*SiegEis6*SiegEis6-691*SiegEis12);
Chi12 := Chi12Const*Chi12Form;

return SiegEis4,SiegEis6,SiegEis10,SiegEis12,Chi10,Chi12;

end intrinsic;



intrinsic UniversalIgusaV2(M::ModFrmHilDGRng) -> any
{Computes the IgusaClebsch invariants for QQ(sqrt(i)), using specified precision}

SiegEis4 := SiegelEisensteinPullbackV2(M,4);
SiegEis6 := SiegelEisensteinPullbackV2(M,6);
SiegEis10 := SiegelEisensteinPullbackV2(M,10);
SiegEis12 := SiegelEisensteinPullbackV2(M,12);


Chi10 := -43867/(2^12*3^5*5^2*7^1*53^1)*(SiegEis4*SiegEis6-SiegEis10);
Chi12Const := 131*593/(2^13*3^7*5^3*7^2*337^1);
Chi12Form := (3^2*7^2*SiegEis4*SiegEis4*SiegEis4+2^1*5^3*SiegEis6*SiegEis6-691*SiegEis12);
Chi12 := Chi12Const*Chi12Form;

return SiegEis4,SiegEis6,SiegEis10,SiegEis12,Chi10,Chi12;

end intrinsic;


intrinsic CanonicalRepresentation(f::ModFrmHilDElt) -> any
{gets this in terms of basis elements}
Mk := Parent(f);
F := Field(f);
M := GradedRing(f);
N := Level(f);

g,r,m := GeneratorsAndRelations(F,N:MaxGeneratorWeight:=Weight(f)[1],Precision:=Precision(f));
bas,m := CanonicalBasis(g,r,f);
f := HMF(Universe(bas),Coefficients(f));
rel := LinearDependence(Append(bas,f));
rel := rel[1];

return bas, [-1*rel[i]/rel[#rel]:i in [1..#rel-1]],m;
end intrinsic;
