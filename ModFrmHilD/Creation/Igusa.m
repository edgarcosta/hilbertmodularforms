intrinsic TotallyPositiveRepresentative(M::ModFrmHilD, bb::RngOrdIdl) -> Any
{Returns a totally positive representative of bb}
ZF := Integers(M);
PositiveRepresentative := [i : i in Representatives(M) | i*ZF eq bb];
return PositiveRepresentative[1];
end intrinsic;



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

intrinsic MultLaw(classrep::RngOrdIdl) -> any
{Computes coefficients of e_1^2, e_1e_2, and e_2^2 in terms of e_1 and e_2}
basechange := MatrixAlgebra(Rationals(),2)!Transpose(BasisMatrix(classrep));
e1 := Basis(classrep)[1];
e2 := Basis(classrep)[2];

e11 := Transpose(Matrix(Rationals(),[Eltseq(e1*e1)]));
e12 := Transpose(Matrix(Rationals(),[Eltseq(e1*e2)]));
e22 := Transpose(Matrix(Rationals(),[Eltseq(e2*e2)]));

a := Transpose(basechange^(-1)*e11);
b := Transpose(basechange^(-1)*e12);
c := Transpose(basechange^(-1)*e22);

return [a,b,c];
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


intrinsic Coeff(classrep::RngOrdIdl, elt::RngOrdElt, siegelWeight::RngIntElt) -> any
{Given a fractional ideal classrep representing a class in the narrow class group,
    an element in that classrep, and a siegel weight, computes the coefficient
    of the pullback of the siegel eisenstein form of that weight at that elt}
verbose := false;

coeff := 0;

multlaw := MultLaw(classrep);
a := Eltseq(multlaw[1]); b := Eltseq(multlaw[2]); c := Eltseq(multlaw[3]);

e1 := Basis(classrep)[1];
e2 := Basis(classrep)[2];
basechange := Matrix(Rationals(),[[e1[1],e2[1]],[e1[2],e2[2]]]);
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
if (Constraint(m1, r) ge 0) then
			      T := SiegelMatrix(m1, r);
sat, newT := SatisfiesRules(T);
if sat then
newcoeff := SiegelCoeff(siegelWeight,newT[1],newT[2],newT[3]);
if verbose then
print newT, elt, newcoeff;
end if;
coeff := coeff + SiegelCoeff(siegelWeight, newT[1], newT[2], newT[3]);
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
coeff := coeff + SiegelCoeff(siegelWeight,newT[1],newT[2],newT[3]);
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
coeff := coeff + SiegelCoeff(siegelWeight, newT[1],newT[2],newT[3]);
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
  prec := Precision(M);
  Cl, mp := NarrowClassGroup(F);
  reps := [mp(g):g in Cl];
  WeightVector := [ Weight : i in [1..Degree(F)]];

  max := #reps;
  // Once we can do higher class number get rid of this max = 1;
  max := 1;
  coeffs := AssociativeArray();
  for i := 1 to max do
     repcoeffs := AssociativeArray();
     numcoeffs := #ShintaniReps(M)[reps[i]];
     elts := ShintaniReps(M)[reps[i]];
  for j := 1 to numcoeffs do
       repcoeffs[ShintaniRepresentativeToIdeal(reps[i],elts[j])]:=Coeff(reps[i],elts[j],Weight);
  end for;
  coeffs[reps[i]]:=repcoeffs;

  end for;
  A := HMF(HMFSpace(M, WeightVector), coeffs);
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

intrinsic CanonicalRepresentation(f::ModFrmHilDElt) -> any
{gets this in terms of basis elements}
Mk := Parent(f);
F := BaseField(f);
M := GradedRing(f);
N := Level(f);

g,r,m := GeneratorsAndRelations(F,N:MaxGeneratorWeight:=Weight(f)[1]);
  bas := CanonicalBasis(g,r,Weight(f)[1]);
rel := LinearDependence(Append(bas,f));
rel := rel[1];

return bas, [-1*rel[i]/rel[#rel]:i in [1..#rel-1]],rel;
end intrinsic;
