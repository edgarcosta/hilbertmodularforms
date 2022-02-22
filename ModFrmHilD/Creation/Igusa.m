intrinsic SatisfiesRules(T::SeqEnum) -> BoolElt
{Having computed some candidate quadratic form, this function ensures it is
    actually integral, with first and last entry >=0, and positive semi-definite}
    if IsIntegral(T[1]) and IsIntegral(T[2]) and IsIntegral(T[3]) and (T[1] ge 0) and (T[3] ge 0) and (4*T[1]*T[3] ge T[2]^2) then
       return true, [Integers()!T[1],Integers()!T[2],Integers()!T[3]];
    end if;
    return false, T;
end intrinsic;


intrinsic SiegelMatrices(a::RngIntElt, b::RngIntElt, D::RngIntElt) -> Any
{Given nu=a e_1+ b e_2 with e_1=1, e_2=(D+sqrt(D))/2, compute possible elligible  values (m_1, m, m_2) such that m_1+m e_2+ m_2 e_2^2=a+b e_2}
values:=[];
if [a,b] eq [0,0] then
  return [[0,0,0]];
end if;
if (b^2*D^2+4*a*b*D+4*a^2-b^2*D) ge 0 then 
  leftpt:=Ceiling(((b*D+2*a)-Sqrt(b^2*D^2+4*a*b*D+4*a^2-b^2*D))/D);
  rightpt:=Floor(((b*D+2*a)+Sqrt(b^2*D^2+4*a*b*D+4*a^2-b^2*D))/D);
  for m_2 in [Max([0, leftpt])..rightpt] do
    booll, T:=SatisfiesRules([a-m_2*(D-D^2)/4, b-m_2*D, m_2]);
    if booll then
      Append(~values, T);
    end if;
  end for;
end if;
return values;
end intrinsic;

intrinsic ConvertBasis(nu::RngOrdElt) -> Any
    {given a Shintani rep gives [a,b] such that a e_1+ b e_2=nu for  e_1=1, e_2=(D+sqrt(D))/2}
    ZF:=Parent(nu);
    D:=Discriminant(ZF);
    assert (D mod 4 eq 0) or (D mod 4 eq 1); 
    if D mod 4 eq 0 then
      Ord:=Order([ZF.1, (D*ZF.1+2*ZF.2)/2]: IsBasis:=true);
    else 
      Ord:=Order([ZF.1, ZF.2+(D-1)/2]: IsBasis:=true);
    end if;
    return Ord!nu;
end intrinsic;


intrinsic Coeff( elt::RngOrdElt, siegelWeight::RngIntElt) -> Any
{Given a fractional ideal classrep representing a class in the narrow class group,
    an element in that classrep, and a siegel weight, computes the coefficient
    of the pullback of the siegel eisenstein form of that weight at that elt}


coeff:=0;

newelt:=ConvertBasis(elt);
a:=Integers()!(newelt[1]); b:=Integers()!(newelt[2]);

candidates:=SiegelMatrices(a, b, Discriminant(Parent(elt)));

for item in candidates do
  coeff+:=SiegelCoeff(siegelWeight,item[1],item[2],item[3]);
end for;

return coeff;
end intrinsic;



// // FIXME documentation string
// intrinsic SiegelEisensteinPullback(M::ModFrmHilDGRng, Weight::RngIntElt) -> Any
// {Does Something}
//   F := BaseField(M);
//   ZF:=Integers(F);
//   coeffs := AssociativeArray();
//   Clplus, mp:=NarrowClassGroup(F);
//   //h:=ClassNumber(F);
//   bb:=mp(Different(ZF)@@mp);
//   repcoeffs := AssociativeArray();
//   elts := ShintaniReps(M)[bb];
//   print(elts);
//   for j := 1 to #elts do
//     print(Norm(elts[j]));
//     repcoeffs[ShintaniRepresentativeToIdeal(M, bb, ZF!elts[j])]:=Coeff(ZF!elts[j],Weight);
//   end for;
//   coeffs[bb]:=repcoeffs;
//   A := HMF(HMFSpace(M, [ Weight : i in [1..Degree(F)]]), CompleteCoeffsZeros(M, coeffs));
//   return A;
// end intrinsic;

intrinsic SiegelEisensteinPullback(M::ModFrmHilDGRng, k::SeqEnum[RngIntElt]) -> Any
{Returns the pullback of the Siegel Eisenstein series of a given weight}
  F := BaseField(M);
  ZF:=Integers(F);
  Clplus, mp:=NarrowClassGroup(F);
  h:=ClassNumber(F);
  bb:=mp(Different(ZF)@@mp);
  _, factors:=IsPrincipal(Different(ZF)/bb);
  if not IsTotallyPositive(factors) then
    factors:=-factors;
  end if;
  G, unitmp := TotallyPositiveUnits(M);

  Mkplus := HMFSpace(M, k);
  if #Clplus gt h then
    minusunitchar := AssociativeArray();
    for bb in NarrowClassGroupReps(M) do
      minusunitchar[bb] := UnitCharacter(F, [-1]);
    end for;
    //X := HeckeCharacterGroup(1*ZF, [1..Degree(BaseField(M))]);
    //chi := X!1;
    Mkminus := HMFSpace(M, k: unitcharacters := minusunitchar);
  else
    Mkminus := Mkplus;
  end if;
  eta:=unitmp(G.1);
  elts := ShintaniReps(M)[bb];
  fpluscoeffs:=AssociativeArray();
  fminuscoeffs:=AssociativeArray();
  for j := 1 to #elts do
    elt:=ZF!(elts[j]*factors);
    anuplus:=Coeff(elt, k[1]);
    anuminus:=Coeff(elt*eta^(-1), k[1]);
    fpluscoeffs[elts[j]]:=1/2*(anuplus+anuminus);
    fminuscoeffs[elts[j]]:=1/2*(anuplus-anuminus);
  end for;
  fplus:=HMFComp(Mkplus, bb, fpluscoeffs);
  fminus:=HMFComp(Mkminus, bb, fminuscoeffs);
  return fplus, fminus;
end intrinsic;



intrinsic UniversalIgusa(M::ModFrmHilDGRng) -> Any
{Computes the IgusaClebsch invariants for QQ(sqrt(i)), using specified precision}

SiegEis4 := SiegelEisensteinPullback(M,[4,4]);
SiegEis6 := SiegelEisensteinPullback(M,[6,6]);
SiegEis10 := SiegelEisensteinPullback(M,[10,10]);
SiegEis12 := SiegelEisensteinPullback(M,[12,12]);


Chi10 := -43867/(2^12*3^5*5^2*7^1*53^1)*(SiegEis4*SiegEis6-SiegEis10);
Chi12Const := 131*593/(2^13*3^7*5^3*7^2*337^1);
Chi12Form := (3^2*7^2*SiegEis4*SiegEis4*SiegEis4+2^1*5^3*SiegEis6*SiegEis6-691*SiegEis12);
Chi12 := Chi12Const*Chi12Form;

return SiegEis4,SiegEis6,SiegEis10,SiegEis12,Chi10,Chi12;

end intrinsic;


intrinsic CanonicalRepresentation(f::ModFrmHilDElt) -> Any
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
