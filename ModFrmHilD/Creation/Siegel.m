////////////////////////////
///// IGUSA Invariants /////
////////////////////////////

/* This code generates Siegel Eisenstein series of a given weight, degree two. 
   It follows Theorem 3.4 from https://arxiv.org/pdf/1005.1234.pdf */

intrinsic Cohen(k::RngIntElt, D::RngIntElt) -> any
 {This is the Cohen function from the above paper}
out := 0;
s := k+1;
D0 := Discriminant(QuadraticField(D));
f:= D div D0;

if f eq 0 then f:= 0; 
 else f:=Round(f^(1/2)); 
end if;

for i := 1 to f do
	   if (f mod i) eq 0 then
			  out := out + MoebiusMu(i)*KroneckerSymbol(D0,i)*i^(s-2)*DivisorSigma(2*s-3,f div i);
end if;

end for;
out := out * Evaluate(LSeries(KroneckerCharacter(D0)),2-s);

return out;
end intrinsic;



intrinsic alpha(D::RngIntElt,k::RngIntElt) -> any
{This is the alpha function from the above paper. It is just a normalized version of Cohen.}
if D eq 0 then return 1; end if;
return Cohen(k-1,D)/Evaluate(RiemannZeta(),3-2*k);
end intrinsic;


intrinsic SiegelCoeff(k::RngIntElt,m1::RngIntElt,m::RngIntElt,m2::RngIntElt) -> RngIntElt
{Takes in an element of Sym_2(Z) and an Eisenstein series indexed by k and returns the associated coeff}
if [m1,m,m2] eq [0,0,0] then return 1; end if;
coeff:=0;
gcd := GreatestCommonDivisor(m1, GreatestCommonDivisor(m, m2));
for i := 1 to gcd do 
	   if gcd mod i eq 0 then 
  coeff:=coeff+i^(k-1)*alpha((m*m-4*m1*m2) div (i*i),k);
end if;
end for;

coeff := coeff*-2*k/BernoulliNumber(k);

return coeff;

end intrinsic;
 

