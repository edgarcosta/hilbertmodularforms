
//////////////////////////////////////////////////////

///////////// Hibert Series/Dimension Formula ////////

//////////////////////////////////////////////////////

// This allows us to compute the dimension without loading the basis for the entire space. 
// Currently only implemented for real quadratic fields with Discriminant D <41. If you want higher discriminants or cubic fields just ask Ben. 
// Formula in Thomas, Vasquez - Rings of Hilbert Modular Forms pg 147-148 Theorem 3.4, Cubic fields pg 149-151 


// Helper functions
//Dedekind Zeta function implemented in Magma
intrinsic DedekindZeta(K::FldNum) -> LSer
	{produces the DedekindZeta function}
    M := MaximalOrder(K);
    r1,r2 := Signature(K);
    gamma := [0: k in [1..r1+r2]] cat [1: k in [1..r2]];
    disc := Abs(Discriminant(M));
    P<x> := PolynomialRing(Integers());
    cf := func<p,d|&*[1-x^Degree(k[1]): k in Decomposition(M,p)]>;
    h := #ClassGroup(M);
    reg := Regulator(K);
    mu := #TorsionSubgroup(UnitGroup(M));
    return LSeries(1, gamma, disc, cf: Parent:=K, Sign:=1, Poles:=[1], Residues := [-2^(r1+r2)*Pi(RealField())^(r2/2)*reg*h/mu]);
end intrinsic;


//List of Coefficients for A3 and the Arithmetic Genus. From HirzeBruch-Hilbert Modular Surfaces (A3 on pg. 198-200, chi on pg 239). This comes from Prestel Die Elliptischen fixpunte der hilbertshen Modulgruppen.
intrinsic A3andGenus(D::RngIntElt) -> List
	{Takes a Fundamental Discriminant D and returns the genus and value for a3}
 	
 	T := [[2,3,5,6,7,10,11,13,14,15,17,19,21,22,23,26,29,30,31,33,34,35,37,38,39,41], [2,2,2,3,4,4,4,4,4,6,2,4,5,8,8,4,6,10,4,3,4,8,8,8,10,2], [1,1,1,1,1,2,2,1,2,1,1,3,1,3,3,5,2,3,4,1,6,4,2,6,7,2]];
 	d,e := SquareFree(D);
 	
 	i := Index(T[1],d);
 	
 	a3 := T[3][i];
 	Genus := T[2][i];

 	return a3, Genus;
end intrinsic;



// Only implemented for certain quadratic fields. Formula in Thomas, Vasquez - Rings of Hilbert Modular Forms pg 147-148 Theorem 3.4
// Generating function for the dimension of the space of HMFs according to weight k
// Input: M = HMFspace
// Output: G = Hilbert Series (i.e. generating function for dimensions)
intrinsic DimensionGeneratingFunction(M::ModFrmHilD) -> RngSerPowElt
{Returns the dimension of the space of Hilbert Modular Forms of weight k}	
	K := BaseField(M);
	Disc := Discriminant(K);
	assert Disc lt 42;
	P<x> := PowerSeriesRing(Rationals(),200);

	zeta := Evaluate(DedekindZeta(K),-1);
	chi, a3 := A3andGenus(Disc);
	h := ClassNumber(K);


	// Computing sd from formula 2.13 on pg 145.
	if Disc ne 0 mod 3 then
		sD := 1/6;
	elif Disc gt 12 and Disc eq 3 mod 9 then
		sD := 4/15;
	elif Disc eq 12 or Disc eq 6 mod 9 then
		sD := 1/3;
	else 
		print "Error";
	end if;

	
	if Disc eq 5 then 
		B := (1+x^20);
		G := (1+x^20)*(1-x^2)^(-1)*(1-x^6)^(-1)*(1-x^(10))^(-1);
	else
		B0 := 1;
		B1 := Round(chi + h - 3);
		B2 := Round(4*zeta - chi - sD*a3 - h + 3);
		B3 := Round(4*zeta + 2*sD*a3 - 2);

		B := B0 + B1*x^2 + B2*x^4 + B3*x^6 + B2*x^8 + B1*x^10 + B0*x^12;
		G := B*(1-x^2)^(-2)*(1-x^6)^(-1);
	end if;
	return G;
end intrinsic;





// Dimension of the space of HMFs of weight k
// Input: M = HMFspace
// Input: k weight
// Output: dim(M(k))
intrinsic Dimension(M::ModFrmHilD,k::RngIntElt) -> RngIntElt
{Returns the dimension of the space of Hilbert Modular Forms of weight k}	 
	assert k mod 2 eq 0;
	DimGen := DimensionGeneratingFunction(M);
	dim := Round(Coefficient(DimGen, k));
	return dim;
end intrinsic;
