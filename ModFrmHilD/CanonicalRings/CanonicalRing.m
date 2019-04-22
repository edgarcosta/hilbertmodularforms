/////////////////////////////////////////////////////

//////////// Canonical Embeddings Code  /////////////

/////////////////////////////////////////////////////







/////////////////  Helper Functions  //////////////////



///////////   Building the Ring  //////////////////

// Builds weighted monomial ring R.
// Input: Gens = An assoctive array indexed by weight of generators
// Output: R = Weighted polynomial ring
intrinsic ConstructRing(Gens::Assoc)-> Any
	{Returns the full weighted polynomial ring}
	
	GenWeights := [];
	for i in Keys(Gens) do
		for j in [1..#Gens[i]] do
			Append(~GenWeights,i);
		end for;
	end for;

	R := PolynomialRing(Rationals(),GenWeights);

	return R;
end intrinsic;


// Builds The ideal I.
// Input: R = weighted polynomial ring 
// Input: Relations = An associative array of relations index by weight
// Output: I
intrinsic ConstructIdeal(R::RngMPol, Relations::Assoc)-> Any
	{Returns the ideal I determined by the relations}

    PolynomialList := [];
	for i in Keys(Relations) do
		PolynomialList cat:= RelationstoPolynomials(R, Relations[i],i);
	end for;
		
	I := ideal<R | PolynomialList>;
	
	return I;
end intrinsic;





///////////////   Conversion  /////////////////////

// This is a subfunction to the ConstructIdeal function
// Input: R = a graded polynomial ring with weighted generators
// Input: Relationlist = A list of relations in weight k. The relations are coefficients in terms of basis from MonomialsOfWeightedDegree(R,k).
// Input: k = the weight.
// Output: polynomials in the graded ring representing the relations
intrinsic RelationstoPolynomials(R::RngMPol, Relationlist::SeqEnum, k::RngIntElt) -> Any
	{Contructs polynomials from the relations}
	
	Monomials := MonomialsOfWeightedDegree(R,k);

	PolynomialList := [];
	for rel in Relationlist do 
		RelationPolynomial := 0;
		for j := 1 to #rel do 
			RelationPolynomial +:= Monomials[j]*rel[j];
		end for;
		Append(~PolynomialList,RelationPolynomial);
	end for;
	return PolynomialList;
end intrinsic;

// Converts the abstract monomials back into HMFS.
// Input: MonomialGens = the list of abstract polynomial generators
// Input: GenList = the list of HMFS cooresponding to the variables of the polynomials
// Output: The evaluated monomials, so a list of modular forms.
intrinsic EvaluateMonomials(Gens::Assoc, MonomialGens::SeqEnum[RngMPolElt]) -> Any 
	{For a given set of HMF this produces all multiples with weight k}
	
	GenList := [];
	for i in Keys(Gens) do
		GenList cat:= Gens[i];
	end for;
		 
	EvalMonomials := [];
	for j := 1 to #MonomialGens do 
		Exp := Exponents(MonomialGens[j]);
		CurrMonomial := 1;
		for k := 1 to #GenList do 
			if Exp[k] ne 0 then
				CurrMonomial *:= GenList[k]^Exp[k];
			end if;
		end for;
		EvalMonomials[j] := CurrMonomial;
	end for;

	return EvalMonomials;

end intrinsic;


////////// Computing new relations in weight k ///////////////////

// Returns monomials generating the weight k space inside R/I
// Input: MonomialsinR = MonomialsOfWeightedDegree(R,k) for the ring R
// Input: Quo = R/I The polynomial ring with weighted generators
// Input: k weight for monomials
// Output: MonomialGens = List of monomials generating the weight k space inside R/I
intrinsic MonomialGenerators(R::RngMPol, Relations::Assoc, k::RngIntElt) -> Any
	{Returns Generators for the weight k monomials in R/I}
	
	monoms := MonomialsOfWeightedDegree(R,k);
	Ideal := ConstructIdeal(R,Relations); 
	leadmonoms := [LeadingMonomial(f) : f in GroebnerBasis(Ideal)];
	MonomialGens := [f : f in monoms | &and[not IsDivisibleBy(f,m) : m in leadmonoms]];

	return MonomialGens;
end intrinsic;

// Given monomials and a number of relations amongst them, computes the rest of a basis of HilbertModularForms(M,k)
// Input: M = Space of HMFs
// Input: k = weight
// Input: EvaluatedMonomials = list of HMF obtained by evaluating the monomials in terms of our generators
// Output: a list of modular forms, one corresponding to each new generator
intrinsic FindNewGenerators(M::ModFrmHilD, N::RngOrdIdl, k::RngIntElt, EvaluatedMonomials::SeqEnum, Basisweightk::SeqEnum)-> Any 
	{Constructs generators for the complement of the subspace generated by multiplication from lower weights}

	// V is basis for modular forms of current weight and W is the subspace of forms coming from multiplication.	
	V := VectorSpaceWithBasis(Matrix([Coefficients(i) : i in Basisweightk]));
	W := sub< V | [Coefficients(i) : i in EvaluatedMonomials] >;

	ExtendMultBasis := ExtendBasis(W,V);

	NewGeneratorsVec := [ExtendMultBasis[i] : i in [Dimension(W)+1..Dimension(V)]];	
	NewGens := [ HMF(M, N, [k,k], Eltseq(vec)) : vec in NewGeneratorsVec ];
	
	return NewGens;

end intrinsic;




////////////////////////// Main functions /////////////////////////////

//////////////////////////////////////////////////////////////////////

/*

There are two versions of this algorithm currently. 

- ConstructGeneratorsAndRelations is slow and check for generators and relations in each level (opens Basis(M) function). 

- Relations takes as input the associtive arrays found in ConstructGeneratorsAndRelations
  It then checks for further relations (NOT GENERATORS!) in higher weights. It doesn't open up the Basis(M) so it runs extremely quickly. 

  As a check, this version prints the dimension of the space from the Hilbert Series vs the dimension we have found to see if 
  a)  you missed any generators or
  b)  your precision is set too low leading to false relations.

I recommend using ConstructGeneratorsAndRelations at High precision (200-1000) and low weight 2-10 to try to find the 
generators. Once you think you have found all generators plug the outputs of this into Relations to check for further relations.

*/

// Iteratively looks for generators and relations up to a bound.
// Input: M = HMFspace
// Input: LowestWeight = first weight with HMFS
// Input: MaxWeight = highest weight to check for relations in
// Output: Associative array of generators in each weight, Associative array of Relations in each weight and Quotient Ring
intrinsic ConstructGeneratorsAndRelations(M::ModFrmHilD, N::RngOrdIdl, LowestWeight::RngIntElt, MaxWeight::RngIntElt) -> Any
	{Finds all Generators and Relations}
	
	Gens := AssociativeArray();
	Relations := AssociativeArray();

	Gens[LowestWeight] := [i : i in Basis(M,N,[LowestWeight,LowestWeight])];


	for i := (LowestWeight div 2 + 1) to (MaxWeight div 2) do
		
		k := 2*i;

		R := ConstructRing(Gens);
		MonomialsinR := MonomialsOfWeightedDegree(R,k);
		MonomialsGens := MonomialGenerators(R,Relations,k);
		EvaluatedMonomials := EvaluateMonomials(Gens, MonomialsGens);	
		
		// I first compute the relations in R/I. 
		RelationsinQuotient := LinearDependence(EvaluatedMonomials);

		// This lifts the relations in R/I to relations in R in terms of MonomialsOfWeightedDegree(R,k). 
		// Mainly for storage.
		RelationsinR := [];
		for rel in RelationsinQuotient do
			relR := [];
			for j in MonomialsinR do
				I := Index(MonomialsGens,j);
				if I ne 0 then
					Append(~relR,rel[I]);
				else 
					Append(~relR,0);
				end if;
			end for;
			Append(~RelationsinR,relR);
		end for;

		if #RelationsinR ne 0 then 
			Relations[k] := RelationsinR;		
		end if;

		Basisweightk := Basis(M,N,[k,k]);

		NewGens := [];
		if #MonomialsGens - #RelationsinR ne #Basisweightk then 
			NewGens := FindNewGenerators(M, N, k, EvaluatedMonomials, Basisweightk);
			Gens[k] := NewGens;
		end if;	

		print "Level:", k,  "     Generators", #NewGens, " Relations", #RelationsinR;
	
	end for;

	return Gens,Relations;
end intrinsic;

/*
intrinsic ConstructGeneratorsAndRelationsSymmetric(M::ModFrmHilD, N::RngOrdIdl, LowestWeight::RngIntElt, MaxWeight::RngIntElt) -> Any
	{Finds all Generators and Relations}
	
	Gens := AssociativeArray();
	Relations := AssociativeArray();

	Gens[LowestWeight] := [i : i in GaloisInvariantBasis(M,N,[LowestWeight,LowestWeight])];


	for i := (LowestWeight div 2 + 1) to (MaxWeight div 2) do
		
		k := 2*i;

		R := ConstructRing(Gens);
		MonomialsinR := MonomialsOfWeightedDegree(R,k);
		MonomialsGens := MonomialGenerators(R,Relations,k);
		EvaluatedMonomials := EvaluateMonomials(Gens, MonomialsGens);	
		
		// I first compute the relations in R/I. 
		RelationsinQuotient := LinearDependence(EvaluatedMonomials);

		// This lifts the relations in R/I to relations in R in terms of MonomialsOfWeightedDegree(R,k). 
		// Mainly for storage.
		RelationsinR := [];
		for rel in RelationsinQuotient do
			relR := [];
			for j in MonomialsinR do
				I := Index(MonomialsGens,j);
				if I ne 0 then
					Append(~relR,rel[I]);
				else 
					Append(~relR,0);
				end if;
			end for;
			Append(~RelationsinR,relR);
		end for;

		if #RelationsinR ne 0 then 
			Relations[k] := RelationsinR;		
		end if;

		Basisweightk := GaloisInvariantBasis(M,N,[k,k]);

		NewGens := [];
		if #MonomialsGens - #RelationsinR ne #Basisweightk then 
			NewGens := FindNewGenerators(M, N, k, EvaluatedMonomials, Basisweightk);
			Gens[k] := NewGens;
		end if;	

		print "Level:", k,  "     Generators", #NewGens, " Relations", #RelationsinR;
	
	end for;

	return Gens,Relations;
end intrinsic;

*/

// Important! In order to run this version you must have already computed the generators for the ring using either ConstructGeneratorsAndRelations or ConstructGeneratorsAndRelationsV1. 
// This version DOES NOT look for any new generators, it only checks for relations amoung the generators you have found.

// Input: M = HMFspace
// Input: Gens = An array of generators computed from ConstructGeneratorsAndRelations or ConstructGeneratorsAndRelationsV1
// Input: Relations = An array of relations computed from ConstructGeneratorsAndRelations or ConstructGeneratorsAndRelationsV1
// Input: MaxWeight = highest weight to check for relations in
// Output: Associative array of generators in each weight, associative array of relations in each weight and quotient ring

intrinsic Relations(M::ModFrmHilD, Gens::Assoc, Relations::Assoc, MaxWeight::RngIntElt) -> Any
	{Finds all Generators and Relations}

	LowestWeight := Max([i : i in Keys(Gens)] cat [i : i in Keys(Relations)]);

	P<x> := PowerSeriesRing(Rationals(),100);
	G := DimensionGeneratingFunction(M);

	for i := (LowestWeight div 2 + 1) to (MaxWeight div 2) do
		
		k := 2*i;

		R := ConstructRing(Gens);
		MonomialsinR := MonomialsOfWeightedDegree(R,k);
		MonomialsGens := MonomialGenerators(R,Relations,k);
		EvaluatedMonomials := EvaluateMonomials(Gens, MonomialsGens);	
		
		// I first compute the relations in R/I. 
		RelationsinQuotient := LinearDependence(EvaluatedMonomials);
		// This lifts the relations in R/I to relations in R in terms of MonomialsOfWeightedDegree(R,k). 
		// Mainly for storage.
		RelationsinR := [];
		for rel in RelationsinQuotient do
			relR := [];
			for j in MonomialsinR do
				I := Index(MonomialsGens,j);
				if I ne 0 then
					Append(~relR,rel[I]);
				else 
					Append(~relR,0);
				end if;
			end for;
			Append(~RelationsinR,relR);
		end for;

		if #RelationsinR ne 0 then 
			Relations[k] := RelationsinR;		
		end if;
		

		print "Level:", k,  "    Dimension:", #MonomialsGens - #RelationsinR, Dimension(M,k), "      Relations", #RelationsinR;;

	end for;

	

	print "Relations";
	for i in Keys(Relations) do
		print i, #Relations[i];
	end for;

	return Gens,Relations;
end intrinsic;







///////////////////////// Aux Functions /////////////////


intrinsic QuadSpace(D::RngIntElt, prec::RngIntElt)-> Any
	{Easy way to produces a quadratic space with Driscriminant D and precision prec}

    K := QuadraticField(D);
    OK := Integers(K);
    M := HMFSpace(K, prec);
    return M,1*OK;

end intrinsic;




intrinsic MakeScheme(Gens::Assoc, Relations::Assoc)-> Any
	{Returns the Scheme}

    R := ConstructRing(Gens);

    PolynomialList := [];
	for i in Keys(Relations) do
		PolynomialList cat:= RelationstoPolynomials(R,Relations[i],i);
	end for;

	P := ProjectiveSpace(R);
	S := Scheme(P, PolynomialList);
	return S;
end intrinsic;




intrinsic MakeHilbertSeries(Gens::Assoc, Relations::Assoc, n::RngIntElt)-> Any
	{Returns Hilbert series with precision n}

    R := ConstructRing(Gens);

    PolynomialList := [];
	for i in Keys(Relations) do
		PolynomialList cat:= RelationstoPolynomials(R,Relations[i],i);
	end for;

	I := ideal<R | PolynomialList>;

	N := HilbertNumerator(I);
	D := HilbertDenominator(I);	
	H := HilbertSeries(I, n);

	//return N,D
	return H;
end intrinsic;

