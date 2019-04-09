//Given what space M of Hilbert Modular Forms I should be looking at, and what level
//Given an Eisenstein series E of weight kE and a weight kS of cusp forms that I want to generate
//Given a collection P of primes for Hecke operators I want to look at
//Computes a basis L for S_{kS + kE}
//Compute LE = [f/E :  f is in L]
//For each p in P and each g in LE, compute T_p g.
//Then check if T_p g is in the span of LE
//If it is not, delete g from LE
//Returns LE

//intrinsic Intersection(Spaces::SeqEnum[SeqEnum[ModFrmHilDElt]]) -> SeqEnum[ModFrmHilDElt]
intrinsic Intersection(Spaces::List) -> List
  {Given a list of bases for spaces of forms, find a basis for the intersection of those spaces}
  //Assuming all forms are living in the same spaces, returns parameters associated to them
  M := Parent(Spaces[1][1]);
  N := Level(Spaces[1][1]);
  k := Weight(Spaces[1][1]);
  F := BaseField(M);
  //Outputs the coefficients of the forms in forms
  A := [[Coefficients(f) : f in Space] : Space in Spaces];
  V := VectorSpace(F, #A[1][1]);
  //Coercing A to live in V, and converting my basis to the vector space it spans
  A1 := [sub<V | [V ! f : f in Space] > : Space in A];
  //The intersection of all the spaces in A1
  intersection := &meet A1;
  B := Basis(intersection);
  return [*HMF(M,N,k,Eltseq(b)) : b in B*]; //We want to take the intersection of the spaces in A1
  //Converts W back to Hilbert modular forms
end intrinsic;

//k is the weight of cusp forms we want to generate, and eta and psi are the characters we want associated to them
//ke is the weight of the eisenstein series we want to work with
intrinsic HeckeStability(M::ModFrmHilD, N::RngOrdIdl, k::SeqEnum[RngIntElt]) -> SeqEnum[ModFrmHilDElt], RngIntElt
  { returns a Basis for weight k cusp forms}
  //We need our eisenstein series
  //There is no particular reason to make ke be 1--but it works, probably
  ke := [2,2];
  H := HeckeCharacterGroup(N);
  //If #H = 1 then E doesn't work down below. But that's the case we are in here
  //There's no particular reason to make these characters trivial--but they work.
  //All eisenstein series we are using as candidates
  E := [EisensteinSeries(M, N, eta, H!1, ke) : eta in Elements(H)]; // | eta ne H!1 ];
  assert E ne [];
  assert #k eq #ke;
  ks := [ke[i] + k[i] : i in [1..#Weight(E[1])] ];
  CB := CuspFormBasis(M, N, ks);
  assert CB ne [];
  BaseCandidates := [* [* c/e : c in CB *] : e in E *];
  //Quotients of CB by E, which will span the cusp forms in weight k.
  //Candidates should be the intersection of the BaseCandidate spaces
  Candidates := Intersection(BaseCandidates);
  return Candidates;
  //Ideals that index the Hecke operators that we will be applying to our forms. We want prime ideals of small norm
  //IdealBound is how far out we go in generating our prime ideals. I really have no idea what this should be
  IdealBound := Precision(M) div 20;
  Ideals := PrimesUpTo(IdealBound,BaseField(M));
  print Ideals;
  //What we get when we apply our Hecke operators to the things in BaseCandidates
  HeckeCandidates := [* [* HeckeOperator(Candidates[i], Ideals[j]) : i in [1..#Candidates] *] : j in [1..#Ideals] *];
  //We have a problem because when you apply Hecke operators, you get forms with different numbers of coefficients, and that is bad
  Basis := Intersection(HeckeCandidates);
  return Basis, #Basis;
end intrinsic;
