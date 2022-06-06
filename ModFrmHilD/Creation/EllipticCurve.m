//////////////////////////////////////////////////////////////
//                                                          //
//              Elliptic curves                             //
//                                                          //
//////////////////////////////////////////////////////////////


// As of right now, I don't know the best way to access elliptic curves over number fields.
// To produce a basis for the Newspace, I'm calling EllipticCurveSearch to find enought elliptic curves. This is a major slowdown!!!!
// Todo: The elliptic curves are already stored on the LMFDB. We need to find a way to cache these so that the can just be pulled to produce the Newspace.


//Todo Check ap at primes of bad reduction
//Todo: This function parallels a_n from newforms, Maybe make a_p -> a_n function for both?
intrinsic EllipticCurveToHMF(M::ModFrmHilDGRng, E::CrvEll) -> ModFrmHilElt
  {Produces the Hilbert Modular form associated to the Elliptic curve E}
  // Coerce into the Bsaefield of M
  require IsIsomorphic(BaseField(E),BaseField(M)) : "BaseField Not Isomorphic";
  _, map := IsIsomorphic(BaseField(E),BaseField(M));
  E := BaseChange(E,map);

  F := BaseField(E);
  N := Conductor(E);
  ZF := Integers(M);
  k := [2 : i in [1..Degree(F)]];
  Mk := HMFSpace(M,N,k);
  ev := AssociativeArray();
  L := LSeries(E);
  for p in PrimeIdeals(M) do
    ev[p] := -Integers()!Coefficient(EulerFactor(L, p),1);
  end for;
  return Eigenform(Mk, ev);
end intrinsic;


// The effort for these functions can ushually be set to 10-20;
intrinsic EllipticNewForms(Mk::ModFrmHilD: Effort:=10) -> SeqEnum
  {Produces all elliptic newforms of conductor N}
  if not assigned Mk`EllipticBasis then
    M := Parent(Mk);
    F := BaseField(Mk);
    N := Level(Mk);
    L := EllipticCurveSearch(N, Effort);
    k := [2 : i in [1..Degree(F)]];
    require Weight(Mk) eq k : "Mk needs to be weight parallel 2";
    NewBasis := [];

    // Repetitive but I think the fastest test for isogeny is literally computing the HMF
    for elt in L do
      f := EllipticCurveToHMF(M,elt);
      if f notin NewBasis then Append(~NewBasis,f); end if;
    end for;

    // Testing to see if dimensions are correct
    MF := HilbertCuspForms(Mk);
    S := NewSubspace(MF);
    require Dimension(S) eq #NewBasis: "Not all elliptic curves found. Set Effort higher!";
    Mk`EllipticBasis := NewBasis;
  end if;
  return Mk`EllipticBasis;
end intrinsic;






intrinsic EllipticCuspFormBasis(Mk::ModFrmHilD, Effort::RngIntElt) -> SeqEnum[ModFrmHilDElt]
  {returns a basis for cuspspace of M of weight k}
  N := Level(Mk);
  k := Weight(Mk);
  require Set(k) eq {2} and k[1] lt 3: "Only works for parallel weight [2,2] or [2,2,2]";
  Cuspbasis := [];
  require IsTrivial(Character(Mk)): "We only support CuspFormBasis  for trivial character, as we rely on the magma functionality";
  for dd in Divisors(N) do
    Mkdd := HMFSpace(Parent(Mk), dd, k);
    // We are taking the Q orbits
    NewSpace_dd := &cat[GaloisOrbitDescent(f) : f in EllipticNewForms(Mkdd,Effort)];
    OldSpace_dd := &cat[Inclusion(elt, Mk) : elt in NewSpace_dd ];
    Cuspbasis cat:= OldSpace_dd;
  end for;
  return Cuspbasis;
end intrinsic;












