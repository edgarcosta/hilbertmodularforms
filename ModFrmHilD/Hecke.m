///////////////////////////////////////////////////
//                                               //
//                Hecke Operators                //
//                                               //
///////////////////////////////////////////////////

///////////// ModFrmHilDElt: Hecke Operators ////////////////
intrinsic HeckeOperator(f::ModFrmHilDElt, mm::RngOrdIdl : MaximalPrecision := false) -> ModFrmHilDElt
  {Returns T(mm)(f) for the character chi modulo the level of f}

  Mk := Parent(f);
  M := Parent(Mk);
  F := BaseField(M);
  Cl, mp := NarrowClassGroup(F);
  ZF := Integers(F);
  k := Weight(f);
  k0 := Max(k);
  chi := Character(Mk);
  K := CoefficientRing(f);

  coeffsTmmf := AssociativeArray();
  prec := AssociativeArray();
  for bb in NarrowClassGroupReps(M) do
    coeffsTmmf[bb] := AssociativeArray();
    prec[bb] := 0;
  end for;

  for bb in NarrowClassGroupReps(M) do
    bbp := NarrowClassGroupRepsToIdealDual(M)[bb];
    bbpinv := bbp^(-1);

    for nu in ShintaniRepsUpToTrace(M, bb, Precision(M)) do //they come sorted
      nn := nu*bbpinv;  // already call mm the ideal for the Hecke operator
      c := 0;
      t := Integers()!Trace(nu);


      // loop over divisors
      // Formula 2.23 in Shimura - The Special Values
      // of the zeta functions associated with Hilbert Modular Forms
      // If a coefficient in the sum is not defined we will set prec[bb] := Trace(nu) - 1;
      for aa in Divisors(ZF!!(nn + mm)) do
        if nn eq 0*ZF then
          //takes care if the coefficients for the zero ideal are different
          c +:= StrongMultiply(K, [* chi(aa), Norm(aa)^(k0 - 1), Coefficients(f)[NarrowClassRepresentative(M, bb*mm/aa^2)][ZF!0] *]);
        else
          b, cf := IsCoefficientDefined(f, ZF!!(aa^(-2) * nn * mm));
          if not b then
            // stop looping through divisors if coefficient for at least one divisor
            // is not defined (if trace (aa^(-2) * (nn*mm)) is greater than precision)
            prec[bb] := t-1;
            break; // breaks loop on aa
          else
            c +:= StrongMultiply(K, [* chi(aa),  Norm(aa)^(k0 - 1), cf *]);
          end if;
        end if;
      end for;
      if prec[bb] ne 0 then // the loop on aa didn't finish
        break; // breaks loop on nu
      else
        coeffsTmmf[bb][nu] := IdlCoeffToEltCoeff(c, nu, k, CoefficientRing(Components(f)[bb]));
      end if;
    end for;
  end for;

  // Attempting to increase precision using a basis
  // This is not very efficient, as it does not remember the underlying vector space, but it works.
  if (assigned Mk`Basis) or MaximalPrecision then
      B := Basis(Mk);
      // These have different numbers of columns
      mats := [* *];
      vec := [];
      for bb in Keys(coeffsTmmf) do
	  nus := Keys(coeffsTmmf[bb]);
	  mat := Matrix([[Coefficients(f)[bb][nu] : nu in nus] : f in B]);
	  Append(~mats, mat);
	  vec cat:= [coeffsTmmf[bb][nu] : nu in nus];
      end for;
      // This does not work with a list
      // mat := HorizontalJoin(mats);
      mat := mats[1];
      for comp_idx in [2..#mats] do
	  mat := HorizontalJoin(mat, mats[comp_idx]);
      end for;
      // If the matrix is invertible, there will be a unique solutions, and we can use it.
      if Rank(mat) eq #B then
	  vec_sol := Solution(mat, Vector(vec));
	  g := &+[vec_sol[i]*B[i] : i in [1..#B]];
	  return g;
      end if;
  end if;
  
  g := HMF(Mk, coeffsTmmf : CoeffsByIdeals:=false, prec:=prec);
  return g;
end intrinsic;


///////////// Eigenbasis computation ////////////////

// This code computes an eigenbasis for a Hecke-stable space 
// of meromorphic ModFrmHilDElt objects by examining the action
// on the Fourier coefficients. 
//
// For most applications, the ModFrmHil/ or Trace.m code should be used. 

intrinsic Eigenbasis(M::ModFrmHilD, basis::SeqEnum[ModFrmHilDElt] : P := 60) -> SeqEnum[ModFrmHilDElt]
  {
    inputs:
      M: A space of forms on which the Hecke algebra acts by
           commuting self-adjoint operators.
      basis: A sequence of linearly independent ModFrmHilDElts
             whose span is preserved by all the Hecke operators.
      P: The largest norm of a prime ideal we check to establish a simultaneous eigenbasis
    returns:
      A sequence of HMFs which are an eigenbasis for the Hecke operators of primes
      up to P. The forms are normalized where possible.
  }
  
  MGRng := Parent(M);
  F := MGRng`BaseField;
  ZF := Integers(F);
  dd := Different(ZF);
  hecke_matrices := [];

  for pp in PrimesUpTo(P, F) do
    Append(~hecke_matrices, HeckeMatrix(basis, pp));
  end for;

  // B stores a matrix such that B * M * B^-1 is
  // diagonal for every Hecke matrix M. 
  // If e_i denotes the ith standard basis vector
  // and v_i denotes the ith eigenvector in the 
  // given basis, then this means that B^-1 e_i = v_i. 
  // Therefore, the ith column of B^-1 is v_i.
  _, B := Diagonalization(hecke_matrices);
  Binv := B^-1;

  eigs := [];

  // the columns of P should be the coefficients
  // of linear combinations of basis vectors giving
  // rise to eigenvectors
  // TODO is there really no way to get the columns of an AlgMatElt? 
  for v in Rows(Transpose(Binv)) do
    Append(~eigs, &+[v[i] * basis[i] : i in [1 .. #basis]]);
  end for;

  frob_traces := AssociativeArray();
  for eig in eigs do
    frob_traces[eig] := AssociativeArray(); 
    bb_1 := NarrowClassRepresentative(MGRng, dd);
    a_1 := Coefficients(eig)[bb_1][MGRng`IdealShitaniReps[bb_1][ideal<ZF|1>]];

    for nn in IdealsUpTo(P, F) do
      bb := NarrowClassRepresentative(MGRng, nn^-1 * dd);
      frob_traces[eig][nn] := Coefficients(eig)[bb][MGRng`IdealShitaniReps[bb][nn]] / a_1;
    end for;
  end for;
  return eigs, frob_traces;
end intrinsic;

intrinsic HeckeMatrix(basis::SeqEnum[ModFrmHilDElt], nn::RngOrdIdl) -> Mtrx
  {
    inputs:
      basis: A sequence of linearly independent ModFrmHilDElts
             whose span is preserved by all the Hecke operators.
      nn: An integral ideal indexing the Hecke operator
    returns:
      A matrix over corresponding to the action of the Hecke operator on
      this space. 
  }

  assert #LinearDependence(basis) eq 0;
  rows := [];

  for f in basis do
    g := HeckeOperator(f, nn);
    lindep := LinearDependence(basis cat [g]);
    assert #lindep eq 1;
    lindep := lindep[1];
    // We will transpose at the end. 
    // For now, each row stores the
    // coefficients of the linear combination 
    // of basis vectors which give rise to g
    Append(~rows, [-1 * lindep[i] / lindep[#basis + 1] : i in [1 .. #basis]]);
  end for;

  return Transpose(Matrix(rows));
end intrinsic;

intrinsic HeckeMatrix(Mk::ModFrmHilD, nn::RngOrdIdl) -> Mtrx
  {
    inputs:
      Mk: A space of HMFs
      nn: An integral ideal indexing the Hecke operator
    returns:
      A matrix over corresponding to the action of the Hecke operator on
      this space. 
  }
  return HeckeMatrix(Basis(Mk));
end intrinsic;
