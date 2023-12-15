// TODO this needs to be *much* smaller, 
TOLERANCE := 0.01;
PRECISION := 20;

R<x> := PolynomialRing(RationalField());

// The quadratic number field Q(sqrt(3)). 

F<a> := NumberField(x^2-3);
ZF := Integers(F);
basis := Basis(ZF);
places := InfinitePlaces(F);
M := GradedRingOfHMFs(F, PRECISION);
bbs := NarrowClassGroupReps(M);

gens := TotallyPositiveUnitsGenerators(F);
assert #(gens) eq 1;
eps := gens[1];

nu := 7*ZF.1 - 4*ZF.2;
nu_prime, eps_prime := FunDomainRep(M, bbs[1], nu);
assert eps_prime eq nu;
assert nu_prime eq F!1;

nu := 10*ZF.1;
nu_prime, eps_prime := FunDomainRep(M, bbs[1], nu);
assert eps_prime eq F!1;
assert nu_prime eq nu;

nu := 45*ZF.1 + 23*ZF.2;
nu_prime, eps_prime := FunDomainRep(M, bbs[1], nu);
assert nu_prime eq nu * eps;

// "lower" wall point stay the same
nu := 2*ZF.1 + 2/3*ZF.2;
nu_prime, eps_prime := FunDomainRep(M, bbs[1], nu);
assert nu_prime eq nu;

// "upper" wall point should be reduced to the lower wall
assert F.1 eq ZF.2;
nu := 2*ZF.1 - 2/3*ZF.2;
nu_prime, eps_prime := FunDomainRep(M, bbs[1], nu);
assert not eps_prime eq 1;
assert nu_prime eq nu / eps;


function test_reps_to_norm(F, bbs, nus, norms)
  ZF := Integers(F);
  dd := Different(ZF);

  TrueFunDomainReps := AssociativeArray();
  for bb in bbs do
    TrueFunDomainReps[bb] := AssociativeArray();
    TrueFunDomainReps[bb][0] := [F!0];

    norms_bb := norms[bb];
    nus_bb := nus[bb];

    max_norm := Max(norms_bb);

    for x in [1 .. PRECISION] do
      TrueFunDomainReps[bb][x] := TrueFunDomainReps[bb][x-1];

      // inefficient but it's a test so whatever
      for i in [1 .. #norms_bb] do
        if norms_bb[i] eq x then
          Append(~TrueFunDomainReps[bb][x], nus[bb][i]);
        end if;
      end for;
    end for;
  end for;

  FunDomainEltReps := FunDomainRepsUpToNorm(M);

  assert Keys(FunDomainEltReps) eq Keys(TrueFunDomainReps);
  for bb in Keys(FunDomainEltReps) do
    assert Keys(FunDomainEltReps[bb]) eq Keys(TrueFunDomainReps[bb]);
    for k in Keys(FunDomainEltReps[bb]) do
      assert SequenceToSet(FunDomainEltReps[bb][k]) eq SequenceToSet(TrueFunDomainReps[bb][k]);
    end for;
  end for;

  return "";
end function;

norms := AssociativeArray();
nus := AssociativeArray();

norms[bbs[1]] := [0, 2, 3, 8, 11, 11, 12, 18];
norms[bbs[2]] := [1, 4, 6, 9, 13, 13, 16];

nus[bbs[1]] := [0, 1/6*a + 1/2, 1/2, 1/3*a + 1, 1/6*a + 1, -1/6*a + 1, 1, 1/2*a + 3/2];
nus[bbs[2]] := [1/6*a + 1/2, 1/3*a + 1, 1, 1/2*a + 3/2, -1/6*a + 3/2, 1/6*a + 3/2, 2/3*a + 2];

test_reps_to_norm(F, bbs, nus, norms);

// testing MPairs

prec := 20;
M := GradedRingOfHMFs(F, prec);
assert BaseField(M) eq F;
bbs := M`NarrowClassGroupReps;

shadows := Shadows(M);
mpairs_new := ComputeMPairs(M);

// hardcoding the old output of MPairs

mpairs := AssociativeArray();
for bb in bbs do
  mpairs[bb] := AssociativeArray();
end for;

reps_1 := [0, 1, 1/6*a + 1/2, 1/6*a + 1, 1/2, 1/2*a + 3/2, 1/3*a + 1, -1/6*a + 1];
mpairs_1_list := [\
  [[<0, 1>, <0, 1>]],
  [[<1/2, 1>, <1/2, 1>], [<1/2 + 1/6*a, a + 2>, <1/2 + 1/6*a, 1>], [<1/2 + 1/6*a, 1>, <1/2 + 1/6*a, a + 2>], [<1, 1>, <0, 1>], [<0, 1>, <1, 1>]],  
  [[<1/2 + 1/6*a, 1>, <0, 1>], [<0, 1>, <1/2 + 1/6*a, 1>]],
  [[<1/2, 1>, <1/2 + 1/6*a, 1>], [<1/2 + 1/6*a, 1>, <1/2, 1>], [<1/1 + 1/6*a, 1>, <0, 1>], [<0, 1>, <1/1 + 1/6*a, 1>]],
  [[<1/2, 1>, <0, 1>], [<0, 1>, <1/2, 1>]],
  [[<1/2, -a + 2>, <1/2, 1>], [<1/2, 1>, <1/2, -a + 2>], [<1/1 + 1/3*a, 1>, <1/2 + 1/6*a, 1>], [<1/2 + 1/6*a, 1>, <1/1 + 1/3*a, 1>], [<3/2 + 1/2*a, 1>, <0, 1>], [<0, 1>, <3/2 + 1/2*a, 1>]],
  [[<1/2 + 1/6*a, 1>, <1/2 + 1/6*a, 1>], [<1/1 + 1/3*a, 1>, <0, 1>], [<0, 1>, <1/1 + 1/3*a, 1>]],
  [[<1/2 + 1/6*a, a + 2>, <1/2, 1>], [<1/2, 1>, <1/2 + 1/6*a, a + 2>], [<1/1 - 1/6*a, 1>, <0, 1>], [<0, 1>, <1/1 - 1/6*a, 1>]]
];

for i in [1 .. #reps_1] do
  mpairs[bbs[1]][reps_1[i]] := mpairs_1_list[i];
end for;

reps_2 := [0, 1, 1/6*a + 1/2, 1/6*a + 3/2, 1/2*a + 3/2, 1/3*a + 1, -1/6*a + 3/2, 2/3*a + 2];
mpairs_2_list := [\
  [[<0, 1>, <0, 1>]],
  [[<1/2 + 1/6*a, a + 2>, <1/2 + 1/6*a, 1>], [<1/2 + 1/6*a, 1>, <1/2 + 1/6*a, a + 2>], [<1, 1>, <0, 1>], [<0, 1>, <1, 1>]],
  [[<1/2 + 1/6*a, 1>, <0, 1>], [<0, 1>, <1/2 + 1/6*a, 1>]],
  [[<1/1 + 1/3*a, 1>, <1/2 + 1/6*a, a + 2>], [<1/2 + 1/6*a, a + 2>, <1/1 + 1/3*a, 1>], [<1, 1>, <1/2 + 1/6*a, 1>], [<1/2 + 1/6*a, 1>, <1, 1>], [<3/2 + 1/6*a, 1>, <0, 1>], [<0, 1>, <3/2 + 1/6*a, 1>]],
  [[<1/1 + 1/3*a, 1>, <1/2 + 1/6*a, 1>], [<1/2 + 1/6*a, 1>, <1/1 + 1/3*a, 1>], [<3/2 + 1/2*a, 1>, <0, 1>], [<0, 1>, <3/2 + 1/2*a, 1>]],
  [[<1/2 + 1/6*a, 1>, <1/2 + 1/6*a, 1>], [<1/1 + 1/3*a, 1>, <0, 1>], [<0, 1>, <1/1 + 1/3*a, 1>]],
  [[<1, 1>, <1/2 + 1/6*a, a + 2>], [<1/2 + 1/6*a, a + 2>, <1, 1>], [<1/1 + 1/3*a, a + 2>, <1/2 + 1/6*a, 1>], [<1/2 + 1/6*a, 1>, <1/1 + 1/3*a, a + 2>], [<3/2 - 1/6*a, 1>, <0, 1>], [<0, 1>, <3/2 - 1/6*a, 1>]],
  [[<1/1 + 1/3*a, 1>, <1/1 + 1/3*a, 1>], [<1/2 + 1/6*a, -a + 2>, <1/2 + 1/6*a, a + 2>], [<1/2 + 1/6*a, a + 2>, <1/2 + 1/6*a, -a + 2>], [<3/2 + 1/2*a, 1>, <1/2 + 1/6*a, 1>], [<1/2 + 1/6*a, 1>, <3/2 + 1/2*a, 1>], [<2/1 + 2/3*a, 1>, <0, 1>], [<0, 1>, <2/1 + 2/3*a, 1>]]
];

for i in [1 .. #reps_2] do
  mpairs[bbs[2]][reps_2[i]] := mpairs_2_list[i];
end for;

for bb in bbs do
  reps := FunDomainRepsUpToNorm(M)[bb][M`Precision];
  for nu in reps do
    coerced_mpairs_set := {}; // MPairs with all eps and nu coerced into F
    for pair in mpairs[bb][nu] do
      nu_1, eps_1 := Explode(pair[1]);
      nu_2, eps_2 := Explode(pair[2]);
      Include(~coerced_mpairs_set, [<F!nu_1, F!eps_1^-1>, <F!nu_2, F!eps_2^-1>]);
    end for;
    mpairs_new_set := SequenceToSet(mpairs_new[bb][nu]);
    if #(mpairs_new_set sdiff coerced_mpairs_set) ne 0 then
      printf "Error at class rep %o and representative %o:\n", IdealOneLine(bb), nu;
      print "mpairs_new is:\n";
      print mpairs_new_set;
      print "coerced mpairs is:\n";
      print coerced_mpairs_set;
    end if;
    assert coerced_mpairs_set eq mpairs_new_set;
  end for;
end for;

// The cubic number field Q(zeta_7)+. 
TOLERANCE := 0.01;
PRECISION := 20;

R<x> := PolynomialRing(RationalField());

F<a> := NumberField(x^3-x^2-2*x+1);
ZF := Integers(F);
basis := Basis(ZF);
places := InfinitePlaces(F);
M := GradedRingOfHMFs(F, PRECISION);
bb := NarrowClassGroupReps(M)[1];

gens := TotallyPositiveUnitsGenerators(F);
assert #(gens) eq 2;
eps_1 := gens[1];
eps_2 := gens[2];

nu := 1*basis[1] + 2*basis[2] + 3*basis[3];
nu_prime, eps_prime := FunDomainRep(M, bb, nu);
assert nu_prime eq nu/eps_2;
//rep_embed := [Evaluate(rep, places[i]) : i in [1, 2, 3]];
//assert Abs(rep_embed[1] - 12.542876546957239435622233943040328966125486709642126932300421480979986755594803638458377953396537060638970481992397465334397641293479711072585112648823806882758838455) lt TOLERANCE;
//assert Abs(rep_embed[2] - 4.4178947925446465132165748450107518219373171256199260573969790264217653029157415164006286696983915185734010485386542777656639632403882414360609929478152080199995595143) lt TOLERANCE;
//assert Abs(rep_embed[3] - 2.0392286604981140511611912119489192119371961647379470103025994925982479414894548451409933769050714207876284694689482568999383954661320474913538944033609850972416020305) lt TOLERANCE;


