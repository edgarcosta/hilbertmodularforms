// Williams, J. Algebra 559 (2020), 679-711, Proposition 12.
// Source: https://arxiv.org/src/1809.08623v2/anc/Qsqrt29.txt (35 relations).
// Source SHA256: 89375f6fec1260ca018481ef7b35a41cc6b3cfcee468ec5c3c0de8f15916b7cf.
// LitData(Rsrc, Rtgt) returns the even ideal, forward and inverse images, citation,
// full Williams ideal, and the seven even generators in that full presentation.
LitData := function(Rsrc,Rtgt)
  assert VariableWeights(Rsrc) eq [2,2,4,6,6,6,8];
  assert VariableWeights(Rtgt) eq VariableWeights(Rsrc);
  W<E2,phi2,phi3,psi3,phi4,phi5,phi6,psi6,phi7,phi8,phi9> :=
    PolynomialRing(Rationals(), [2,2,3,3,4,5,6,6,7,8,9]);
  rels := [ W |
    phi2^3+phi3*psi3-phi2*phi4,
    E2*phi2^2-phi3^2+4*phi2*phi4,
    psi3*phi4-phi2*phi5,
    phi2^2*phi3+E2*phi2*psi3-phi3*phi4+4*phi2*phi5,
    phi2^2*phi4-phi4^2+phi3*phi5,
    phi2*phi3*psi3+E2*psi3^2-phi3*phi5+4*psi3*phi5,
    E2^3*phi2+20*E2*phi3^2-136*E2*phi3*psi3+384*E2*psi3^2+512*phi2*psi3^2+128*E2*phi2*phi4-1248*phi3*phi5
    +1536*psi3*phi5-phi2*psi6,
    phi3*phi6-phi2*phi7,
    E2^3*psi3+20*E2^2*phi2*psi3+136*phi3^2*psi3-384*phi3*psi3^2+512*psi3^3+72*E2*phi2*phi5+320*phi2^2*phi5
    -864*phi4*phi5-psi3*psi6,
    E2^3*phi3+20*E2^2*phi2*phi3-136*E2^2*phi2*psi3-384*phi3^2*psi3+512*phi3*psi3^2+208*E2*phi3*phi4
    -1408*E2*phi2*phi5-3456*phi4*phi5-phi3*psi6,
    psi3*phi7-phi2*phi8,
    phi2^2*phi6-phi4*phi6+phi2*phi8,
    E2*phi2*phi6+4*phi4*phi6-phi3*phi7,
    E2^3*phi4+20*E2^2*phi2*phi4+208*E2*phi4^2-136*E2*phi3*phi5-1248*phi2*phi3*phi5-864*E2*psi3*phi5
    +512*phi2*psi3*phi5-3456*phi5^2-phi4*psi6,
    phi3*phi8-phi2*phi9,
    phi2^2*phi7-phi4*phi7+phi2*phi9,
    phi2*psi3*phi6-phi5*phi6+psi3*phi8,
    E2*psi3*phi6+4*phi5*phi6-phi2*phi9,
    phi2^2*phi8-phi4*phi8+psi3*phi9,
    E2*phi2*phi8+4*phi4*phi8-phi3*phi9,
    phi5*phi7-phi4*phi8,
    E2^3*phi6+512*psi3^2*phi6-512*phi2*phi4*phi6-phi6*psi6+20*E2*phi3*phi7+128*phi2*phi3*phi7-1216*phi4*phi8
    -8*phi3*phi9+384*psi3*phi9,
    phi3^2*psi3^2+26*phi3*psi3^3-27*psi3^4+E2^2*phi4^2-36*E2*phi2*phi4^2-176*phi4^3-6*E2*phi2*phi3*phi5
    -4*E2^2*psi3*phi5-54*E2*phi2*psi3*phi5-56*phi2^2*psi3*phi5-16*phi3*phi4*phi5-96*phi2*phi5^2-phi6^2,
    E2*psi3*phi8+4*phi5*phi8+phi2^2*phi9-phi4*phi9,
    E2^3*phi7+20*E2^2*phi2*phi7+208*E2*phi4*phi7-psi6*phi7+512*phi2*psi3*phi8-136*E2*phi2*phi9-384*phi2^2*phi9
    -864*phi4*phi9,
    E2^2*psi3^3-26*E2*phi2*psi3^3-27*phi2^2*psi3^3-E2^2*phi2*phi3*phi4+36*E2*phi3*phi4^2+176*phi2*phi3*phi4^2
    +22*E2*phi3^2*phi5-83*E2*phi3*psi3*phi5+336*E2*psi3^2*phi5+435*phi2*psi3^2*phi5+336*E2*phi2*phi4*phi5
    +768*phi4^2*phi5-1100*phi3*phi5^2+1328*psi3*phi5^2-phi2*phi5*psi6+phi6*phi7,
    E2^3*phi8+512*psi3^2*phi8-512*phi2*phi4*phi8-psi6*phi8+20*E2*phi3*phi9+128*phi2*phi3*phi9-8*E2*psi3*phi9
    -384*phi2*psi3*phi9-864*phi5*phi9,
    E2*phi6^2+4*phi2*phi6^2-phi7^2+4*phi6*phi8,
    E2^2*phi2*phi4^2-36*E2*phi4^3-176*phi2*phi4^3+E2^2*phi2*phi3*phi5-20*E2^2*phi2*psi3*phi5
    -135*phi3^2*psi3*phi5+410*phi3*psi3^2*phi5-539*psi3^3*phi5-6*E2*phi3*phi4*phi5-192*phi2*phi3*phi4*phi5
    -318*E2*phi2*phi5^2-376*phi2^2*phi5^2-phi2*phi6^2+psi3*phi5*psi6-phi6*phi8,
    phi7*phi8-phi6*phi9,
    E2^2*phi3*phi4^2-36*E2*phi2*phi3*phi4^2-176*phi3*phi4^3-E2^2*psi3^2*phi5+26*E2*phi2*psi3^2*phi5
    +27*phi2^2*psi3^2*phi5-58*E2^2*phi2*phi4*phi5-568*E2*phi4^2*phi5-768*phi2*phi4^2*phi5+83*E2*phi3*phi5^2
    +332*phi2*phi3*phi5^2-4*E2*psi3*phi5^2-435*phi2*psi3*phi5^2+phi4*phi5*psi6-phi2*phi6*phi7-phi6*phi9,
    E2*phi6*phi8+4*phi2*phi6*phi8+4*phi8^2-phi7*phi9,
    E2*phi3*psi3^2*phi5+26*E2*psi3^3*phi5+27*phi2*psi3^3*phi5+E2^2*phi3*phi4*phi5-36*E2*phi2*phi3*phi4*phi5
    -176*phi3*phi4^2*phi5-58*E2^2*phi2*phi5^2-82*phi3^2*phi5^2+332*phi3*psi3*phi5^2-435*psi3^2*phi5^2
    -486*E2*phi4*phi5^2-440*phi2*phi4*phi5^2+phi5^2*psi6-phi2*phi6*phi8-phi8^2,
    864*E2^2*phi2*psi3^2*phi5+607392*phi3*psi3^3*phi5-606528*psi3^4*phi5-22464*E2^2*phi4^2*phi5
    -1264896*E2*phi2*phi4^2*phi5-4561920*phi4^3*phi5-1728*E2^2*phi3*phi5^2-508032*E2*phi2*phi3*phi5^2
    -509760*E2^2*psi3*phi5^2-1232064*E2*phi2*psi3*phi5^2-1234656*phi2^2*psi3*phi5^2+55296*phi3*phi4*phi5^2
    -1679616*E2*phi5^3-2712096*phi2*phi5^3-22464*phi5*phi6^2+E2^3*phi5*psi6+20*E2^2*phi2*phi5*psi6
    +136*phi3^2*phi5*psi6-384*phi3*psi3*phi5*psi6+512*psi3^2*phi5*psi6+72*E2*phi4*phi5*psi6
    +320*phi2*phi4*phi5*psi6-phi5*psi6^2-864*phi2*phi6*phi9-864*phi8*phi9,
    2985984*E2^2*phi2*phi3*phi4*phi5-107495424*E2*phi3*phi4^2*phi5-525533184*phi2*phi3*phi4^2*phi5
    -1679616*E2^4*phi5^2+383698944*E2*phi3^2*phi5^2-3514503168*E2*phi3*psi3*phi5^2
    +10970505216*E2*psi3^2*phi5^2+15751065600*phi2*psi3^2*phi5^2-282175488*E2^2*phi4*phi5^2
    +2609750016*E2*phi2*phi4*phi5^2-4395368448*phi4^2*phi5^2-37205360640*phi3*phi5^3+45712429056*psi3*phi5^3
    +E2^6*psi6+293632*E2^2*phi2*psi3^2*psi6-90778624*phi3*psi3^3*psi6+99248640*psi3^4*psi6
    -3057920*E2^2*phi4^2*psi6+111819776*E2*phi2*phi4^2*psi6+546349056*phi4^3*psi6+13696*E2^2*phi3*phi5*psi6
    +19134464*E2*phi2*phi3*phi5*psi6+12418816*E2^2*psi3*phi5*psi6+165814784*E2*phi2*psi3*phi5*psi6
    +182665216*phi2^2*psi3*phi5*psi6+49268736*phi3*phi4*phi5*psi6+1430784*E2*phi5^2*psi6
    +230790144*phi2*phi5^2*psi6+3104256*phi6^2*psi6-2*E2^3*psi6^2-400*phi3^2*psi6^2-2560*phi3*psi3*psi6^2
    -30656*psi3^2*psi6^2+1280*phi2*phi4*psi6^2+psi6^3-2985984*phi4*phi6*phi8+746496*E2*phi8^2-746496*phi9^2
  ];
  WilliamsIdeal := ideal<W | rels>;
  evenGenerators := [W | E2,phi2,phi4,phi6,psi6,psi3^2,phi8];

  x := [Rsrc.i : i in [1..Rank(Rsrc)]];
  // The example checks the kernel and generation of the even subring.
  equations := [
    x[1]^3*x[2] + 20*x[1]^2*x[2]^2 + 136*x[1]*x[2]^3 + 384*x[2]^4 + 72*x[1]*x[2]*x[3] + 480*x[2]^2*x[3]
    - 864*x[3]^2 - x[2]*x[5] + 512*x[2]*x[6],
    x[1]^4*x[2] - 264*x[1]^2*x[2]^3 - 2336*x[1]*x[2]^4 - 7168*x[2]^5 + 72*x[1]^2*x[2]*x[3]
    - 960*x[1]*x[2]^2*x[3] - 10624*x[2]^3*x[3] - 864*x[1]*x[3]^2 + 17792*x[2]*x[3]^2 - x[1]*x[2]*x[5]
    + 20*x[2]^2*x[5] - 10240*x[2]^2*x[6] - 2048*x[3]*x[6],
    x[2]^2*x[4] - x[3]*x[4] + x[2]*x[7],
    x[1]^5*x[2] - 30144*x[1]*x[2]^5 - 306304*x[2]^6 + 3488*x[1]^2*x[2]^2*x[3] + 134016*x[1]*x[2]^3*x[3]
    + 1479680*x[2]^4*x[3] - 864*x[1]^2*x[3]^2 - 169920*x[1]*x[2]*x[3]^2 - 1753728*x[2]^2*x[3]^2
    + 62208*x[3]^3 - 2944*x[4]^2 - x[1]^2*x[2]*x[5] + 20*x[1]*x[2]^2*x[5] - 264*x[2]^3*x[5]
    + 72*x[2]*x[3]*x[5] - 1071872*x[2]^3*x[6] - 702720*x[1]*x[3]*x[6] + 104192*x[2]*x[3]*x[6]
    + 2944*x[5]*x[6] - 1586816*x[6]^2,
    x[1]^3*x[4] + 20*x[1]^2*x[2]*x[4] + 208*x[1]*x[3]*x[4] - x[4]*x[5] + 512*x[4]*x[6] - 136*x[1]*x[2]*x[7]
    - 384*x[2]^2*x[7] - 864*x[3]*x[7],
    20*x[1]*x[2]^5 + 136*x[2]^6 - 40*x[1]*x[2]^3*x[3] - 488*x[2]^4*x[3] + 20*x[1]*x[2]*x[3]^2
    + 568*x[2]^2*x[3]^2 - 216*x[3]^3 + x[1]^3*x[6] + 384*x[2]^3*x[6] + 208*x[1]*x[3]*x[6]
    - 64*x[2]*x[3]*x[6] - x[5]*x[6] + 512*x[6]^2,
    x[1]^6*x[2] + 282816*x[1]*x[2]^6 + 2829312*x[2]^7 - 894464*x[1]*x[2]^4*x[3] + 26434944*x[2]^5*x[3]
    - 864*x[1]^3*x[3]^2 + 17891776*x[1]*x[2]^2*x[3]^2 - 72526592*x[2]^3*x[3]^2 + 9611136*x[1]*x[3]^3
    + 154978688*x[2]*x[3]^3 + 10816*x[1]*x[4]^2 + 634752*x[2]*x[4]^2 + 40*x[1]^2*x[2]^2*x[5]
    - 128*x[1]*x[2]^3*x[5] - 5504*x[2]^4*x[5] + 144*x[1]*x[2]*x[3]*x[5] + 15744*x[2]^2*x[3]*x[5]
    - 20512*x[3]^2*x[5] - x[2]*x[5]^2 + 29580608*x[2]^4*x[6] + 19823232*x[2]^2*x[3]*x[6]
    - 82446272*x[3]^2*x[6] + 8832*x[1]*x[5]*x[6] - 29632*x[2]*x[5]*x[6] - 4760448*x[1]*x[6]^2
    + 30450048*x[2]*x[6]^2 + 78592*x[4]*x[7],
    x[1]^4*x[4] - 192*x[1]^2*x[3]*x[4] - 4160*x[1]*x[2]*x[3]*x[4] - x[1]*x[4]*x[5] + 20*x[2]*x[4]*x[5]
    - 12288*x[2]*x[4]*x[6] + 264*x[1]^2*x[2]*x[7] + 2336*x[1]*x[2]^2*x[7] + 7168*x[2]^3*x[7]
    - 864*x[1]*x[3]*x[7] + 17792*x[2]*x[3]*x[7] - 2048*x[6]*x[7],
    x[1]^7*x[2] + 112299776/3*x[2]^8 + 70495232/3*x[1]*x[2]^5*x[3] - 25168107008/3*x[2]^6*x[3]
    - 13407889408/3*x[1]*x[2]^3*x[3]^2 + 55747835008/3*x[2]^4*x[3]^2 - 6718010368/3*x[1]*x[2]*x[3]^3
    - 37719793920*x[2]^2*x[3]^3 + 50855040*x[3]^4 - 8305664/3*x[1]*x[2]*x[4]^2 - 467697664/3*x[3]*x[4]^2
    - 928*x[1]^2*x[2]^3*x[5] - 5056/3*x[1]*x[2]^4*x[5] - 44992*x[2]^5*x[5] - 16/9*x[1]^3*x[3]*x[5]
    + 976/9*x[1]^2*x[2]*x[3]*x[5] - 53056/9*x[1]*x[2]^2*x[3]*x[5] + 71936/3*x[2]^3*x[3]*x[5]
    - 4288/3*x[1]*x[3]^2*x[5] + 2835904*x[2]*x[3]^2*x[5] - x[1]*x[2]*x[5]^2 + 40*x[2]^2*x[5]^2
    + 16/9*x[3]*x[5]^2 - 3799254528*x[2]^5*x[6] - 6254226944*x[2]^3*x[3]*x[6]
    + 2818519936/3*x[1]*x[3]^2*x[6] + 15661485568*x[2]*x[3]^2*x[6] - 1280/3*x[1]^2*x[5]*x[6]
    + 273152*x[2]^2*x[5]*x[6] + 48790528/9*x[3]*x[5]*x[6] + 689920/3*x[1]^2*x[6]^2
    - 3917033984*x[2]^2*x[6]^2 - 2920918528*x[3]*x[6]^2 - 512/3*x[1]*x[4]*x[7] + 139513344*x[2]*x[4]*x[7]
    + 6144*x[7]^2
  ];
  I := ideal<Rsrc | equations>;

  y := [Rtgt.i : i in [1..Rank(Rtgt)]];
  PhiImages := [Rtgt |
    -y[1],
    -y[2],
    y[3],
    -y[2]^3 - y[1]*y[3] + 17*y[2]*y[3] + 2*y[4] - 4*y[5] + 11*y[6],
    -y[1]^3 - 20*y[1]^2*y[2] - 136*y[1]*y[2]^2 - 384*y[2]^3 - 72*y[1]*y[3] - 480*y[2]*y[3] + 864*y[5] - 512*y[6],
    -y[6],
    137/4*y[2]^4 - y[1]*y[2]*y[3] - 109/2*y[2]^2*y[3] + 2*y[2]*y[4] - y[1]*y[5] + 193/4*y[2]*y[5]
    - 141/4*y[1]*y[6] + 11*y[2]*y[6] + 2*y[7]
  ];
  inverse := GradedInverseImages(Rtgt,PhiImages);
  PsiImages := [Rsrc | Evaluate(f,[Rsrc.i : i in [1..Rank(Rsrc)]]) : f in inverse];
  citation := "Williams, J. Algebra 559 (2020), 679-711, Proposition 12";
  return I,PhiImages,PsiImages,citation,WilliamsIdeal,evenGenerators;
end function;
return LitData;
