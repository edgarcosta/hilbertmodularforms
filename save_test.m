M := HMFSpace(QuadraticField(2), 200);
F<w> := BaseField(M);
ZF := Integers(F);
primesArray := [
[ 2, w ],
[ 7, w + 3 ],
[ 7, w + 4 ],
[ 3 ],
[ 17, w + 6 ],
[ 17, w + 11 ],
[ 23, w + 18 ],
[ 23, w + 5 ],
[ 5 ],
[ 31, w + 23 ],
[ 31, w + 8 ],
[ 41, w + 24 ],
[ 41, w + 17 ],
[ 47, w + 7 ],
[ 47, w + 40 ],
[ 71, w + 59 ],
[ 71, w + 12 ],
[ 73, w + 32 ],
[ 73, w + 41 ],
[ 79, w + 9 ],
[ 79, w + 70 ],
[ 89, w + 64 ],
[ 89, w + 25 ],
[ 97, w + 83 ],
[ 97, w + 14 ],
[ 103, w + 38 ],
[ 103, w + 65 ],
[ 113, w + 62 ],
[ 113, w + 51 ],
[ 11 ],
[ 127, w + 16 ],
[ 127, w + 111 ],
[ 137, w + 31 ],
[ 137, w + 106 ],
[ 151, w + 46 ],
[ 151, w + 105 ],
[ 167, w + 13 ],
[ 167, w + 154 ],
[ 13 ],
[ 191, w + 57 ],
[ 191, w + 134 ],
[ 193, w + 141 ],
[ 193, w + 52 ],
[ 199, w + 20 ],
[ 199, w + 179 ]
];
M`Primes := [ideal<ZF | {F!x : x in I}> : I in primesArray];

M`HeckeEigenvalues := AssociativeArray();
NN := ideal<ZF|[ 3, 3*w ]>;
k := \[ 2, 2 ];
key := LevelAndWeightInitialize(NN, k);
EVlist := [* *];
l := [ RationalField() | -2, -2, -2, -1, -2, -2, 4, 4, 6, 2, 2, 2, 2, -12, -12, 12, 12, -6, -6, 10, 10, -10, -10, -2, -2, -6, -6, -6, -6, 22, -2, -2, 18, 18, -18, -18, 8, 8, 10, -8, -8, -6, -6, 10, 10 ];
Append(~EVlist, l);
M`HeckeEigenvalues[key] := EVlist;
NN := ideal<ZF|[ 3, 3*w ]>;
k := \[ 4, 4 ];
key := LevelAndWeightInitialize(NN, k);
EVlist := [* *];
l := [ ext<K|Polynomial(K, [72, -30, -2, 1])> where K is RationalField() |
[ RationalField() | 0, 1, 0 ],
[ RationalField() | 50, -4, -2 ],
[ RationalField() | 50, -4, -2 ],
[ RationalField() | -9, 0, 0 ],
[ RationalField() | -162, 0, 8 ],
[ RationalField() | -162, 0, 8 ],
[ RationalField() | -36, 8, 4 ],
[ RationalField() | -36, 8, 4 ],
[ RationalField() | 86, 32, 0 ],
[ RationalField() | -130, -28, 2 ],
[ RationalField() | -130, -28, 2 ],
[ RationalField() | 594, -64, -24 ],
[ RationalField() | 594, -64, -24 ],
[ RationalField() | -180, 40, 4 ],
[ RationalField() | -180, 40, 4 ],
[ RationalField() | 468, 24, -36 ],
[ RationalField() | 468, 24, -36 ],
[ RationalField() | -886, 32, 48 ],
[ RationalField() | -886, 32, 48 ],
[ RationalField() | 470, -12, -22 ],
[ RationalField() | 470, -12, -22 ],
[ RationalField() | -378, 0, 16 ],
[ RationalField() | -378, 0, 16 ],
[ RationalField() | -706, -64, 16 ],
[ RationalField() | -706, -64, 16 ],
[ RationalField() | 470, 180, -38 ],
[ RationalField() | 470, 180, -38 ],
[ RationalField() | 1242, -64, -16 ],
[ RationalField() | 1242, -64, -16 ],
[ RationalField() | 3686, -256, -128 ],
[ RationalField() | -2110, 284, 94 ],
[ RationalField() | -2110, 284, 94 ],
[ RationalField() | -2142, 448, 88 ],
[ RationalField() | -2142, 448, 88 ],
[ RationalField() | 1058, 92, -18 ],
[ RationalField() | 1058, 92, -18 ],
[ RationalField() | 1080, -112, -120 ],
[ RationalField() | 1080, -112, -120 ],
[ RationalField() | 4250, -192, -64 ],
[ RationalField() | 8712, -656, -312 ],
[ RationalField() | 8712, -656, -312 ],
[ RationalField() | -2758, 416, 48 ],
[ RationalField() | -2758, 416, 48 ],
[ RationalField() | -1786, -172, 202 ],
[ RationalField() | -1786, -172, 202 ]
];
Append(~EVlist, l);
M`HeckeEigenvalues[key] := EVlist;

return M;

