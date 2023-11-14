// tests the function IsCompatibleWeight in ModFrmHilD/Space.m

F := QuadraticField(5);
// the signs of the units are
//
//      inf_1  inf_2
// U.1  -1     -1
// U.2   1     -1
ZF := Integers(F);
N := 1*ZF;
H := HeckeCharacterGroup(N, [1,2]);

// the trivial character is compatible with any 
// weight whose components are all even

assert IsCompatibleWeight(H.0, [2,2]);
assert not IsCompatibleWeight(H.0, [2,3]);
assert IsCompatibleWeight(H.0, [2,4]);

// nontrivial level
N := 23*ZF;
H := HeckeCharacterGroup(N, [1,2]); // H = Z/22

assert IsCompatibleWeight(H.0, [2,2]);
assert not IsCompatibleWeight(H.0, [2,3]);

// the character H.1 sends 
//       (23) | psi_0
// U.1    1   |   1                  
// U.2   -1   |  -1

assert IsCompatibleWeight(H.1, [5,7]);
assert not IsCompatibleWeight(H.1, [9,4]);

// multiple finite bad primes
N := 21*ZF;
H := HeckeCharacterGroup(N, [1,2]); // H = Z/2 x Z/24
                                    
// the character H.2 sends 
//       (3)   (7) | psi_0
// U.1    1     1  |   1                  
// U.2   -1     1  |  -1
//
assert IsCompatibleWeight(H.2, [3,3]);
assert not IsCompatibleWeight(H.2, [2,2]);

// order dependent,
// components have values outside 1 and -1
N := 11*ZF;
H := HeckeCharacterGroup(N, [1,2]); // H = Z/10 x Z/2
// the character H.1 sends 
//        pp          pp'        | psi_0
// U.1     1          -1         |  -1                  
// U.2     z    -(z^3+z^2+z+1)   |   1
// where z = zeta_5.

assert IsCompatibleWeight(H.1, [3,2]);
assert not IsCompatibleWeight(H.1, [2,3]);

