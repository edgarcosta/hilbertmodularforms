
/*
====================
Tests for Q(5);
====================
*/

load "config.m";
F := QuadraticField(5);
ZF := Integers(F);
M := GradedRingOfHMFs(F,20);

/*
=====================
1*ZF, [4,4]
=====================
*/

M4 := HMFSpace(M,1*ZF,[4,4]);
TR := STraceForm(M4);
assert TR eq HMFZero(M4);

/*
=====================
1*ZF, [6,6]
=====================
*/

M6 := HMFSpace(M,1*ZF,[6,6]);
TR := STraceForm(M6);
B6 := Basis(M6);
assert TR eq B6[2];


/*
=====================
1*ZF, [8,8]
=====================
*/


M8 := HMFSpace(M,1*ZF,[8,8]);
TR := STraceForm(M8);
B8 := Basis(M8);
assert TR eq B8[2];


/*
=====================
1*ZF, [10,10]
=====================
*/


M10 := HMFSpace(M,1*ZF,[10,10]);
TR := STraceForm(M10);
B10 := Basis(M10);
LinDep := LinearDependence([TR] cat B10);
assert #LinDep ne 0;


////// Level Structure /////////

/*
=====================
2*ZF, [4,4]
=====================
*/

M4 := HMFSpace(M,2*ZF,[4,4]);
NN := Level(M4);
B4 := Basis(M4);

TR := STraceForm(M4);
LinDep := LinearDependence([TR] cat B4);
assert #LinDep ne 0;
// CTR := CoprimeTraceForm(M4);
// CoprimeLinearDependence([CTR] cat B4,NN);


/*
=====================
3*ZF, [4,4]
=====================
*/

M4 := HMFSpace(M,3*ZF,[4,4]);
NN := Level(M4);
B4 := Basis(M4);

TR := STraceForm(M4);
LinDep := LinearDependence([TR] cat B4);
assert #LinDep ne 0;
// CTR := CoprimeTraceForm(M4);
// CoprimeLinearDependence([CTR] cat B4,NN);


/*
======================
3*ZF, [6,6]
======================
*/

M6 := HMFSpace(M,3*ZF,[6,6]);
NN := Level(M6);
B6 := Basis(M6);

TR := STraceForm(M6);
LinDep := LinearDependence([TR] cat B6);
assert #LinDep ne 0;
// CTR := CoprimeTraceForm(M6);
// CoprimeLinearDependence([CTR] cat B6,NN);


/*
======================
5*ZF, [4,4]
======================
*/

M4 := HMFSpace(M,5*ZF,[4,4]);
NN := Level(M4);
B4 := Basis(M4);

TR := STraceForm(M4);
LinDep := LinearDependence([TR] cat B4);
assert #LinDep ne 0;
// CTR := CoprimeTraceForm(M4);
// CoprimeLinearDependence([CTR] cat B4,NN);


/*
=====================
5*ZF, [6,6]
=====================
*/

M6 := HMFSpace(M,5*ZF,[6,6]);
NN := Level(M6);
B6 := Basis(M6);

TR := STraceForm(M6);
LinDep := LinearDependence([TR] cat B6);
assert #LinDep ne 0;
// CTR := CoprimeTraceForm(M6);
// CoprimeLinearDependence([CTR] cat B6,NN);


/*
===================================================
                 Tests for Q(2)
====================================================
*/



load "config.m";
F := QuadraticField(2);
ZF := Integers(F);
M := GradedRingOfHMFs(F,20);


/*
=====================
1*ZF, [4,4]
=====================
*/

M4 := HMFSpace(M,1*ZF,[4,4]);
TR := STraceForm(M4);
B4 := Basis(M4);
assert TR eq B4[2];


/*
=====================
1*ZF, [6,6]
=====================
*/

M6 := HMFSpace(M,1*ZF,[6,6]);
TR := STraceForm(M6);
B6 := Basis(M6);
assert TR eq B6[2];



/*
=====================
1*ZF, [8,8]
=====================
*/

M8 := HMFSpace(M,1*ZF,[8,8]);
TR := STraceForm(M8);
B8 := Basis(M8);
assert #LinearDependence([TR] cat B8) ne 0;


/*
=====================
1*ZF, [10,10]
=====================
*/

M10 := HMFSpace(M,1*ZF,[10,10]);
TR := STraceForm(M10);
B10 := Basis(M10);
assert TR eq B10[2];


/*
====================
Profiling
====================

SetProfile(true);
G := ProfileGraph();
ProfilePrintByTotalTime(G);
*/













