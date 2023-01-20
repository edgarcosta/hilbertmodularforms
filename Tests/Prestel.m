
// Encoding of Prestel's table (which does contain some errors).

// Entries in the table consist of
//    Discriminant,
//    <2> singularities (SL case),
//    <3> singularities (SL case),
//    <4> singularities (SL case),
//    <5> singularities (SL case),
//    <6> singularities (SL case),
//
//    <2> singularities (GL case),
//    <3> singularities (GL case),
//    <4> singularities (GL case),
//    <6> singularities (GL case),
//   <12> singularities (GL case),

// Read entries from Prestel's table
function ReadPretzelTable()

// // "D",2,3,4,5,6,2,3,4,6,12 // Header row.
table := [
[2,2,2,2,0,0,0,0,0,0,0],
[3,3,2,0,0,1,3,1,1,0,1],
[5,2,2,0,2,0,0,0,0,0,0],
[6,6,3,0,0,0,12,1,2,1,0],
[7,4,4,0,0,0,5,2,2,0,0],
[10,6,4,0,0,0,0,0,0,0,0],
[11,10,4,0,0,0,5,2,4,0,0],
[13,2,4,0,0,0,0,0,0,0,0],
[14,12,4,0,0,0,8,2,4,0,0],
[15,8,6,0,0,0,0,0,0,0,0],
[17,4,2,0,0,0,0,0,0,0,0],
[19,10,4,0,0,0,9,2,4,0,0],
[21,4,5,0,0,0,6,2,0,1,0],
[22,6,8,0,0,0,12,4,2,0,0],
[23,12,8,0,0,0,7,4,6,0,0],
[26,18,4,0,0,0,0,0,0,0,0],
[29,6,6,0,0,0,0,0,0,0,0],
[30,12,10,0,0,0,0,0,0,0,0],
[31,12,4,0,0,0,11,2,6,0,0],
[33,4,3,0,0,0,18,1,0,1,0],
[34,12,4,0,0,0,0,0,0,0,0],
[35,20,8,0,0,0,0,0,0,0,0],
[37,2,8,0,0,0,0,0,0,0,0],
[38,18,8,0,0,0,16,4,6,0,0],
[39,16,10,0,0,0,0,0,0,0,0],
[41,8,2,0,0,0,0,0,0,0,0],
[42,12,12,0,0,0,0,0,0,0,0],
[43,10,12,0,0,0,13,6,4,0,0],
[46,12,8,0,0,0,16,4,4,0,0],
[47,20,8,0,0,0,13,4,10,0,0],
[51,20,12,0,0,0,0,0,0,0,0],
[53,6,10,0,0,0,0,0,0,0,0],
[55,16,8,0,0,0,0,0,0,0,0],
[57,4,5,0,0,0,18,2,0,1,0],
[58,6,12,0,0,0,0,0,0,0,0],
[59,30,4,0,0,0,15,2,12,0,0],
[61,6,8,0,0,0,0,0,0,0,0],
[62,24,12,0,0,0,20,6,8,0,0],
[65,8,4,0,0,0,0,0,0,0,0],
[66,24,10,0,0,0,0,0,0,0,0],
[67,10,12,0,0,0,17,6,4,0,0],
[69,8,9,0,0,0,12,3,0,3,0],
[70,12,8,0,0,0,0,0,0,0,0],
[71,28,8,0,0,0,11,4,14,0,0],
[73,4,4,0,0,0,0,0,0,0,0],
[74,30,12,0,0,0,0,0,0,0,0],
[77,8,12,0,0,0,8,6,0,0,0],
[78,12,18,0,0,0,0,0,0,0,0],
[79,20,12,0,0,0,13,6,10,0,0],
[82,12,12,0,0,0,0,0,0,0,0],
[83,30,12,0,0,0,19,6,12,0,0],
[85,4,12,0,0,0,0,0,0,0,0],
[86,30,8,0,0,0,20,4,10,0,0],
[87,24,18,0,0,0,0,0,0,0,0],
[89,12,2,0,0,0,0,0,0,0,0],
[91,20,8,0,0,0,0,0,0,0,0],
[93,4,15,0,0,0,14,6,0,3,0],
[94,24,8,0,0,0,28,4,8,0,0],
[95,32,16,0,0,0,0,0,0,0,0],
[97,4,4,0,0,0,0,0,0,0,0]
];
return table; //[<QuadraticField(elt[1])> cat <x : i->x in elt | i gt 1> : elt in table];
end function;

function StandardizePretzelTable(table)
    // If the GL+ entries are completely empty, then Prestel means one should
    // copy the row.

    // NOTE: Also need to be careful about the difference between GL+ and Gamma_e0
    for j in [1..#table] do
        row := table[j];
        if &and [row[i] eq 0 : i in [7..11]] then
            for i in [7..11] do
                table[j][i] := row[i-5];
            end for;
        end if;
    end for;

    // Return.
    return table;
end function;

function Find(table, disc)
    for entry in table do
	if entry[1] eq disc then
	    return entry;
	end if;
    end for;
    error "Entry not found in table.", disc;
end function;

//////////////////////////
// Script begin

prestelTable := StandardizePretzelTable(ReadPretzelTable());

// Check data entry.
assert #{#entry : entry in prestelTable} eq 1;

// Tests?
print "\n\nStarting SL tests...";
for row in prestelTable do

    D := row[1];
    F := QuadraticField(D);

    // Need to look over all components?
    G := CongruenceSubgroup("SL", F);

    counts := CountEllipticPoints(G);
    lst := Sort([ <rho, &+[x : x in counts[rho]]> : rho in Keys(counts)],
                func<x,y | x[1] - y[1]>);

    print "------";
    print "Disc: ", D;
    print "Narrow_Class_Number: ", NarrowClassNumber(F);
    print "Unit_index: ", IndexOfTotallyPositiveUnitsModSquares(F);
    print [* x[2] : x in lst *];
    print row[2..6];
    
end for;


print "\n\nStarting GL+ tests...";
for row in prestelTable do

    D := row[1];
    F := QuadraticField(D);

    // Need to look over all components?
    G := CongruenceSubgroup("GL+", F);

    counts := CountEllipticPoints(G);
    lst := Sort([ <rho, &+[x : x in counts[rho]]> : rho in Keys(counts)],
                func<x,y | x[1] - y[1]>);

    // When the class number is 2 and the narrow class number is not 2, then
    // there is a discrepency between GL+ and Gamma_e0. (???).
    print "------";
    print "Disc: ", D;
    print "Class_number: ", ClassNumber(F);
    print "Narrow_Class_Number: ", NarrowClassNumber(F);
    print "Unit_index: ", IndexOfTotallyPositiveUnitsModSquares(F);
    print [* x[2] : x in lst *];
    print row[7..11];
    
end for;


/* if IndexOfTotallyPositiveUnitsModSquares(F) eq 1 then */
/*     D := Discriminant(F); */
/*     D := Valuation(D, 2) gt 0 select D div 4 else D; */
/*     print D, args; */
/* end if; */
