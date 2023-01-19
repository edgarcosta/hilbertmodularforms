
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


// // "D",2,3,4,5,6,2,3,4,6,12 // Header row.

// Read entries from Prestel's table
function ReadPretzelTable()
    io := Open("PrestelTable.csv", "r");
    data := [* *];

    // Read the header row and ignore.
    line := Gets(io);
    
    while true do
        line := Gets(io);
        if IsEof(line) then break; end if;
        args := eval("[* " * line * " *]");

        // Replace D with the discriminant.
        F := QuadraticField(args[1]);
        args[1] := Discriminant(F);
        
        // Update.
        Append(~data, args);
    end while;
    return data;
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
