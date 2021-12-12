dimensions := AssociativeArray();
/*
Generated with
foo.m:
d := StringToInteger(d);
F := QuadraticField(d);
ZF := Integers(F);
print Sprintf("dimensions[%o] := %o;\n", d, [[Dimension(HilbertCuspForms(F, n*ZF, [k,k])) : n in [1..5]]: k in [4..16 by 2]]);
exit;

and 
parallel --eta magma -b d:={1} foo.m ::: 5 8 12 13 17 20 21 24 28 29 32 33 37 40 41 44 45 48 52 53 56 57 60 61 65 68 69 72 73 76 77 80 84 85 88 89 92 93 96 97
*/
dimensions[68] := [
[ 2, 14, 16, 54, 40 ],
[ 5, 38, 43, 150, 110 ],
[ 9, 74, 83, 294, 214 ],
[ 14, 122, 136, 486, 352 ],
[ 21, 182, 203, 726, 526 ],
[ 29, 254, 283, 1014, 734 ],
[ 38, 338, 376, 1350, 976 ]
];

dimensions[17] := [
[ 2, 14, 16, 54, 40 ],
[ 5, 38, 43, 150, 110 ],
[ 9, 74, 83, 294, 214 ],
[ 14, 122, 136, 486, 352 ],
[ 21, 182, 203, 726, 526 ],
[ 29, 254, 283, 1014, 734 ],
[ 38, 338, 376, 1350, 976 ]
];

dimensions[32] := [
[ 1, 3, 5, 9, 11 ],
[ 2, 7, 12, 25, 29 ],
[ 3, 13, 22, 49, 55 ],
[ 4, 21, 35, 81, 89 ],
[ 6, 31, 52, 121, 133 ],
[ 8, 43, 72, 169, 185 ],
[ 10, 57, 95, 225, 245 ]
];

dimensions[72] := [
[ 1, 3, 5, 9, 11 ],
[ 2, 7, 12, 25, 29 ],
[ 3, 13, 22, 49, 55 ],
[ 4, 21, 35, 81, 89 ],
[ 6, 31, 52, 121, 133 ],
[ 8, 43, 72, 169, 185 ],
[ 10, 57, 95, 225, 245 ]
];

dimensions[8] := [
[ 1, 3, 5, 9, 11 ],
[ 2, 7, 12, 25, 29 ],
[ 3, 13, 22, 49, 55 ],
[ 4, 21, 35, 81, 89 ],
[ 6, 31, 52, 121, 133 ],
[ 8, 43, 72, 169, 185 ],
[ 10, 57, 95, 225, 245 ]
];

dimensions[52] := [
[ 1, 4, 12, 15, 20 ],
[ 3, 12, 34, 43, 56 ],
[ 5, 22, 66, 83, 108 ],
[ 7, 34, 108, 135, 176 ],
[ 11, 52, 162, 203, 264 ],
[ 15, 72, 226, 283, 368 ],
[ 19, 94, 300, 375, 488 ]
];

dimensions[13] := [
[ 1, 4, 12, 15, 20 ],
[ 3, 12, 34, 43, 56 ],
[ 5, 22, 66, 83, 108 ],
[ 7, 34, 108, 135, 176 ],
[ 11, 52, 162, 203, 264 ],
[ 15, 72, 226, 283, 368 ],
[ 19, 94, 300, 375, 488 ]
];

dimensions[5] := [
[ 0, 1, 2, 3, 5 ],
[ 1, 3, 5, 9, 13 ],
[ 1, 5, 9, 17, 25 ],
[ 2, 7, 14, 27, 41 ],
[ 3, 11, 21, 41, 61 ],
[ 3, 15, 29, 57, 85 ],
[ 4, 19, 38, 75, 113 ]
];

dimensions[80] := [
[ 0, 1, 2, 3, 5 ],
[ 1, 3, 5, 9, 13 ],
[ 1, 5, 9, 17, 25 ],
[ 2, 7, 14, 27, 41 ],
[ 3, 11, 21, 41, 61 ],
[ 3, 15, 29, 57, 85 ],
[ 4, 19, 38, 75, 113 ]
];

dimensions[20] := [
[ 0, 1, 2, 3, 5 ],
[ 1, 3, 5, 9, 13 ],
[ 1, 5, 9, 17, 25 ],
[ 2, 7, 14, 27, 41 ],
[ 3, 11, 21, 41, 61 ],
[ 3, 15, 29, 57, 85 ],
[ 4, 19, 38, 75, 113 ]
];

dimensions[45] := [
[ 0, 1, 2, 3, 5 ],
[ 1, 3, 5, 9, 13 ],
[ 1, 5, 9, 17, 25 ],
[ 2, 7, 14, 27, 41 ],
[ 3, 11, 21, 41, 61 ],
[ 3, 15, 29, 57, 85 ],
[ 4, 19, 38, 75, 113 ]
];

dimensions[41] := [
[ 7, 55, 62, 216, 220 ],
[ 18, 151, 169, 600, 604 ],
[ 34, 295, 329, 1176, 1180 ],
[ 55, 487, 542, 1944, 1948 ],
[ 82, 727, 809, 2904, 2908 ],
[ 114, 1015, 1129, 4056, 4060 ],
[ 151, 1351, 1502, 5400, 5404 ]
];

dimensions[37] := [
[ 4, 19, 60, 75, 98 ],
[ 12, 55, 168, 211, 274 ],
[ 22, 105, 328, 411, 534 ],
[ 34, 169, 540, 675, 878 ],
[ 52, 255, 808, 1011, 1314 ],
[ 72, 355, 1128, 1411, 1834 ],
[ 94, 469, 1500, 1875, 2438 ]
];

dimensions[21] := [
[ 3, 10, 18, 33, 56 ],
[ 6, 24, 52, 87, 152 ],
[ 10, 44, 100, 167, 296 ],
[ 15, 70, 162, 273, 488 ],
[ 22, 104, 244, 407, 728 ],
[ 30, 144, 340, 567, 1016 ],
[ 39, 190, 450, 753, 1352 ]
];

dimensions[84] := [
[ 3, 10, 18, 33, 56 ],
[ 6, 24, 52, 87, 152 ],
[ 10, 44, 100, 167, 296 ],
[ 15, 70, 162, 273, 488 ],
[ 22, 104, 244, 407, 728 ],
[ 30, 144, 340, 567, 1016 ],
[ 39, 190, 450, 753, 1352 ]
];

dimensions[12] := [
[ 2, 6, 10, 19, 22 ],
[ 4, 14, 27, 51, 58 ],
[ 6, 26, 51, 99, 110 ],
[ 8, 42, 82, 163, 178 ],
[ 12, 62, 123, 243, 266 ],
[ 16, 86, 171, 339, 370 ],
[ 20, 114, 226, 451, 490 ]
];

dimensions[48] := [
[ 2, 6, 10, 19, 22 ],
[ 4, 14, 27, 51, 58 ],
[ 6, 26, 51, 99, 110 ],
[ 8, 42, 82, 163, 178 ],
[ 12, 62, 123, 243, 266 ],
[ 16, 86, 171, 339, 370 ],
[ 20, 114, 226, 451, 490 ]
];

dimensions[61] := [
[ 9, 42, 132, 165, 300 ],
[ 25, 118, 368, 461, 828 ],
[ 47, 228, 720, 901, 1620 ],
[ 75, 372, 1188, 1485, 2676 ],
[ 113, 558, 1776, 2221, 3996 ],
[ 157, 778, 2480, 3101, 5580 ],
[ 207, 1032, 3300, 4125, 7428 ]
];

dimensions[24] := [
[ 5, 17, 30, 56, 86 ],
[ 9, 41, 79, 152, 230 ],
[ 15, 77, 151, 296, 446 ],
[ 23, 125, 246, 488, 734 ],
[ 33, 185, 367, 728, 1094 ],
[ 45, 257, 511, 1016, 1526 ],
[ 59, 341, 678, 1352, 2030 ]
];

dimensions[53] := [
[ 6, 27, 54, 105, 138 ],
[ 17, 77, 149, 295, 384 ],
[ 31, 147, 289, 575, 748 ],
[ 48, 237, 474, 945, 1230 ],
[ 73, 357, 709, 1415, 1840 ],
[ 101, 497, 989, 1975, 2568 ],
[ 132, 657, 1314, 2625, 3414 ]
];

dimensions[40] := [
[ 12, 66, 168, 252, 318 ],
[ 32, 178, 468, 700, 878 ],
[ 60, 346, 916, 1372, 1718 ],
[ 96, 570, 1512, 2268, 2838 ],
[ 144, 850, 2260, 3388, 4238 ],
[ 200, 1186, 3156, 4732, 5918 ],
[ 264, 1578, 4200, 6300, 7878 ]
];

dimensions[29] := [
[ 3, 12, 24, 45, 84 ],
[ 8, 34, 65, 127, 228 ],
[ 14, 64, 125, 247, 444 ],
[ 21, 102, 204, 405, 732 ],
[ 32, 154, 305, 607, 1092 ],
[ 44, 214, 425, 847, 1524 ],
[ 57, 282, 564, 1125, 2028 ]
];

dimensions[96] := [
[ 5, 17, 30, 56, 86 ],
[ 9, 41, 79, 152, 230 ],
[ 15, 77, 151, 296, 446 ],
[ 23, 125, 246, 488, 734 ],
[ 33, 185, 367, 728, 1094 ],
[ 45, 257, 511, 1016, 1526 ],
[ 59, 341, 678, 1352, 2030 ]
];

dimensions[44] := [
[ 8, 36, 58, 129, 198 ],
[ 18, 92, 152, 353, 534 ],
[ 32, 176, 292, 689, 1038 ],
[ 50, 288, 478, 1137, 1710 ],
[ 74, 428, 712, 1697, 2550 ],
[ 102, 596, 992, 2369, 3558 ],
[ 134, 792, 1318, 3153, 4734 ]
];

dimensions[28] := [
[ 5, 21, 52, 77, 82 ],
[ 11, 53, 138, 205, 222 ],
[ 19, 101, 266, 397, 430 ],
[ 29, 165, 436, 653, 706 ],
[ 43, 245, 650, 973, 1054 ],
[ 59, 341, 906, 1357, 1470 ],
[ 77, 453, 1204, 1805, 1954 ]
];

dimensions[57] := [
[ 13, 98, 126, 381, 278 ],
[ 32, 266, 352, 1053, 764 ],
[ 60, 518, 688, 2061, 1492 ],
[ 97, 854, 1134, 3405, 2462 ],
[ 144, 1274, 1696, 5085, 3676 ],
[ 200, 1778, 2368, 7101, 5132 ],
[ 265, 2366, 3150, 9453, 6830 ]
];

dimensions[33] := [
[ 7, 44, 58, 165, 122 ],
[ 15, 116, 155, 453, 330 ],
[ 27, 224, 299, 885, 642 ],
[ 43, 368, 490, 1461, 1058 ],
[ 63, 548, 731, 2181, 1578 ],
[ 87, 764, 1019, 3045, 2202 ],
[ 115, 1016, 1354, 4053, 2930 ]
];

dimensions[85] := [
[ 28, 136, 432, 540, 812 ],
[ 80, 384, 1204, 1508, 2252 ],
[ 152, 744, 2356, 2948, 4412 ],
[ 244, 1216, 3888, 4860, 7292 ],
[ 368, 1824, 5812, 7268, 10892 ],
[ 512, 2544, 8116, 10148, 15212 ],
[ 676, 3376, 10800, 13500, 20252 ]
];

dimensions[76] := [
[ 18, 90, 234, 345, 522 ],
[ 44, 242, 640, 953, 1434 ],
[ 82, 470, 1248, 1865, 2802 ],
[ 132, 774, 2058, 3081, 4626 ],
[ 196, 1154, 3072, 4601, 6906 ],
[ 272, 1610, 4288, 6425, 9642 ],
[ 360, 2142, 5706, 8553, 12834 ]
];

dimensions[56] := [
[ 11, 51, 82, 186, 280 ],
[ 25, 131, 216, 506, 760 ],
[ 45, 251, 416, 986, 1480 ],
[ 71, 411, 682, 1626, 2440 ],
[ 105, 611, 1016, 2426, 3640 ],
[ 145, 851, 1416, 3386, 5080 ],
[ 191, 1131, 1882, 4506, 6760 ]
];

dimensions[88] := [
[ 21, 111, 286, 420, 456 ],
[ 53, 295, 778, 1156, 1256 ],
[ 99, 571, 1514, 2260, 2452 ],
[ 159, 939, 2494, 3732, 4044 ],
[ 237, 1399, 3722, 5572, 6040 ],
[ 329, 1951, 5194, 7780, 8432 ],
[ 435, 2595, 6910, 10356, 11220 ]
];

dimensions[77] := [
[ 11, 48, 94, 185, 238 ],
[ 29, 132, 256, 509, 658 ],
[ 53, 252, 496, 989, 1282 ],
[ 83, 408, 814, 1625, 2110 ],
[ 125, 612, 1216, 2429, 3154 ],
[ 173, 852, 1696, 3389, 4402 ],
[ 227, 1128, 2254, 4505, 5854 ]
];

dimensions[93] := [
[ 17, 74, 162, 279, 358 ],
[ 42, 196, 456, 761, 984 ],
[ 78, 376, 888, 1481, 1920 ],
[ 125, 614, 1458, 2439, 3166 ],
[ 186, 916, 2184, 3641, 4728 ],
[ 258, 1276, 3048, 5081, 6600 ],
[ 341, 1694, 4050, 6759, 8782 ]
];

dimensions[69] := [
[ 13, 52, 114, 189, 328 ],
[ 29, 132, 309, 509, 904 ],
[ 53, 252, 597, 989, 1768 ],
[ 85, 412, 978, 1629, 2920 ],
[ 125, 612, 1461, 2429, 4360 ],
[ 173, 852, 2037, 3389, 6088 ],
[ 229, 1132, 2706, 4509, 8104 ]
];

dimensions[60] := [
[ 22, 114, 216, 444, 548 ],
[ 56, 306, 608, 1212, 1508 ],
[ 104, 594, 1184, 2364, 2948 ],
[ 166, 978, 1944, 3900, 4868 ],
[ 248, 1458, 2912, 5820, 7268 ],
[ 344, 2034, 4064, 8124, 10148 ],
[ 454, 2706, 5400, 10812, 13508 ]
];

dimensions[65] := [
[ 26, 218, 244, 864, 724 ],
[ 70, 602, 672, 2400, 2004 ],
[ 134, 1178, 1312, 4704, 3924 ],
[ 218, 1946, 2164, 7776, 6484 ],
[ 326, 2906, 3232, 11616, 9684 ],
[ 454, 4058, 4512, 16224, 13524 ],
[ 602, 5402, 6004, 21600, 18004 ]
];

dimensions[73] := [
[ 17, 149, 264, 594, 430 ],
[ 47, 413, 734, 1650, 1194 ],
[ 91, 809, 1438, 3234, 2338 ],
[ 149, 1337, 2376, 5346, 3862 ],
[ 223, 1997, 3550, 7986, 5770 ],
[ 311, 2789, 4958, 11154, 8058 ],
[ 413, 3713, 6600, 14850, 10726 ]
];

dimensions[97] := [
[ 26, 230, 408, 918, 664 ],
[ 72, 638, 1134, 2550, 1844 ],
[ 140, 1250, 2222, 4998, 3612 ],
[ 230, 2066, 3672, 8262, 5968 ],
[ 344, 3086, 5486, 12342, 8916 ],
[ 480, 4310, 7662, 17238, 12452 ],
[ 638, 5738, 10200, 22950, 16576 ]
];

dimensions[89] := [
[ 21, 177, 198, 702, 708 ],
[ 56, 489, 545, 1950, 1956 ],
[ 108, 957, 1065, 3822, 3828 ],
[ 177, 1581, 1758, 6318, 6324 ],
[ 264, 2361, 2625, 9438, 9444 ],
[ 368, 3297, 3665, 13182, 13188 ],
[ 489, 4389, 4878, 17550, 17556 ]
];




weights := [4..16 by 2];
levels := [1..5];

printf "Checking STrace and Trace at 1*ZF...d=";
function check(d)
    printf "%o ", d;
    F := QuadraticField(d);
    ZF := Integers(F);
    prec := 1;
    R := GradedRingOfHMFs(F, prec);
    dims := [[Integers()!STrace(HMFSpace(R, n*ZF, [k, k]), 1*ZF) : n in levels]: k in weights];
    assert dimensions[d] eq dims;

    k := Random(weights);
    n := Random(levels);
    dim := Integers()!Trace(HMFSpace(R, n*ZF, [k, k]), 1*ZF);
    assert Integers()!STrace(HMFSpace(R, n*ZF, [k, k]), 1*ZF) eq dim;
    return true;
end function;

ds := [];
for counter in [1..5] do
    if Set(ds) eq Keys(dimensions) then
        break;
    end if;
    d := Random(Keys(dimensions));
    while d in ds do
        d := Random(Keys(dimensions));
    end while;
    Append(~ds, d);
    _ := check(d);
end for;
return true;