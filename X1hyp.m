
R<t, s> := FunctionField(Rationals(), 2);

Qx<x> := PolynomialRing(Rationals());

j2B := 256*(s+1)^3 / (s);

// Define the hyperelliptic model of C1
C1 := HyperellipticCurve(x^6 - 10*x^3 + 1);


Qt<t> := FunctionField(Rationals());
Ps<s> := PolynomialRing(Qt);
j9a := ((t^2 - 3*t + 3)^3 * (t^2 + 3)^3 * (t^2 + 3*t + 3)^3 * (t^3 + 3)^3 * (t^3
+ 9)^3) /
       (t^9 * (t^6 + 9*t^3 + 27)^3);
//j9b := ((t^3 - 3*t^2 - 9*t + 3)^3 * (t^3 + 9*t^2 - 9*t - 9)^3 *
//        (t^6 - 18*t^5 + 171*t^4 + 180*t^3 - 297*t^2 - 162*t + 189)^3) /
//       (8 * (t^2 - 1)^3 * (t^2 + 3)^9 * (t^3 - 9*t^2 - 9*t + 9)^3);

// This defines the curve in Q(t)[s]
f := Numerator(Ps!j9a * (s) - 256*(s+1)^3);

Qt_poly_ring := Parent(Denominator(j9a));
den := Denominator(j9a);
num := Numerator(j9a);

cleared_expr := num * (s) - den*256*(s+1)^3;
cleared_expr;

//    (-256*t^27 - 6912*t^24 - 82944*t^21 - 559872*t^18 - 2239488*t^15 - 5038848*t^12
//        - 5038848*t^9)*s^3 + (-768*t^27 - 20736*t^24 - 248832*t^21 - 1679616*t^18 -
//        6718464*t^15 - 15116544*t^12 - 15116544*t^9)*s^2 + (t^36 + 36*t^33 +
//        594*t^30 + 5820*t^27 + 36855*t^24 + 153576*t^21 + 603612*t^18 + 4146552*t^15
//        + 26867295*t^12 + 114555060*t^9 + 315675954*t^6 + 516560652*t^3 +
//        387420489)*s - 256*t^27 - 6912*t^24 - 82944*t^21 - 559872*t^18 -
//        2239488*t^15 - 5038848*t^12 - 5038848*t^9


Qts<t, s> := PolynomialRing(Rationals(), 2);
cleared_poly := (-256*t^27 - 6912*t^24 - 82944*t^21 - 559872*t^18 - 2239488*t^15
- 5038848*t^12
    - 5038848*t^9)*s^3 + (-768*t^27 - 20736*t^24 - 248832*t^21 - 1679616*t^18 -
    6718464*t^15 - 15116544*t^12 - 15116544*t^9)*s^2 + (t^36 + 36*t^33 +
    594*t^30 + 5820*t^27 + 36855*t^24 + 153576*t^21 + 603612*t^18 + 4146552*t^15
    + 26867295*t^12 + 114555060*t^9 + 315675954*t^6 + 516560652*t^3 +
    387420489)*s - 256*t^27 - 6912*t^24 - 82944*t^21 - 559872*t^18 -
    2239488*t^15 - 5038848*t^12 - 5038848*t^9;
   
    
A2<t, s> := AffineSpace(Rationals(), 2);
C1_modular := Curve(A2, cleared_poly);
//IsHyperelliptic(C1_modular);
boo, C, mp := IsHyperelliptic(C1_modular);
Qx<x> := PolynomialRing(Rationals());
C1_known := HyperellipticCurve(x^6 - 10*x^3 + 1);
tr, mapToC1 := IsIsomorphic(C, C1_known);
tr;
J := Jacobian(C);
Jac1 := Jacobian(C1_known);
RankBounds(Jac1);
Chabauty0(Jac1);
 pts := Chabauty0(Jac1);
//  {pt @@ mapToC1 : pt in pts};

// for a pt in pts
// (pt @@ mapToC1) @@ mp returns a 0-dimensional scheme
pts_on_C1_modular := { Points((pt @@ mapToC1) @@ mp) : pt in pts };
pts_on_C1_modular;
//
//{
//    {@ @},
//    {@ (0, 0) @}
//}
// s = 0 implies j2B = infty