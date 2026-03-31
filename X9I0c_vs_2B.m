// This is a part of the Proof of Theorem 3.1
// showing that j_{2B}(s) = j_{9I09c}(t)
// does not lead to any non-CM elliptic curves.
// Completely analogous to X1hyp.m and X9I0b.m,  
// so there are less comments.

R<t, s> := FunctionField(Rationals(), 2);

j2B := 256*(s+1)^3 / (s);

Qx<x> := PolynomialRing(Rationals());
Qt<t> := FunctionField(Rationals());
Ps<s> := PolynomialRing(Qt);

j9I0c := (t^3-3*t^2+1)^3*(t^9-9*t^8+27*t^7-48*t^6+54*t^5-45*t^4+27*t^3-9*t^2+1)^3/(t^9*(t-1)^9*(t^2-t+1)^3*(t^3-6*t^2+3*t+1));

// Get a common denominator and numerator over Q[t]
Qt_poly_ring := Parent(Denominator(j9I0c));
den := Denominator(j9I0c);
num := Numerator(j9I0c);


cleared_expr := num * (s) - den*256*(s+1)^3;
cleared_expr;


Qts<t, s> := PolynomialRing(Rationals(), 2);
    
cleared_poly := (-256*t^27 + 4608*t^26 - 36864*t^25 + 179712*t^24 - 608256*t^23 + 1532160*t^22 - 2992128*t^21 + 4642560*t^20 - 5801472*t^19 + 5868288*t^18 - 4790016*t^17 + 3115008*t^16 - 1569792*t^15 + 578304*t^14 - 133632*t^13 + 6912*t^12 + 6912*t^11 -
    2304*t^10 + 256*t^9)*s^3 + (-768*t^27 + 13824*t^26 - 110592*t^25 + 539136*t^24 - 1824768*t^23 + 4596480*t^22 - 8976384*t^21 + 13927680*t^20 - 17404416*t^19 + 17604864*t^18 - 14370048*t^17 + 9345024*t^16 - 4709376*t^15 + 1734912*t^14
    - 400896*t^13 + 20736*t^12 + 20736*t^11 - 6912*t^10 + 768*t^9)*s^2 + (t^36 - 36*t^35 + 594*t^34 - 6000*t^33 + 41859*t^32 - 215892*t^31 + 860466*t^30 - 2733948*t^29 + 7083369*t^28 - 15216344*t^27 + 27431082*t^26 - 41847624*t^25 +
    54305784*t^24 - 60083100*t^23 + 56639466*t^22 - 45323100*t^21 + 30557196*t^20 - 17163036*t^19 + 7983204*t^18 - 3312360*t^17 + 1823931*t^16 - 1794528*t^15 + 1913220*t^14 - 1609416*t^13 + 969579*t^12 - 355212*t^11 + 8802*t^10 +
    79072*t^9 - 48717*t^8 + 11124*t^7 + 2262*t^6 - 2124*t^5 + 378*t^4 + 84*t^3 - 36*t^2 + 1)*s - 256*t^27 + 4608*t^26 - 36864*t^25 + 179712*t^24 - 608256*t^23 + 1532160*t^22 - 2992128*t^21 + 4642560*t^20 - 5801472*t^19 + 5868288*t^18 -
    4790016*t^17 + 3115008*t^16 - 1569792*t^15 + 578304*t^14 - 133632*t^13 + 6912*t^12 + 6912*t^11 - 2304*t^10 + 256*t^9;
    

 A2<t, s> := AffineSpace(Rationals(), 2);
X3_modular := Curve(A2, cleared_poly);
printf "Genus is %o.\n", Genus(X3_modular);
boo, C, mp := IsHyperelliptic(X3_modular);
Qx<x> := PolynomialRing(Rationals());
printf "This curve is isomorphic to the following.\n";
C;
Cs, mapToCs := SimplifiedModel(C);
Js := Jacobian(Cs);
printf "Rank bounds for the Jacobian:  %o.\n", RankBounds(Js);
//0 0
printf "We find its rational points. \n";
Chabauty0(Js);
//{@ (1 : -1 : 0), (1 : 1 : 0), (-1 : 1 : 1), (-1 : -1 : 1), (0 : 1 : 1), (0 : -1 : 1) @}
pts := Chabauty0(Js);
printf "So we pull them back onto our original modular curve.\n";

// Again preimages are 0-dimensional schemes. One can check this by running
// [Dimension((pt @@ mapToCs) @@ mp): pt in pts];
[Points((pt @@ mapToCs) @@ mp): pt in pts];
//[
//    {@ @},
//    {@ (1, 0) @},
//    {@ @},
//    {@ @},
//    {@ @},
//   {@ (0, 0) @}

printf "Birational map is undefined for:";
Points(SingularSubscheme(ProjectiveClosure(X3_modular)));
// {@ (0 : 1 : 0) @}


printf "So we get points at infinity and points with s=0,
which is again a zero of the denominator for j_2B.";
// So we are done.
