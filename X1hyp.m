// This is a part of the proof of Theorem 3.1.
// This script finds rational points on a modular
// curve given by the intersection of the 
// images of two j-maps, j_{2B} and j_{9H0-9B}.

R<t, s> := FunctionField(Rationals(), 2);

// Define polynomial ring for hyperelliptic curves
Qx<x> := PolynomialRing(Rationals());

// j-invariant of an elliptic curve with G_E(2)=2B
// from Zywina's paper
j2B := 256*(s+1)^3 / (s);

Qt<t> := FunctionField(Rationals());
Ps<s> := PolynomialRing(Qt);

// j-invariant corresponding to 9H0-9b
// taken from https://math.mit.edu/~drew/SZ16/g0groups.m
j9H09b := ((t^3 - 3*t^2 - 9*t + 3)^3 * (t^3 + 9*t^2 - 9*t - 9)^3 *
        (t^6 - 18*t^5 + 171*t^4 + 180*t^3 - 297*t^2 - 162*t + 189)^3) /
       (8 * (t^2 - 1)^3 * (t^2 + 3)^9 * (t^3 - 9*t^2 - 9*t + 9)^3);


// Get a denominator and numerator over Q[t]
Qt_poly_ring := Parent(Denominator(j9H09b));
den := Denominator(j9H09b);
num := Numerator(j9H09b);

// Equate the two j-maps, j9Hb = j2B, and clear denominators.
// This gives the polynomial defining the modular curve.
cleared_expr := num * (s) - den*256*(s+1)^3;
print "Comparing the two j-maps gives the following expression: ";
cleared_expr;


// We then use this same polynomial
// (pasted to avoid Magma's coercion errors)

Qts<t, s> := PolynomialRing(Rationals(), 2);
    
cleared_poly := 
(-256*t^33 + 6912*t^32 - 61440*t^31 + 221184*t^30 - 768000*t^29 + 3151872*t^28 -
    20480*t^27 + 26099712*t^26 + 52503552*t^25 + 136553472*t^24 + 382537728*t^23
    + 451878912*t^22 + 1114601472*t^21 + 837568512*t^20 + 606154752*t^19 +
    262766592*t^18 - 4130735616*t^17 - 2549657088*t^16 - 7300730880*t^15 -
    5321023488*t^14 + 6006306816*t^13 - 1330255872*t^12 + 19591041024*t^11 +
    8707129344*t^10 - 6389259264*t^9 + 9251324928*t^8 - 28298170368*t^7 -
    4353564672*t^6 + 9795520512*t^5 - 9795520512*t^4 + 19591041024*t^3 -
    11019960576*t + 3673320192)*s^3 + (-768*t^33 + 20736*t^32 - 184320*t^31 +
    663552*t^30 - 2304000*t^29 + 9455616*t^28 - 61440*t^27 + 78299136*t^26 +
    157510656*t^25 + 409660416*t^24 + 1147613184*t^23 + 1355636736*t^22 +
    3343804416*t^21 + 2512705536*t^20 + 1818464256*t^19 + 788299776*t^18 -
    12392206848*t^17 - 7648971264*t^16 - 21902192640*t^15 - 15963070464*t^14 +
    18018920448*t^13 - 3990767616*t^12 + 58773123072*t^11 + 26121388032*t^10 -
    19167777792*t^9 + 27753974784*t^8 - 84894511104*t^7 - 13060694016*t^6 +
    29386561536*t^5 - 29386561536*t^4 + 58773123072*t^3 - 33059881728*t +
    11019960576)*s^2 + (1/8*t^36 - 9/2*t^35 + 243/4*t^34 - 825/2*t^33 +
    16713/8*t^32 - 10980*t^31 + 1610658*t^30 - 28440756*t^29 + 237016125/2*t^28
    + 1167802122*t^27 - 9887517963*t^26 - 9057112038*t^25 + 424266139089/2*t^24
    - 12569189580*t^23 - 2188199457234*t^22 + 221409705636*t^21 +
    50410741781367/4*t^20 - 230457016755*t^19 - 88875216956295/2*t^18 -
    1439486254035*t^17 + 410256510600519/4*t^16 + 3681976329252*t^15 -
    161342940580434*t^14 - 149463647820*t^13 + 352146482879841/2*t^12 -
    10731404056230*t^11 - 132681309032331*t^10 + 18501496865226*t^9 +
    133843439764845/2*t^8 - 15158765688372*t^7 - 20995438702302*t^6 +
    6681138077340*t^5 + 27682298804889/8*t^4 - 2930549021145/2*t^3 -
    659002251789/4*t^2 + 218634295959/2*t - 44725543119/8)*s - 256*t^33 +
    6912*t^32 - 61440*t^31 + 221184*t^30 - 768000*t^29 + 3151872*t^28 -
    20480*t^27 + 26099712*t^26 + 52503552*t^25 + 136553472*t^24 + 382537728*t^23
    + 451878912*t^22 + 1114601472*t^21 + 837568512*t^20 + 606154752*t^19 +
    262766592*t^18 - 4130735616*t^17 - 2549657088*t^16 - 7300730880*t^15 -
    5321023488*t^14 + 6006306816*t^13 - 1330255872*t^12 + 19591041024*t^11 +
    8707129344*t^10 - 6389259264*t^9 + 9251324928*t^8 - 28298170368*t^7 -
    4353564672*t^6 + 9795520512*t^5 - 9795520512*t^4 + 19591041024*t^3 -
    11019960576*t + 3673320192;    

printf "\n ================== Analyzing the Modular Curve ================== \n";
A2<t, s> := AffineSpace(Rationals(), 2);
X1_modular := Curve(A2, cleared_poly);
printf "Genus is %o.\n", Genus(X1_modular);
// Test if the curve is hyperelliptic and find a model C.
// This takes a while (5 minutes on our server)
time boo, C, mp := IsHyperelliptic(X1_modular);
// boo;
// true

printf "This curve is isomorphic to the following.\n";
C;
Cs, mapToCs := SimplifiedModel(C);
Js := Jacobian(Cs);
printf "Rank bounds for the Jacobian: %o .\n", RankBounds(Js);

printf "So we can determine all its rational points:\n";
Chabauty0(Js);
pts := Chabauty0(Js);

printf "Now we pull those points back to get (s, t) values.\n";
// Since the preimage is a 0-dimensional scheme,
// we do it like this:
pts_on_X1_modular := { Points((pt @@ mapToCs) @@ mp) : pt in pts };
pts_on_X1_modular;
//{
//    {@ (1, 0) @},
//    {@ @},
//    {@ (-1, 0) @}
//}

printf "s = 0 implies j2B = infty\n";
// So we are done.

//Analogous code for the remaining two curves
// appearing in the Proof of Theorem 3.1
// are in X9I0b.m and X9I0c.m
