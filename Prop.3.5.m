//Here we prove a major part of the Proposition 3.5,
// that G_E(3) = 3Cs.1.1 is incompatible with
// level-9 subgroup j9B0-9a

Qx<x> := PolynomialRing(Rationals());
Qt<t> := FunctionField(Rationals());
Ps<s> := PolynomialRing(Qt);


//We take j-map for level-9 subgroup from
// https://math.mit.edu/~drew/SZ16/g0groups.m
j9B0 := (t+3)^3*(t^3+9*t^2+27*t+3)^3/(t*(t^2+9*t+27));

// Get a denominator and numerator over Q[t]
Qt_poly_ring := Parent(Denominator(j9B0));
den := Denominator(j9B0);
num := Numerator(j9B0);


//3Cs.1.1 j-map is taken from Zywina's paper
numerator := 27 * (s + 1)^3 * (s + 3)^3 * (s^2 + 3)^3;
denominator := s^3 * (s^2 + 3*s + 3)^3;

cleared_expr := num * (denominator) - den*numerator;
print "Comparing the two j-maps gives the following expression: ";
cleared_expr;



Qts<t, s> := PolynomialRing(Rationals(), 2);
    
cleared_poly := (-27*t^3 - 243*t^2 - 729*t)*s^12 + (-324*t^3 - 2916*t^2 - 8748*t)*s^11 +
    (-1782*t^3 - 16038*t^2 - 48114*t)*s^10 + (t^12 + 36*t^11 + 594*t^10 +
    5868*t^9 + 38151*t^8 + 169128*t^7 + 512028*t^6 + 1028376*t^5 + 1276479*t^4 +
    833976*t^3 + 144342*t^2 - 157464*t + 729)*s^9 + (9*t^12 + 324*t^11 +
    5346*t^10 + 52812*t^9 + 343359*t^8 + 1522152*t^7 + 4608252*t^6 + 9255384*t^5
    + 11488311*t^4 + 7545879*t^3 + 1659933*t^2 - 334611*t + 6561)*s^8 + (36*t^12
    + 1296*t^11 + 21384*t^10 + 211248*t^9 + 1373436*t^8 + 6088608*t^7 +
    18433008*t^6 + 37021536*t^5 + 45953244*t^4 + 30215592*t^3 + 6928416*t^2 -
    472392*t + 26244)*s^7 + (81*t^12 + 2916*t^11 + 48114*t^10 + 475308*t^9 +
    3090231*t^8 + 13699368*t^7 + 41474268*t^6 + 83298456*t^5 + 103394799*t^4 +
    68001120*t^3 + 15733278*t^2 - 629856*t + 59049)*s^6 + (108*t^12 + 3888*t^11
    + 64152*t^10 + 633744*t^9 + 4120308*t^8 + 18265824*t^7 + 55299024*t^6 +
    111064608*t^5 + 137859732*t^4 + 90646776*t^3 + 20785248*t^2 - 1417176*t +
    78732)*s^5 + (81*t^12 + 2916*t^11 + 48114*t^10 + 475308*t^9 + 3090231*t^8 +
    13699368*t^7 + 41474268*t^6 + 83298456*t^5 + 103394799*t^4 + 67912911*t^3 +
    14939397*t^2 - 3011499*t + 59049)*s^4 + (27*t^12 + 972*t^11 + 16038*t^10 +
    158436*t^9 + 1030077*t^8 + 4566456*t^7 + 13824756*t^6 + 27766152*t^5 +
    34464933*t^4 + 22517352*t^3 + 3897234*t^2 - 4251528*t + 19683)*s^3 +
    (-144342*t^3 - 1299078*t^2 - 3897234*t)*s^2 + (-78732*t^3 - 708588*t^2 -
    2125764*t)*s - 19683*t^3 - 177147*t^2 - 531441*t;

//This polynomial factors as
// (-3 s^3 + 81 t + 81 s t + 27 s^2 t + 27 t^2 + 27 s t^2 + 9 s^2 t^2 + 
//     3 t^3 + 3 s t^3 + s^2 t^3) (-27 + 81 s t + 81 s^2 t + 27 s^3 t + 
//     27 s t^2 + 27 s^2 t^2 + 9 s^3 t^2 + 3 s t^3 + 3 s^2 t^3 + 
//     s^3 t^3) (243 + 729 s + 972 s^2 + 729 s^3 + 324 s^4 + 81 s^5 + 
//     9 s^6 + 729 s t + 2916 s^2 t + 2916 s^3 t + 972 s^4 t + 81 s^5 t + 
//     243 s t^2 + 3159 s^2 t^2 + 3159 s^3 t^2 + 1053 s^4 t^2 + 
//     27 s^5 t^2 + 27 s t^3 + 1566 s^2 t^3 + 1566 s^3 t^3 + 
//     522 s^4 t^3 + 3 s^5 t^3 + 405 s^2 t^4 + 405 s^3 t^4 + 
//     135 s^4 t^4 + 54 s^2 t^5 + 54 s^3 t^5 + 18 s^4 t^5 + 3 s^2 t^6 + 
//     3 s^3 t^6 + s^4 t^6)


printf "\n ================== Analyzing the first factor ================== \n"; 
A2<t, s> := AffineSpace(Rationals(), 2);

C := Curve(A2, 3 * s^3 - 81 * t - 81 * s * t - 27 * s^2 * t - 27 * t^2 -
27 * s * t^2 - 9 * s^2 * t^2 - 3 * t^3 - 3 * s * t^3 - s^2 * t^3);
printf "Genus is %o\n", Genus(C);
//1
PC := ProjectiveClosure(C);
E, mp := EllipticCurve(PC, PC! [0, 0, 1]);
E;
RankBounds(E);
//0 0

T, mT := TorsionSubgroup(E);
// Z/3Z
torsion_gen := [mT(g) : g in Generators(T)][1];
Dimension(torsion_gen @@ mp);
//0
//preimage is 0-dimensional scheme
Points(torsion_gen @@ mp);
//{@ (-3 : -3 : 1), (0 : 1 : 0), (1 : 0 : 0) @}

printf "We get points at infinity
while t and s=-3 correspond to j=0 which has CM
and analogously for (2*torsion_gen) and (3*torsion_gen)\n";

printf "\n ============== Analyzing the second factor (analogous) ============== \n"; 
C2 := Curve(A2, (-27 + 81 * s * t + 81 * s^2 * t + 27 * s^3 * t + 27 * s * t\
^2 + 27 * s^2 * t^2 + 9 * s^3 * t^2 + 3 * s * t^3 + 3 * s^2 * t^3 + s^3 * t^3)\
);
Genus(C2);
//1
PC2 := ProjectiveClosure(C2);
PointSearch(PC2, 10);
//[ (-3 : -1 : 1), (0 : 1 : 0), (1 : 0 : 0) ]
E2, mp2 := EllipticCurve(PC2, PC2 ! [0, 1, 0]);
RankBounds(E2);
//0 0
T, mT := TorsionSubgroup(E2);
// Z/3Z again
torsion_gen := [mT(g) : g in Generators(T)][1];
Dimension(torsion_gen @@ mp2);
//0
//preimage is 0-dimensional scheme
 Points(torsion_gen @@ mp2);
//{@ (-3 : -1 : 1), (0 : 1 : 0), (1 : 0 : 0) @}
//we get points at infinity,
// while t = -3 corresponds to j=0 which has CM
//analogously for (2*torsion_gen) and (3*torsion_gen)




// Now we move on to the third factor which defines a highly singular plane curve.
printf "\n \n \n ================== Analyzing the third factor ================== \n"; 
f := 243 + 729 * s + 972 * s^2 + 729 * s^3 + 324 * s^4 + 81 * s^5 + 9 * s^6 + 729 * s * t + 2916 * s^2 * t + 2916 * s^3 * t + 972 * s^4 * t + 81 * s^5 * t + 243 * s * t^2 + 3159 * s^2 * t^2 + 3159 * s^3 * t^2 + 1053 * s^4 * t^2 + 27 * s^5 * t^2 + 27 * s * t^3 + 1566 * s^2 * t^3 + 1566 * s^3 * t^3 + 522 * s^4 * t^3 + 3 * s^5 * t^3 + 405 * s^2 * t^4 + 405 * s^3 * t^4 + 135 * s^4 * t^4 + 54 * s^2 * t^5 + 54 * s^3 * t^5 + 18 * s^4 * t^5 + 3 * s^2 * t^6 + 3 * s^3 * t^6 + s^4 * t^6;

C := Curve(A2, f);
printf "\n We compute the canonical map (to P1) and use its equations.\n";
CanMapC := CanonicalMap(C);

//we use the equations
CanMapEqs := DefiningEquations(CanMapC);
F1 := CanMapEqs[1];
F2 := CanMapEqs[2];


P<t,s,u> := PolynomialRing(Rationals(), 3);
F1p := Evaluate(F1, [t,s]);
F2p := Evaluate(F2, [t,s]);
G := F1p - u*F2p;
//G;

u_s_t := -Coefficient(G, u, 0)/Coefficient(G, u, 1);  // linear in u

// Suppose u_s_t = N/D
N := Numerator(u_s_t);
D := Denominator(u_s_t);
//D;
R<t,s,u> := PolynomialRing(Rationals(),3);
H := u*R!D - R!N;    // polynomial in s,t,u

//We copy h because f is defined in a polynomial
// ring with less variables
//(and Magma is strict about this).

h := 243 + 729 * s + 972 * s^2 + 729 * s^3 + 324 * s^4 + 81 * s^5 + 9 * s^6 +
729 * s * t + 2916 * s^2 * t + 2916 * s^3 * t + 972 * s^4 * t + 81 * s^5 * t +
243 * s * t^2 + 3159 * s^2 * t^2 + 3159 * s^3 * t^2 + 1053 * s^4 * t^2 + 27 *
s^5 * t^2 + 27 * s * t^3 + 1566 * s^2 * t^3 + 1566 * s^3 * t^3 + 522 * s^4 * t^3
+ 3 * s^5 * t^3 + 405 * s^2 * t^4 + 405 * s^3 * t^4 + 135 * s^4 * t^4 + 54 * s^2
* t^5 + 54 * s^3 * t^5 + 18 * s^4 * t^5 + 3 * s^2 * t^6 + 3 * s^3 * t^6 + s^4 * t^6;
res := Resultant(H, R!h, s);   // eliminates s, result in R[t,u]
printf "printing resultant's factorisation:\n";
//print res - 31381059609*(3+27*t+9*t^2+t^3)^8 *(t^6 + 18*t^5 + 135*t^4 + 504*t^3 + 891*t^2 + 486*t - 27)^2 *(u^2 + 29*u + 211)^3;
print Factorisation(res);

print "Resultant factors as
31381059609 (t^3 + 9*t^2 + 27*t + 3)^8 (-27+486 t+891 t^2+504 t^3+135 t^4+18 t^5+t^6)^2 (211+29 u+u^2)^3. 
None of the factors have rational solutions t nor u,
implying our curve has no affine rational points
 (after the following verifications).";


// we only need to check singular points, and the points where F2=0
PC := ProjectiveClosure(C);

printf "\n Singular points on the (projective closure of) our curve are: %o", SingularPoints(PC);
// {@ (0 : 1 : 0), (1 : 0 : 0) @}



printf "\n We also check the points where F2 = f = 0:\n";

P<t,s> := PolynomialRing(Rationals(), 2);
// The equation for a curve C
f := 243 + 729*s + 972*s^2 + 729*s^3 + 324*s^4 + 81*s^5 + 9*s^6
    + 729*s*t + 2916*s^2*t + 2916*s^3*t + 972*s^4*t + 81*s^5*t
    + 243*s*t^2 + 3159*s^2*t^2 + 3159*s^3*t^2 + 1053*s^4*t^2 + 27*s^5*t^2
    + 27*s*t^3 + 1566*s^2*t^3 + 1566*s^3*t^3 + 522*s^4*t^3 + 3*s^5*t^3
    + 405*s^2*t^4 + 405*s^3*t^4 + 135*s^4*t^4 + 54*s^2*t^5 + 54*s^3*t^5
    + 18*s^4*t^5 + 3*s^2*t^6 + 3*s^3*t^6 + s^4*t^6;
// The second polynomial F_2 from the canonical map
F2 := -2/27*t^5*s^5 + 2/9*t^5*s^4 + 4/3*t^5*s^3 + 2*t^5*s^2 + 2/3*t^5*s
    - 10/9*t^4*s^5 + 10/3*t^4*s^4 + 20*t^4*s^3 + 30*t^4*s^2 + 10*t^4*s
    - 20/3*t^3*s^5 + 20*t^3*s^4 + 120*t^3*s^3 + 180*t^3*s^2 + 60*t^3*s
    + 2/9*t^2*s^6 - 50/3*t^2*s^5 + 60*t^2*s^4 + 340*t^2*s^3 + 510*t^2*s^2 +
186*t^2*s + 12*t^2
    + 4/3*t*s^6 - 10*t*s^5 + 90*t*s^4 + 420*t*s^3 + 630*t*s^2 + 306*t*s + 72*t
    + 2*s^6 + 12*s^5 + 54*s^4 + 144*s^3 + 216*s^2 + 216*s + 108;
// 3. Create the ideal from the two polynomials
I := ideal< P | f, F2 >;
A2 := AffineSpace(P);
// Define the scheme inside this space using your ideal I
V := Scheme(A2, I); // Correct
Dimension(V);
Points(V);
RationalPoints(V);
//empty lists


// Completely nalogous computation for 9J0-9b
// is in a separate file 9J0-9b.m.