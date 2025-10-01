// this is an example how to confirm that
// the mod 3 Galois representation of an
// elliptic curve y^2 + y = x^3 - x
// is surjective

// Set the memory limit to 8 Gigabytes (8 * 1024^3 bytes)
SetMemoryLimit(8 * 1024^3);

// Set verbose printing for GaloisGroup to see progress
SetVerbose("GaloisGroup", 1);

Qx<x> := PolynomialRing(Rationals());
E := EllipticCurve([0, 0, 1, -1, 0]);
printf "Defined Elliptic Curve E: %o\n\n", E;

// Compute the 3rd division polynomial
psi3 := Qx!DivisionPolynomial(E, 3);
printf "The 3rd division polynomial is: %o\n\n", psi3;

// Construct the splitting field of the x-coordinates (Kx)
printf "Constructing the splitting field of psi3 (Kx)...\n";
time Kx := SplittingField(psi3);
printf "Degree of Kx/Q is: %o\n\n", Degree(Kx);

// Define the discriminant for the y-coordinates
D_poly := 1 + 4*(x^3 - x);

// Construct the full 3-division field L (as a relative extension)
Kx_poly<y> := PolynomialRing(Kx);
a := Roots(psi3, Kx)[1][1];
D_a := Evaluate(D_poly, a);

L := Kx; 
if not IsSquare(D_a) then
    printf "Adjoining sqrt of discriminant to get the relative field L...\n";
    L := ext< Kx | y^2 - D_a >;
end if;
printf "Absolute degree of L/Q is: %o\n\n", AbsoluteDegree(L);

// Create the absolute field from the tower Q -> Kx -> L
printf "Constructing the absolute field L_abs from the tower...\n";
L_abs := AbsoluteField(L);

// Compute the Galois group of the absolute field
printf "Computing the absolute Galois group Gal(L_abs/Q). This will take time...\n";
time G := GaloisGroup(L_abs);

printf "The order of the computed Galois group is: %o\n", Order(G);

// Define GL(2, F_3) for comparison
GL2F3 := GeneralLinearGroup(2, 3);
printf "The order of GL(2, F_3) is: %o\n", Order(GL2F3);

// Check if the computed group is isomorphic to GL(2, F_3)
printf "Checking for isomorphism with GL(2, F_3)...\n";
is_iso := IsIsomorphic(G, GL2F3);
printf "Is Gal(Q(E[3])/Q) isomorphic to GL(2, F_3)? %o\n", is_iso;