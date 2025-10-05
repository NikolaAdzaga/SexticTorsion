//This code is checking the 1st case in the proof of Proposition 3.4, i.e.
//E does not have a rational 9-isogeny, has a rational 3-isogeny and G_E(2)=2B

A<x,y>:=AffineSpace(Rationals(),2);
C:=Curve(A,(x+3)*(x^2-3*x+9)*(x^3+3)^3*y-256*(y+1)^3*x^3);
PC:=ProjectiveClosure(C);
R<x,y>:=PolynomialRing(Rationals(),2);
tr,X:=IsHyperelliptic(PC);
simplX,f:=SimplifiedModel(X);
f2:=Inverse(f);
simplX;
J:=Jacobian(simplX);
RankBound(J);

tr,g:=IsIsomorphic(PC, X);
tr,g2:=IsInvertible(g);
g2:=Inverse(g);

pts:=Chabauty0(J);
for i:=1 to #pts do
g2(f2(pts[i]));
end for;

//The only points on PC for which xy=/=0 are (3,-16,1) and (-3,-1,1). Plugging in y=-16 and y=-1 in j(E)=256(y+1)^3/y we get that 
// j(E)=54000 or j(E)=0. In both of these cases, E has CM.

// The second part of the proof is in
// https://github.com/NikolaAdzaga/SexticTorsion/blob/main/rat9isogeny.m
// where we also show how one can create an elliptic curve from its
// j-invariant and confirm it has CM.
