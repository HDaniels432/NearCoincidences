/*
***********************************************
*                                             *
*      Near Coincidences of Division Fields   *
*            and Other Results                *
*                                             *
*           Authors:                          *
*           Harris B. Daniels                 *
*           Jeremy Rouse                      *
*                                             *
***********************************************

Copyright (c) [2024] Harris B. Daniels, Jeremy Rouse

This code is licensed under the GNU General Public 
License v2.0 or later. You are welcome to use and/or 
modify this code under GPL version 2 or any later version 
(but please be sure to cite the paper).
*/


//Below we compute the maximal nilpotent subgroups of GL_2(Z/pqZ) 
//for p and q distince primes in [2,3,5,7].
Combos := AssociativeArray();

for p,q in [2,3,5,7] do
    if p lt q then
        Combos[p*q] :=[];
    end if;
end for;




for p,q in [2,3,5,7] do
    if p lt q then
        [p,q];
        S1 := MaxNilGroups[p];
        S2 := MaxNilGroups[q];
        for G1 in S1 do
            for G2 in S2 do
                G := LiftGroups(G1,G2);
                Append(~Combos[p*q],G);
            end for;
        end for;
    end if;
end for;


CombosLabel := AssociativeArray();

for k in Keys(Combos) do
    CombosLabel[k] := [GL2Label(h) : h in Combos[k]];
end for;



for k in Keys(CombosLabel) do
    k;
    CombosLabel[k];
    print " ";
end for;

 
G4 := GL(2,Integers(8));
G2, pi2 := ChangeRing(G4,Integers(2));

Im2 := GL2NonsplitCartan(2);
Im4 := sub<G4|Inverse(pi2)(Im2),Kernel(pi2)>;

PossibleIms := [n`subgroup : n in NilpotentSubgroups(Im4) | GL2DeterminantIndex(n`subgroup) eq 1 and pi2(n`subgroup) eq Im2 and GL2ContainsComplexConjugation(n`subgroup)];

max := MaximalGroups(PossibleIms);

G2 := GL2Borel(2);
#ChangeLevel(G2,4);


//This function takes a group G of level m and an integer n such that 
//either n divides m or m divides n and changes the level of G to n.
//If n divides m, then the function returns G mod n. 
//If m divides n, then the function returns the preiamge of G under 
//the natural reduction map pi:GL_2(Z/nZ)-->GL_2(Z/mZ).
function ChangeLevel(G,n)
    I := BaseRing(G);
    if #I ge n then
    H := ChangeRing(G,Integers(n));
    end if;
    if not #I ge n then
    GL2n := GL(2,Integers(n));
    _,pi  := ChangeRing(GL(2,Integers(n)),I);
    H := sub<GL2n | Inverse(pi)(G),Kernel(pi) >;
    end if;
    return H;
end function;



//This function takes in two groups of level N1 and N1 and returns
//ChangeLevel(G1,N) meet ChangeLevel(G2,N), there N = LCM(N1,N2).
function LiftGroups(G1,G2)
    N1 := #BaseRing(G1);
    N2 := #BaseRing(G2);
    N := LCM(N1,N2);
    G1Lift :=  ChangeLevel(G1,N);
    G2Lift :=  ChangeLevel(G2,N);
    return G1Lift meet G2Lift;
end function;


G3s := GL2SplitCartanNormalizer(3);
G5s := GL2SplitCartanNormalizer(5);

G9s := ChangeLevel(G3s,9);
G25s := ChangeLevel(G5s,25);

NS9s := [n`subgroup : n in NilpotentSubgroups(G9s) | GL2DeterminantIndex(n`subgroup) eq 1 and ChangeRing(n`subgroup,Integers(3)) eq G3s ];
NS25s := [n`subgroup : n in NilpotentSubgroups(G25s) | GL2DeterminantIndex(n`subgroup) eq 1 and ChangeRing(n`subgroup,Integers(5)) eq G5s ];




G3ns := GL2NonsplitCartanNormalizer(3);
G5ns := GL2NonsplitCartanNormalizer(5);
G7ns := GL2NonsplitCartanNormalizer(7);

G9ns := ChangeLevel(G3ns,9);
G25ns := ChangeLevel(G5ns,25);
G49ns := ChangeLevel(G7ns,49);


NS9ns := [n`subgroup : n in NilpotentSubgroups(G9ns) | GL2DeterminantIndex(n`subgroup) eq 1 and ChangeRing(n`subgroup,Integers(3)) eq G3ns ];
NS25ns := [n`subgroup : n in NilpotentSubgroups(G25ns) | GL2DeterminantIndex(n`subgroup) eq 1 and ChangeRing(n`subgroup,Integers(5)) eq G5ns ];
NS49ns := [n`subgroup : n in NilpotentSubgroups(G49ns) | GL2DeterminantIndex(n`subgroup) eq 1 and ChangeRing(n`subgroup,Integers(7)) eq G7ns ];



G2 := GL(2,Integers(2));
list2 := [n`subgroup : n in NilpotentSubgroups(G2)| GL2DeterminantIndex(n`subgroup) eq 1 ];
maxlist2 := MaximalGroups(list2);


G3 := GL(2,Integers(3));
list3 := [n`subgroup : n in NilpotentSubgroups(G3)| GL2DeterminantIndex(n`subgroup) eq 1 ];
maxlist3 := MaximalGroups(list3);

G5 := GL(2,Integers(5));
list5 := [n`subgroup : n in NilpotentSubgroups(G5)| GL2DeterminantIndex(n`subgroup) eq 1 ];
maxlist5 := MaximalGroups(list5);

G7 := GL(2,Integers(7));
list7 := [n`subgroup : n in NilpotentSubgroups(G7) | GL2DeterminantIndex(n`subgroup) eq 1 ];
maxlist7 := MaximalGroups(list7);

GL2Label(MaxList3[1]);





// G21 := maxlist2[1];
// G22 := maxlist2[2];

// G3 := maxlist3[1];

// G5 := maxlist5[1];

// G7 := maxlist7[1];

// GL2Label(G21),GL2Label(G3),GL2Label(LiftGroups(G21,G3));
// GL2Label(G22),GL2Label(G3),GL2Label(LiftGroups(G22,G3));

// GL2Label(G21),GL2Label(G5),GL2Label(LiftGroups(G21,G5));
// GL2Label(G22),GL2Label(G5),GL2Label(LiftGroups(G22,G5));

// GL2Label(G21),GL2Label(G7),GL2Label(LiftGroups(G21,G7));
// GL2Label(G22),GL2Label(G7),GL2Label(LiftGroups(G22,G7));

// GL2Label(G3),GL2Label(G5),GL2Label(LiftGroups(G3,G5));
// GL2Label(G3),GL2Label(G7),GL2Label(LiftGroups(G3,G7));
// GL2Label(G5),GL2Label(G7),GL2Label(LiftGroups(G5,G7));







//Code for Proposition 4.3.

function ChangeLevel(G,n)
I := BaseRing(G);
if #I ge n then
H := ChangeRing(G,Integers(n));
end if;
if not #I ge n then
GL2n := GL(2,Integers(n));
_,pi := ChangeRing(GL(2,Integers(n)),I);
H := sub<GL2n | Inverse(pi)(G),Kernel(pi) >;
end if;
return H;
end function;

G3s := GL2SplitCartanNormalizer(3);
G5s := GL2SplitCartanNormalizer(5);

G9s := ChangeLevel(G3s,9);
G25s := ChangeLevel(G5s,25);

NS9s := [n`subgroup : n in NilpotentSubgroups(G9s) | GL2DeterminantIndex(n`subgroup) eq 1 and ChangeRing(n`subgroup,Integers(3)) eq G3s ];
NS25s := [n`subgroup : n in NilpotentSubgroups(G25s) | GL2DeterminantIndex(n`subgroup) eq 1 and ChangeRing(n`subgroup,Integers(5)) eq G5s ];

assert #NS9s eq 1;
assert #NS25s eq 1;

assert GL2Label(NS9s[1]) eq "9.162.4.3";
assert GL2Label(NS25s[1]) eq "25.1875.116.1";

assert IsIsomorphic(NS9s[1], DirectProduct(G3s/sub<G3s|G3s.0>,CyclicGroup(3)));
assert IsIsomorphic(NS25s[1], DirectProduct(G5s/sub<G5s|G5s.0>,CyclicGroup(5)));


//Code for the j-map of 6.9.0.1
FF<t> := FunctionField(Rationals());
f := (256-t)^3/t^2;
g := t^3;
R<x,y>:=PolynomialRing(Rationals(),2);
h:=Numerator(Evaluate(f,x)-Evaluate(g,y));
assert IsIrreducible(h);
C := ProjectiveClosure(Curve(AffineSpace(Rationals(),2),h));
Co,phi1:=Conic(C);
assert HasPoint(Co);
P1:=Curve(ProjectiveSpace(Rationals(),1));
phi2:=Parametrization(Co,P1);
phi3:=Expand(phi2*Inverse(phi1));
phi3polys:=DefiningPolynomials(phi3);
h:=Evaluate(f,phi3polys[1]/phi3polys[3]);
j:=Evaluate(h,[t,1]);


//Code for the j-map of 15.45.1.1
FF<t> := FunctionField(Rationals());
f := t^3;
g := (t+5)^3*(t^2-5)^3*(t^2+5*t+10)^3/(t^2+5*t+5)^5;
R<x,y>:=PolynomialRing(Rationals(),2);
h:=Numerator(Evaluate(f,x)-Evaluate(g,y));
assert IsIrreducible(h);
C := ProjectiveClosure(Curve(AffineSpace(Rationals(),2),h));
P := C![1,0,0];
E1,map1 := EllipticCurve(C,P);  
E2,map2 := MinimalModel(E1);
boo, inv := IsInvertible(map1 *map2);
Eqs := DefiningEquations(inv);
j := Evaluate(f, Eqs[1]/Eqs[3]);
P<x,y> := PolynomialRing(Rationals(),2);
Factorization(Evaluate(Numerator(j),[x,y,1]));
Factorization(Evaluate(Denominator(j),[x,y,1]));


//Code for the j-map of 21.63.1.1
// What's the model for the fiber product of 3.3.0.1 and 7.21.0.1?
// We have j = (2t-1)^3*(t^2-t+2)^3*(2t^2+5t+4)^3*(5*t^2+2*t-4)^3/(t^3+2t^2-t-1)^7 for 7.21.0.1
// We have j = t^3 for 3.3.0.1.
R<y,t,z> := PolynomialRing(Rationals(),3);
pol := y^3 - (t^3 + 2*t^2*z - t*z^2 - z^3);

C := Curve(ProjectiveSpace(Rationals(),2),pol);
P1 := ProjectiveSpace(Rationals(),1);
P1map := map<C -> P1 | [C.2,C.3]>;

pts := PointSearch(C,500);
p := C![1,1,1];
E0, phi0 := EllipticCurve(C,p);
E, phi := MinimalModel(E0);
chk, phi0inv := IsInvertible(phi0);

bigmap := Inverse(phi)*phi0inv*P1map;
T := E![0,3];
P := E![2,-5];

bigmap2 := Extend(Expand(bigmap));
// Code above gives t = (x^2 + 5x - 14)/(x^2 - 4x + 3y + 19)

// Checking
Q<x> := FunctionField(Rationals());
S := PolynomialRing(Q);
pol := S.1^2 + S.1 - (x^3 + 12);
K<y> := FunctionField(pol);
elt := (x^2 + 5*x - 14)/(x^2 - 4*x + 3*y + 19);
assert IsPower(elt^3 + 2*elt^2 - elt - 1,3);




