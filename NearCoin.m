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

Attach("~/GL2.m");
load "~/GL2data.m";

//This is data from RSZB.

X2 := GL2Load("gl2_big2adic.txt");
X3 := GL2Load("gl2_3adic.txt");
X5 := GL2Load("gl2_5adic.txt");
X7 := GL2Load("gl2_7adic.txt");
X11 := GL2Load("gl2_11adic.txt");
X13 := GL2Load("gl2_13adic.txt");
X17 := GL2Load("gl2_17adic.txt");
X19 := GL2Load("gl2_19adic.txt");
X23 :=  GL2Load("gl2_23adic.txt");
X29 :=  GL2Load("gl2_29adic.txt");
X31 :=  GL2Load("gl2_31adic.txt");
X37 :=  GL2Load("gl2_37adic.txt");




//Give a set S of subgroups of the GL_2(Z/nZ), this function returns the 
//maximal subgroups ordered by containment upto conjugation. 
function MaximalGroups(S)
    assert #S ne 0;
    n := #BaseRing(S[1]);
    G := GL(2,Integers(n));
    I:=Sort([<Index(G,S[i]),i>:i in [1..#S]]);
    indexes:={i[1]:i in I};
    U:=[<S[I[1][2]],I[1][1],AssociativeArray(indexes)>];
    for n in indexes do if IsDivisibleBy(n,U[1][2]) then U[1][3][n] := [K`subgroup: K in Subgroups(U[1][1]:IndexEqual:=n div U[1][2])]; end if; end for;
    for i:=2 to #I do
        H:=S[I[i][2]];
        Hn :=I[i][1];
        keep := true;
        for j:=1 to #U do
            if IsDivisibleBy(Hn,U[j][2]) then
                for K in U[j][3][Hn] do assert #H eq #K; if IsConjugate(G,H,K) then keep:= false; break; end if; end for;
                if not keep then break; end if;
            end if;
        end for;
        if keep then
            r:=<H,Hn,AssociativeArray(indexes)>;
            for n in indexes do if IsDivisibleBy(n,Hn) then r[3][n] := [K`subgroup:K in Subgroups(H:IndexEqual:=n div Hn)]; end if; end for;
            U:=Append(U,r);
        end if;
    end for;
    t:=Cputime();
    S:=[r[1]:r in U];
    return S;
end function;

//This is a function that determine is Q(E[n]) = Q(E[m],zeta_n)
function RepresntsNearCoincedence(G,n,m)
    assert Integers(n)!#BaseRing(G) eq 0;
    assert Integers(m)!n eq 0;
    G := ChangeRing(G,Integers(n));
    GLn := GL(2,Integers(n));
    GLm, pi := ChangeRing(GLn,Integers(m));
    Kdet := SL(2,Integers(n)) meet G; //This is the kernel of the determinant map and it fixes Q(zeta_n)
    Km := Kernel(pi) meet G; //This fixes Q(E[m])
    N := Kdet meet Km; // This fixes Q(E[m],zeta_n)
    return #N eq 1;
end function;


//Near Coincidences for powers of 2.
p := 2;
GL16 := GL(2,Integers(16));
GL8 := GL(2,Integers(8));
GL4 := GL(2,Integers(4));
time Subs4 := Subgroups(GL4);
time Subs8 := Subgroups(GL8);
time Subs16 := Subgroups(GL16);

Subs4 := [h`subgroup : h in Subs4 | GL2DeterminantIndex(h`subgroup) eq 1 ];
Subs8 := [h`subgroup : h in Subs8 | GL2DeterminantIndex(h`subgroup) eq 1 ];
Subs16 := [h`subgroup : h in Subs16 | GL2DeterminantIndex(h`subgroup) eq 1 ];


time Keep4 := MaximalGroups([h : h in Subs4 | RepresntsNearCoincedence(h,4,2)]);
time Keep8 := MaximalGroups([h : h in Subs8 | RepresntsNearCoincedence(h,8,4)]);
time Keep16 := MaximalGroups([h : h in Subs16 | RepresntsNearCoincedence(h,16,8)]);

Keep4Lab := [GL2LookupLabel(X2,h) : h in Keep4];
Keep8Lab := [GL2LookupLabel(X2,h) : h in Keep8];
//Keep16Lab := [GL2Label(h) : h in Keep16];

assert Keep4Lab eq [ "4.16.0.1", "4.16.0.2", "4.48.0.3" ];
//4.16.0.1
//4.16.0.2 Q(E[2]) = Q(E[4]) Ie X20b
//4.48.0.3 Q(E[2]) = Q and Q(E[4]) = Q(i) Ie X58i

assert Keep8Lab eq ["8.192.5.2", "8.192.5.6", "8.192.3.71", "8.192.3.72", 
"8.192.5.3", "8.192.5.5", "8.192.3.73", "8.192.3.74", "8.192.3.42", 
"8.192.3.45", "8.192.1.57", "8.192.1.58", "8.192.3.43", "8.192.3.46", 
"8.192.1.65", "8.192.1.66", "8.192.1.67", "8.192.1.71", "8.192.1.55", 
"8.192.1.59", "8.192.3.51", "8.192.3.55", "8.192.3.49", "8.192.3.47", 
"8.192.1.70", "8.192.1.76", "8.192.1.62", "8.192.1.64", "8.192.3.54", 
"8.192.3.59", "8.192.3.40", "8.192.3.38", "8.192.1.56", "8.192.1.60", 
"8.192.1.69", "8.192.1.72", "8.192.3.37", "8.192.3.39", "8.192.3.58", 
"8.192.3.53", "8.192.1.61", "8.192.1.63", "8.192.1.68", "8.192.1.75", 
"8.192.3.48", "8.192.3.50", "8.192.3.56", "8.192.3.52", "8.192.5.7", 
"8.192.5.8", "8.192.5.1", "8.192.5.4", "8.192.3.75", "8.192.3.76", 
"8.192.3.70", "8.192.3.69", "8.192.3.57", "8.192.3.60", "8.192.3.41", 
"8.192.3.44", "8.192.1.73", "8.192.1.74", "8.192.1.54", "8.192.1.53", 
"8.192.3.82", "8.192.3.81", "8.192.1.105", "8.192.1.106"];
//These all have genus 1 or higer and so their only possible rational
//points are cusps and CM points. 
//We will check for CM near coincedences below. 


time for g in Keep16 do
    assert GL2Genus(g) gt 1;
end for;
//Again, these all have genus 1 or higer and so their only possible rational
//points are cusps and CM points. 
//We will check for CM near coincedences below. 



//This is a list of all the posible 2-adic images a CM elliptic curve can have. 
//These come from pages 63 and 64 of RSZB
S16:={"16.64.2.1", "16.96.4.13", "16.192.9.83", 
    "16.192.9.143", "16.192.9.145", "16.192.9.178", 
    "16.192.9.189", "16.384.9.462", "16.384.9.568", 
    "16.384.9.600", "16.384.9.633", "16.384.9.817", 
    "16.384.9.819", "16.384.9.829", "16.384.9.831", 
    "16.96.3.325", "16.192.3.540", "16.192.3.545", 
    "16.192.3.554", "16.192.3.563", "16.96.3.353", 
    "16.96.3.366", "16.96.4.13", "16.96.5.135", 
    "16.192.5.602", "16.192.5.607", "16.192.5.617", 
    "16.192.5.624", "16.192.9.205"};


//We now check for CM cureves with 2-powered near coincedences. 
CMKeep8 := [X2[lab] : lab in S16 | RepresntsNearCoincedence(X2[lab]`subgroup,8,4) ];
CMKeep16 := [X2[lab] : lab in S16 | RepresntsNearCoincedence(X2[lab]`subgroup,16,8) ];

assert #CMKeep8 eq 0;
assert #CMKeep16 eq 0;
//We see that there are none. 



//Near Coincidences p=3
GL27 := GL(2,Integers(27));
GL9 := GL(2,Integers(9));
time Subs27 := Subgroups(GL27);
time Subs9 := Subgroups(GL9);

time Subs27 := [h`subgroup : h in Subs27 | GL2DeterminantIndex(h`subgroup) eq 1 ];
time Subs9 := [h`subgroup : h in Subs9 | GL2DeterminantIndex(h`subgroup) eq 1 ];

time Keep9 := MaximalGroups([h : h in Subs9 | RepresntsNearCoincedence(h,9,3)  ]);
time Keep27 := MaximalGroups([h : h in Subs27 | RepresntsNearCoincedence(h,27,9)]);

Keep9Lab := [GL2Label(G) : G in Keep9];
assert Keep9Lab eq ["9.27.0.1", "9.162.4.1", "9.324.10.1"];
//9.27.0.1 is the only one of these curves with rational points!

Keep27Lab := [GL2Label(G) : G in Keep27];
assert Keep27Lab eq [ "27.729.43.1", "27.4374.280.4", "27.4374.280.1", 
    "27.4374.280.3", "27.4374.280.2", "27.8748.568.2", "27.8748.568.5", 
    "27.8748.568.1", "27.8748.568.3"];
//The only rational points on these curves are cusps and CM points.
//We will check for CM near coincedences below. 


//This is a list of all the posible 3-adic images a CM elliptic curve can have. These come from pages 63 and 64 of RSZB
S27:={"27.324.18.1", "27.648.18.1", "27.648.18.4", "27.972.55.16", 
    "27.972.55.22", "27.972.55.23", "27.1944.55.31", "27.1944.55.37", 
    "27.1944.55.43", "27.1944.55.44", "27.1944.55.49", "27.1944.55.50", 
    "27.486.28.7", "27.324.18.1", "27.648.18.1", "27.648.18.4", 
    "27.243.12.1", "27.324.13.16", "27.648.13.25", "27.648.13.34"};

CMKeep27 := [X3[lab] : lab in S27 | RepresntsNearCoincedence(X3[lab]`subgroup,27,9) ];

assert #CMKeep27 eq 0;

















