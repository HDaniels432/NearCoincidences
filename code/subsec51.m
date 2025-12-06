// Magma script that considers possible mod 4 images of Galois
// that are nilpotent and surject onto the order 3 subgroup of GL_2(Z/2Z).

S := Subgroups(GL(2,Integers(4)));
goodsubs := [ S[i]`subgroup : i in [1..#S] | IsNilpotent(S[i]`subgroup) and (S[i]`order mod 6 eq 0)
and not (S[i]`subgroup subset SL(2,Integers(4)))];
// We find two subgroups with surjective determinant, order a multiple of 6, that are nilpotent.
// The first is contained in the second.
assert goodsubs[1] subset goodsubs[2];

// Let's check to see whether goodsubs[2] is admissible.
// We need to find whether there is an element of order 2 that fixes an element of
// (Z/4Z)^2.

C := ConjugacyClasses(goodsubs[2]);
M2 := RMatrixSpace(Integers(4),2,2);
I := IdentityMatrix(Integers(4),2);
for k in [1..#C] do
  if C[k][1] eq 2 then
    printf "Conjugacy class representatitve %o has order 2.\n",k;
    K := Kernel(M2!C[k][3] - I);
    chk := &and [ (2*k eq K!0) : k in K];
    if chk then
      printf "Every element in the kernel of M-I has order 2.\n";
    else
      printf "Conjugacy class %o is a possible image of complex conjugation.\n";
    end if;
  end if;
end for;