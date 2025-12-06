// Magma script that does computations for p = 5 and p = 7 in
// the proof of Proposition 3.5.

// We wish to find and understand admissible subgroups H of GL_2(Z/p^2 Z)
// so that |H| divides |GL_2(Z/p^2Z)|/p^4(p+1)/2 and so that
// H is non-abelian.

for p in [5,7] do
  GL2 := GL(2,Integers(p^2));
  GL1 := GL(1,Integers(p^2));
  // Make the determinant homomorphism
  det := hom<GL2 -> GL1 | x :-> GL1![Determinant(x)]>;
  ord := Integers()!(#GL2/(p^4*(p+1)/2));
  // Compute subgroups whose order divides ord
  sublist := Subgroups(GL2 : OrderDividing := ord);
  // Check to see which have surjective determinant and are not abelian.
  goodsubs := [ sublist[i]`subgroup : i in [1..#sublist] 
	| (#det(sublist[i]`subgroup) eq #GL1) and (not IsAbelian(sublist[i]`subgroup))];
  // Build the mod p^2 normalizer of a split Cartan.
  splitcartannorm := sub<GL2 | [[PrimitiveRoot(p^2),0,0,1], 
	[1,0,0,PrimitiveRoot(p^2)], [0,1,1,0]]>;
  // Check to see if each element of goodsubs is conjugate to a subgroup of splitcartannorm
  chklist := [ IsConjugateSubgroup(GL2,splitcartannorm,goodsubs[i]) : i in [1..#goodsubs]]; 
  printf "For p = %o there are %o conjugacy classes of subgroups. Of these, %o are conjugate to a subgroup of the normalizer of the split Cartan mod %o.\n",p,#goodsubs,#[ k : k in [1..#chklist] | chklist[k] eq true],p^2;
end for;  