This repository hosts code and data related to the paper
**_Near coincidences and nilpotent division fields_**


by Harris B. Daniels and Jeremy Rouse, arXiv:2409.00881 (2024).

The directory structure is organized as follows:

data/

This directory contains external data files required for our computations.

data/RSZB/

This subdirectory contains Magma code and data imported from
Rouse–Sutherland–Zureick-Brown,
ℓ-adic images of Galois for elliptic curves over Q (arXiv:2106.11141),
which we cite as [33] in the paper.

It includes:

gl2.m
gl2data.m
gl2_big2adic.txt
gl2_3adic.txt

These files are included verbatim to make our results easily reproducible.

code/

This directory contains the Magma scripts written for this project.

code/NearCoin.m

Implements the search for near coincidences of division fields arising from groups of 2-power and 3-power level.

code/NilpModels.m

Computes models of modular curves of composite level whose rational points correspond to elliptic curves with nilpotent division fields.

code/prop35.m

Searches GL(2,Z/p^2 Z) for p=5 and 7 for admissible subgroups that could give a near coincidence when the mod-p image lies in the normalizer of a split Cartan.

code/subsec51.m

Searches for nilpotent subgroups of GL₂(ℤ/4ℤ) that surject onto the order-3 subgroup of GL(2,Z/2Z), and checks whether any of those subgroups are admissible.