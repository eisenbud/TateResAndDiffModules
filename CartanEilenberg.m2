newPackage(
        "CartanEilenberg",
        Version => "1.0", 
        Date => "March 29,2020",
        Authors => {{Name => "David Eisenbud", 
                  Email => "de@berkeley.edu", 
                  HomePage => "http://www.msri.org/~de"}},
        Headline => "Cartan-Eilenberg resolution of a differential module",
        DebuggingMode => true
        )
export{
    "CE",
    "cplxToDM",
    "Ures",
    "resPlusAug"}


--code to create a Cartan-Eilenberg resolution of a differential module C
-- that is, a free complex surjecting to C such that the induced map on homology is surjective,
--and the induced map on cycles and boundaries are also surjective.

resPlusAug = method(Options => {LengthLimit =>3})
resPlusAug Module := o -> M -> (
    M' := prune M;
    p := M'.cache.pruningMap;
    F := res(M', LengthLimit => o.LengthLimit);
    aug' := inducedMap(M',F_0);
    assert(p*aug'*F.dd_1 == 0);
    {F,p*aug'}
    )
TEST///
restart
loadPackage"CartanEilenberg"
S = ZZ/101[a,b,c,SkewCommutative =>true]
M = coker vars S
assert(length((resPlusAug(M,LengthLimit =>7))_0) == 7)
M = ker random(S^3,S^{3:-1})
///

Ures = method()
Ures(ChainComplex, List, List) := (C, L0,L2) -> (
    --C is a right exact chain complex C_2 -> C_1 -> C_0 -> 0 of modules. 
    --Li is a list consisting of a resolution of Ci and an augmentation to C_i 
    --for i = 0,2 of length = o.LengthLimit
    --Output is a 
    --split double complex of free resolutions. F_2 -> F_1 -> F_0 -> 0
    --covering C
    --with F1 = F2++F0 as modules
    --plus an augmentation map (F1_0 --> C_1).
    --caveat: if the resolutions of C2 and C0 have lengths a,b, then the resulting
    --complex has length max(a,b), but is only a resolution for min(a,b) steps!
    F0 := L0_0;
    ell0 := length F0;
    F2 := L2_0;
    ell2 := length F2;    
    ell := min(ell0,ell2);
    F0dd := apply(ell, i->F0.dd_(i+1)); 
    F0' := chainComplex(drop(F0dd,1)); -- F1_1<--F1_2<-- ... NOTE: START IN HOM POSITION 0
    e0 := map(C_0,F0_0,L0_1); --we need the augmentation map!
    e2 := map(C_2,F2_0,L2_1);
    phi0 := ((e0//C.dd_1)*F0.dd_1)//(C.dd_2*e2);
    phi := extend(F2,F0',phi0, Verify =>true);
    F1 := chainComplex apply(ell, i-> (
	    map(F0_i++F2_i, F0_(i+1)++F2_(i+1),
		      matrix{{F0.dd_(i+1),0},{(-1)^(i+1)*phi_i,F2.dd_(i+1)}})));

    aug := map(C_1,F1_0,(e0//C.dd_1)*((F1_0)^[0]) + C.dd_2*e2*((F1_0)^[1]));
    
    assert (F1.dd^2 == 0);
    assert(aug*F1.dd_1 == 0);

    delta2 := map(F1,F2,i->(F1_i)_[1]);
    delta1 := map(F0,F1,i->(F1_i)^[0]);
    {delta1,delta2,aug} -- needs to return the augmentation map of F1, and F0,F2 should come with aug maps.
)

TEST///
restart
loadPackage"CartanEilenberg"
S = ZZ/101[a,b,c,SkewCommutative =>true]
k = coker vars S
M = S^{-1}**coker transpose vars S
phi = map(k,M,random(S^1,S^3))
N = ker phi
psi = inducedMap(M,ker phi)
C = chainComplex(phi,psi)
assert(C.dd^2 == 0)
assert isHomogeneous C
U = Ures(C,resPlusAug(k, LengthLimit =>5), resPlusAug(N,LengthLimit => 3));
FM = source U_0
all(2,i->prune HH_(i+1)FM == 0)
betti res M
///

cplxToDM = method()
cplxToDM ChainComplex := F -> (
    --F is a 3-term complex
    minF := min F;
    maxF := max F;
    evens := positions (toList(minF..maxF), i->i%2==0);
    odds := positions (toList(minF..maxF), i->i%2!=0);
    F0 := directSum apply(evens, i-> F_i);
    F1 := directSum apply(odds, i-> F_i);
    D1 := F0_[0]*F.dd_1;
    D0 := map(F1,F0,F.dd_2*F0^[1]);
    map(F0++F1,F0++F1, matrix{{0*id_F0,D1},{D0,0*id_F1}})
	)
TEST///
restart
loadPackage"CartanEilenberg"
S = ZZ/101[a,b,c,SkewCommutative =>true]
k = coker vars S
M = (coker transpose vars S)**S^{-1}
phi = map(k,M,random(S^1,cover M))
N = ker phi
psi = inducedMap(M,ker phi)
C = chainComplex(phi,psi)
assert isHomogeneous C
assert(C.dd^2 == 0)
assert((DM = cplxToDM C)^2 == 0)
assert isHomogeneous DM
///


CE = method(Options =>{LengthLimit =>3})
CE(Matrix) := o-> d ->(
    --d is a homogeneous map M -> M, d^2 == 0
    --returns a map D:F->F of free complexes F, 
    --where F is a nonmin res of M, and D^2 == 0
M := source d;
K := ker d;
d' := inducedMap(M,K); --K to M
B := image d;
d'' := map(B,M,1); --M to B
d2 := inducedMap(M,image d)//(inducedMap(M,ker d)); --B to K
assert(K == target d2 and B == source d2);
assert(d == d'*d2*d'');
assert(d''*d' == 0);
H := coker d2; -- this is the homology
if prune H != 0 then (
d1 := inducedMap(coker d2, K); -- the map from K to H, the homology

CK := chainComplex(d1,d2); -- CK: 0 --> B --> K --> H-->0
assert(0==CK.dd^2);
UK := Ures (CK, 
     resPlusAug(CK_0,LengthLimit => o.LengthLimit), 
     resPlusAug(CK_2, LengthLimit => o.LengthLimit));
FK := source(UK_0)
 ) else (
UK = resPlusAug(K,LengthLimit => o.LengthLimit);
FK = UK_0);
augK := UK_1;

CM := chainComplex(map(image d,M,1),d');-- CM: 0 --> K --> M --> B --> 0
assert(CM.dd^2 == 0);
UM := Ures(CM,resPlusAug(CM_0,LengthLimit => o.LengthLimit),{FK,augK});
FM := source (UM_0);
augM := UM_2;

D' := extend(FK,FM,(d2*d''*augM)//augK);
D'' := map(FM,FK,i->(FM_i)_[1]);
assert(D'*D'' == 0);
D''*D')

TEST///
restart
loadPackage"CartanEilenberg"
S = ZZ/101[a,b,c,SkewCommutative =>true]
k = coker vars S
M = (coker transpose vars S)**S^{-1}
phi = map(k,M,random(S^1,cover M))
N = ker phi
psi = inducedMap(M,ker phi)
C = chainComplex(phi,psi)
assert isHomogeneous C
assert(C.dd^2 == 0)
assert((DM = cplxToDM C)^2 == 0)
assert isHomogeneous DM
D = CE(DM, LengthLimit =>5);
FM = source D
all(4,i->prune HH_(i+1)FM == 0)
betti res M
///

beginDocumentation()
multidoc ///
 Node
  Key
   CartanEilenberg
  Headline
     Cartan-Eilenberg resolution of a differential module
  Description
   Text
    {\em FirstPackage} is a basic package to be used as an example.
  Caveat
    Still trying to figure this out.

 Node
  Key
   (CE,Matrix)
   CE
  Headline
   a silly first function
  Usage
   firstFunction n
  Inputs
   n:
  Outputs
   :
    a silly string, depending on the value of {\tt n}
  Description
   Text
    Here we show an example.
   Example
    assert(1==1)

///

TEST ///
    
///

end--
restart
loadPackage "CartanEilenberg"


S = ZZ/101[a,b,c]
M = S^1++S^{1:-1}++S^{-3}
d0 = random(M,M)
d = (d0-diagonalMatrix apply(numcols d0,i->d0_(i,i)))^2
assert(d^2 == 0)
D = CE (M,d)
assert isHomogeneous D
assert(D^2 == 0)
FM = source D
prune coker FM.dd_1
degrees oo --- this is a problem
degrees M
-----------------
S = ZZ/101[x]
N = S^1/x^3
M = N++(N**S^{-2})
d = map(N++(N**S^{-2}),N++(N**S^{-2}), matrix{{0,x^2},{0,0}})

assert(d^2 == 0)
assert isHomogeneous d
D = CE(M,d)
assert isHomogeneous D
assert (D^2 == 0)
FM = source D
prune coker FM.dd_1
degrees oo --- this is a problem
degrees M

-----------------
E = ZZ/101[x,y,SkewCommutative =>true]
M = E^{0,-1}
d = map(M,M, matrix{{0,x},{0,0}})
isHomogeneous d
d^2
D = CE(M,d,LengthLimit => 7) -- lengthLimit isn't working
assert(D^2 ==0)
isHomogeneous D 
FM = source D
prune coker FM.dd_1
degrees oo --- this is a problem
degrees M
FM.dd

---------------
S = ZZ/101[y,x]
N = S^1/ideal(x*y)
M = N**S^{0,-1,-2}
d = map(M,M, matrix{{0,x,0},{0,0,y},{0,0,0}})
assert(d^2 == 0)
assert isHomogeneous d
D = CE(M,d)
D^2
assert isHomogeneous D
assert (D^2 == 0)
FM = source D
FM.dd
coker FM.dd_1
degrees oo --- this is a problem
degrees M
degrees prune coker FM.dd_1

-----------------
