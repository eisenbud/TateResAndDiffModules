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

Ures = method(Options =>{LengthLimit => 3})        
Ures(ChainComplex, List, List) := o -> (C, L0,L2) -> (
    --C is a right exact chain complex C_2 -> C_1 -> C_0 -> 0 of modules. 
    --Li is a list consisting of a resolution of Ci and an augmentation to C_i 
    --for i = 0,2 of length = o.LengthLimit
    --Output is a 
    --split double complex of free resolutions. F_2 -> F_1 -> F_0 -> 0
    --covering C
    --with F1 = F2++F0 as modules
    --plus an augmentation map (F1_0 --> C_1).
    F0 := L0_0;
    F2 := L2_0;
    F0dd := apply(2+length F0, i->F0.dd_(i+1));
    F0' := chainComplex(drop(F0dd,1)); -- F1_1<--F1_2<-- ...
    e0 := map(C_0,F0_0,L0_1); --we need the augmentation map!
    e2 := map(C_2,F2_0,L2_1);
    phi0 := ((e0//C.dd_1)*F0.dd_1)//(C.dd_2*e2);
    phi := extend(F2,F0',phi0, Verify =>true);
    F1 := chainComplex apply(2+length F2, i-> 
	    map(F0_i++F2_i, F0_(i+1)++F2_(i+1),
		      matrix{{F0.dd_(i+1),0},{(-1)^(i+1)*phi_i,F2.dd_(i+1)}}));
    aug := map(C_1,F1_0,(e0//C.dd_1)*((F1_0)^[0]) + C.dd_2*e2*((F1_0)^[1]));
    
    assert (F1.dd^2 == 0);
    assert(aug*F1.dd_1 == 0);

    delta2 := map(F1,F2,i->(F1_i)_[1]);
    delta1 := map(F0,F1,i->(F1_i)^[0]);
    {delta1,delta2,aug} -- needs to return the augmentation map of F1, and F0,F2 should come with aug maps.
)

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


CE = method(Options =>{LengthLimit =>3})
CE(Module,Matrix) := o-> (M,d) ->(
    --d is a homogeneous map M -> M, d^2 == 0
    --returns a map D:F->F of free complexes F, 
    --where F is a nonmin res of M, and D^2 == 0
K := ker d;
d' = inducedMap(M,K); --K to M
B = image d;
d'' = map(B,M,1); --M to B
d2 := inducedMap(M,image d)//(inducedMap(M,ker d)); --B to K
assert(K == target d2 and B == source d2);
assert(d == d'*d2*d'');
assert(d''*d' == 0);
d1 := inducedMap(coker d2, K); -- the map from K to H, the homology

CK := chainComplex(d1,d2); -- CK: 0 --> B --> K --> H-->0
assert(0==CK.dd^2);
UK := Ures(CK, resPlusAug(CK_0), resPlusAug(CK_2), LengthLimit => o.LengthLimit);
FK := source(UK_0);
augK := UK_2;

CM := chainComplex(map(image d,M,1),d');-- CM: 0 --> K --> M --> B --> 0
assert(CM.dd^2 == 0);
UM := Ures(CM,resPlusAug(CM_0),{FK,augK}, LengthLimit =>o.LengthLimit);
FM := source (UM_0);
augM := UM_2;

D' = extend(FK,FM,(d2*d''*augM)//augK);
--D'' = extend(FM,FK,(d'*augK)//augM);
D'' = map(FM,FK,i->(FM_i)_[1]);
D = D''*D';
assert(D'*D'' == 0);
D)


end--
restart
load "CartanEilenberg.m2"
debug 10

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
