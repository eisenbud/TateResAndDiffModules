-*
exports {
    "addTateData",
    "dualRingToric",
    "RRFunctor",
    "sortedMonomials",
    "positionInKoszulComplex",
    "dualElement",
    "addZeroTerms", -- should be superflous?
    "completeToMapOfChainComplexes", -- might use addTerms in an option
    "greaterEqual",
    "strictlyGreater",
    "degreeTruncation",
    "isChainComplexMap", -- should be in the core of M2
    "degreeTruncationAbove", -- working from the other side, not tested
    "degreeSetup", -- get the degree range from a starting set of degrees
                   -- using c multiplications with variabels in S
    "strictDegreeTruncationAbove",
    "concatMatrices",
    "matrixContract",
    "tallyComplex",
    "annHH",
    "dimHH",
    "relevantAnnHH",
    "beilinsonWindow",
    "factors", -- now superflous, because the last degree component in E
               -- give this information
    "entry", -- need to be rewritten?
    "DMonad",
    "DMHH",
    "DMHHalt",
    "cacheComplexes",
    "cachePhi",
    "diffModToChainComplexMaps",
    "bigChainMap"	               
    }

*-
--load "TateDM.m2"

addTateData = method()
addTateData (Ring,Ideal) := (S,irr) ->(
    S.irr = irr;
    S.exterior = dualRingToric S;
    S.koszul = koszul vars S;
    S.sortedMons = sortedMonomials S.exterior;
    S.complexes = cacheComplexes S;
    S.phis = cachePhi S;
    S.degs = keys S.complexes;
    S.degOmega = -(degrees S.koszul_(numgens S))_0;
)


///
restart
load"KoszulFunctor.m2"

kk=ZZ/101
L = {1,1,2}
S=kk[x_0..x_(#L-1),Degrees=>L]
irr = ideal vars S

addTateData(S,irr)
S.irr
S.exterior
S.sortedMons
S.complexes
S.phis
S.degs
S.degOmega
values S.complexes/betti
values S.phis/source/betti
values S.phis/target/betti
de=first keys S.phis
S.phis#de
wrongCase=S.phis#((keys S.phis)_6)
betti target wrongCase, betti source wrongCase
///

dualRingToric = method();
dualRingToric(PolynomialRing) := (S) ->(
--  Input: a polynomial ring
--  Output:  the Koszul dual exterior algebra, but with an additional 
--           ZZ-degree, the ``standard grading'' where elements of \bigwedge^k
--           have degree k.
    kk := coefficientRing S;
    degs := apply(degrees S,d-> (-d)|{1});
    ee := apply(#gens S, i-> e_i);
    kk[ee,Degrees=>degs,SkewCommutative=>true]    
    );





sortedMonomials=method()
sortedMonomials(Ring) := E -> (
    -- input: E = \Lambda V, an exterior algebra
    -- Output: a HashTable of Monomial i=> basis of \Lambda^i V
    --         in Koszul order
    kk := coefficientRing E;
    E' := kk[gens E,SkewCommutative=>true];
    bases:= apply(numgens E+1,i->(
    matrix{reverse (entries gens trim (ideal  vars E')^i)_0}));
    bases1:= apply(numgens E+1,i->i=>map(E^1,,sub(bases_i,E)));
    new HashTable from bases1
    )


 
positionInKoszulComplex=method()
positionInKoszulComplex(ChainComplex,HashTable,RingElement) := (K,sortedMons,m) -> (
    -- Input: The KosulComplex and an exterior monomial
    -- Output: (i,j) with j the column number of K_dd_i corresponding to m
    S := ring K;
    i := factors(m, sortedMons);
    j := position((entries sortedMons#i)_0,n->n==m); 
    (i,j))


-*TEST ///
m=sortedMons#2_{2}_(0,0)
factors(m,sortedMons)
#factor sub(m,vars S)
///
*-
 
dualElement=method()
dualElement(Ring,RingElement) := (E,m) -> (
    socle:=product gens E;
    n := contract(m,socle);
    sign := contract(socle,m*n);
    sign*n)
-*
TEST///
restart
load "KoszulFunctor.m2"
kk=ZZ/101
L={1,1,2,3}
S=kk[x_0..x_3,Degrees=>L]
irr=ideal vars S
elapsedTime addTateData(S,irr) -- 0.428813 seconds elapsed
E=S.exterior
sortedMons=S.sortedMons
i=random(numgens S+1)
j=random(rank source sortedMons#i)
m=(entries sortedMons#i)_0_j
n=dualElement(E,m)
assert(m*n==product gens E)
///*-

addZeroTerms=method()
   -- add Zero modules in front or after the last differential
addZeroTerms(ChainComplex,ZZ) := (K,n) -> (
    a := min K;
    b:= max K;
    C := new ChainComplex;
    C.ring = ring K;
    scan(toList(a..b),i->C_i=K_i);
    scan(toList(b+1..b+n),i->C_i=S^0);
    scan(toList(a+1..b),i->C.dd_i=K.dd_i);
    scan(toList(b+1..b+n),i->C.dd_i=map(C_(i-1),C_i,0));
    C)

addZeroTerms(ZZ,ChainComplex) := (n,K) -> (
    a := min K;
    b:= max K;
    C := new ChainComplex;
    C.ring = ring K;
    scan(toList(a..b),i->C_i=K_i);
    scan(toList(a-n..a-1),i->C_i=S^0);
    scan(toList(a+1..b),i->C.dd_i=K.dd_i);
    scan(toList(a-n+1..a),i->C.dd_i=map(C_(i-1),C_i,0));
    C)
-* 
TEST ///
addZeroTerms(K,2)
K2=addZeroTerms(2,K)
addZeroTerms(K2,2)
addZeroTerms(1,K2)
/// 
*-

completeToMapOfChainComplexes=method(Options =>{Complete => false})
completeToMapOfChainComplexes(ChainComplex,RingElement) := o -> (K,m) -> (
-- Input: m a monomial in \Lambda^i \subset E, 
--        K the KoszulComplex
-- Goal: map of complexes given by contraction with m
-- m: K_0 <- K_i the  map which maps m to 1 and the other generators to 0
-- complete this to a map
-- K <- K[i]**S^{deg m} of complexes
   S:= ring K;
   r:= length K;
   (i,j) := positionInKoszulComplex(K,S.sortedMons,m);
   --(degrees K_i)_j==-degree m
   stK := K[i]**S^{-drop(degree m,-1)}; --shifted twisted K
   assert(degrees source stK.dd_0_{j}==degrees K_0);
   phi0 := matrix{apply(rank stK_0,k->if k==j then 1_S else 0)};
   if o.Complete == false then return extend(K,stK,phi0,Verify=>true);
      tstK := chainComplex apply(r-i,p->stK.dd_(p+1)); -- truncted shifted twisted
   phi1 := extend(K,tstK,phi0,Verify=>true);
   Ke := addZeroTerms(min K- min stK,K);
   stKe :=addZeroTerms(stK,max K-max stK);
-- map(K,stK,i->phi1_i)
   map(Ke,stKe,i->if i >= min K and i <= max stKe then phi1_i else map(Ke_i,stKe_i,0))
)
-* TEST ///
restart
load "KoszulFunctor.m2"
kk=ZZ/101
S=kk[x_0..x_5,Degrees=>{{1,0,0},{1,2,0},2:{0,1,0},{0,0,1},{0,0,2}}]
irr=ideal(x_0,x_1)*ideal(x_2,x_3)*ideal(x_4,x_5)
elapsedTime addTateData(S,irr) -- 7.33095 seconds elapsed

E=S.exterior
K=S.koszul
sortedMons = S.sortedMons
(i1,j1) = (3,4)
m=sortedMons#i1_{j1}_(0,0)
phi=completeToMapOfChainComplexes(K,m,Complete =>false)
keys phi
phi#2
(cone phi).dd^2
betti source phi
betti target phi
source phi
target phi
isHomogeneous phi
///

*-

greaterEqual=method()
greaterEqual(List,List) := (d1,d2) -> all(d1-d2,i->i>=0)
strictlyGreater=method()
strictlyGreater(List,List) := (d1,d2) -> all(d1-d2,i->i>=0) and d1!=d2
-*
TEST ///
greaterEqual({1,1},{0,1})==true
greaterEqual({1,0},{0,1}), {1,0}>{0,1}
greaterEqual({0,1},{1,0})==false
strictlyGreater({1,1},{0,1})==true
strictlyGreater({1,1},{1,1})
/// *-

degreeTruncation=method()
degreeTruncation(Matrix,List) := (M,d) -> (
    --rows and cols with degrees <= d.
    rows:= positions(degrees target M,d'-> greaterEqual(d,d'));
    columns:= positions(degrees source M,d'-> greaterEqual(d,d'));
    sourceInc := (id_(source M))_columns;
    targetInc := (id_(target M))_rows;    
    ((M^rows)_columns,targetInc,sourceInc)
    )
-*
TEST ///
restart
load "KoszulFunctor.m2"
kk=ZZ/101
S=kk[x_0..x_5,Degrees=>{{1,0,0},{1,2,0},2:{0,1,0},{0,0,1},{0,0,2}}]
irr=ideal(x_0,x_1)*ideal(x_2,x_3)*ideal(x_4,x_5)
addTateData(S,irr)
K=S.koszul
M = K.dd_3
degrees source M
(tM,ti,ts) = degreeTruncation(M,{1,4,0})
M*ts == ti*tM
///
*-
isChainComplexMap = phi -> (
    so = source phi;
    ta = target phi;
    mini = max(min so, min ta);
    maxi = min(max so, max ta);
   all(toList(mini..maxi-1),i-> phi_(i)*so.dd_(i+1) == ta.dd_(i+1)*phi_(i+1))
   )

degreeTruncation(ChainComplex,List) := (K,d) -> (
    --subcomplex where all rows and cols of differentials have degrees <= d.
    a := min K;
    Ka := K[a];
    L := apply(length Ka,i->degreeTruncation(Ka.dd_(i+1),d));
--    L := apply(toList(min(K[a]).. max(K[a])-1),i->degreeTruncation(Ka.dd_(i+1),d));    
    tKa:=chainComplex(apply(length Ka,i->L_i_0));
    phi := map(K,tKa[-a], i-> if i == a then L_(i-a)_1 else L_(i-a-1)_2);
    assert(isChainComplexMap phi);
    phi
    )

-*
 ///
restart
load"KoszulFunctor.m2"
S = ZZ/101[x_0..x_3]
addTateData(S,ideal vars S)
K = koszul(vars S)
(K[3])_(-3) == K_0
dtK = degreeTruncation(K[3],{2})
sdtK = source dtK
target dtK
sdtK_(-3) == K_0
sdtK_(-3)== (K[3])_(-3)
betti sdtK
sdtK_(-3)
 ///
*-

degreeTruncation(ChainComplexMap,List) := (phi,d) -> (
    G := target phi;
    F := source phi;
    phiF := degreeTruncation(F,d);
    F' := source (phiF = degreeTruncation(F,d));
    G' := source (phiG = degreeTruncation(G,d));
    map(G', F', i->(phi_i * phiF_i)// phiG_i)
    )




-*///
restart
load "KoszulFunctor.m2"
--debug needsPackage "TateOnProducts"
--Hirzebruch S(2,0)xPP(1,2)
kk=ZZ/101
S=kk[x_0..x_5,Degrees=>{{1,0,0},{1,2,0},2:{0,1,0},{0,0,1},{0,0,2}}]
irr=ideal(x_0,x_1)*ideal(x_2,x_3)*ideal(x_4,x_5)
addTateData(S,irr)

E=S.exterior
K=koszul vars S
sortedMons = S.sortedMons 
(i,j) = (3,10)
m=sortedMons#i_{j}_(0,0)
phi=completeToMapOfChainComplexes(K,m,Complete => true)
d=drop(-degree m,-1)
phiTrunc=degreeTruncation(phi,d)
source phiTrunc
target phiTrunc

phiTruncShifted=degreeTruncation(phi**S^{-{1,2,1}},d)
source phiTruncShifted
target phiTruncShifted
conePhi=cone phiTruncShifted
conePhi.dd^2

///
*-
--the following function are not used so far
degreeTruncationAbove=method()
    --rows and cols with degrees not <= d.
degreeTruncationAbove(Matrix,List) := (M,d) -> (
    rows:= positions(degrees target M,d'-> not greaterEqual(d,d'));
    columns:= positions(degrees source M,d'-> not greaterEqual(d,d'));
    (M^rows)_columns
    )

degreeTruncationAbove(ChainComplex,List) := (K,d) -> (
    -- quotient complex where all rows and cols of differentials have degrees NOT <= d.    
    a := min K;
    Ka := K[a];
    tKa:=chainComplex(apply(length Ka,i->degreeTruncationAbove(Ka.dd_(i+1),d)));
    tKa[-a]
    )

strictDegreeTruncationAbove=method()

strictDegreeTruncationAbove(Matrix,List) := (M,d) -> (
    --rows and cols with degrees > d.
    rows:= positions(degrees target M,d'-> strictlyGreater(d',d));
    columns:= positions(degrees source M,d'-> strictlyGreater(d',d));
    (M^rows)_columns
    )

strictDegreeTruncationAbove(ChainComplex,List) := (K,d) -> (
    -- quotient complex where all rows and cols of differentials have degrees >d.    
    a := min K;
    Ka := K[a];
    tKa:=chainComplex(apply(length Ka,i->degreeTruncationAbove(Ka.dd_(i+1),d)));
    tKa[-a]
    )


degreeSetup=method()
degreeSetup(Ring,List,ZZ) := (S,lows,c)->(
    -- Input: S a Cox ring
    --      lows =list of starting degrees 
    --      c number of multiplications
    -- Output: HashTable i=> List of degrees one can obtain 
    --         by multiplication by monomials with i factors
    range := new MutableHashTable;
    degS:=degrees  S;
    range#0=lows; 
    scan(c,i->range#(i+1)=
	unique flatten apply(degS,d->apply(range#i,e->e+d)));
    new HashTable from range
    )
-*
TEST ///

lows={{0,0,0}}
c=3
degreeSetup(S,lows,c)
M=coker presentation image vars S
///
*-
concatMatrices=method()
concatMatrices(List) := L -> (
    m:= first L;
    scan(#L-1,i->m=m|L_(i+1));
    m)

matrixContract=method()
matrixContract(Matrix,Matrix) := (M,N) -> (
    S := ring M;
    if M==0 or N==0 then return map(S^(-degrees source N),S^(degrees source M),0);
    assert(rank source M == rank target N); 
    --map(target M, , matrix apply(rank target M,i->apply(rank source N,j->
    transpose map(S^(-degrees source N), , transpose matrix apply(rank target M,i->apply(rank source N,j->		
           sum(rank source M,k->contract(M_(i,k),N_(k,j) ))
	    )))
    )
///
restart
load"KoszulFunctor.m2"
kk=ZZ/101
S=kk[x_0..x_1,Degrees=>{{1,1},{2,1}}]
E=kk[e_0..e_1,SkewCommutative=>true,Degrees=>-degrees S ]
SE := S**E;
use SE
M = matrix {{x_0, 0}, {0, x_0}}
N= matrix {{x_0*e_0}, {x_0*e_1}}
isHomogeneous( P =matrixContract(M,N))
///

tallyComplex =method()
-- print degrees of the free modules in a ChainComplex
tallyComplex(ChainComplex) := F -> apply(toList(min F..max F),
    i->tally degrees F_i)

annHH=method()
annHH(ChainComplex) := F -> apply(toList(min F..max F),
    i->ann HH_i F) 

dimHH=method()
dimHH(ChainComplex) := F -> apply(toList(min F..max F),
    i->dim HH_i F) 

relevantAnnHH=method()
relevantAnnHH(ChainComplex,Ideal) := (F,irr) -> (
    -- irr the ireelevant ideal
    apply(toList(min F..max F),i->saturate(ann HH_i F,irr))) 

factors=method()
factors(RingElement,HashTable) := (m,sortedMons) -> (
    (select(keys sortedMons,k->member(m,(entries sortedMons#k)_0)))_0)


cacheComplexes=method()
cacheComplexes(Ring) := S-> (
    --produces a hashTable of those subcomplexes of the Koszul complex obtained by degree
    --truncation that have relevant homology. the ideal irr = irrelevant ideal should
    --be cached in S or otherwise a global var.
    --K:=koszul vars S; 
    K := S.koszul;
    koszulRange :=unique flatten apply(length K+1,i->degrees K_i);
    truncatedComplexes := new HashTable from apply(koszulRange, d-> 
	(d,source degreeTruncation(K,d)));
    relDegs:=select(koszulRange,d->
	#select(relevantAnnHH(truncatedComplexes#d,S.irr),j->j!=ideal 1_S)>0);
    new HashTable from apply(relDegs,d->(d,(truncatedComplexes#d)**S^{d}))
    ) 

cachePhi=method()
cachePhi Ring := S -> (
    cplx := S.complexes;
    degs := keys cplx;
    es := (entries concatMatrices values S.sortedMons)_0;
    --es := drop((entries concatMatrices values S.sortedMons)_0,-1);
    possiblePairs := select(flatten apply(degs,d->apply(es,m -> (d,m))), dm-> 
	member( dm_0-drop(degree dm_1,-1),degs)
	);
    netList (allPhi=apply(possiblePairs,dm->(
	--	dm=possiblePairs_3
	d:=dm_0;m:=dm_1;
	phi := completeToMapOfChainComplexes(S.koszul,m,Complete => false);

	(dm,degreeTruncation(phi,d)[-factors(m, S.sortedMons)]**S^{d})))); 
    new HashTable from allPhi)

///
restart
load"KoszulFunctor.m2"

kk=ZZ/101
L = {1,1,2}
S=kk[x_0..x_(#L-1),Degrees=>L]
irr = ideal vars S

addTateData(S,irr)
S.irr
S.exterior
S.sortedMons
S.complexes
S.phis
S.degs
S.degOmega
keys S.phis
values S.complexes/betti
values S.phis/source/betti
values S.phis/target/betti
dm=first keys S.phis
	d:=dm_0;m:=dm_1;
	phi := completeToMapOfChainComplexes(S.koszul,m,Complete => false);
betti target phi, betti source phi
phitrunc=degreeTruncation(phi,d)[-factors(m, S.sortedMons)]**S^{d}
betti target phitrunc, betti source phitrunc


///


---------------------------------------
---finished creating cached data
---------------------------------------

RRFunctor = method();
--Input: (M,L) M a (multi)-graded S-module.
--             L a list of degrees.
--Question:  should E be part of the input??
--Output:  The differenial module RR(M) in degrees from L.
RRFunctor(Module,List) := (M,L) ->(
    S := ring(M);
    E := S.exterior;
    relationsM := gens image presentation M;
--    numvarsE := numgens E;
--    ev := map(E,S,vars E);
    --L := degreeSetup(low,c,r);
    f0 := gens image basis(L_0,M);
    scan(#L-1,i-> f0 = f0 | gens image basis(L_(i+1),M));
    --f0 is the basis for M in degrees given by L
    --df0 := apply(degrees source f0,i-> (-1)*i|{0});
    --df1 := apply(degrees source f0,i-> (-1)*i|{-1});
    df0 := apply(degrees source f0,i-> i|{0});
    df1 := apply(degrees source f0,i-> i|{-1});
    SE := S**E;
    tr := sum(dim S, i-> SE_i*SE_(dim S+i));
    newf0 := sub(f0,SE)*tr;
    relationsMinSE := sub(relationsM,SE);
    newf0 = newf0 % relationsMinSE;
    newg := matrixContract(transpose sub(f0,SE),newf0);
    g' := transpose sub(newg,E);
    chainComplex map(E^df0,E^df1, g')
    )


RRFunctor(Module,List,Boolean) := (M,LL,X) ->(
    S :=ring(M);
    E := S.exterior;
    relationsM := gens image presentation M;
    numvarsE := rank source vars E;
    f0 := gens image basis(LL_0,M);
    scan(#LL-1,i-> f0 = f0 | gens image basis(LL_(i+1),M));
    --f0 is the basis for M in degrees given by L
    df0 := apply(degrees source f0,i-> (-1)*i|{0});
    df1 := apply(degrees source f0,i-> (-1)*i|{-1});
    SE := S**E;
    tr := sum(dim S, i-> SE_i*SE_(dim S+i));
    newf0 := sub(f0,SE)*tr;
    relationsMinSE := sub(relationsM,SE);
    newf0 = newf0 % relationsMinSE;
    newg := contract(transpose sub(f0,SE),newf0);
    g' := sub(newg,E);
    chainComplex map(E^df0,E^df1, g')
    )


-*
--  The RR functor with variants.
TM = RRFunctor(M,LL,true)
betti TM
TB = beilinsonWindow(TM,-S.degs)
TB.dd_1
betti TB
RRFunctor = method();
--Input: (M,L) M a (multi)-graded S-module.
--             L a list of degrees.
--Question:  should E be part of the input??
--Output:  The differenial module RR(M) in degrees from L.
RRFunctor(Module,List) := (M,L) ->(
    S := ring(M);
    --E := dualRingToric S;
    relationsM := gens image presentation M;
    numvarsE := rank source vars E;
    ev := map(E,S,vars E);
    --L := degreeSetup(low,c,r);
    f0 := gens image basis(L_0,M);
    scan(#L-1,i-> f0 = f0 | gens image basis(L_(i+1),M));
    --f0 is the basis for M in degrees given by L
    df0 := apply(degrees source f0,i-> (-1)*i|{0});
    df1 := apply(degrees source f0,i-> (-1)*i|{-1});
    SE := S**E;
    tr := sum(dim S, i-> SE_i*SE_(dim S+i));
    newf0 := sub(f0,SE)*tr;
    relationsMinSE := sub(relationsM,SE);
    newf0 = newf0 % relationsMinSE;
    newg := contract(transpose sub(f0,SE),newf0);
    g' := transpose sub(newg,E);
    chainComplex map(E^df0,E^df1, g')
    )


--  The RR functor with variants.
RRFunctor = method();
--Input: (M,L) M a (multi)-graded S-module.
--             L a list of degrees.
--Question:  should E be part of the input??
--Output:  The differenial module RR(M) in degrees from L.
RRFunctor(Module,List) := (M,L) ->(
    S := ring(M);
    --E := dualRingToric S;
    relationsM := gens image presentation M;
    numvarsE := rank source vars E;
    ev := map(E,S,vars E);
    f0 := gens image basis(L_0,M);
    scan(#L-1,i-> f0 = f0 | gens image basis(L_(i+1),M));
    --f0 is the basis for M in degrees given by L
    df0 := apply(degrees source f0,i-> (-1)*i|{0});
    df1 := apply(degrees source f0,i-> (-1)*i|{-1});   
    SE := S**E;
    tr := sum(dim S, i-> SE_i*SE_(dim S+i));
    newf0 := sub(f0,SE)*tr;
    relationsMinSE := sub(relationsM,SE);
    newf0 = newf0 % relationsMinSE;
    newg := contract(transpose sub(f0,SE),newf0);
    g' := sub(newg,E);
    chainComplex map(E^df0,E^df1, g')
    )

RRFunctor(Module,List,Boolean) := (M,L,bbb) ->(
    if bbb == true then return RRFunctor(M,L);
    S := ring(M);
    --E := dualRingToric S;
    relationsM := gens image presentation M;
    numvarsE := rank source vars E;
    ev := map(E,S,vars E);
    f0 := gens image basis(L_0,M);
    scan(#L-1,i-> f0 = f0 | gens image basis(L_(i+1),M));
    --f0 is the basis for M in degrees given by L
    df0 := apply(degrees source f0,i-> (-1)*i);
    df1 := apply(degrees source f0,i-> (-1)*i);   
    SE := S**E;
    tr := sum(dim S, i-> SE_i*SE_(dim S+i));
    newf0 := sub(f0,SE)*tr;
    relationsMinSE := sub(relationsM,SE);
    newf0 = newf0 % relationsMinSE;
    newg := contract(transpose sub(f0,SE),newf0);
    g' := sub(newg,E);
    chainComplex map(E^df0,E^df1, g')
    )

*-
-*
TEST 
restart
load "KoszulFunctor.m2"
kk=ZZ/101
A={1,1,2} --   like A = degree matrix
S=kk[x_0..x_2,Degrees=> A]
addTateData(S,ideal vars S)

E=S.exterior
degrees source vars E
M=S^1/ideal x_0
L=apply(10,i->{i}+S.degOmega)
T=RRFunctor(M,L)
T.dd_1 
source (T.dd_1)==target (T.dd_1)**E^{{0,-1}}
(T.dd_1)*((T.dd_1)**E^{{0,-1}})
netList degrees target T.dd_1, netList degrees source T.dd_1
isHomogeneous T.dd_1
degs =keys S.complexes
TB = beilinsonWindow(T,-degs)
TB.dd_1
betti TB
E.FlatMonoid
*-

beilinsonWindow=method()
beilinsonWindow(ChainComplex,List) := (T,degs) -> (
    --Input: T a Tate DM module,
    --     : degs the relevant degrees 
    --Output: The restiction of T to these degrees
    pos:=positions(degrees T_0,d->member(drop(d,-1),degs));
    chainComplex(T.dd_1_pos^pos) 
    )

---------------
-- DMonond 
------------------
diffModToChainComplexMaps = TB->(
    --Input:  a free diff module for Beilinson window
    --Output:  a hash table H where H#(i,j) is the chain complex
    --         map corresponding to that entry
    --Caveat:  might require monomial entries??
    --In essence, this codes just takes the (i,j) entry of a matrix,
    --spits out the corresponding map of chain complex (under the proposed U-functor)
    --and then encodes that in a hash table (i,j) => (corresponding chain complex map)
    --
    ijs := flatten apply(rank TB_0,i->apply(rank TB_1,j->(i,j)));
    zeroijs := select(ijs,ij->TB.dd_1_ij==0);
    nonzeroijs := select(ijs,ij->TB.dd_1_ij!=0);
--   allKeys := apply(ijs,ij-> {ij=> (i=ij_0;(-drop((degrees TB_0)_i,-1),TB.dd_1_ij))});
--   HT := hashTable flatten allKeys;
    degsTB = apply(degrees TB_0,d-> drop(d,-1));
    --  zeroMaps go the wrong direction for our RRfunctor!
    zeroMaps := apply(zeroijs,ij->(ij => map(S.complexes#(-degsTB#(ij_0)),
	                                    S.complexes#(-degsTB#(ij_1))[1],
	                                    k -> 0))
				    );
    --  nzMaps go the wrong direction for our RRfunctor!
    nzMaps := apply(nonzeroijs, ij->(
	    --i := ij_0;
	    --j := ij_1;
	    d := -drop((degrees TB_0)_(ij_0),-1);
	    ij =>  map(
		       S.complexes#(-degsTB#(ij_0)),		
		       S.complexes#(-degsTB#(ij_1))[1],
		       k-> (entry(TB.dd_1_ij,d,S)[1])_k)
	    )
	);
    hashTable(zeroMaps|nzMaps)
    )
-*
betti TM
TM.dd_1
S.complexes#(degsTB#i)
		       S.complexes#(degsTB#(ij_1))[-1]
		       k-> (entry(TB.dd_1_ij,d,S))_k)
TEST ///
restart
load "KoszulFunctor.m2"
kk=ZZ/101
L = {1,1,2}
S=kk[x_0..x_(#L-1),Degrees=>L]
irr=ideal vars S
addTateData(S,irr)

M= S^1/ideal(x_0+2*x_1,x_2)
LL=apply(10,i->S.degOmega+{i})
elapsedTime betti(TM=RRFunctor(M,LL))
TB=beilinsonWindow(TM,-S.degs)
TB.dd_1
HT = diffModToChainComplexMaps(TB);
HT#(1,2)
kHT = keys HT
netList apply(toList(min(kHT/first)..max(kHT/first)), i->(
	    apply(toList (min(kHT/last)..max(kHT/last)), j->(
		    betti target HT#(i,j)))))

///
*-
entry=method()
entry(RingElement,List,Ring) := (f,d,S) -> (
    -- Input: f an homogeneous element of the exterior algebra
    --        d the target degree, so d1= d+ +/-degree of m is source degree
    -- return 0 should be improved to rteurn a zero map between the right complexes
    E := ring f;
    if f==0_E then return 0; --should not occure in the new version
    cf := coefficients f;
    cs := (entries cf_0)_0;
    kk := coefficientRing S;
    fs := flatten (entries sub(cf_1,kk));
    phi := sum(#fs,n->(m=cs_n;fs_n*(S.phis#(d,m))));
--    phi := sum(#fs,n->(m=cs_n;fs_n*(S.phis#(drop(d,-1),m)))); --version for old DMonad   
    phi
    )


bigChainMap = (TB)->(
--  Input:  the Beilinson window chain complex.  Might require
--           differential entries to be monomials(?)
--  Output:  the Beilinson monad (??)
--  In essence, this code just concatenates the chain complex maps from the HashTable
--  diffModToChainComplexMaps(TB).
    HT = diffModToChainComplexMaps(TB);
    rows = apply(rank TB_0,i->(
	    mm := HT#(i,0);
	    scan(rank TB_1-1,j-> mm = mm|HT#(i,j+1));
--	    scan(rank TB_1-1,j-> mm = mm|map(target mm,,HT#(i,j+1)));
	    mm
	    ));
    nn = rows_0;
    scan(#rows -1,i-> nn = nn||rows_(i+1));
    assert(isHomogeneous nn);
    nn    
    )

--  just a different name for same function
altDMonad = TB -> S^{-last S.degs}**bigChainMap(TB)
--
horHom = method()
horHom ChainComplexMap := B->(
    --
    --should return a complex of homology modules
assert(B*(B[1])==0);
tB = target B;
sB = source B;
assert(sB == tB[1]);
K = ker(B[-1]);
I = image B;
inc = inducedMap(K,I);
H = coker inc
)
DMHH = method()
DMHH ChainComplexMap := B -> HH horHom B

-*
TEST /// --here!
restart
load "KoszulFunctor.m2"
kk=ZZ/101
L = {1,1,1,2}
S=kk[x_0..x_(#L-1),Degrees=>L]
irr=ideal vars S
addTateData(S,irr)
E = S.exterior

M= S^1/ideal(x_0+2*x_1,x_2,x_3)
M1= (S^{1}/ideal(x_0+2*x_1,x_2,x_3))
M = M++M1


LL=apply(toList(-10..10),i->S.degOmega+{i})
elapsedTime betti(TM=RRFunctor(M,LL))
TB=beilinsonWindow(TM,-S.degs)
TB.dd_1
BM = bigChainMap TB
--BM=altDMonad(TB)
prune DMHH BM
presentation truncate(0,M)
presentation M
-- works
-- the following does not work:

restart
load "KoszulFunctor.m2"
kk=ZZ/101
L = {1,1,1,3}
S=kk[x_0..x_(#L-1),Degrees=>L]
irr=ideal vars S
addTateData(S,irr)
E = S.exterior

M= S^1/ideal(x_0,x_2)
M1= (S^{1}/ideal(x_1,x_2))
M = M++M1
M = M**S^{{5}}
--M = S^1/ideal(x_0,x_2)

LL=apply(toList(-10..10),i->S.degOmega+{i})
elapsedTime betti(TM=RRFunctor(M,LL))
TB=beilinsonWindow(TM,-S.degs)
TB.dd_1
BM = bigChainMap TB;
--BM=altDMonad(TB)
prune DMHH BM
presentation truncate(0,M)
presentation M
-- the following does not work:
restart
load "KoszulFunctor.m2"
kk=ZZ/101
L = {1,1,2}
S=kk[x_0..x_(#L-1),Degrees=>L]
irr=ideal vars S
addTateData(S,irr)
E = S.exterior

M= S^1/ideal(x_2)

M1= (S^{1}/ideal(x_0+3*x_1))
M = M++M1
M = S^{1}**M
--M = S^1/ideal(x_0,x_2)

LL=apply(toList(-10..10),i->S.degOmega+{i})
elapsedTime betti(TM=RRFunctor(M,LL))
--elapsedTime betti(TM=RRFunctor(M1,LL))
TB=beilinsonWindow(TM,-S.degs)
betti TB
TB.dd_1
BM = bigChainMap TB
betti source BM
values(S.complexes)/betti
H = DMHH BM
presentation truncate(0,M)
presentation M

radical ann(H#0)
ann M
 
sum(4, i-> (i+1)*betti(S.complexes#{3-i}))



///--there!
restart
load "KoszulFunctor.m2"
kk=ZZ/101
L = {1,1,1}
S=kk[x_0..x_(#L-1),Degrees=>L]
irr=ideal vars S
addTateData(S,irr)
E = S.exterior

M= S^1/ideal(x_2)
M = S^{1}**M
--M1= (S^{1}/ideal(x_0+3*x_1))
--M = M++M1
--M = S^1/ideal(x_0,x_2)


LL=apply(toList(-10..10),i->S.degOmega+{i})
elapsedTime betti(TM=RRFunctor(M,LL,true))
TM.dd_1
--elapsedTime betti(TM=RRFunctor(M1,LL))
TB=beilinsonWindow(TM,-S.degs)
--CHANGED BACK TO -S.degs!!
betti TB
TB.dd_1
BM = bigChainMap TB
assert(BM*(BM[1])==0)

betti target BM
betti source BM
(source BM).dd
(target BM).dd

DMHH = B -> HH horHom B
D = DMHH BM
viewHelp GradedModule
B = BM
rank D
horHom BM    
ker (BM[-1])
values(S.complexes)/betti
H = DMHH BM
DMHHalt BM
--  The "alt" version seems to get the shift more correct, but the twist is still off

presentation truncate(0,M)
--Twist off by 1


restart
load "KoszulFunctor.m2"
kk=ZZ/101
L = {1,1,1}
S=kk[x_0..x_(#L-1),Degrees=>L]
irr=ideal vars S
addTateData(S,irr)
E = S.exterior
M = S^{3}/ideal(x_0^3+2*x_1^3+3*x_2^3)
LL = toList(-5..5)
elapsedTime betti(TM=RRFunctor(M,LL,true))
TB=beilinsonWindow(TM,-S.degs)
betti TB
TB.dd_1
BM = bigChainMap TB
betti source BM
DMHHalt BM
presentation truncate(-2,M)
--  Twist is off, but I also don't know why these aren't these are the same
*-

DMonad = method()

DMonad(List,Ring) := (di,S) -> (
    -- Input: di degree of a monomial in E
    --        
    -- Output: a ChainComplex
    --         perhaps twist and shift are not right 
    d:= drop(di,-1);
    i:=last di;
    cplx:=(S.complexes#d)[i]) -- maybe [i]

DMonad(Sequence,Ring) := (dm,S) -> (
    -- Input: dm a pair of a degree d and a exterior monomial m;
    --        is a key od S.phis
    -- Output: phi a map of chainComplex --
    --         perhaps twist and shift are not right 
    d:= dm_0;
    m:= dm_1;
    i:=last degree m;
    phi:=(S.phis#dm)[i]) -- maybe [i]

-*
TEST  ///
restart
load "KoszulFunctor.m2"
kk=ZZ/101
L = {1,1,2}
S=kk[x_0..x_(#L-1),Degrees=>L]
irr=ideal vars S
addTateData(S,irr)
d=(keys S.complexes)_1    
i=0
di=append(d,i)
cplx=DMonad(di,S)
use S.exterior
dm=(d,e_1)
d=first dm
d1=d-drop(degree dm_1,-1)
betti S.complexes#d, betti S.complexes#d1
di=append(d,i)
phi=DMonad(dm,S)
betti target phi,betti source phi
d1i=append(d1,i+1)
cplx1=DMonad(d1i,S)
betti cplx, betti cplx1
phi1=map(cplx,cplx1,q->map(cplx_q,cplx1_q,phi_q))
phi2=map(cplx,cplx1,q->phi_q)
phi1==phi2
f=dm_1+2*e_0
entry(f,di,S)
apply(values S.phis,phi->(betti target phi,betti source phi))
keys S.phis
///
*-




 
DMonad(ChainComplex,Ring) := (TM, S) -> (
    -- Input: DTate = Tate res as diff module
    -- S polynomial ring
    --degs "relevant" degrees: in general 
    --the degrees corresponding to a full exceptional sequence would be best.
    --calls on: cplx, a hash table of complexes corresponding to the relevant degrees.
    --sortedMons: a hash table of the monomials in the exterior algebra.
    --these two should be cached.
    if not S.?complexes then error"ring needs ToricTateData; use addTateData(S,irr)";
    --cplx := S.complexes;
--   
-- DTate=TM
    TB := beilinsonWindow(TM,S.degs);
    tot := directSum apply(degrees TB_0,d->DMonad(d,S));
--betti tot
    tot1 := directSum apply(degrees TB_1,d->DMonad(d,S));
--    betti tot,betti tot1
    Lphi:= apply(rank TB_0,i-> apply(rank TB_1,j-> (
--(i,j)=(0,1)	
	     di := (degrees TB_0)_i; -- degree of i-th row
	     di1 := (degrees TB_1)_j; -- degree of j-th col
--di, di1
	     ee := TB.dd_1_(i,j); --(i,j) entry, as an element of E
--ee, di, degree ee, di1, degree TB_1_j
--S^(drop(di,-1)), 
	     ff := entry(ee,di,S); --map of complexes corresponding to ee.

--ff)))
	     --probably correct except when ee == 0.
--TB.dd,	    ee, ff	     
--DMonad(-di,S), 
--DMonad(-di1,S)
	     (map(DMonad(di,S),DMonad(di1,S),q->
		     if class ff === ZZ then 0 else ff_q)) -- possibly wrong twist.
-*
di,di1
q=2
ff
betti target ff, betti source ff
betti DMonad(di,S), betti DMonad(di1,S)
map(
    betti (DMonad(di,S))_q, betti (DMonad(di1,S))_q,betti ff_q 
    )
*-          
   )));
    map(tot,tot1,p->matrix apply(rank TB_0,i-> apply(rank TB_1,j-> (Lphi_i_j)_p)))
)
-*
DMHH=method()
DMHH(ChainComplexMap) := BM ->( 
    BBM:= BM[1]; 
    prune HH coker( 
    map(ker BM, source BBM, i->BBM_i//inducedMap(target BBM_i,ker BM_i)))
)

-- Daniel:  I tried a different shift here which seems to work better.
DMHHalt=method()
DMHHalt(ChainComplexMap) := BM ->( 
    BM = BM[-1]; 
    prune HH coker( 
    map(ker BBM, source BM, i->BM_i//inducedMap(target BM_i,ker BBM_i)))
)
*-
-*
TEST ///


restart
load "KoszulFunctor.m2"
kk=ZZ/101
L = {1,1,2}
S=kk[x_0..x_(#L-1),Degrees=>L]

irr=ideal vars S
addTateData(S,irr)
restart
load "KoszulFunctor.m2"
kk=ZZ/101
L = {1,1,2}
S=kk[x_0..x_(#L-1),Degrees=>L]
irr=ideal vars S
addTateData(S,irr)
E=S.exterior

M= S^1/ideal(x_0)**S^{{-10}}
LL=apply(toList(-10..10),i->S.degOmega+{i})
elapsedTime betti(TM=RRFunctor(M,LL))
DTate=TM
TM.dd
TB=beilinsonWindow(TM,-S.degs)
betti TB
degrees TB_0
TB.dd_1
degrees TB_1
BM=altDMonad TB
DMHH BM
betti res truncate(0,M)

ijs=flatten apply(rank TB_0,i->apply(rank TB_1,j->(i,j)))
nonzeroijs=select(ijs,ij->TB.dd_1_ij!=0)
apply(nonzeroijs,ij->(i=ij_0;(degrees TB_0)_i))
neededKeys=apply(nonzeroijs,ij->(i=ij_0;(drop((degrees TB_0)_i,-1),TB.dd_1_ij)))
apply(neededKeys,dm->S.phis#dm)

TB.dd
isHomogeneous TB.dd
netList degrees TB_0,netList degrees TB_1
BM=DMonad(TB,S)
(drop(di,-1),m)
betti tot, betti tot1
tot1==tot[1]
(di,m)
keys S.phis
TB_0
degrees oo
d
cplx#(-1)
DMHH BM


///
*-


-*
restart
load"KoszulFunctor.m2"
needsPackage "NormalToricVarieties"
--viewHelp NormalToricVarieties
P112 = weightedProjectiveSpace{1,1,2}

--ToricRingWithTateData = new type of MutableHashTable


kk=ZZ/101
L = {1,1,2}
S=kk[x_0..x_(#L-1),Degrees=>L]
irr = ideal vars S
addTateData(S,irr)
S.irr
S.exterior
S.sortedMons
S.complexes

values cplx/betti
    

K=koszul vars S
irr=ideal vars S
E=dualRingToric S
sortedMons=sortedMonomials E
cplx = cacheComplexes(S)
values cplx/betti
M=S^1/ideal(x_0)
LL=apply(10,i->{i})
T=RRFunctor(M,LL)
isHomogeneous T
T.dd
keys cplx
TB=beilinsonWindow(T,-keys cplx)

netList degrees target TB.dd_1,netList degrees source TB.dd_1
isHomogeneous TB.dd_1
es=(entries concatMatrices values sortedMons)_0
phis=cachePhi(S,irr)

*-



end--


















restart
load"KoszulFunctor.m2"
kk=ZZ/101
L = {1,1,2,3,4}
S=kk[x_0..x_(#L-1),Degrees=>L]
irr=ideal vars S
E=kk[e_0..e_(numgens S - 1),SkewCommutative=>true,Degrees=>-degrees S ]
K=koszul vars S
sortedMons = sortedMonomials E
es=drop((entries concatMatrices values sortedMons)_0,1)
-- derived category should have O(d) with d in - reverse {0,1,.., sum(L)-1}
-- as natural generators (basis?)
degs=apply(sum L,i->{-i})

possiblePairs = select(flatten apply(degs,d->apply(es,m -> (d,m))), dm-> member(dm_0+degree dm_1,degs)) 
#oo
netList (allPhi=apply(possiblePairs,dm->(
	d=dm_0;m=dm_1;
	phi=completeToMapOfChainComplexes(K,m,Complete => false);
	(dm,degreeTruncation(phi,-d)[-factors(m,sortedMons)]**S^{-d})))) 



phis= new HashTable from allPhi;
netList (composablePhis = select(
    apply(keys phis,dm->(dm,select(keys phis, dm' -> dm'_0==dm_0+degree dm_1))),
      dmL->#dmL_1 >0));
netList (composablePhis1=flatten apply(composablePhis,ab->(a=ab_0;apply(ab_1,b->(a,b)))))
netList apply(composablePhis1,ab->(ab,phis#(ab_0),phis#(ab_1)));
netList apply(composablePhis1,ab->(ab,betti source phis#(ab_0), min source phis#(ab_0),betti target phis#(ab_1), min target phis#(ab_1)))
oks= select(composablePhis1,ab->betti source phis#(ab_0)==betti target phis#(ab_1)[factors(ab_1_1,sortedMons)])
notOks=  select(composablePhis1,ab->betti source phis#(ab_0)=!=betti target phis#(ab_1)[factors(ab_1_1,sortedMons)])
(#oks,#notOks)


all(oks,ab->
    (phis#(ab_0)*(phis#(ab_1)[factors(ab_1_1,sortedMons)])==0 and ab_0_1*ab_1_1==0) or 
	(phis#(ab_0)*(phis#(ab_1)[factors(ab_1_1,sortedMons)])=!=0 and ab_0_1*ab_1_1=!=0))
use E
nonTrivialOks=select (oks,ab->ab_0_1*ab_1_1 !=0)
minusNonTrivialOks=select(nonTrivialOks,ab->(
	pos=positions(apply(keys phis,k->k_1),m->m==-(ab_0_1*ab_1_1));
	#pos>0));
plusNonTrivialOks=select(nonTrivialOks,ab->(
	pos=positions(apply(keys phis,k->k_1),m->m==(ab_0_1*ab_1_1));
	#pos>0));

all(minusNonTrivialOks,ab->(
--	ab=minusNonTrivialOks_8
	pos=positions(apply(keys phis,k->k_1),m->m==-(ab_0_1*ab_1_1));
	k=first select((keys phis)_pos,k->k_0==ab_0_0);
	AB=(phis#(ab_0)*(phis#(ab_1)[factors(ab_1_1,sortedMons)]));
	K = -phis#k[factors(ab_1_1,sortedMons)];
        assert(target AB== target K and source AB==source K );
	AB==K or AB==-K))
all(plusNonTrivialOks,ab->(
--	ab=minusNonTrivialOks_8
	pos=positions(apply(keys phis,k->k_1),m->m==(ab_0_1*ab_1_1));
	k=first select((keys phis)_pos,k->k_0==ab_0_0);
	AB=(phis#(ab_0)*(phis#(ab_1)[factors(ab_1_1,sortedMons)]));
	K = phis#k[factors(ab_1_1,sortedMons)];
        assert(target AB== target K and source AB==source K );
	AB==K or AB==-K))
all(nonTrivialOks,ab->(
--	ab=minusNonTrivialOks_8
	pos=positions(apply(keys phis,k->k_1),m->m==(ab_0_1*ab_1_1) or m==-(ab_0_1*ab_1_1));
	k=first select((keys phis)_pos,k->k_0==ab_0_0);
	AB=(phis#(ab_0)*(phis#(ab_1)[factors(ab_1_1,sortedMons)]));
	K = phis#k[factors(ab_1_1,sortedMons)];
        assert(target AB== target K and source AB==source K );
	AB==K or AB==-K))	
-- above is a working case 





restart
load "KoszulFunctor.m2"
--debug needsPackage "TateOnProducts"
--Hirzebruch S(2,0)xPP(1,2)
kk=ZZ/101
S=kk[x_0..x_5,Degrees=>{{1,0,0},{1,2,0},2:{0,1,0},{0,0,1},{0,0,2}}]
irr=ideal(x_0,x_1)*ideal(x_2,x_3)*ideal(x_4,x_5)
degrees S
E=kk[e_0..e_5,SkewCommutative=>true,Degrees=>-degrees S ]
K=koszul vars S
sortedMons = sortedMonomials E
(i,j) = (3,10)
m=sortedMons#i_{j}_(0,0)
M=K.dd_i_{j}
d=-degree m

F=source degreeTruncation(K,d)
F=source degreeTruncation(K,{1,1,1})
netList tallyComplex F, netList (tallyComplex K)_{0..5}
annHH F
relevantAnnHH (F,irr)
prune HH_2 F
primaryDecomposition ann HH_2 F
irr
dimHH F
n=numgens S
es=(entries concatMatrices values sortedMons)_0

netList select(apply(es,m->(
  F=source degreeTruncation(K,-degree m);
  (m,-degree m,T = tally select(relevantAnnHH(F,irr), I -> I != ideal 1_S and I != ideal 0_S)))),
p -> #(keys p_2 )>0)

netList (nonTrivList=unique select(apply(es,m->(
  F=source degreeTruncation(K,-degree m);
  (-degree m,T = 
      tally select(relevantAnnHH(F,irr), 
	  I -> I != ideal 1_S),betti F))),
p -> #(keys p_1 )>0))
nonTrivDegs=sort apply(nonTrivList,c->c_0)
#nonTrivDegs
netList apply(nonTrivDegs,d->(F=source degreeTruncation(K,d);
	(d,prune HH F)))
degES=sort unique apply(es,m->-degree m)   
trivDegs = select(degES,d->not member(d,nonTrivDegs))
netList apply(trivDegs,d->(F=source degreeTruncation(K,d);
	(d,prune HH F)))

source degreeTruncation(K,{3,3,2})==source degreeTruncation(K,{2,3,2})
F=source degreeTruncation(K,d);(d,prune HH F)
relevantAnnHH(F,irr)



phi=completeToMapOfChainComplexes(K,m,Complete => true)

isHomogeneous phi

d=-degree m
e = d-{0,0,1} --- e = d + {0,0,1} works too
G=target phi
F= source phi
phiF = degreeTruncation(F,d)
F' = source (phiF = degreeTruncation(F,e))
G' = source (phiG = degreeTruncation(G,e))
F ==F'

map(G', F', i->(phi_i * phiF_i)// phiG_i)




--------------
--weighted proj L
restart
load "KoszulFunctor.m2"
kk=ZZ/101
L = {1,1,2}
S=kk[x_0..x_(#L-1),Degrees=>L]
degrees S
irr=ideal vars S
E=kk[e_0..e_(numgens S - 1),SkewCommutative=>true,Degrees=>-degrees S ]
K=koszul vars S
sortedMons = sortedMonomials E
d = {2}
F=source degreeTruncation(K,d)
netList tallyComplex F, netList (tallyComplex K)_{0..numgens S}
annHH F
relevantAnnHH (F,irr)
prune HH F
n=numgens S
es=(entries concatMatrices values sortedMons)_0

netList (relEs=select(apply(es,m->(
  F=source degreeTruncation(K,-degree m);
  (m,-degree m,T = tally select(relevantAnnHH(F,irr), I -> I != ideal 1_S)))),
p -> #(keys p_2 )>0))
relDegs=apply(relEs,m->-degree m_0)
degs=apply(3,i->{i})

netList (relHH=unique apply(degs,d->(
  F=source degreeTruncation(K,d);(d,prune HH F))))





----------------- Example: The stacky point on P(1,1,2)
restart
load"KoszulFunctor.m2"
kk=ZZ/101
L = {1,1,2}
S=kk[x_0..x_(#L-1),Degrees=>L]
irr=ideal vars S
E=kk[e_0..e_(numgens S - 1),SkewCommutative=>true,Degrees=>-degrees S ]
K=koszul vars S
sortedMons = sortedMonomials E
es=(entries concatMatrices values sortedMons)_0

use S 
M= S^{{-7}}/ideal(x_0,x_1)
lows={{0}}
c=5
degs = apply(4, i->{-i})

elapsedTime betti(TM=RRFunctor(M,E,lows,c))
T=TM**E^{{12}}
T=TM
tally degrees T_0
tally degrees T_1

TB=beilinsonWindow(T,degs)

betti TB, betti T
TB.dd_1^2
TB.dd
netList (apply(degs,d->betti source degreeTruncation(K,-d)[0]))

cplxes=new HashTable from (    
    apply(es,m-> (i := #factor sub(m,vars S);
	(m,source degreeTruncation(K,-degree m)[i]))))

use E
m = e_2
phi=degreeTruncation(completeToMapOfChainComplexes(K,e_2,Complete => true), {0})[-factors(m,sortedMons)]
phi=phi**S^{{-5}}
tot = source phi++target phi
betti tot, betti source phi, betti target phi
BM = map(tot, tot, i-> matrix{{0*id_(source phi_i),map(source phi_i, target phi_i, 0)},
	       {phi_i,0*id_(target phi_i)}})
BM *BM       
prune HH coker map(ker BM, source BM, i->BM_i//inducedMap(target BM_i,ker BM_i))
BM

BM'=BM**S^{{-5}}
prune HH coker map(ker BM', source BM', i->BM'_i//inducedMap(target BM'_i,ker BM'_i))
M
betti(target phi**S^{{-5}}), betti(source phi**S^{{-5}})
-- upt to twist korrekt!
betti (tot**S^{{-5}})
betti source BM'


----------------- Example: a smooth point on P(1,1,2) -- correct up to tist and shift
restart
load"KoszulFunctor.m2"
kk=ZZ/101
L = {1,1,2}
S=kk[x_0..x_(#L-1),Degrees=>L]
irr=ideal vars S
E=kk[e_0..e_(numgens S - 1),SkewCommutative=>true,Degrees=>-degrees S ]
K=koszul vars S
sortedMons = sortedMonomials E
es=(entries concatMatrices values sortedMons)_0

use S 
M= S^{{2}}/ideal(x_0,x_2)
lows={{0}}
c=6
degs = apply(sum L, i->{-i})

elapsedTime betti(TM=RRFunctor(M,E,lows,c))
T=TM**E^{{10}}
tally degrees T_0
tally degrees T_1

TB=beilinsonWindow(T,degs)

betti TB, betti T
TB.dd_1^2
TB.dd
netList (apply(degs,d->betti source degreeTruncation(K,-d)))

cplxes=new HashTable from (    
    apply(es,m-> (i := #factor sub(m,vars S);
	(m,source degreeTruncation(K,-degree m)[i]))))
use E
cplxes#(e_0).dd
cplxes#(e_1).dd

use E
m = e_1
phi0=degreeTruncation(completeToMapOfChainComplexes(K,m,Complete => true), {0})[-3]--[-factors(m,sortedMons)]
phi1=degreeTruncation(completeToMapOfChainComplexes(K,m,Complete => true), {1})[-2]**S^{{1}}--[-factors(m,sortedMons)]
phi2=degreeTruncation(completeToMapOfChainComplexes(K,m,Complete => true), {2})[-1]**S^{{2}}--[-factors(m,sortedMons)]

phi0*phi1, phi1*phi2

TB.dd
netList {source phi0, target phi0},netList {source phi1, target phi1}, netList  {source phi2, target phi2},
netList {target phi0, source phi1, source phi2}
source phi0==target phi1, source phi1==target phi2 
tot = source phi2 ++ source phi1 ++ source phi0++ target phi0
netList (reverse {source phi2,source phi1,source phi0,target phi0}/betti)
betti tot
BM = map(tot, tot, i-> matrix{
{0*id_(source phi2_i), map(source phi2_i, source  phi1_i, 0), map(source phi2_i, source phi0_i, 0), map(source phi2_i, target phi0_i, 0)},
   {phi2_i,            map(source phi1_i, source  phi1_i, 0), map(source phi1_i, source phi0_i, 0), map(source phi1_i, target phi0_i, 0)},
{map(source phi0_i, source  phi2_i, 0), phi1_i,               map(source phi0_i, source phi0_i, 0), map(source phi0_i, target phi0_i, 0)},
{map(target phi0_i, source  phi2_i, 0), map(target phi0_i, source phi1_i, 0),       phi0_i,         map(target phi0_i, target phi0_i, 0)}
})      

A=apply(toList(-3..0), i-> 
matrix{{0*id_(source phi2_i), map(source phi2_i, source  phi1_i, 0), map(source phi2_i, source phi0_i, 0), map(source phi2_i, target phi0_i, 0)},
   {phi2_i,            map(source phi1_i, source  phi1_i, 0), map(source phi1_i, source phi0_i, 0), map(source phi1_i, target phi0_i, 0)},
{map(source phi0_i, source  phi2_i, 0), phi1_i,               map(source phi0_i, source phi0_i, 0), map(source phi0_i, target phi0_i, 0)},
{map(target phi0_i, source  phi2_i, 0), map(target phi0_i, source phi1_i, 0),       phi0_i,         map(target phi0_i, target phi0_i, 0)}}
)      

BM

BM * BM == 0       
prune HH coker map(ker BM, source BM, i->BM_i//inducedMap(target BM_i,ker BM_i)) 
DMHH BM
presentation M -- homological degree and twist have to be adapted

betti tot
BM'=BM**S^{{-1}}
TB.dd


netList (reverse {source phi2**S^{{-1}},source phi1**S^{{-1}},source phi0**S^{{-1}},target phi0**S^{{-1}}}/betti)
betti source BM'

netList (apply(degs,d->(d,betti (source degreeTruncation(K,-d)[ -sum L- sum d+1]**S^{-d-{1}}))))              
,           	netList (reverse {source phi2**S^{{-1}},source phi1**S^{{-1}},source phi0**S^{{-1}},target phi0**S^{{-1}}}/betti)
betti source BM'

cplx=new HashTable from apply(degs,d->
    (d,source degreeTruncation(K,-d)[ -sum L- sum d+1]**S^{-d-{1}})) 
             
netList (values cplx/betti)
apply(degrees source TB.dd_1,d1->d1-degree e_1)
apply(drop(degrees source TB.dd_1,-1),d1->d1-degree e_1)==drop(degrees target TB.dd_1,1)
degree (e_1*e_2)
es/degree

degrees source TB.dd_1 
TB.dd
DMHH BM'
betti target BM'
M
prune HH coker map(ker BM', source BM', i->BM'_i//inducedMap(target BM'_i,ker BM'_i)) 
M
netList (reverse {source phi2,source phi1,source phi0,target phi0}/betti)
betti tot


-------- On a general weighted projective space
restart
load"KoszulFunctor.m2"
kk=ZZ/101
L = {1,1,2,3,4}
S=kk[x_0..x_(#L-1),Degrees=>L]
irr=ideal vars S
E=kk[e_0..e_(numgens S - 1),SkewCommutative=>true,Degrees=>-degrees S ]
K=koszul vars S
sortedMons = sortedMonomials E
es=drop((entries concatMatrices values sortedMons)_0,1)
-- derived category should have O(d) with d in - reverse {0,1,.., sum(L)-1}
-- as natural generators (basis?)
degs=apply(sum L,i->{-i})

possiblePairs = select(flatten apply(degs,d->apply(es,m -> (d,m))), 
                                   dm-> member(dm_0+degree dm_1,degs)) 
#oo
netList (allPhi=apply(possiblePairs,dm->(
	d=dm_0;m=dm_1;
	phi=completeToMapOfChainComplexes(K,m,Complete => false);
	(dm,degreeTruncation(phi,-d)[-factors(m,sortedMons)]**S^{-d})))) ;


-*
each degree corresp to a complex. 
We need only these: 0..-omega+1 --> complex (Beilinson window).

each monomial m in E corresponds to maps of complex 
from a deg to that degree + weighted deg m,
shifted by the number of factors of m. 

To compose two composable maps, corresp to phis#m *phis#n
you have to shift the second complex by the number of factors of n.
*-
phis= new HashTable from allPhi;
netList (composablePhis = select(
    apply(keys phis,dm->(dm,select(keys phis, dm' -> dm'_0==dm_0+degree dm_1))),
      dmL->#dmL_1 >0));
netList (composablePhis1=flatten apply(composablePhis,ab->(a=ab_0;apply(ab_1,b->(a,b)))))
netList apply(composablePhis1,ab->(ab,phis#(ab_0),phis#(ab_1)));
netList apply(composablePhis1,ab->(ab,betti source phis#(ab_0), min source phis#(ab_0),betti target phis#(ab_1), min target phis#(ab_1)));
oks= select(composablePhis1,ab->betti source phis#(ab_0)==betti target phis#(ab_1)[factors(ab_1_1,sortedMons)])
notOks=  select(composablePhis1,ab->betti source phis#(ab_0)=!=betti target phis#(ab_1)[factors(ab_1_1,sortedMons)])
(#oks,#notOks)


all(oks,ab->
    (phis#(ab_0)*(phis#(ab_1)[factors(ab_1_1,sortedMons)])==0 and ab_0_1*ab_1_1==0) or 
	(phis#(ab_0)*(phis#(ab_1)[factors(ab_1_1,sortedMons)])=!=0 and ab_0_1*ab_1_1=!=0))
use E

nonTrivialOks=select (oks,ab->ab_0_1*ab_1_1 !=0); -- wedge product not 0

minusNonTrivialOks=select(nonTrivialOks,ab->(
	pos=positions(apply(keys phis,k->k_1),m->m==-(ab_0_1*ab_1_1));
	#pos>0));

plusNonTrivialOks=select(nonTrivialOks,ab->(
	pos=positions(apply(keys phis,k->k_1),m->m==(ab_0_1*ab_1_1));
	#pos>0));

all(minusNonTrivialOks,ab->(
--ab=minusNonTrivialOks_9
	pos=positions(apply(keys phis,k->k_1),m->m==-(ab_0_1*ab_1_1));
	k=first select((keys phis)_pos,k->k_0==ab_0_0);
	AB=(phis#(ab_0)*(phis#(ab_1)[factors(ab_1_1,sortedMons)]));
	K = -phis#k[factors(ab_1_1,sortedMons)];
        assert(target AB== target K and source AB==source K );
	AB==K or AB==-K))

all(plusNonTrivialOks,ab->(
--	ab=minusNonTrivialOks_8
	pos=positions(apply(keys phis,k->k_1),m->m==(ab_0_1*ab_1_1));
	k=first select((keys phis)_pos,k->k_0==ab_0_0);
	AB=(phis#(ab_0)*(phis#(ab_1)[factors(ab_1_1,sortedMons)]));
	K = phis#k[factors(ab_1_1,sortedMons)];
        assert(target AB== target K and source AB==source K );
	AB==K or AB==-K))

all(nonTrivialOks,ab->(
--	ab=minusNonTrivialOks_8
	pos=positions(apply(keys phis,k->k_1),m->m==(ab_0_1*ab_1_1) or m==-(ab_0_1*ab_1_1));
	k=first select((keys phis)_pos,k->k_0==ab_0_0);
	AB=(phis#(ab_0)*(phis#(ab_1)[factors(ab_1_1,sortedMons)]));
	K = phis#k[factors(ab_1_1,sortedMons)];
        assert(target AB== target K and source AB==source K );
	AB==K or AB==-K))	
	
	


-- above is a working case 


    


--jetsum
TEST///
restart
load "KoszulFunctor.m2"
kk=ZZ/101
S=kk[x_0..x_5,Degrees=>{{1,0,0},{1,2,0},2:{0,1,0},{0,0,1},{0,0,2}}]
irr=ideal(x_0,x_1)*ideal(x_2,x_3)*ideal(x_4,x_5)
--(S,irr) is the Toric variety correpondingto the product of S(3,1) x P(1,2)
-- a Hirzebruch surface times a weighted projective line

degrees S
E=kk[e_0..e_5,SkewCommutative=>true,Degrees=>-degrees S ]
K=koszul vars S
sortedMons = sortedMonomials E

(i,j) = (3,4)
m=sortedMons#i_{j}_(0,0)
d=-degree m


phi = degreeTruncation(K,d)
lK=source phi
       
lK.dd^2
HlK=HH lK
prune HlK#1
prune HlK#2
prune HlK#3
uK=degreeTruncationAbove(K,d)
lK
HuK=HH uK
netList apply(toList(2..6),i->prune HuK#i)
source degreeTruncation(K,{0,0,0})

for i from 0 to numgens S do(
    for j from 0 to binomial(numgens S, i)-1 do(
m = sortedMons#i_{j}_(0,0);
d = -degree m;
lK = source degreeTruncation(K,d);
HlK = HH lK;
H := apply(toList(0..length lK-1),ell->prune HlK#ell);
<<(i,m)<<" "<<positions(H, h-> h!=0)<<" "<<endl<<flush;
))


degsK=sort unique flatten apply(length K+1,i->degrees K_i)
netList( L=apply(degsK,d->(g=degreeTruncation(K,d);
    (d,betti target g,betti source g)) ))
tally apply(L,c->c_1)
netList(L1=apply(L,c->(c_0,c_2)))
netList(L2=apply(degsK,d->(d,source degreeTruncation(K,d)) ))
netList apply(L2,F->prune HH F_1) 
netList apply(L2,dF->(F=dF_1;tally apply(length F+1,i-> 
	    saturate(ann prune HH_i F, irr))))
L3=select(L2,dF->(F=dF_1;#tally apply(length F+1,i-> 
	    saturate(ann prune HH_i F, irr))>1));
#L3
netList (L3HH=apply(L3,dF -> (F=dF_1;d=dF_0;
	homologicalDegs=select(length F+1,i->
	    saturate(ann prune HH_i F, irr)!=ideal(1_S));
	(d,betti F,apply(homologicalDegs,i->(h=prune HH_i F;
		(i,h,betti h)))) )))

tally apply(L3HH,c->#c_2)
cplx = new HashTable from L3

keys cplx

--NOTE: there's always 0th homology;
-- but the other homology degrees seem to form a 
-- consecutive sequence.
-- Why??
///

 -*
RRFunctor = method();
RRFunctor(Module,Ring,List,ZZ) := (M,E,lows,c) ->(
    S :=ring(M);
    M1 := prune coker presentation M;
    relationsM := gens image presentation M1;
    numvarsE := numgens E;
    ev := map(E,S,vars E);
    range := degreeSetup(S,lows,c);
    alldegs:= range#0; newdegs:={};
    scan(toList(1..c),i->(newdegs = select(range#i,d->not member(d,alldegs));
	    alldegs=alldegs|newdegs));
    bases := concatMatrices apply(alldegs,d->basis(d,M));
    bases1 =map(S^(degrees target bases),, lift(bases,S));

    kk:=coefficientRing S;
    SE := kk[gens S|gens E,Degrees=>degrees S|degrees E];
    tr := sum(dim S, i-> SE_i*SE_(dim S+i));
    baseTr := map(SE^(degrees target bases1),,tr*sub(bases1,SE));
--netList apply(baseTr,m->(isHomogeneous m,degrees target m,degrees source m,m))
    relationsMinSE := sub(relationsM,SE);
--isHomogeneous relationsMinSE
    reducedBaseTr:= baseTr % relationsMinSE;
    F = E^(-degrees source bases1);
    multTable :=matrixContract(transpose sub(bases1,SE),reducedBaseTr);
    F:= E^(-degrees source bases1);
    chainComplex map(F,F, sub(multTable,E))
    )
*-
-* TEST ///
restart
load "KoszulFunctor.m2"

kk=ZZ/101
S=kk[x_0..x_2,Degrees=>{{1,0},{1,2},{0,1}}]
degrees S
E=kk[e_0..e_2,SkewCommutative=>true,Degrees=>-degrees S ]
M=S^1
c=3
lows={{3,3}}

TM=RRFunctor(M,E,lows,c)
TM.dd^2
TM.dd_1


restart
load "KoszulFunctor.m2"

kk=ZZ/101
S=kk[x_0..x_2,Degrees=>{2:{1},{2}}]
degrees S
E=kk[e_0..e_2,SkewCommutative=>true,Degrees=>-degrees S ]
M=truncate({1},S^1)
c=2
lows={{0}}

TM=RRFunctor(M,E,lows,c)
assert(isHomogeneous TM)
assert((TM.dd_1)^2==0)
TM.dd_1
betti TM

///*-

///
--simplest bad example?
--line in PP^2
restart
load "KoszulFunctor.m2"
kk=ZZ/101
L = {1,1,1}
L = {1,1}
S=kk[x_0..x_(#L-1),Degrees=>L]
irr=ideal vars S
addTateData(S,irr)
E = S.exterior

M= S^1/ideal(x_0^2)
M = S^{1}**M
betti res M
M = S^{1}
--M1= (S^{1}/ideal(x_0+3*x_1))
--M = M++M1
--M = S^1/ideal(x_0,x_2)


LL=apply(toList(-10..10),i->S.degOmega+{i})
elapsedTime betti(TM=RRFunctor(M,LL,true))
TM.dd_1
--elapsedTime betti(TM=RRFunctor(M1,LL))
TB=beilinsonWindow(TM,-S.degs)
betti TB
TB.dd_1
BM = bigChainMap TB
assert(BM*(BM[1])==0)

betti target BM
betti source BM
(source BM).dd
(target BM).dd

horHom BM    
ker (BM[-1])
values(S.complexes)/betti
H = DMHH BM
presentation M
S.complexes


