-*
exports {
    "addTateData",
    "dualRingToric",
    "RRFunctor",
    "sortedMonomials",
    "positionInKoszulComplex",
    "dualElement",  --keep.
    "addZeroTerms", -- drop.
    "completeToMapOfChainComplexes", -- might use addTerms in an option.  drop "true" option and option altogether?
    "greaterEqual",
    "strictlyGreater",  --drop.
    "degreeTruncation",
    "isChainComplexMap", -- should be in the core of M2
    "degreeTruncationAbove", -- working from the other side, not tested
    "degreeSetup", -- get the degree range from a starting set of degrees
                   -- using c multiplications with variabels in S
    "strictDegreeTruncationAbove",  --drop.
    "concatMatrices",
    "matrixContract",
    "tallyComplex",
    "annHH", --drop
    "dimHH", --drop
    "relevantAnnHH",  --keep
    "beilinsonWindow",
    "factors", -- now superflous, because the last degree component in E
               -- give this information
    "entry", 
    "DMonad", --drop
    "cacheComplexes",
    "cachePhi",
    "diffModToChainComplexMaps",  
    "bigChainMap",
    "RRTable",
    "doubleComplexBM"	               
    }

*-
--load "TateDM.m2"
needs "IsIsomorphic.m2"

addTateData = method()
addTateData (Ring,Ideal) := (S,irr) ->(
    S.irr = irr;
    S.exterior = dualRingToric S;
    S.koszul = koszul vars S;
    S.degOmega = -(degrees S.koszul_(numgens S))_0;
    S.sortedMons = sortedMonomials S.exterior;
--    S.complexes = cacheComplexes S;
    S.complexes = cacheComplexes(S,true);
    S.phis = cachePhi S;
    S.degs = keys S.complexes;
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

isIsoWithMap = (A,B)->(
    S := ring A;
    H := Hom(A,B);
    Hp := prune H;
    pmap := Hp.cache.pruningMap;
    f := homomorphism(pmap*map(Hp,S^1, random(target presentation Hp,S^1)));
    t := if prune coker f == 0 then true else false;
    (t,f))

isHomogeneousIso = (A,B)->(
        if not isHomogeneous A and isHomogeneous B then error"inputs not homogeneous";
    	S := ring A;
	A1 := prune A;
	B1 := prune B;

	--handle the cases where one of A,B is 0
	isZA1 = A1==0;
	isZB1 = B1==0;	
    	if isZA1 =!= isZB1 then return false;
	if isZA1 and isZB1 then return true;

	-- from now on, A1 and B1 are nonzero
	dA := degree A1_*_0;
	dB := degree B1_*_0;
	df := dB-dA;
        H := Hom(A1,B1);       
	kk := ultimate(coefficientRing, ring A);
	sH := select(H_*, f-> degree f == df);
	if #sH ==0 then return false;
	g := sum(sH, f-> random(kk)*homomorphism matrix f);
	kmodule := coker vars S;
	gbar := kmodule ** g;
	if gbar==0  then return false;
--	error();
	(prune coker gbar) == 0 and prune ker g == 0
	)
isIso = isHomogeneousIso	

isLocalIso = (A,B)->(
    if isHomogeneous A and isHomogeneous B and
            all(A_*, a->degree a == degree(A_*_0)) and 
	    all(B_*, a->degree a == degree(B_*_0)) then
	return isHomogeneousIso(A,B);

	S := ring A; 
	kk := ultimate(coefficientRing, S);
	kmod := coker vars S;
	A1 := prune A;
	B1 := prune B;

--handle the cases where one of A,B is 0
	isZA1 = A1==0;
	isZB1 = B1==0;	
    	if isZA1 =!= isZB1 then return false;
	if isZA1 and isZB1 then return true;

--now we can assume both are nonzero
        H1 := Hom(A1,B1);      
	if #H1_* == 0 then return false;
	g1 := sum(H1_*, f-> random(kk)*(kmod**homomorphism matrix f));
	t1 = (prune coker g1 == 0);
	if t1 == false then return false else(
	    <<"there is a surjection arg1 -> arg2"<<endl;
            H2 := Hom(B1,A1);      
	    if #H2_* == 0 then return false;	    
	    g2 := sum(H2_*, f-> random(kk)*(kmod**homomorphism matrix f));
	    prune coker g2 == 0)
	)



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
--    E' := kk[e'_0..e'_(numgens E - 1),SkewCommutative=>true];
    bases:= apply(numgens E+1,i->(
    matrix{reverse (entries gens trim (ideal  vars E)^i)_0}));
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

completeToMapOfChainComplexes=method()
completeToMapOfChainComplexes(ChainComplex,RingElement) :=  (K,m) -> (
-- Input: m a monomial in \Lambda^i \subset E, 
--        K the KoszulComplex
-- Goal: map of complexes given by contraction with m
-- m: K_0 <- K_i the  map which maps m to 1 and the other generators to 0
-- complete this to a map
-- K <- K[i]**S^{deg m} of complexes
   S:= ring K;
   r:= length K;
   (i,j) := positionInKoszulComplex(K,S.sortedMons,m);
   stK := K[i]**S^{-drop(degree m,-1)}; --shifted twisted K
   assert(degrees source stK.dd_0_{j}==degrees K_0);
   phi0 := matrix{apply(rank stK_0,k->if k==j then 1_S else 0)};
   return extend(K,stK,phi0,Verify=>true);
)

completeToMapOfChainComplexes(Ring,RingElement) :=  (S,m) -> (
-- Input: m a monomial in \Lambda^i \subset E, 
--        K the KoszulComplex
-- Goal: map of complexes given by contraction with m
-- m: K_0 <- K_i the  map which maps m to 1 and the other generators to 0
-- complete this to a map
-- K <- K[i]**S^{deg m} of complexes
   K:= S.koszul;
   (i,j) := positionInKoszulComplex(K,S.sortedMons,m);
   stK := K[i]**S^{-drop(degree m,-1)}; --shifted twisted K
   stK.dd = (-1)^i*stK.dd;
   --assert(degrees source stK.dd_0_{j}==degrees K_0);
   phi0 := matrix{apply(rank stK_0,k->if k==j then 1_S else 0)};
   extend(K,stK,phi0,Verify=>true)
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
phi=completeToMapOfChainComplexes(K,m)
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
--Daniel: I think the first option (without the Ring as input) is irrelevant now.
greaterEqual(List,List) := (d1,d2) -> all(d1-d2,i->i>=0)
greaterEqual(List,List,Ring) := (d1,d2,S) -> hilbertFunction(d1-d2,S) != 0


strictlyGreater=method()
--Daniel: I think the first option (without the Ring as input) is irrelevant now.
strictlyGreater(List,List) := (d1,d2) -> all(d1-d2,i->i>=0) and d1!=d2
strictlyGreater(List,List,Ring) := (d1,d2,S) ->hilbertFunction(d1-d2,S) != 0 and d1!=d2
-*
TEST ///
greaterEqual({1,1},{0,1})==true
greaterEqual({1,0},{0,1}), {1,0}>{0,1}
greaterEqual({0,1},{1,0})==false
strictlyGreater({1,1},{0,1})==true
strictlyGreater({1,1},{1,1})
/// *-

degreeTruncation=method()
--  Daniel:  I think these are unnecessary now.  See below (input includes ring).
degreeTruncation(Matrix,List) := (M,d) -> (
    --rows and cols with degrees <= d.
    rows:= positions(degrees target M,d'-> greaterEqual(d,d'));
    columns:= positions(degrees source M,d'-> greaterEqual(d,d'));
    sourceInc := (id_(source M))_columns;
    targetInc := (id_(target M))_rows;    
    ((M^rows)_columns,targetInc,sourceInc)
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
degreeTruncation(ChainComplexMap,List) := (phi,d) -> (
    G := target phi;
    F := source phi;
    phiF := degreeTruncation(F,d);
    F' := source (phiF = degreeTruncation(F,d));
    G' := source (phiG = degreeTruncation(G,d));
    map(G', F', i->(phi_i * phiF_i)// phiG_i)
    )








--Daniel:  these are the ones we are using now.
degreeTruncation(Matrix,List,Ring) := (M,d,S) -> (
    --rows and cols with degrees <= d.
    rows:= positions(degrees target M,d'-> greaterEqual(d,d',S));
    columns:= positions(degrees source M,d'-> greaterEqual(d,d',S));
    sourceInc := (id_(source M))_columns;
    targetInc := (id_(target M))_rows;    
    ((M^rows)_columns,targetInc,sourceInc)
    )

degreeTruncation(ChainComplex,List,Ring) := (K,d,S) -> (
    --subcomplex where all rows and cols of differentials have degrees <= d.
    a := min K;
    Ka := K[a];
    L := apply(length Ka,i->degreeTruncation(Ka.dd_(i+1),d,S));
--    L := apply(toList(min(K[a]).. max(K[a])-1),i->degreeTruncation(Ka.dd_(i+1),d));    
    tKa:=chainComplex(apply(length Ka,i->L_i_0));
    phi := map(K,tKa[-a], i-> if i == a then L_(i-a)_1 else L_(i-a-1)_2);
    assert(isChainComplexMap phi);
    phi
    )


degreeTruncation(ChainComplexMap,List,Ring) := (phi,d,S) -> (
    G := target phi;
    F := source phi;
    phiF := degreeTruncation(F,d,S);
    F' := source (phiF = degreeTruncation(F,d,S));
    G' := source (phiG = degreeTruncation(G,d,S));
    map(G', F', i->(phi_i * phiF_i)// phiG_i)
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
    
    --needs fixing to work with toric varieties where the effective cone isn't the first quadrant?
    
    K := S.koszul;
--    koszulRange :=unique flatten apply(length K+1,i->degrees K_i);
    koszulRange :=apply(toList(0..-S.degOmega_0-1), i->{i});
--    zz := apply(#(degree S_0),i-> 0); 
--    koszulRange := drop(zz..-(S.degOmega),-1); --
    truncatedComplexes := new HashTable from apply(koszulRange, d-> 
	(d,source degreeTruncation(K,d,S)));
    relDegs:=select(koszulRange,d->
	#select(relevantAnnHH(truncatedComplexes#d,S.irr),j->j!=ideal 1_S)>0);
    new HashTable from apply(relDegs,d->(d,(truncatedComplexes#d)**S^{d}))
    ) 

--TESTING A NEW KOSZUL RANGE FUNCTION on 5/14/20

cacheComplexes(Ring, Boolean) := (S, X)-> (
    --TESTING
    K := S.koszul;
    koszulDegs := unique flatten apply(length K+1,i->degrees K_i);
    -- this is supposed to some sort of saturation of the koszul Degrees
    koszulRange = unique flatten flatten apply(koszulDegs, i->(
	    apply(koszulDegs,j-> toList(i..j)|toList(j..i))
	    ));
    truncatedComplexes := new HashTable from apply(koszulRange, d-> 
	(d,source degreeTruncation(K,d,S)));
    relDegs := koszulRange;
--    relDegs:=select(koszulRange,d->
--	#select(relevantAnnHH(truncatedComplexes#d,S.irr),j->j!=ideal 1_S)>0);
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
	phi := completeToMapOfChainComplexes(S.koszul,m);
--	phi := completeToMapOfChainComplexes(S,m);--uses shifted complex without changing sign of maps
	(dm,degreeTruncation(phi,d,S)[-factors(m, S.sortedMons)]**S^{d})))); 
    new HashTable from allPhi)
///
restart
load"KoszulFunctor.m2"

kk=ZZ/101
L = {1,1,2}
L = {1,3}
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
	phi := completeToMapOfChainComplexes(S.koszul,m);
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
--Output:  The differenial module RR(M) in degrees from L.

RRFunctor(Module,List) := (M,L) ->(
    --M is an S-module
    --LL a list of the degrees where the terms B^e of RR M might occur,
    --output is the strictly lower triangular map from sum_e B^e to itself
    S := ring(M);
    E := S.exterior;
    relationsM := gens image presentation M;
    numvarsE := rank source vars E;
    f0 := gens image basis(LL_0,M);
    scan(#LL-1,i-> f0 = f0 | gens image basis(LL_(i+1),M));
    --f0 is the basis for M in degrees given by L
    df0 := apply(degrees source f0,i-> (-1)*i|{0});
    df1 := apply(degrees source f0,i-> (-1)*i|{-1});
    SE := S**E;
    --print degrees SE;
    --Does this create a problem with degrees?
    tr := sum(dim S, i-> SE_i*SE_(dim S+i));
    newf0 := sub(f0,SE)*tr;
    relationsMinSE := sub(relationsM,SE);
    newf0 = newf0 % relationsMinSE;
    newg := matrixContract(transpose sub(f0,SE),newf0);
    --THIS contract DOES SOMETHING WRONG IN THE NON-CYCLIC CASE -- should be fixed
    g' := sub(newg,E);
    chainComplex map(E^df0,E^df1, g')
    )

RRTable = method()
RRTable(Module, List) := (M,LL) ->(
    --M is an S-module
    --LL a list of integers
    --Output is a hashTable Bmaps with keys
    --(p_0,p_1,x), with p_0, p_1 \in LL andn
    --deg x == p_0-p_1 (in particular, p_0> p_1).
    --and values Bmaps#(p_0,p_1,x) the map 
    --from 
    --to source basis(p_0)
    --induced by multiplication with x.
    --note that the entries of these maps are scalars.
    --
    S :=ring M;
    if not S.?irrelevantIdeal then (
    	irr := ideal vars S;
	addTateData(S,irr)
	);
    E := S.exterior;
    triples = flatten flatten apply(LL, ell -> apply(LL, ell' -> apply(gens S, x ->(ell,ell', x))));
    st = select(triples, p->{p_0-p_1} == (degree p_2));
    B = hashTable apply(LL, ell -> (ell, basis(ell, M)));
    Mmaps = hashTable apply(st, 
	p -> (p,
	    map(M, 
		M**S^{p_1-p_0}, 
		id_M**matrix{{p_2}})));
    Bmaps = hashTable apply(st, p -> 
	(p,map(
		source B#(p_0), 
		source B#(p_1)**S^{p_1-p_0}, 
		(Mmaps#p*(B#(p_1)**S^{p_1-p_0})//B#(p_0)))));
    degsList = unique apply(gens S, x -> degree x);
    Svars = hashTable apply(degsList, d -> (d, select(gens S, x -> degree x == d)));
    ev = map(E,S,vars E, DegreeMap => d -> -d|{1});
    BEmaps = hashTable apply(st, p ->((p_0,p_1,ev p_2), ev p_2**ev Bmaps#p))
    )
///
restart
load "KoszulFunctor.m2"

kk=ZZ/101
L = {1,2}
S=kk[x_0..x_(#L-1),Degrees=>L]
M= S^1/ideal(x_0^2)
M = S^{5}**M
LL = toList(-4..0)

irr=ideal vars S
addTateData(S,irr)
E = S.exterior

betti res M
///        

-*


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
	    --i := ij_0; ij = (6,1)
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

entry(TB.dd_1_ij,d,S)
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
    phi := sum(#fs,n->(m=cs_n;sub(fs_n,S)*(S.phis#(d,m))));
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


doubleComplexBM = method()
doubleComplexBM ChainComplex := ChainComplex => TB->(
    --Input:  a free diff module for Beilinson window
    --Output: a double complex corresponding to the diff Mod.
    BC := bigChainMap(TB);
    FF := target BC;
    BM = chainComplex apply(dim S, i-> FF.dd_(i+1) - BC_i);
    --the maps already anticommute.
    --apply(dim S,i->  BC_(i-1)*FF.dd_(i+1) + FF.dd_(i)*BC_i)
    --so any sign change should affect both pieces simultaneously.
    assert(BM.dd^2==0);
    BM
    --seems to yield a double complex...  should check sign carefully.
    )

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

M= S^{4}/ideal(x_0+2*x_1,x_2,x_3)
M1= (S^{5}/ideal(x_0+2*x_1,x_2,x_3))
M = M++M1


LL=apply(toList(-10..10),i->S.degOmega+{i})
elapsedTime betti(TM=RRFunctor(M,LL))
TB=beilinsonWindow(TM,-S.degs)
betti TB
TB.dd_1
BM = doubleComplexBM TB
BM.dd^2 == 0
isIso(HH_0 BM, truncate(4,M))
prune HH BM
presentation prune HH_0 BM
--fails 5/12/20
--works on 5/14/20

-- the following does not work (working as of 5/14/20)

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
betti TB
BM = doubleComplexBM TB
prune HH BM
isIso(HH_0 BM, truncate(-sum L + 1,M))
--fails 5/12/20
--works 5/14/20

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
M = S^{4}**M
--M = S^1/ideal(x_0,x_2)

LL=apply(toList(-10..10),i->S.degOmega+{i})
elapsedTime betti(TM=RRFunctor(M,LL))
--elapsedTime betti(TM=RRFunctor(M1,LL))
TB=beilinsonWindow(TM,-S.degs)
betti TB
TB.dd_1
BM = doubleComplexBM TB
prune HH BM
isIso(HH_0 BM, truncate(-sum L +1,M))
-- works on 5/14/20


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
elapsedTime betti(TM=RRFunctor(M,LL))
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
elapsedTime betti(TM=RRFunctor(M,LL))
TB=beilinsonWindow(TM,-S.degs)
betti TB
TB.dd_1
BM = bigChainMap TB
betti source BM
DMHHalt BM
presentation truncate(-2,M)
--  Twist is off, but I also don't know why these aren't these are the same

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





    



--
--For April 28
restart
--Regular PP2
load "KoszulFunctor.m2"
kk=ZZ/101
L = {1,1,1}
S=kk[x_0..x_(#L-1),Degrees=>L]
irr=ideal vars S
addTateData(S,irr)
E = S.exterior

M = S^1/ideal(x_0^2)
M = S^{2}**M
LL=apply(toList(-5..5),i->S.degOmega+{i})
elapsedTime betti(TM=RRFunctor(M,LL));
TM.dd_1;
TB=beilinsonWindow(TM,-S.degs);
betti TB
TB.dd_1
BM = doubleComplexBM(TB)
betti BM
M' = prune HH_0 BM
isIso(M,M')


M= S^1/ideal(x_0^3+x_1^3+x_2^3)
M = S^{3}**M
LL=apply(toList(-5..5),i->S.degOmega+{i})
elapsedTime betti(TM=RRFunctor(M,LL));
TM.dd_1;
TB=beilinsonWindow(TM,-S.degs);
betti TB
TB.dd_1
BM = doubleComplexBM(TB)
prune HH BM
M'' = prune truncate(-2,M)
M' = prune HH_0 BM
isIso(M'',M')
-- what's with the truncation???



--  PP^n, \Omega^i(i)
--  this one times out when n = 3
restart
load "KoszulFunctor.m2"
n = 3
kk=ZZ/101
L = apply(n+1,i-> 1)
S=kk[x_0..x_(#L-1),Degrees=>L]
irr=ideal vars S
addTateData(S,irr)
E = S.exterior
--  omega2 is \Omega^2(2)
omega2 = ker(S.complexes#{2}.dd_2)
betti res omega2

M = prune omega2
M = M**S^{4}
LL = apply(toList(-3..1),i->{i})
elapsedTime betti(TM=RRFunctor(M,LL));
TB=beilinsonWindow(TM,-S.degs);
betti TB
-- time issues
BM = doubleComplexBM(TB)
prune HH BM

--- Omega^1(1) on PP^2 works:
--- but you need to twist more positively to get higher cohomology outside of the
--  window.  So it's really Omega^1(4)...
restart
load "KoszulFunctor.m2"
n = 2
kk=ZZ/101
L = apply(n+1,i-> 1)
S=kk[x_0..x_(#L-1),Degrees=>L]
irr=ideal vars S
addTateData(S,irr)
E = S.exterior
omega1 = ker(S.complexes#{1}.dd_1)
betti res omega1

M = prune omega1
M = M**S^{3}
LL = apply(toList(-3..1),i->{i})
elapsedTime betti(TM=RRFunctor(M,LL));
TB=beilinsonWindow(TM,-S.degs);
betti TB
-- time issues
BM = doubleComplexBM(TB)
prune HH BM



TM.dd_1;
TB=beilinsonWindow(TM,-S.degs);
betti TB
TB.dd_1
BM = doubleComplexBM(TB)
prune HH BM
M'' = prune truncate(-2,M)
M' = prune HH_0 BM
isIso(M'',M')


-- Weighted PP2
restart
load "KoszulFunctor.m2"
kk=ZZ/101
L = {1,1,2}
S=kk[x_0..x_(#L-1),Degrees=>L]
irr=ideal vars S
addTateData(S,irr)
--E = S.exterior
--KK = select(keys S.phis,i-> i_1 == e_2)
--apply(KK,k-> S.phis#k)

--rational curve, twisted to avoid higher cohomology.
M = (S^{4}/ideal(x_0^2+x_1^2+x_2))

--M = M++M1
LL=apply(toList(-6..6),i->S.degOmega+{i})
elapsedTime betti(TM=RRFunctor(M,LL))
TB=beilinsonWindow(TM,-S.degs)
betti TB
TB.dd_1
BM = doubleComplexBM(TB)
M'' = prune truncate(-3,M)
M' = prune HH_0 BM
isIso(M'',M')


--nonrational curve, twisted to avoid higher cohomology.
M = (S^{5}/ideal(random(5,S)))
LL=apply(toList(-6..6),i->S.degOmega+{i})
elapsedTime betti(TM=RRFunctor(M,LL))
TB=beilinsonWindow(TM,-S.degs)
betti TB
TB.dd_1
BM = doubleComplexBM(TB)
--not a chain complex
(prune HH BM)
--
M'' = prune truncate(-3,M)
M' = prune HH_0 BM
isIso(M',M'')


--------working examples in weighted projective space....with 2 variables
restart
load "KoszulFunctor.m2"
kk=ZZ/101
----------
d = 4
L = {1,d}
S=kk[x_0..x_(#L-1),Degrees=>L]
irr=ideal vars S
addTateData(S,irr)
M = (S^{d}/ideal(x_0^d-x_1))
---
LL=apply(toList(-6..6),i->S.degOmega+{i})
elapsedTime betti(TM=RRFunctor(M,LL))
TB=beilinsonWindow(TM,-S.degs)
BM = doubleComplexBM(TB)
BM.dd^2 == 0
--truncations don't matter: we're a point.
prune truncate ({0},prune HH_0 BM)
prune truncate({0},M)
BM.dd_1
prune HH BM
M

--------examples with varying dim, codim in proj space
restart
load "KoszulFunctor.m2"
kk=ZZ/101
----------
n = 3
c = 2
d = 3
tw = c*d

L = apply(n,i->1)
S=kk[x_0..x_(#L-1),Degrees=>L]
irr=ideal vars S
addTateData(S,irr)

M = S^{tw}/ideal apply(c, i->x_i^d)
---
LL=apply(toList(-6..6),i->S.degOmega+{i})
elapsedTime betti(TM=RRFunctor(M,LL))
TB=beilinsonWindow(TM,-S.degs)
BM = doubleComplexBM(TB)
--truncations don't matter: we're a point.
prune truncate ({0},prune HH_0 BM)
prune truncate({0},M)
BM.dd_1
prune HH BM
M
