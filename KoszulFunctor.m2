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

-*TEST  /// 
--Hirzebruch S(2,0)xPP(1,2)
restart
load "KoszulFunctor.m2"
kk=ZZ/101
S=kk[x_0..x_5,Degrees=>{{1,0,0},{1,2,0},2:{0,1,0},{0,0,1},{0,0,2}}]
E=kk[e_0..e_5,SkewCommutative=>true,Degrees=>-degrees S ]
K=koszul vars S
sortedMons = sortedMonomials E
--test by personal inspection
K.dd_2 
sortedMons#2
---
(i1,j1) = (3,4)
m=sortedMons#i1_{j1}_(0,0)
(i,j)=positionInKoszulComplex(K,sortedMons,m)
assert((i,j) ==(i1,j1))
assert(ideal K.dd_i_{j}==ideal apply(toList factor sub(m,vars S),f->first f))
///
*-
 
positionInKoszulComplex=method()
positionInKoszulComplex(ChainComplex,HashTable,RingElement) := (K,sortedMons,m) -> (
    -- Input: The KosulComplex and an exterior monomial
    -- Output: (i,j) with j the column number of K_dd_i corresponding to m
    S := ring K;
    i := #factor sub(m,vars S);
    j := position((entries sortedMons#i)_0,n->n==m); 
    (i,j))


-*TEST ///
m=sortedMons#3_{4}_(0,0)
#factor sub(m,vars S)
///
*-

dualElement=method()
dualElement(Ring,RingElement) := (E,m) -> (
    socle:=product gens E;
    n := contract(m,socle);
    sign := contract(socle,m*n);
    sign*n)
-*TEST///
sortedMons=sortedMonomials E
i=random(numgens E+1)
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
completeToMapOfChainComplexes(ChainComplex,RingElement) := (K,m) -> (
-- Input: m a monomial in \Lambda^i \subset E, 
--        K the KoszulComplex
-- Goal: map of complexes given by contraction with m
-- m: K_0 <- K_i the  map which maps m to 1 and the other generators to 0
-- complete this to a map
-- K <- K[i]**S^{deg m} of complexes
   S:= ring K;
   r:= length K;
   (i,j) := positionInKoszulComplex(K,sortedMons,m);
   --(degrees K_i)_j==-degree m
   stK := K[i]**S^{-degree m}; --shifted twisted K
   assert(degrees source stK.dd_0_{j}==degrees K_0);
   phi0 := matrix{apply(rank stK_0,k->if k==j then 1_S else 0)};
   tstK := chainComplex apply(r-i,p->stK.dd_(p+1)); -- truncted shifted twisted
   phi1 := extend(K,tstK,phi0,Verify=>true);
   Ke := addZeroTerms(min K- min stK,K);
   stKe :=addZeroTerms(stK,max K-max stK);
-- map(K,stK,i->phi1_i)
   map(Ke,stKe,i->if i >= min K and i <= max stKe then phi1_i else map(Ke_i,stKe_i,0))
)
-* TEST ///
kk=ZZ/101
S=kk[x_0..x_5,Degrees=>{{1,0,0},{1,2,0},2:{0,1,0},{0,0,1},{0,0,2}}]
E=kk[e_0..e_5,SkewCommutative=>true,Degrees=>-degrees S ]
K=koszul vars S
sortedMons = sortedMonomials E
(i1,j1) = (3,4)
m=sortedMons#i1_{j1}_(0,0)
phi=completeToMapOfChainComplexes(K,m)
isHomogeneous phi
///
*-

greaterEqual=method()
greaterEqual(List,List) := (d1,d2) -> all(d1-d2,i->i>=0)
strictlyGreater=method()
strictlyGreater(List,List) := (d1,d2) -> all(d1-d2,i->i>=0) and d1!=d2
-*TEST ///
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
TEST///
restart
load "KoszulFunctor.m2"
kk=ZZ/101
S=kk[x_0..x_5,Degrees=>{{1,0,0},{1,2,0},2:{0,1,0},{0,0,1},{0,0,2}}]
S=kk[x_0..x_5,Degrees=>{{1,0,0},{1,2,0},2:{0,1,0},{1,0,1},{0,0,2}}]
degrees S
E=kk[e_0..e_5,SkewCommutative=>true,Degrees=>-degrees S ]
K=koszul vars S
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
    tKa:=chainComplex(apply(length Ka,i->L_i_0));
    phi := map(K,tKa[-a], i-> if i == a then L_(i-a)_1 else L_(i-a-1)_2);
    assert(isChainComplexMap phi);
    phi
    )

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

TEST///
restart
load "KoszulFunctor.m2"
kk=ZZ/101
S=kk[x_0..x_5,Degrees=>{{1,0,0},{1,2,0},2:{0,1,0},{0,0,1},{0,0,2}}]
S=kk[x_0..x_5,Degrees=>{{1,0,0},{1,2,0},2:{0,1,0},{1,0,1},{0,0,2}}]
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
--NOTE: there's always 0th homology;
-- but the other homology degrees seem to form a 
-- consecutive sequence.
-- Why??
///



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

RRfunctor = method();
RRfunctor(Module,Ring,List,ZZ) := (M,E,lows,c) ->(
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

TM=RRfunctor(M,E,lows,c)
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

TM=RRfunctor(M,E,lows,c)
assert(isHomogeneous TM)
assert((TM.dd_1)^2==0)
TM.dd_1
betti TM

///*-

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
end

restart
load "KoszulFunctor.m2"
debug needsPackage "TateOnProducts"
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
annHH F
dimHH F
n=numgens S
es=(entries concatMatrices values sortedMons)_0
apply(es,c->(
  (i=random n,j= random binomial(n,i),m=sortedMons#i_{j}_(0,0),d=-degree m);
  F=source degreeTruncation(K,d);
  (m,tally relevantAnnHH(F,irr))))




phi=completeToMapOfChainComplexes(K,m)
isHomogeneous phi
F=target phi
source phi
netList tallyComplex F

F=degreeTruncation(target phi,d)
netList tallyComplex (sF=source F),netList tallyComplex (tF=target F)
sF

sF.dd
G = degreeTruncation(source phi,d)
netList tallyComplex (sG=source G),netList tallyComplex (tG=target G)
sG

