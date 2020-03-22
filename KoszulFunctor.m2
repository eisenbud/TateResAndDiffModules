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


--From Daniel, but altered in a wrong way
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
    assert(rank source M == rank target N); 
    matrix apply(rank target M,i->apply(rank source N,j->
	    sum(rank source M,k->contract(M_(i,k),N_(k,j) ))
	    ))
    )

RRfunctor = method();
RRfunctor(Module,Ring,List,ZZ) := (M,E,lows,c) ->(
    -- wrong need to take the level into account
    S :=ring(M);
    M1 := prune coker presentation M;
    relationsM := gens image presentation M1;
    numvarsE := numgens E;
    ev := map(E,S,vars E);
    range := degreeSetup(S,lows,c);
    bases := apply(c+1,i->
	concatMatrices apply(range#i,d->basis(d,M)));
    bases1 :=apply(bases, B-> map(S^(degrees target B),, lift(B,S)));

    SE := S**E;
    tr := sum(dim S, i-> SE_i*SE_(dim S+i));
    baseTr := apply(bases1, B-> tr*sub(B,SE));
--    tr*sub(bases,SE) == tr*sub(bases1,SE) -- == false!
    relationsMinSE := sub(relationsM,SE);
    reducedBaseTr := baseTr % relationsMinSE;
    multTable := matrixContract(transpose sub(bases1,SE),reducedBaseTr);
    F:= E^(-degrees source bases1);
    chainComplex map(F,F, sub(multTable,E))
    )

-* TEST ///

kk=ZZ/101
S=kk[x_0..x_3,Degrees=>{{1,0},{1,2},2:{0,1}}]
degrees S
E=kk[e_0..e_3,SkewCommutative=>true,Degrees=>-degrees S ]
M=truncate({1,1},S^1)
c=2
lows={{1,0}}
TM=RRfunctor(M,E,lows,c)
TM.dd_1
betti TM
TM.dd_1
(TM.dd_1)^2
///*-
end

restart
load "KoszulFunctor.m2"
debug needsPackage "TateOnProducts"
--Hirzebruch S(2,0)xPP(1,2)
kk=ZZ/101
S=kk[x_0..x_5,Degrees=>{{1,0,0},{1,2,0},2:{0,1,0},{0,0,1},{0,0,2}}]
degrees S
E=kk[e_0..e_5,SkewCommutative=>true,Degrees=>-degrees S ]
K=koszul vars S
sortedMons = sortedMonomials E
(i,j) = (3,4)
m=sortedMons#i_{j}_(0,0)
M=K.dd_i
d=-degree m
phi=completeToMapOfChainComplexes(K,m)
isHomogeneous phi


-------------------
debug needsPackage "TateOnProducts"
(S,E) = (productOfProjectiveSpaces{2,2})
--E = ZZ/101[e_0..e_3, SkewCommutative => true]
--S = 
sortedBasis({2},E)
sortedB = (sortedBases E)#1
sortedB#1
keys sortedB
koszulmap(2,sortedB,S)
koszul(2,vars S)


---------------
--Want: the map koszul --> koszul corresponding to diff by e_0
truncateShiftComplex = (i,K) -> S^{i}**chainComplex(apply(length K -i, j-> (-1)^(i*j)* K.dd_(j+i+1)))

S = ZZ/101[w,x,y,z]
K = koszul vars S
K1 = chainComplex apply(2,i->(K[1]).dd_(i+1))
(K[1])_0
phi_0 = map(S^{1}**K_0,(K[1])_0,matrix{{1_S,0,0}})
phi = extend(S^{1}**K,K1, phi_0)

--map wedge^k S^n --> S diff by a monomial.

(koszul vars S).dd
pos = (positions ((entries (sortedBases S)#0#2)_0, i->i==x*y))_0
K = koszul vars S

phi0=map(K_0,S^{2}**K_2,matrix{apply(rank K_2, i-> if i == pos then 1_S else 0_S)})

extend(K,truncateShiftComplex(2,K),phi0, Verify =>true)
