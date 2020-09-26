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
    "doubleComplexBM",
    "isIsomorphic",
    "Variable",
    "SkewVariable",
    "unfold"
    }

To Dos:
1.  toricLL ChainComplex  (to implement Michael's algorithm for sheaf cohomology tables...)
2.  truncate(ChainComplex, degree) over polynomial ring
3.  Tor of a non-minimal free DM for the "corner complex".  (Does not need minimal...)
4.  


Tor_E(RR S, k) = "betti numbers of tail RR" != "betti numbers of RR S"
tail RR S --> RR S
tail RR

Tor_E(RR M, k) in cat of diff modules... = "betti numbers of corner complex of RR M"

*-
--load "TateDM.m2"

needsPackage "Polyhedra";

DifferentialModule = new Type of ChainComplex
DifferentialModule.synonym = "differential module"

differentialModule = method(TypicalValue => DifferentialModule)
differentialModule ChainComplex := C -> (
    --Daniel: should we add error if C is not of the right form??
  new DifferentialModule from C);

differentialModule Matrix := phi -> (
    --check if the source and target are the same up to a twist
    d := (degrees source phi)_0 - (degrees target phi)_0;
    if target phi != source phi**R^{d} then error "source and target of map are not the same, up to a twist";
    new DifferentialModule from (chainComplex(phi**R^{d},phi)[1]));






ring(DifferentialModule) := Ring => D -> D.ring;
module DifferentialModule :=  (cacheValue symbol module)(D -> D_0);
degree DifferentialModule := ZZ => (D -> (degrees D_1)_0 - (degrees D_0)_0);
differential = method();
differential DifferentialModule := Matrix=> (D->D.dd_1);
kernel DifferentialModule := Module => opts -> (D -> kernel D.dd_0); 
image DifferentialModule := Module => (D -> image D.dd_1); 
homology DifferentialModule := Module => opts -> (D -> HH_0 D);

unfold = method();
--Input:  a differential module and a pair of integers low and high
--Output:  the unfolded chain complex of the differential module, in homological degrees
--         low through high.
unfold(DifferentialModule,ZZ,ZZ) := ChainComplex => (D,low,high)->(
    L := toList(low..high);
    d := degree D;
    R := ring D;
    phi := differential D;
    chainComplex apply(L,l-> phi**R^{l*d})[-low]
    )


TEST ///
restart
load "ToricTate.m2";
R = QQ[x];
M = R^1/(x^3);
phi = map(M,M**R^{-2},matrix{{x^2}})
D = differentialModule(phi)
assert(degree D == {2})
assert(module D == M)
assert(isHomogeneous unfold(D,-3,6))
assert(kernel D / image D != 0)
assert(degree HH D == 1)
///

dualRingToric = method(
        Options => {
    	    Variable        => getSymbol "x",
	    SkewVariable => getSymbol "e"
	}
    );

dualRingToric(PolynomialRing) := opts -> (S) ->(
--  Input: a polynomial ring OR an exterior algebra
--  Output:  the Koszul dual exterior algebra, but with an additional 
--           ZZ-degree, the ``standard grading'' where elements of \bigwedge^k
--           have degree k.
    kk := coefficientRing S;
    degs := null;
    if isSkewCommutative S == false then(
    	degs = apply(degrees S,d-> (-d)|{1});
	e := opts.SkewVariable;
    	ee := apply(#gens S, i-> e_i);
    	return kk[ee,Degrees=>degs,SkewCommutative=>true]
	); 
    if isSkewCommutative S == true then(
    	degs = apply(degrees S,d-> remove(-d,-1));
	y := opts.Variable;
    	yy := apply(#gens S, i-> y_i);
    	return kk[yy,Degrees=>degs,SkewCommutative=>false]
	);       
    );

TEST ///
restart
needsPackage "NormalToricVarieties"
S = ring(hirzebruchSurface(2, Variable => y));
E = dualRingToric(S,SkewVariable => f);
SY = dualRingToric(E);
assert(degrees SY == degrees S)
///


--Input:    A list of matrices with the same number of rows.
--Output:   The concatenation of those matrices.
concatMatrices=method()
concatMatrices(List) := L -> (
    m:= first L;
    scan(#L-1,i->m=m|L_(i+1));
    m)

--Input:    A pair of matrices (M,N)
--Output:   The effect of contracting M by N. 
matrixContract=method()
matrixContract(Matrix,Matrix) := (M,N) -> (
    S := ring M;
    if M==0 or N==0 then return map(S^(-degrees source N),S^(degrees source M),0);
    assert(rank source M == rank target N); 
    transpose map(S^(-degrees source N), , transpose matrix apply(rank target M,i->apply(rank source N,j->		
           sum(rank source M,k->contract(M_(i,k),N_(k,j) ))
	    )))
    )


toricRR = method();
--Input: (M,LL) M a (multi)-graded S-module.
--             LL a list of degrees.
--Output:  The differenial module RR(M) in degrees from LL,
--         presented as a complex in homological degrees -1, 0 ,1
--         and with the same differential in both spots.
toricRR(Module,List) := (M,LL) ->(
    S := ring(M);
    if not isCommutative S then error "ring M is not commutative";
    if not S.?exterior then S.exterior = dualRingToric(S);
    E := S.exterior;
    relationsM := presentation M;
    -- this used to say "gens image presentation M"... just in case a bug arises
    f0 := gens image basis(LL_0,M);
    scan(#LL-1,i-> f0 = f0 | gens image basis(LL_(i+1),M));
    df0 := apply(degrees source f0,i-> (-1)*i|{0});
    df1 := apply(degrees source f0,i-> (-1)*i|{-1});
    dfneg1 := apply(degrees source f0,i-> (-1)*i|{1});
    SE := S**E;
    --the line below is better for degrees,it overwrites S somehow...
    --SE := coefficientRing(S)[gens S|gens E, Degrees => apply(degrees S,d->d|{0}) | degrees E, SkewCommutative => gens E];
    tr := sum(dim S, i-> SE_i*SE_(dim S+i));
    newf0 := sub(f0,SE)*tr;
    relationsMinSE := sub(relationsM,SE);
    newf0 = newf0 % relationsMinSE;
    newg := matrixContract(transpose sub(f0,SE),newf0);
    g' := sub(newg,E);
    differentialModule(chainComplex{map(E^dfneg1,E^df0, g'),map(E^df0,E^df1, g')}[1])
    )

TEST ///
restart
load "ToricTate.m2"
kk=ZZ/101
S=kk[x_0,x_1,Degrees=>{1,2}]
D = toricRR(S^1,{0,1,2,3,4,5})
assert(D.dd^2 == 0)
assert(isHomogeneous D)
///


toricLL = method();
--Input: N a (multi)-graded E-module.
--Caveat: Assumes N is finitely generated.
--Caveat 2:  arrows of toricLL(N) correspond to exterior multiplication (not contraction)
toricLL(Module) := (N) ->(
    E := ring(N);
    if not isSkewCommutative E then error "ring N is not skew commutative";
    if not E.?symmetric then E.symmetric = dualRingToric(E);
    S := E.symmetric;
    bb := basis(N);
    b := (degrees source bb);
    homDegs := sort unique apply(b, i-> last i);
    inds := new HashTable from apply(homDegs, i-> i=> select(#b, j-> last(b#j) == i));
    sBasis := new HashTable from apply(homDegs, i-> i => (bb)_(inds#i));
    FF := new HashTable from apply(homDegs, i ->(
	    i => S^(apply((degrees sBasis#i)_1, j-> remove(j,-1)))
	    )
	);
    relationsN := presentation N;
    SE := S**E;
    --SE := coefficientRing(S)[gens S|gens E, Degrees => apply(degrees S,d->d|{0}) | degrees E, SkewCommutative => gens E];
    --why is this overwriting the definition of e_i?
    tr := sum(dim S, i-> SE_i*SE_(dim S+i));
    f0 := gens image basis(N);
    newf0 := sub(f0,SE)*tr;
    relationsMinSE := sub(relationsN,SE);
    newf0 = newf0 % relationsMinSE;
    newg := matrixContract(transpose sub(f0,SE),newf0);
    g' := sub(newg,S);
    --Now we have to pick up pieces of g' and put them in the right homological degree.
    --Note:  perhaps we want everything transposed??
    dual(chainComplex apply(remove(homDegs,-1), i-> map(FF#i,FF#(i+1),transpose g'_(inds#i)^(inds#(i+1))))[-homDegs#0])
    )


--  Input:  a map of (finitely generated) modules N and M over the exterior exterior algebra
--  Output:  the map of chain complex toricLL(N) --> toricLL(M).
toricLL(ModuleMap) := (phi) ->(
    Ns := source phi;
    Nt := target phi;
    E := ring(Nt);
    if not isSkewCommutative E then error "ring N is not skew commutative";
    if not E.?symmetric then E.symmetric = dualRingToric(E);
    S := E.symmetric;
    bbs := basis(Ns);
    bs := (degrees source bbs);
    bbt := basis(Nt);
    bt := (degrees source bbt);
    homDegs := sort unique apply(bs, i-> last i);
    homDegt := sort unique apply(bt, i-> last i);
    inds := new HashTable from apply(homDegs, i-> i=> select(#bs, j-> last(bs#j) == i));
    indt := new HashTable from apply(homDegt, i-> i=> select(#bt, j-> last(bt#j) == i));
    sBasisNs := new HashTable from apply(homDegs, i-> i => (bbs)_(inds#i));
    sBasisNt := new HashTable from apply(homDegt, i-> i => (bbt)_(indt#i));
    LLNs := toricLL(Ns);
    LLNt := toricLL(Nt);
    homDegCommon :=  toList(max(min homDegs,min homDegt)..min(max homDegs,max homDegt));
    f := new HashTable from apply(homDegCommon, i-> -i=>(-1)^i*sub(phi*(sBasisNs#i) // sBasisNt#i,S));
    map(LLNt,LLNs, i-> f#i)
)


--  Input:  degrees d1, d2, and a ring S
--          Assumes d1,d2 are lists of integers of length n and that the variables
--          of S have degrees which are lists of integers of length n.
--  Output:  Checks whether d1 - d2 is an effective degree on S.
greaterEqual=method()
greaterEqual(List,List,Ring) := (d1,d2,S) -> hilbertFunction(d1-d2,S) != 0

degreeTruncation=method()
degreeTruncation(Matrix,List) := (M,d) -> (
    --rows and cols with degrees <= d.
    S := ring(M);
    rows:= positions(degrees target M,d'-> greaterEqual(d,d',S));
    columns:= positions(degrees source M,d'-> greaterEqual(d,d',S));
    sourceInc := (id_(source M))_columns;
    targetInc := (id_(target M))_rows;    
    ((M^rows)_columns,targetInc,sourceInc)
    )

degreeTruncation(ChainComplex,List) := (K,d) -> (
    --subcomplex where all rows and cols of differentials have degrees <= d.
    S := ring(K);
    a := min K;
    Ka := K[a];
    L := apply(length Ka,i->degreeTruncation(Ka.dd_(i+1),d));
--    L := apply(toList(min(K[a]).. max(K[a])-1),i->degreeTruncation(Ka.dd_(i+1),d));    
    tKa:=chainComplex(apply(length Ka,i->L_i_0));
    phi := map(K,tKa[-a], i-> if i == a then L_(i-a)_1 else L_(i-a-1)_2);
--    assert(isChainComplexMap phi);
    phi
    )


degreeTruncation(ChainComplexMap,List) := (phi,d) -> (
    S := ring(phi);
    G := target phi;
    F := source phi;
    phiF := degreeTruncation(F,d);
    F' := source (phiF = degreeTruncation(F,d));
    G' := source (phiG = degreeTruncation(G,d));
    map(G', F', i->(phi_i * phiF_i)// phiG_i)
    )


truncatedKoszul = method();
truncatedKoszul(Ring,List) := (S,d)->(
    F := (toricLL(E^1))[-dim S];
    canon := sum degrees S;
    G := F**(ring F)^{-canon+d};
    source degreeTruncation(G,{0})
    )

truncatedKoszulMap = method();
truncatedKoszulMap(Ring,List,List,RingElement) := (S,d1,d2,f)->(
    if -remove(degree f,-1) != d2-d1 then error "Wrong degree for such a map";
    N1 := ptrunc(E^1,d1);
    N2 := ptrunc(E^1,d2);
    phi := map(N1**E^{d1|{0}},N2**E^{d2|{-last degree f}},matrix{{f}});
    toricLL phi
    )

oneStepCorner = method();
oneStepCorner(List,DifferentialModule) := (cDeg,F) -> (
    E := ring F;
    dF := degree F;
    H := res(coker F.dd_1,LengthLimit => 2);
    newSyz := (H.dd_2**(ring H)^{dF}) % H.dd_1;
    G = chainComplex newSyz;
    newSpots = {};
    D := degrees G_1;
    D1 := apply(D,i-> remove(i,-1));
--  keep nontrivial new syzygies which are "below" the corner
    scan(#D1, i->(if greaterEqual(cDeg,D1#i,S) and D1#i != cDeg and submatrix(newSyz,{i}) != 0 
	    then(newSpots = newSpots|{i};)));
    Gpre := E^(apply(newSpots,i-> -D#i + dF));
    phi := map(G_0,Gpre,(newSyz)_(newSpots));
    psi := gens trim image(phi % (matrix H.dd_1));
    Gnew := source psi;
    d1 := psi|H.dd_1;    
    d2 := map(Gnew**E^{dF},Gnew++H_1, (i,j)->0);
    d := (d2||d1);
    differentialModule(chainComplex(d**E^{dF},d)[1])
)




resDM = method(TypicalValue => DifferentialModule,
            Options => {
    	    LengthLimit => 3
    	    });

resDM(DifferentialModule) := opts -> (D) ->(
    --n := opts.LengthLimit;
    d := degree D;
    cyc := res kernel D;
    -- this is code which turns a resolution into a differential module...
    L := apply(length cyc+1,j->(
	    transpose concatMatrices apply(m+1,i->map(cyc_j,cyc_i, if i == j+1 then cyc.dd_i else 0))
	));
    cycDiff := transpose(concatMatrices L);
    cycMod := cyc_0;
    scan(m+1, i-> cycMod = cycMod ++ ((cyc_(i+1))**(ring FF)^{(i+1)*d}));
    bou := res image D;
    L' := apply(length bou+1,j->(
	    transpose concatMatrices apply(m+1,i->map(bou_j,bou_i, if i == j+1 then bou.dd_i else 0))
	));
    bouDiff := transpose(concatMatrices L');
    bouMod := bou_0**(ring FF)^{d};
    scan(m+1, i-> bouMod = bouMod ++ ((bou_(i+1))**(ring FF)^{(i+2)*d}));
    --cycDiff and bouDiff are the differentials of cycle and boundary resolutions, as a diff module
    psi := map(cyc_0,bou_0,gens image D // gens kernel D);
    PSI = {psi};
    m := min(length cyc, length bou);
    scan(m,i-> PSI = PSI|{PSI_(i)*bou.dd_(i+1) // cyc.dd_(i+1)} );
    K := apply(length cyc + 1,j->(
	    apply(length bou+1,i->(
		    map(cyc_j,bou_i, if j == i then PSI_i else 0)
		    ))));
    bouToCycDiff := transpose concatMatrices apply(K,i-> transpose concatMatrices i);
    lastMap := map(bouMod,cycMod**(ring D)^{-d},0);
    CEdiff := map(cycMod++bouMod,(cycMod++bouMod)**(ring D)^{-d}, (cycDiff|bouToCycDiff) || (lastMap|bouDiff));
    differentialModule(chainComplex(CEdiff**(ring D)^{d},CEdiff)[1])
	)



--  Input: a differential module D
--  Output: the module D' that would be the minimal part of D.  (We don't work out the differentials.)
minimalPart = method();
minimalPart(DifferentialModule) := G->(
    phi := map(ring G,ring G, apply(# gens ring G, i-> 0));
    Gbar := differentialModule phi(G);
    source mingens HH Gbar
    )


--NOW WE GET TO THE PART THAT NEEDS MORE WORK
--The idea is to develop a "corner complex" code
--cornerDM works for weighted projective spaces but seems to have
--issues for other varieties.

cornerDM = method(TypicalValue => DifferentialModule,
            Options => {
    	    LengthLimit => 3
    	    });


-- options including lengthLimit?
cornerDM(List,DifferentialModule) := opts -> (cDeg,F)->(
    n := opts.LengthLimit;
    scan(n, i-> F = oneStepCorner(cDeg,F));
    F
    )   


oneStepCorner(List,DifferentialModule) := (cDeg,F) -> (
    E := ring F;
    dF := degree F;
    H := res(coker F.dd_1,LengthLimit => 2);
    newSyz := (H.dd_2**(ring H)^{dF}) % H.dd_1;
    G = chainComplex newSyz;
    newSpots = {};
    D := degrees G_1;
    D1 := apply(D,i-> remove(i,-1));
--  keep nontrivial new syzygies which are "below" the corner
    scan(#D1, i->(if greaterEqual(cDeg,D1#i,S) and D1#i != cDeg and submatrix(newSyz,{i}) != 0 
	    then(newSpots = newSpots|{i};)));
    Gpre := E^(apply(newSpots,i-> -D#i + dF));
    phi := map(G_0,Gpre,(newSyz)_(newSpots));
    psi := gens trim image(phi % (matrix H.dd_1));
    Gnew := source psi;
    d1 := psi|H.dd_1;    
    d2 := map(Gnew**E^{dF},Gnew++H_1, (i,j)->0);
    d := (d2||d1);
    differentialModule(chainComplex(d**E^{dF},d)[1])
)








--  Input:  a polynomial ring S
--  Output:  a list of all degrees between 0 and the anti-canonical degree
--  CAVEAT:  needs "Polyhedra" package.
koszulDegrees = method();
koszulDegrees(PolynomialRing) := S ->(
    K := koszul vars S;
    L := unique flatten apply(dim S+1,i-> degrees K_i);
    P := convexHull transpose matrix L;
    LP := latticePoints P;
    sort flatten apply(#LP,i-> entries transpose (latticePoints P)_(i))
    )

end;

TEST ///
restart
load "ToricTate.m2";
S = ZZ/101[x_0,x_1,x_2, Degrees => {{1},{1},{2}}];
cDeg = {3}
F = toricRR(S^1,apply(koszulDegrees(S),i-> i+cDeg))
time G = cornerDM(cDeg,F,LengthLimit => 2)
--takes a few seconds

restart
load "ToricTate.m2";
needsPackage "NormalToricVarieties"
X = hirzebruchSurface(1)
S = ring X
F = toricRR(S^1,apply(koszulDegrees S,i-> i+{1,1}))
G = cornerDM({1,1},F,LengthLimit => 1);
tally degrees minimalPart G - tally degrees F_0
--None of these seem to be the "right" cohomology groupsl
--If you investigate the (1,0), we'd expect two syzygies
--corresponding to x_0 and x_2, the elements of degree (1,0).
--But there is a third fake syzygy which seems to correspond to x_3/x_1,
--which is not an element of S but which has degree (1,0).
--I think the issue is that, somehow, we are not taking the irrelevant ideal 
--into account in any way.  But I don't see how to make that intuition precise.



restart
load "ToricTate.m2";
S = ZZ/101[x_0,x_1,x_2,x_3, Degrees => {{1},{1},{1},{3}}];
F = toricRR(S^1,toList({2}..{6}))
cDeg = {2}
G = cornerDM(cDeg,F,LengthLimit => 10)
--really slowly converges!!
tally degrees minimalPart G


code res
addTateData = method()
addTateData (Ring,Ideal) := (S,irr) ->(
    S.irr = irr;
    S.exterior = dualRingToric S;
    S.koszul = koszul vars S;
    S.degOmega = -(degrees S.koszul_(numgens S))_0;
--    Dan: I commented out this other "TateData" for now.  Not sure how we want to proceed with it.
--    S.sortedMons = sortedMonomials S.exterior;
--    S.complexes = cacheComplexes S;
--    S.complexes = cacheComplexes(S,true);
--    S.phis = cachePhi S;
--    S.degs = keys S.complexes;
)


end;
///

S = QQ[x_1,x_2,x_3]
I = (ideal(x_1,x_2,x_3))^2
r = res I
r.dd_3
///        


restart
n = 3
d = 2
S = ZZ/101[x_1..x_4]
M = matrix{{x_1,x_2,x_3,x_4,0},{0,x_1,x_2,x_3,x_4}}
betti res minors(2,M)
mingens minors(2,M) 
M = matrix{{x_1,x_2,x_3,0,0},{0,x_1,x_2,x_3,0},{0,0,x_1,x_2,x_3}}
betti res minors(3,M)
minors(3,M) == (ideal vars S)^3
eagonNorthcott M
