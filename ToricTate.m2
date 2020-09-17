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

*-
--load "TateDM.m2"


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

DMHH = method();
DMHH(DifferentialModule) := Module => (D -> HH_0 D);
DMker = method();
DMker(DifferentialModule) := Module => (D-> kernel D.dd_0);
DMimage = method();
DMimage(DifferentialModule) := Module => (D-> image D.dd_1);


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
target phi == source phi**R^{2}
D = differentialModule(phi)
assert(degree D == {2})
assert(module D == M)
assert(degree DMHH D == 1)
assert(isHomogeneous unfold(D,-3,6))
kernel D
image D
HH D
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
    --the line below is better for degrees, but it doesn't get skew commutativity right...
    --SE := kk[gens S|gens E, Degrees => apply(degrees S,d->d|{0}) | degrees E];
    tr := sum(dim S, i-> SE_i*SE_(dim S+i));
    newf0 := sub(f0,SE)*tr;
    relationsMinSE := sub(relationsM,SE);
    newf0 = newf0 % relationsMinSE;
    newg := matrixContract(transpose sub(f0,SE),newf0);
    g' := sub(newg,E);
    differentialModule(chainComplex{map(E^dfneg1,E^df0, g'),map(E^df0,E^df1, g')}[1])
    )

TEST ///
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


--Input:  A module M over an exterior algebra E (which is dual to a symmetric algebra S)
--        a degree d from the grading group of S.
--Output:  The module M' where we quotient by an element of M' whose degree (ignoring the "extra grading")
--         is larger than d.
ptrunc = method();
ptrunc(Module,List) := (M,d) ->(
    toDrop := select(unique (degrees basis(M))_1, i-> hilbertFunction(d+remove(i,-1),S) == 0);
    if #toDrop == 0 then return M;
    M / image concatMatrices apply(toDrop, e-> basis(e,M))
    )

TEST ///
restart
load "ToricTate.m2";
S = ZZ/101[x_0,x_1,x_2, Degrees => {1,1,2}];
E = dualRingToric S;
FF = toricLL(E^1/(e_0*e_1));
assert(FF.dd^2 == 0)
assert(isHomogeneous FF)
Nt = E^1/(e_0*e_1);
Ns = E^{{1,-1}};
phi = map(Nt,Ns,matrix{{e_0}});
assert(isHomogeneous toricLL(phi));
--

--now let's get these truncated koszul complexes
restart
load "ToricTate.m2";
S = ZZ/101[x_0,x_1,x_2, Degrees => {1,1,2}];
E = dualRingToric S;

truncatedKoszul = method();
truncatedKoszul(Ring,List) := (S,d)->(
    F := toricLL ptrunc(E^1,d);
    F**(ring F)^{d}
    )


truncatedKoszulMap = method();
truncatedKoszulMap(Ring,List,List,RingElement) := (S,d1,d2,f)->(
    if -remove(degree f,-1) != d2-d1 then error "Wrong degree for such a map";
    N1 := ptrunc(E^1,d1);
    N2 := ptrunc(E^1,d2);
    phi := map(N1**E^{d1|{0}},N2**E^{d2|{-last degree f}},matrix{{f}});
    toricLL phi
    )
(d1,d2,f) = ({3},{4},e_0)
truncatedKoszulMap(S,d1,d2,f)
d1 = {1}
d2 = {2}
f = e_0
degree f
///

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





