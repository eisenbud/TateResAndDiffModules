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
---
---
---HELPER FUNCTIONS
---
---

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



---
---
---
---GENERAL STUFF ON DIFFERENTIAL MODULES
---
---
---
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

isFreeModule(DifferentialModule) := D ->(
    isFreeModule module D
    )

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



--  This code uses the Cartan-Eilenberg construction to build a "free resolution"
--  of an arbitrary differential module.
--  It could use some work.

resDM = method(TypicalValue => DifferentialModule,
            Options => {
    	    LengthLimit => 3
    	    });

resDM(DifferentialModule) := opts -> (D) ->(
    n := opts.LengthLimit;
    d := degree D;
    cyc := res(kernel D,LengthLimit =>n);
    bou := res(image D,LengthLimit =>n);
    R := ring D;
    m := max(length cyc, length bou);
    -- this is code which turns a resolution into a differential module...
    L := apply(length cyc+1,j->(
	    transpose concatMatrices apply(m+1,i->map(cyc_j,cyc_i, if i == j+1 then cyc.dd_i else 0))
	));
    cycDiff := transpose(concatMatrices L);
    cycMod := cyc_0;
    scan(m+1, i-> cycMod = cycMod ++ ((cyc_(i+1))**(R)^{(i+1)*d}));
    L' := apply(length bou+1,j->(
	    transpose concatMatrices apply(m+1,i->map(bou_j,bou_i, if i == j+1 then bou.dd_i else 0))
	));
    bouDiff := transpose(concatMatrices L');
    bouMod := bou_0**(R)^{d};
    scan(m+1, i-> bouMod = bouMod ++ ((bou_(i+1))**(R)^{(i+2)*d}));
    --cycDiff and bouDiff are the differentials of cycle and boundary resolutions, as a diff module
    psi := map(cyc_0,bou_0,gens image D // gens kernel D);
    PSI = {psi};
    scan(m,i-> PSI = PSI|{PSI_(i)*bou.dd_(i+1) // cyc.dd_(i+1)} );
    K := apply(length cyc + 1,j->(
	    apply(length bou+1,i->(
		    map(cyc_j,bou_i, if j == i then PSI_i else 0)
		    ))));
    bouToCycDiff := transpose concatMatrices apply(K,i-> transpose concatMatrices i);
    lastMap := map(bouMod,cycMod**R^{-d},0);
    CEdiff := map(cycMod++bouMod,(cycMod++bouMod)**(ring D)^{-d}, (cycDiff|bouToCycDiff) || (lastMap|bouDiff));
    differentialModule(chainComplex(CEdiff**(ring D)^{d},CEdiff)[1])
	)
    
--  Input: a free differential module D
--  Output: the module D' that would be the minimal part of D. 
-- (We don't work out the differentials.)
minimalPart = method();
minimalPart(DifferentialModule) := G->(
    if not isFreeModule G then error "G is not free";
    phi := map(ring G,ring G, apply(# gens ring G, i-> 0));
    Gbar := differentialModule phi(G);
    source mingens HH Gbar
    )



---
---
---
---TORIC BGG STUFF
---
---
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


--Input: (M,LL,VV) M a (multi)-graded S-module.
--             LL a list of degrees.
--    	      VV a list of positive integers e.g {1,3,5} paremtrizing variables from S
--            (eg x_1, x_3,x_5)  which we'll use to construct RR.
--Output:  The differenial module RR(M) in degrees from LL,
--         presented as a complex in homological degrees -1, 0 ,1
--         and with the same differential in both spots.
toricRR(Module,List,List) := (M,LL,VV) ->(
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
    tr := sum(VV, i-> SE_i*SE_(dim S+i));
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
S=kk[x_0,x_1,Degrees=>{1,1}]
D = toricRR(S^1,{0,1})
G = cornerDM({0},D,LengthLimit => 3)
G_0 == minimalPart G
tally degrees G_0
--So it
F = resDM(D, LengthLimit => 2)
tally degrees F_0
tally degrees minimalPart F
F.dd_1
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

--  Input:  a polynomial ring S
--  Output:  a list of all degrees between 0 and the anti-canonical degree
--  CAVEAT:  needs "Polyhedra" package.
effectivePart = method();
effectivePart(PolynomialRing,ZZ) := (S,n) ->(
    zd := {apply(#(degree S_0),i-> 0)};
    ed := degrees S|zd;
    P := convexHull transpose (n*(matrix ed));
    LP := latticePoints P;
    sort flatten apply(#LP,i-> entries transpose (latticePoints P)_(i))
    )

--  Input:  degrees d1, d2, and a ring S
--          Assumes d1,d2 are lists of integers of length n and that the variables
--          of S have degrees which are lists of integers of length n.
--  Output:  Checks whether d1 - d2 is an effective degree on S.
greaterEqual=method()
greaterEqual(List,List,Ring) := (d1,d2,S) -> hilbertFunction(d1-d2,S) != 0


--  Input:  A module/matrix/chain complex and a multidegree d.
--  Output:  The truncated module/matrix/chain complex in degrees <= d.
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


--   Input:  a ring S and a multidegree d.
--   Output:  the truncated Koszul complex of summands of degrees <= d.
truncatedKoszul = method();
truncatedKoszul(Ring,List) := (S,d)->(
    E := dualRingToric S;
    F := (toricLL(E^1))[-dim S];
    canon := sum degrees S;
    G := F**(ring F)^{-canon+d};
    source degreeTruncation(G,{0})
    )


--   Input:  a ring S, degrees d1 and d2, and a map f between koszul complexes of degree d2-d1.
--   Output:  the inducted map on truncated Koszul complexes.
truncatedKoszulMap = method();
truncatedKoszulMap(Ring,List,List,RingElement) := (S,d1,d2,f)->(
    if -remove(degree f,-1) != d2-d1 then error "Wrong degree for such a map";
    N1 := ptrunc(E^1,d1);
    N2 := ptrunc(E^1,d2);
    phi := map(N1**E^{d1|{0}},N2**E^{d2|{-last degree f}},matrix{{f}});
    toricLL phi
    )



--NOW WE GET TO A PART THAT REALLY NEEDS MORE WORK.
--The following develops a "corner complex" code.
--For weighted projective spaces, this can be used to compute parts of the Tate resolution,
--and therefore compute sheaf cohomology.
--But for other toric varieties, these corner complexes seem to compute something else.
--This actually raises a significant theoretical question:  is there any analogue of the corner complex
--for arbitrary toric varieties??

--Input:  a differential module F, and a corner degree cDeg.
--Output:  a new differential module F' where we have adjoined "killed" cycles of F of degree <= cDeg
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




cornerDM = method(TypicalValue => DifferentialModule,
            Options => {
    	    LengthLimit => 3
    	    });


--Input:  a differential module F, and a corner degree cDeg, and an (optional) LengthLimit.
--Output:  a new differential module F' where we have adjoined "killed" cycles of F of degree <= cDeg,
--         and we have itereated that procedure for the specified number of steps.
cornerDM(List,DifferentialModule) := opts -> (cDeg,F)->(
    n := opts.LengthLimit;
    scan(n, i-> F = oneStepCorner(cDeg,F));
    F
    )   



--
--Specialized functions for a Hirzebruch surface.
--


---
--  Does oneStepHirz but also lifts the map phi to the new module.
oneStepRows = (topDeg,F,rows,aut) -> (
    E := ring F;
    dF := degree F;
    H := res(coker F.dd_1,LengthLimit => 2);
    newSyz := (H.dd_2**(ring H)^{dF}) % H.dd_1;
    G = chainComplex newSyz;
    newSpots = {};
    D := degrees G_1;
    D1 := apply(D,i-> remove(i,-1));
--  We keep the syzygies which are:
--    "below" a specified degree topDeg (to avoid boundary effects)
--    in the specified rows, and
--    are nontrivial.
    scan(#D1, i->(if greaterEqual(topDeg,D1#i,S) and isSubset(set{D1#i#1},set(rows)) and submatrix(newSyz,{i}) != 0 
	    then(newSpots = newSpots|{i};)));
    phi := map(G_0,E^(apply(newSpots,i-> -D#i + dF)),(newSyz)_(newSpots));
--    assert(H.dd_1*phi == 0);
    psi := gens trim image(phi % (matrix H.dd_1));
--    assert(H.dd_1*psi == 0);
    Gnew := source psi;
    psiGF := map(Gnew**E^{dF},Gnew,0) || psi;
--This maps the new syzygies into G++F where G=Gnew and F=F_0.
    d1 := psi|(-1)*H.dd_1; 
    d2 := map(Gnew**E^{dF},Gnew++H_1, (i,j)->0);
    d := (d2||d1);
--This is the new differential on G++F.
--    assert(d^2 == 0)
--Now we extend the automorphism.
    oldAutGF := map(Gnew**E^{dF}, Gnew, (i,j) ->0)++aut;
    newAutGF := map(source d**E^{dF},Gnew,aut*psi // d1);
    --newAutGF := map(source d**E^{dF},Gnew,oldAutGF*(psiGF**E^{-dF}) // d);
    newAut := newAutGF | (map(Gnew,source aut, (i,j)->0)||-aut);
--    assert(-d*newAut - newAut*d == 0)
--assert(newAut^2 == 0).. 
    newF := differentialModule(chainComplex(d**E^{dF},d)[1]);
    (newF, newAut)  
)

multiStepRows = (topDeg,F,rows,aut,n) -> (
    for i from 1 to n do(
	LL := oneStepRows(topDeg,F,rows,aut);
	F = LL_0;
	aut = LL_1;
	);
    (F,aut)
)

--assumes "rows" is a singleton set.
oneStepVert = (botLeft,topRight,F,rows) -> (
    E := ring F;
--This code uses the parameter of the hirzebruch.
    a := (degree E_1)_0;
    dF := degree F;
    H := res(coker F.dd_1,LengthLimit => 2);
    newSyz := (H.dd_2**(ring H)^{dF}) % H.dd_1;
    G = chainComplex newSyz;
    newSpots = {};
    D := degrees G_1;
    D1 := apply(D,i-> remove(i,-1));
--    We keep the syzygies which are:
--    in the triangle (directions spanned by degrees of e_1,e_3)
--    in the specified rows, and are nontrivial.
--    scan(#D1, i->(if D1#i#0+D1#i#1 >= sum botLeft  and isSubset(set{D1#i#1},set(rows)) and(
    scan(#D1, i->(if D1#i#0+a*(D1#i#1) >= sum botLeft  and D1#i#1 <= min rows+1 and(
		 submatrix(newSyz,{i}) != 0 and D1#i#0 <= topRight#0 )
	    then(newSpots = newSpots|{i};)));
    phi := map(G_0,E^(apply(newSpots,i-> -D#i + dF)),(newSyz)_(newSpots));
--    assert(H.dd_1*phi == 0);
    psi := gens trim image(phi % (matrix H.dd_1));
--    assert(H.dd_1*psi == 0);
    Gnew := source psi;
    psiGF := map(Gnew**E^{dF},Gnew,0) || psi;
--This maps the new syzygies into G++F where G=Gnew and F=F_0.
    d1 := psi|(-1)*H.dd_1; 
    d2 := map(Gnew**E^{dF},Gnew++H_1, (i,j)->0);
    d := (d2||d1);
    differentialModule(chainComplex(d**E^{dF},d)[1])
    )


multiStepVert = (botLeft,topRight,F,rows,n)->(
     for i from 1 to n do(
	 F = oneStepVert(botLeft,topRight,F,rows);
	 --rows = rows + {-1};
	 );
    F
    )

botLeftAndTopRight = L->(
    min1 = min apply(L,l-> l_1);
    bL = min select(L,l-> l_1 == min1);
    max1 = max apply(L,l-> l_1);
    tR = max select(L,l-> l_1 == max1);
    (bL,tR)
    )

topLeft = L->(
    max1 = max apply(L,l-> l_1);
    tL = min select(L,l-> l_1 == max1);
    tL
    )

hirzResolve = (M,L,n1,n2)->(
    rows := unique apply(L,i-> i_1);
    F := toricRR(M,L,{0,2});
    aut = differential toricRR(M,L,{1,3});
    topDeg := topLeft(L);
    GA := multiStepRows(topDeg,F,rows,aut,n1);
    vertF := differentialModule( chainComplex(GA_1**(ring (GA_0))^{degree (GA_0)},GA_1)[1]);
    (botLeft,topRight) = botLeftAndTopRight(unique degrees vertF_0);
    multiStepVert(botLeft,topRight,vertF,{min rows - 1},n2)
    )

--Input:  the list of degrees computed in a Tate resolution.
--Output:  the vertices of the corresponding polytope.
corners = L->(
    LL := apply(L,l-> remove(l,-1));
    P := convexHull transpose matrix LL;
    vertices P
    )

matrixCorners = L->(
    LL := apply(L,l-> remove(l,-1));
    min1 := min apply(L,l-> l_1);
    max1 := max apply(L,l-> l_1);
    min0 := min apply(L,l-> l_0);
    max0 := max apply(L,l-> l_0);
    a := max0 - min0 + 1;
    b := max1 - min1 + 1;
    transpose map(ZZ^a,ZZ^b, (i,j) -> if (i+min0,max1 - j) == (0,0) then 5 else(
	    if isSubset(set({{i+min0,max1 - j}}),set(LL)) then 1 else 0)
	)
    )


makeConvex = L->(
    needsPackage "Polyhedra";
    P = convexHull transpose matrix L;
    LP = latticePoints P;
    flatten apply(#LP,i-> entries transpose (latticePoints P)_(i))
    )

end;

















restart
load "ToricTate.m2"
needsPackage "NormalToricVarieties"
X = hirzebruchSurface(1)
S = ring X
L = apply(effectivePart(S,2),i-> i+{2,1})
F = toricRR(S^1,L,{0,2})
aut = differential toricRR(S^1,L,{1,3});
topDeg = {0,3};
rows = {1,2,3};
GA = multiStepRows(topDeg,F,rows,aut,10);
--Computes by resolving the rows.
corners unique degrees GA_0_0
--This is the range of degree we've computed in.  Some long skinny trapezoid.
GA_0 --this is the new differential
(GA_1)^2 ==0  --this is the lifted automorphism, which still squares to zero.

--The rows correctly compute the cohomology groups.
T = tally degrees minimalPart(GA_0)
tally apply(keys T, k-> T#k == rank HH^(k#2)(X,sheaf S^{{k#0,k#1}}))
--everything correct up to this stage...

--Now we shift perspectives and use the lifted automorphism 
--to define a new differential on the same underlying module.
vertF = differentialModule( chainComplex(GA_1**(ring (GA_0))^{degree (GA_0)},GA_1)[1])
--We don't keep track of the automorphism at this stage (though maybe  we could?)
(botLeft,topRight) = botLeftAndTopRight(unique degrees vertF_0)
Fnew = multiStepVert(botLeft,topRight,vertF,{0},10)
T = tally degrees minimalPart Fnew;
corners keys T
--Kinda' like a big triangle: (2,3) -- (2,-9) -- (-9,1).
--This plots the degrees we are considering in a matrix (the "5" is the origin)
matrixCorners keys T
tally apply(keys T, k-> T#k == rank HH^(k#2)(X,sheaf S^{{k#0,k#1}}))
--And they're all correct!

--The "hirzResolve" code streamlines the process
restart
load "ToricTate.m2"
needsPackage "NormalToricVarieties"
X = hirzebruchSurface(1)
S = ring X
L = apply(effectivePart(S,1),i-> i+{2,1})
(M,L,n1,n2) = (S^1,L,14,14)
Fnew = hirzResolve(M,L,n1,n2)
T = tally degrees minimalPart Fnew;
tally apply(keys T, k-> T#k == rank HH^(k#2)(X,sheaf S^{{k#0,k#1}}))
corners keys T
matrixCorners keys T
--So it is correctly computing cohomology groups of the structure sheaf
--in a pretty huge range.


--The code also works on P^1 x P^1 (even though some aspects were hard-coded for the other example.)
restart
load "ToricTate.m2"
needsPackage "NormalToricVarieties"
X = hirzebruchSurface(0)
S = ring X
L = apply(effectivePart(S,2),i-> i+{2,1})
(M,L,n1,n2) = (S^1,L,12,11)
Fnew = hirzResolve(M,L,n1,n2)
T = tally degrees minimalPart Fnew;
tally apply(keys T, k-> T#k == rank HH^(k#2)(X,sheaf S^{{k#0,k#1}}))
--That false is just a boundary effect from a hard-coded thing.
scan(keys T, k-> if T#k != rank HH^(k#2)(X,sheaf(M**S^{{k#0,k#1}})) then print k)
--But setting the parameters right seems to be tricky...
matrixCorners keys T



--If we start working with other modules, then it gets more
--complicated, but still seems to work
restart
load "ToricTate.m2"
needsPackage "NormalToricVarieties"
X = hirzebruchSurface(1)
S = ring X
L = apply(effectivePart(S,2),i-> i+{2,1})
(M,L,n1,n2) = (S^1 / ideal(x_0+x_2),L,12,11)
Fnew = hirzResolve(M,L,n1,n2)
T = tally degrees minimalPart Fnew;
tally apply(keys T, k-> T#k == rank HH^(k#2)(X,sheaf (M**S^{{k#0,k#1}})))
matrixCorners keys T

--Things get subtle as the examples get more complicated.
restart
load "ToricTate.m2"
needsPackage "NormalToricVarieties"
X = hirzebruchSurface(1)
S = ring X
L = apply(effectivePart(S,2),i-> i+{2,1})
(M,L,n1,n2) = (S^1 / ideal(x_0*x_1+x_3),L,12,5)
Fnew = hirzResolve(M,L,n1,n2)
T = tally degrees minimalPart Fnew;
tally apply(keys T, k-> T#k == rank HH^(k#2)(X,sheaf (M**S^{{k#0,k#1}})))
scan(keys T, k-> if T#k != rank HH^(k#2)(X,sheaf(M**S^{{k#0,k#1}})) then print k)
--So there's one bad group, in degree {1,-4}.

--It doesn't seem to "disappear" via non-minimality if you keep resolving.
--(M,L,n1,n2) = (S^1 / ideal(x_0*x_1+x_3),L,12,8)
--Fnew = hirzResolve(M,L,n1,n2)
--T = tally degrees minimalPart Fnew;
--scan(keys T, k-> if T#k != rank HH^(k#2)(X,sheaf(M**S^{{k#0,k#1}})) then print k)

--But you can kind of see the issue:
matrixCorners keys T
--We've hit some funny boundary on the right hand side...


--So we might hope that increasing the positivity of the original truncation will let
--go further.  And that seems to work!
--Namely, if we shift "L" to the right by one...
L = apply(effectivePart(S,2),i-> i+{3,1})
(M,L,n1,n2) = (S^1 / ideal(x_0*x_1+x_3),L,12,6)
Fnew = hirzResolve(M,L,n1,n2)
T = tally degrees minimalPart Fnew;
--... then the first "error" doesn't appear until row -5.
scan(keys T, k-> if T#k != rank HH^(k#2)(X,sheaf(M**S^{{k#0,k#1}})) then print k)

--And if you shift to the right even further...
L = apply(effectivePart(S,2),i-> i+{6,1})
(M,L,n1,n2) = (S^1 / ideal(x_0*x_1+x_3),L,16,9)
time Fnew = hirzResolve(M,L,n1,n2)   --This one takes like 7 seconds.
T = tally degrees minimalPart Fnew;
--... then the first "error" doesn't appear until row -8.
scan(keys T, k-> if T#k != rank HH^(k#2)(X,sheaf(M**S^{{k#0,k#1}})) then print k)
--So we've gotten 156 cohomology groups correct in some wonky window 
matrixCorners keys T
#keys T
L = keys T;


---
---
---A bit of experimentation on a different hirzebruch.
---
load "ToricTate.m2"
needsPackage "NormalToricVarieties"
X = hirzebruchSurface(3)
S = ring X
L = makeConvex apply(effectivePart(S,1),i-> i+{1,1})
(M,L,n1,n2) = (S^1,L,16,0)
--
--Just resolving the rows
--
time Fnew = hirzResolve(M,L,n1,n2)
T = tally degrees minimalPart Fnew;
tally apply(keys T, k-> T#k == rank HH^(k#2)(X,sheaf(M**S^{{k#0,k#1}})))
matrixCorners keys T
--A couple false but they seem to just be "non-minimal effects".
--Namely the "falses" but pushed deeper as you keep resolving.
Fnew = hirzResolve(M,L,4,0);
T = tally degrees minimalPart Fnew;
scan(keys T, k-> if T#k != rank HH^(k#2)(X,sheaf(M**S^{{k#0,k#1}})) then print k)

Fnew = hirzResolve(M,L,7,0);
T = tally degrees minimalPart Fnew;
scan(keys T, k-> if T#k != rank HH^(k#2)(X,sheaf(M**S^{{k#0,k#1}})) then print k)


Fnew = hirzResolve(M,L,10,0);
T = tally degrees minimalPart Fnew;
scan(keys T, k-> if T#k != rank HH^(k#2)(X,sheaf(M**S^{{k#0,k#1}})) then print k)
--In other words, as we keep computinb and minimize, the falses disappear.



--Now resolving rows then going vertically.
--We now that we'll get some "falses" near the edges, from the rows.
--Amazingly, those "falses" don't seem to propogate:
(M,L,n1,n2) = (S^1,L,20,4)
time Fnew = hirzResolve(M,L,n1,n2)
--takes 23 seconds.
T = tally degrees minimalPart Fnew;
tally apply(keys T, k-> T#k == rank HH^(k#2)(X,sheaf(M**S^{{k#0,k#1}})))
matrixCorners keys T



































load "ToricTate.m2";
S = ZZ/101[x_0,x_1,x_2,x_3, Degrees => {{1},{1},{1},{3}}];
F = toricRR(S^1,toList({2}..{6}))
cDeg = {2}
G = cornerDM(cDeg,F,LengthLimit => 10)
--really slowly converges!!
tally degrees minimalPart G




restart
load "ToricTate.m2"
kk=ZZ/101
S=kk[x_0,x_1]
D = toricRR(S^1,toList(0..15))
FD = resDM(D,LengthLimit => 8)
tally degrees minimalPart FD
tally degrees minimalPart cornerDM({0},D,LengthLimit =>8)

needsPackage "NormalToricVarieties"
X = smoothFanoToricVariety(2,3)
S = ring X
F = toricRR(S^1, effectivePart(S,3),{0,2})
d4 = differential toricRR(S^1, effectivePart(S,3),{1,3,4});
d02 = differential F;
d4*d02+d02*d4



d = differential F
d^2
UGH!!!!!


G = cornerDM({0,0,0},F,LengthLimit =>2)
T = tally degrees minimalPart G - tally degrees F_0
HH^1(X,sheaf S^{{-2,1,-1}})
apply(keys T,t-> rank HH^(t_3)(X, sheaf S^{remove(t,-1)}) == T#t)

degree(x_0)
tally apply(keys T,t-> ((T#t)#3), remove((T#t),-1))
degrees S
HH^1(X,sheaf S^{{-2,1,-1}})



rank matrix((degrees S)_{0,2,4})
decompose ideal X
degrees S

kk=ZZ/101
S=kk[x_0,x_1,Degrees =>{1,2}]
D = toricRR(S^1,{0,1,2,3})
FD = resDM D
tally degrees minimalPart FD
tally degrees minimalPart cornerDM({0},D,LengthLimit =>5)



restart
load "ToricTate.m2"
S=ZZ/101[x,y];
M = S^1/(x^2,y^2);
phi = map(M,M**S^{-2},matrix{{x*y}})
D = differentialModule( chainComplex(phi**S^{-2},phi)[1])
FD = resDM D
tally degrees minimalPart FD
betti res HH D
betti res HH FD

restart
load "ToricTate.m2"
needsPackage "NormalToricVarieties"
X = hirzebruchSurface(1)
S = ring X
F = toricRR(S^1,apply(effectivePart(S,2),i-> i+{2,1}),{0,2})
aut = differential toricRR(S^1,apply(effectivePart(S,2),i-> i+{2,1}),{1,3})
tally degrees F_0
FD = corner   DM({2,1},F,LengthLimit => 1)
tally degrees minimalPart FD - tally degrees F_0
hilbertFunction({2,0},S)


rk = res kernel F
tally degrees rk_0
tally degrees rk_1

rb = res image F
tally degrees rb_0
tally degrees rb_1

load "ToricTate.m2"
S=ZZ/101[x];
M = S^1/(x^16);
phi = map(M**S^{-10},M,matrix{{x^10}})
D = differentialModule( chainComplex(phi,phi**S^{10})[1])
differential D
HH D
FD = resDM D
FD.dd_1
minimalPart FD


--Input a differential module D
--Output:  the CE complex F (with a map F-->D??)
compResDM = method(TypicalValue => DifferentialModule,
            Options => {
    	    LengthLimit => 3
    	    });
compResDM(DifferentialModule,List) := opts -> (D,cDeg) ->(
--we only want to keep cycles of low enough degree.
    n := opts.LengthLimit;
    d := degree D;
    cyc := res(kernel D,LengthLimit =>n);
    bou := res(image D,LengthLimit =>n);
    R := ring D;
    m := max(length cyc, length bou);
    -- this is code which turns a resolution into a differential module...
    L := apply(length cyc+1,j->(
	    transpose concatMatrices apply(m+1,i->map(cyc_j,cyc_i, if i == j+1 then cyc.dd_i else 0))
	));
    cycDiff := transpose(concatMatrices L);
    cycMod := cyc_0;
    scan(m+1, i-> cycMod = cycMod ++ ((cyc_(i+1))**(R)^{(i+1)*d}));
    L' := apply(length bou+1,j->(
	    transpose concatMatrices apply(m+1,i->map(bou_j,bou_i, if i == j+1 then bou.dd_i else 0))
	));
    bouDiff := transpose(concatMatrices L');
    bouMod := bou_0**(R)^{d};
    scan(m+1, i-> bouMod = bouMod ++ ((bou_(i+1))**(R)^{(i+2)*d}));
    --cycDiff and bouDiff are the differentials of cycle and boundary resolutions, as a diff module
    psi := map(cyc_0,bou_0,gens image D // gens kernel D);
    PSI = {psi};
    scan(m,i-> PSI = PSI|{PSI_(i)*bou.dd_(i+1) // cyc.dd_(i+1)} );
    K := apply(length cyc + 1,j->(
	    apply(length bou+1,i->(
		    map(cyc_j,bou_i, if j == i then PSI_i else 0)
		    ))));
    bouToCycDiff := transpose concatMatrices apply(K,i-> transpose concatMatrices i);
    lastMap := map(bouMod,cycMod**R^{-d},0);
    CEdiff := map(cycMod++bouMod,(cycMod++bouMod)**(ring D)^{-d}, (cycDiff|bouToCycDiff) || (lastMap|bouDiff));
    differentialModule(chainComplex(CEdiff**(ring D)^{d},CEdiff)[1])
	)