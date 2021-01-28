
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

--crazy new example
restart
load "ToricTate.m2";
R = QQ[x,y]
M = R^2;
phi = map(M,M**R^{-2},matrix{{x*y, -x^2},{y^2,-x*y}})
D = differentialModule(phi)
r = resDM D
assert(r.dd_1^2 == 0)
r.dd_1
(r,eps) = resDMwMap D
D.dd_0*eps - eps*r.dd_1
betti res homology D
betti res prune homology r


restart
load "ToricTate.m2";
R = QQ[x,y,z]
M = R^1/ideal(x^2,y^2,z^2);
phi = map(M,M**R^{-3},matrix{{x*y*z}})
D = differentialModule(phi)
r = resDM(D,LengthLimit => 3)
r.dd_1^2
r.dd_1
eps = map(D_0,r_0,{{z,y,x,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0}})
D.dd_0*eps - eps*r.dd_1
--so we have a well defined map r-->D of differential modules.
betti res homology D
betti res prune homology r
--seem to have the same homology.
isHomogeneous r.dd_1


restart
load "ToricTate.m2";
R = QQ[x,y,z]
M = R^1/ideal(x^2,y^2,z^2);
phi = map(M,M**R^{-3},matrix{{x*y*z}})
D = differentialModule(phi)
r = resDM(D,LengthLimit => 3)
r.dd_1^2 == 0
r.dd_1
isHomogeneous r.dd_1
betti res kernel D
betti res image D
rank(r.dd_1 % ideal(x,y,z))
-- 22 - 14 = 8
tally degrees minimalPart r

///


--  This code uses the Cartan-Eilenberg construction to build a "free resolution"
--  of an arbitrary differential module.
--  It could use some work.
--  Weirdly it only involves elements of Ext^0 and Ext^1... (see the file

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
    -- this is code which turns a free complex into a differential module...
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
    epsB0 = map(D_0,bou_0, gens image D.dd_0 // gens image D.dd_0);
    epsZ0 = map(D_0,cyc_0,gens kernel D);
    psi := -map(cyc_0,bou_0,gens image D // gens kernel D);
    PSI = {psi};
    scan(m,i-> PSI = PSI|{-PSI_(i)*bou.dd_(i+1) // cyc.dd_(i+1)} );
    tau := map(cyc_0,bou_1, -epsB0*bou.dd_1 // epsZ0);
    dummy := map(bou_0,0,0);
    TAU = {dummy,tau};
    scan(toList(2..m),i-> TAU = TAU|{-TAU_(i-1)*bou.dd_i // cyc.dd_(i-1)});
--I want TAU_i to be the map from bou_i, so we adjoin a dummy variable.
    K := apply(length cyc + 1,j->(
	    apply(length bou+1,i->(
		    map(cyc_j,bou_i, if j == i then PSI_i else 0)
		    ))));
    bouToCycPSI := transpose concatMatrices apply(K,i-> transpose concatMatrices i);
    K' := apply(length cyc + 1,j->(
	    apply(length bou+1,i->(
		    map(cyc_j,bou_i, if j == i - 1 then TAU_i else 0)
		    ))));
    bouToCycTAU := transpose concatMatrices apply(K',i-> transpose concatMatrices i);
    bouToCyc = bouToCycPSI + bouToCycTAU;
    lastMap := map(bouMod,cycMod**R^{-d},0);
    CEdiff := map(cycMod++bouMod,(cycMod++bouMod)**(ring D)^{-d}, (cycDiff|bouToCyc) || (lastMap|bouDiff));
    differentialModule(chainComplex(CEdiff**(ring D)^{d},CEdiff)[1])
	)

--  same as resDM except it outputs a pair (r,eps)
--  where r is the resDM and epsilon is the map r-->D.
resDMwMap = method(TypicalValue => DifferentialModule,
            Options => {
    	    LengthLimit => 3
    	    });

resDMwMap(DifferentialModule) := opts -> (D) ->(
    n := opts.LengthLimit;
    d := degree D;
    cyc := res(kernel D,LengthLimit =>n);
    bou := res(image D,LengthLimit =>n);
    R := ring D;
    m := max(length cyc, length bou);
    -- this is code which turns a free complex into a differential module...
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
    epsB0 = map(D_0,bou_0, gens image D.dd_0 // gens image D.dd_0);
    epsZ0 = map(D_0,cyc_0,gens kernel D);
    psi := -map(cyc_0,bou_0,gens image D // gens kernel D);
    PSI = {psi};
    scan(m,i-> PSI = PSI|{-PSI_(i)*bou.dd_(i+1) // cyc.dd_(i+1)} );
    tau := map(cyc_0,bou_1, -epsB0*bou.dd_1 // epsZ0);
    dummy := map(bou_0,0,0);
    TAU = {dummy,tau};
    scan(toList(2..m),i-> TAU = TAU|{-TAU_(i-1)*bou.dd_i // cyc.dd_(i-1)});
--I want TAU_i to be the map from bou_i, so we adjoin a dummy variable.
    K := apply(length cyc + 1,j->(
	    apply(length bou+1,i->(
		    map(cyc_j,bou_i, if j == i then PSI_i else 0)
		    ))));
    bouToCycPSI := transpose concatMatrices apply(K,i-> transpose concatMatrices i);
    K' := apply(length cyc + 1,j->(
	    apply(length bou+1,i->(
		    map(cyc_j,bou_i, if j == i - 1 then TAU_i else 0)
		    ))));
    bouToCycTAU := transpose concatMatrices apply(K',i-> transpose concatMatrices i);
    bouToCyc = bouToCycPSI + bouToCycTAU;
    lastMap := map(bouMod,cycMod**R^{-d},0);
    CEdiff := map(cycMod++bouMod,(cycMod++bouMod)**(ring D)^{-d}, (cycDiff|bouToCyc) || (lastMap|bouDiff));
    RD := differentialModule(chainComplex(CEdiff**(ring D)^{d},CEdiff)[1]);
    epsBou = concatMatrices( {epsB0} | apply(length bou, i-> map(D_0,bou_(i+1),0))    );
    epsCyc = concatMatrices( {epsZ0} | apply(length cyc, i-> map(D_0,cyc_(i+1),0))    );
    eps := epsCyc|epsBou;
    (RD,eps)
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



--  Input:  a free complex F and a degree d
--  Output: the corresponding free differential module of degree da
foldComplex = method();
foldComplex(ChainComplex,ZZ) := DifferentialModule => (F,d)->(
    R := ring F;
    L := apply(length F+1,j->(
	    transpose concatMatrices apply(length F+1,i->map(F_j,F_i, if i == j+1 then F.dd_i else 0))
	));
    FDiff := transpose(concatMatrices L);
    FMod := F_0;
    scan(length F+1, i-> FMod = FMod ++ ((F_(i+1))**(R)^{(i+1)*d}));
    differentialModule(chainComplex(FDiff**(ring F)^{d},FDiff)[1])
    )