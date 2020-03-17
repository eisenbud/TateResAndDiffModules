--needsPackage "BGG";


--  Input: a polynomial ring
--  Output:  the Koszul dual exterior algebra, but with an additional 
--           ZZ-degree, the ``standard grading'' where elements of \bigwedge^k
--           have degree k.
dualRingToric = method();
dualRingToric(PolynomialRing) := (S) ->(
    kk := coefficientRing S;
    degs := apply(degrees S,d-> (-d)|{1});
    ee := apply(#gens S, i-> e_i);
    kk[ee,Degrees=>degs,SkewCommutative=> not isSkewCommutative S]    
    );



--
--
--
-- BGG for weighted projective space.
-- This came from "weightedBGG070816.m2" which is
-- old code Daniel, David and Frank wrote at Oberwolfach 
-- several years ago to do BGG 
-- on a weighted projective space (really the stack).  
--
-- The new code is a bit further down.
--

--  This is the starting point for computing a Tate module over weighted projective space.
--  Input:  a list L of degrees (should be consecutive probably, e.g. 3..10).
--          M an S-module where S is a polynomial ring with a nonstandard grading.
--          E the Koszul dual exterior algebra.  
--  Output: The free differential module RR(M) in degrees L.
--  Notes:  there were some subtleties about how large L needed to be relative
--          to the degrees of the variables of S, and we never sorted this out
--          precisely.
bggWeighted = method()
bggWeighted(List,Module,PolynomialRing) := Matrix => (L,M,E) ->(
    S :=ring(M);
    numvarsE := rank source vars E;
    ev := map(E,S,vars E);
    f0 := gens image basis(L_0,M);
    scan(#L-1,i-> f0 = f0 | gens image basis(L_(i+1),M));
    df0 = apply(flatten (degrees f0)#1,i-> {i,0});
    df1 = apply(flatten (degrees f0)#1,i-> {i,-1});
    SE := S**E;
    tr = sum(dim S, i-> SE_i*SE_(dim S+i));
    newf0 = sub(f0,SE)*tr;
    newg = contract(transpose sub(f0,SE),newf0);
    g' = sub(newg,E);
    map(E^df0,E^df1, g')
    )


--This ``resolves'' a free differential module one degree at a time.
--Input: A free differential module G which is exact up in degrees \geq bot
--Output: A larger free differential module G' which is exact in
--        degrees \geq bot - 1.
oneStep = (bot,G) -> (
    newSpots = {};
    D = degrees G_2;
    scan(#D, i->(if (D#i)_0 == -bot+1 then  newSpots = newSpots|{i};));
    --the above (D#i)_0 will need to be a dot product
    --or something when we leave weighted projective space
    Gpre = E^(apply(newSpots,i-> -D#i + {0,1}));
    phi = map(G_0,Gpre,(G.dd_2)_(newSpots));
    psi = gens trim image(phi % (matrix G.dd_1));
    Gnew = source psi;
    d1 = psi|G.dd_1;    
    d2 = map(Gnew**E^{{0,1}},Gnew++G_1, (i,j)->0);
    d = (d2||d1)
)

--Used for computing the Tate module..
--This just iterates the oneStep code, adjusting the bottom
--degree accordingly.
multistep = (bot,G,n)->(
    scan(n, i-> G = res(coker oneStep(bot-i,G),LengthLimit =>2));
    G
    )




--
--
--
--  This is the new code, which is currently hardcode for a Hirzebruch
--  of type 1, e.g. a blowup of PP^2 at a single point.
--  
--
--
--
needsPackage "NormalToricVarieties";

--  This is a (hacky) way to build the degree ranges that we use
--      in the various constructions.
--  Input:  a degree low and two integers c and r.
--  Output: the list of degrees L in a parallelogram
--          with lower left corner low, and the extends in directions (c,0)
--          and (-r,r).
degreeSetup = (low,c,r)->(
    addends := flatten apply(c+1,i->apply(r+1,j-> {i-j,j}));
    apply(addends,i-> low + i)  
)

--  This is the RR functor.  
--Input: (M,low,c,r) M is a module over S=Cox(X)
--         low is a degree, (c,r) integers.
--Output:  The differenial module RR(M) in degrees degreeSetup(low,c,r)
--
--NOTE: while this code is largely to the code for weighted projective space, 
--      it won't apply directly since degrees in weighted proj space are integers
--      and this code assumes degrees are lists.
RRfunctor = method();
RRfunctor(Module,List,ZZ,ZZ) := (M,low,c,r) ->(
    S :=ring(M);
    relationsM := gens image presentation M;
    numvarsE := rank source vars E;
    ev := map(E,S,vars E);
    L := degreeSetup(low,c,r);
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

--
--  EDITS START HERE on 3/15/2020
--  Idea is to compute via a "corner complex"
--  
--
--  EDITS
--Input:  F a free differential module
--Output:  a differential module which is acylic
--         in one lower degree... some total grading?  not working here.
--         The "degree" function is just (i_0,i_1) --> i_0+i_1.  I tried other ones too.
oneStepCornerHirz = (bot,F) -> (
    r := max apply(degrees F_0,i-> i_1+1);
    G := res(coker F.dd_1,LengthLimit => 2);
    newSpots = {};
    D := degrees G_2;
    scan(#D, i->(if (D#i)_0 + (D#i)_1 == bot-1 and (D#i)_1<r then(
		    newSpots = newSpots|{i};)));
    --
    Gpre := E^(apply(newSpots,i-> -D#i + {0,0,1}));
    phi := map(G_0,Gpre,(G.dd_2)_(newSpots));
    psi := gens trim image(phi % (matrix G.dd_1));
    Gnew := source psi;
    d1 := psi|G.dd_1;    
    d2 := map(Gnew**E^{{0,0,1}},Gnew++G_1, (i,j)->0);
    d := (d2||d1);
    chainComplex map(target d, source d, d)
)


--  Input:  F a free diff modeul
--  Output:  the degrees homology elements
homologyDegrees = F->(
    G := res(coker F.dd_1,LengthLimit => 2);
    newSpots = {};
    T := tally degrees G_0;
    D := degrees G_2;
    scan(#D, i->(if T#?{(D#i)_0 , (D#i)_1 , 0} == false then(
		    newSpots = newSpots|{D#i};)));
    tally newSpots	
    )

--  Input: F a free diff module
--  Output:  the degrees of homology (computed a different way)
homDegs2 = F->(
    F' = chainComplex(F.dd_1,(F.dd_1)**E^{{0,0,-1}});
    G := res HH_1 F';
    tally degrees G_0
)
--  Iterates oneStepCornerHirz
resCornerHirz = (bot,F,n)->(
    scan(n, i-> F = oneStepCornerHirz(bot-i,F));
    F
    )
-*
M = S^1
low = {1,1}
F = RRfunctor(M,low,4,4)
homologyDegrees F
homDegs2 F
--why does this give such a different answer???
tally degrees F_0
dF = F.dd_1;
target dF
source dF
target (dF**E^{{0,0,-1}})
source F.dd_1
G := res(coker F.dd_1,LengthLimit => 2);
tally degrees G_2
tally degrees G_0
bot = (low_0)+(low_1)
tally degrees F_0
G = resCornerHirz(bot,F,0)
checkCohomGroups(M,G)
tally degrees F_0
G = resCornerHirz(bot,F,1)
checkCohomGroups(M,G)
tally degrees G_0
hilbertFunction({1,2},S)
basis({1,0},S)
tally degrees F_0
    T := tally degrees G_0;
    cor := 0;
    scan(keys T,k->(
	    if rank HH^(k#2)(X,sheaf(M**S^{{k#0,k#1}})) == T#k then cor = cor +1 else print k;
	    --cor = cor+1;
	   ));
   HH^(0)(X,sheaf(S^{{1,0}}))
cor    out := toString(cor)|"/"|toString(#(keys T))|" cohom groups correct";
    out
*-




----EDITS ENDED HERE.  NOT WORKING!  










--Input: (M,L,v) same as above but v is a subset of the variables
--       and L = degreeSetup(low,c,r), since I was getting a bug for using
--       too many parameters.
--Output:  The differenial module RR(M)
--         but only including the degrees from v.
RRfunctor(Module,List,List) := (M,L,v) ->(
    S :=ring(M);
    relationsM := gens image presentation M;
    numvarsE := rank source vars E;
    ev := map(E,S,vars E);
    --L := degreeSetup(low,c,r);
    f0 := gens image basis(L_0,M);
    scan(#L-1,i-> f0 = f0 | gens image basis(L_(i+1),M));
    --f0 is the basis for M in degrees given by L
    df0 := apply(degrees source f0,i-> i|{0});
    df1 := apply(degrees source f0,i-> i|{-1});
    SE := S**E;
    tr := sum(v, i-> SE_i*SE_(dim S+i));
    newf0 := sub(f0,SE)*tr;
    relationsMinSE := sub(relationsM,SE);
    newf0 = newf0 % relationsMinSE;
    newg := contract(transpose sub(f0,SE),newf0);
    g' := transpose sub(newg,E);
    chainComplex map(E^df0,E^df1, g')
    )





--  Input:  M a module on Cox ring of a Hirzebruch
--          low the starting bidegree     
--          r = # rows
--          c = # cols
-- Output:  A free differential module in degree low .. low+{c-1,r-1}
--          where the differential is the "horizontal" one, i.e. the one
--          involving e_0 and e_2.  So these are the strands.
hirzRowRR = (M,low,c,r)->(
    S :=ring(M);
    relationsM := gens image presentation M;
    numvarsE := rank source vars E;
    ev := map(E,S,vars E);
    L := degreeSetup(low,c,r);
    f0 := gens image basis(L_0,M);
    scan(#L-1,i-> f0 = f0 | gens image basis(L_(i+1),M));
    df0 := apply(degrees source f0,i-> (-1)*i|{0});
    df1 := apply(degrees source f0,i-> (-1)*i|{-1});
    SE := S**E;
    f0 = sub(f0,SE);
    newf0 := f0*(sum({0,2}, i-> SE_i*SE_(dim S+i)));
    relationsMinSE := sub(relationsM,SE);
    newf0 = newf0 % relationsMinSE;
    newg := contract(transpose sub(f0,SE),newf0);
    g' := sub(newg,E);
    chainComplex map(E^df0,E^df1, g')
    ) 

--Input:  M a module
--        low = a corner bidegree
--        c = the number of columns we want to start with
--        Note: we are currently coding this with just two rows.  
--              That was to make it easier to debug, but it's probably not need anymore.
--Output: A pair (F,phi) where F is the free differential module on M
--        but whose differential only involves e_0 and e_2.  And where phi is a
--        map F -> F given by the differential only involving e_1 and e_3.
hirzRowWMap = (M,low,c)->(
    S :=ring(M);
    relationsM := gens image presentation M;
    numvarsE := rank source vars E;
    ev := map(E,S,vars E);
    --  Note that we've hardcoded L to only involve 2 rows.
    L := degreeSetup(low,c,1);
    f0 := gens image basis(L_0,M);
    scan(#L-1,i-> f0 = f0 | gens image basis(L_(i+1),M));
    df0 := apply(degrees source f0,i-> (-1)*i|{0});
    df1 := apply(degrees source f0,i-> (-1)*i|{-1});
    SE := S**E;
    f0 = sub(f0,SE);
    --  The following hardcodes the trace element to only involve e_0 and e_2
    newf0 := (sum apply({0,2},i-> SE_i*SE_(dim S+i)))*id_(target f0)*f0;
    relationsMinSE := sub(relationsM,SE);
    newf0 = newf0 % relationsMinSE;
    newg := contract(transpose sub(f0,SE),newf0);
    g' := sub(newg,E);
    F :=  chainComplex map(E^df0,E^df1, g');
    --Up to this point, this is basically the same code as  hirzRowRR.
    --But now we want to build the map F->F given by the e_1,e_3 part of the differential
    tr2 := sum({1,3}, i-> SE_i*SE_(dim S+i));
    nf0 := sub(f0,SE)*tr2;
    nf0 = nf0 % relationsMinSE;
    ng := contract(transpose sub(f0,SE),nf0);
    g'' := sub(ng,E);
    phi := map(F,F**E^{{0,0,-1}},i->g'');
    (F,phi)   
    )

--
--
--   This is to "resolve" the free differential module F one step at a time.
--   It is used in "resAndExtend" below.  It is a variation on the oneStep
--   code we wrote for weighted projective space.
--  
--Input:  F a free differential module with differential only involving e_0,e_2.
--        We assume were acyclic in degrees \geq bot.
--        this corrects for issues that arise from our choice of L
--        in the construction of F.
--Output:  a differential module which is acylic
--         in one lower degree
oneStepHirz = (bot,F) -> (
    r := max apply(degrees F_0,i-> i_1+1);
    --  We seemed to get bugs if we didn't limit the range where we allowed
    --  new generators.  I think these are boundary issues from the fact that
    --  RR(M) doesn't extend infinitely in the positive directions.
    G := res(coker F.dd_1,LengthLimit => 2);
    newSpots = {};
    D := degrees G_2;
    scan(#D, i->(if (D#i)_0 + (D#i)_1 == bot-1 and (D#i)_1<r then(
		    newSpots = newSpots|{i};)));
    Gpre := E^(apply(newSpots,i-> -D#i + {0,0,1}));
    phi := map(G_0,Gpre,(G.dd_2)_(newSpots));
    psi := gens trim image(phi % (matrix G.dd_1));
    Gnew := source psi;
    d1 := psi|G.dd_1;    
    d2 := map(Gnew**E^{{0,0,1}},Gnew++G_1, (i,j)->0);
    d := (d2||d1);
    chainComplex map(target d, source d, d)
)


--  Iterates oneStepHirz.  But this is vestigial, replaced by multiResAndExtend
resHirz = (bot,F,r,n)->(
    scan(n, i-> F = oneStepHirz(bot-i,F,r));
    F
    )


--  Does oneStepHirz but also lifts the map phi to the new module.
resAndExtend = (bot,F,phi) ->(
    r := max apply(degrees F_0,i-> i_1+1);
    Fres := oneStepHirz(bot,F);
    diffRank := rank Fres_0 - rank F_0;
    Fnew := E^(apply(diffRank, i-> (-1)*(degrees (Fres_0))_i));
    phiPadded := map(Fnew,Fnew**E^{{0,0,-1}},(i,j)->0)++phi_0;
    S1 := toList(0..diffRank-1);
    S2 := toList(diffRank..rank Fres_0-1);
    epsilon := map(Fres_0**E^{{0,0,-1}},Fnew**E^{{0,0,-2}},(Fres.dd_1)_S1);
    phiNewGuy := -phiPadded*epsilon // Fres.dd_1;
    phiN := phiNewGuy|phiPadded_S2;
    phiNew := map(Fres,Fres**E^{{0,0,-1}},i->phiN);
    (Fres,phiNew)
    )


--  Iterates resAndExtend.
multiResAndExtend = (bot,F,phi,n)->(
    scan(n, i-> (F,phi) = resAndExtend(bot-i,F,phi));
    (F,phi)
    )




--  This is basically oneStepHirz, but using the e_1,e_3 differential
--  instead of the e_0,e_2 differential.
altStepHirz = (bot,F,s,t) -> (
    G := res(coker F.dd_1,LengthLimit => 2);
    newSpots = {};
    D := degrees G_2;
    scan(#D, i->(if (D#i)_1 == bot-1 and (D#i)_0<s and (D#i)_0+(D#i)_1>t  then(
		    newSpots = newSpots|{i};)));
    Gpre := E^(apply(newSpots,i-> -D#i + {0,0,1}));
    phi := map(G_0,Gpre,(G.dd_2)_(newSpots));
    psi := gens trim image(phi % (matrix G.dd_1));
    Gnew := source psi;
    d1 := psi|G.dd_1;    
    d2 := map(Gnew**E^{{0,0,1}},Gnew++G_1, (i,j)->0);
    d := (d2||d1);
    chainComplex map(target d, source d, d)
)

--  Iterates altStepHirz.
multiAltStepHirz = (bot,F,s,t,n)->(
    scan(n, i-> F = altStepHirz(bot-i,F,s,t));
    F
    )


--  Finally, this puts it all together.
--  Input:  M a multigraded module over the Cox ring of the Hirzebruch surface X
--          low = the lower corner degree.  Should probably be in reg(M) or something.
--          c = the number columns we start with.
--          So we start by computing RR(M) for degrees in the parallelogram spanned
--          by low, low+(-1,1), low+(c,0), and low + (c-1,1).
--          Then we "resolve" n1 steps with respect to the differential on e_0,e_2
--          As we resolve, we lift the differential on e_1,e_3.
--          Finally we resolve n2 steps with respect to the differential on e_1,e_3.
--  Output:  G' a free differential module that agrees with the Tate module in some degrees
--          
tateCompute = (M,low,c,n1,n2)->(
    (F,phi) := hirzRowWMap(M,low,c);
    (G,psi) = multiResAndExtend(sum low,F,phi,n1);
    F' = chainComplex psi_0;
    G' = multiAltStepHirz(low_1,F',c,sum low - n1,n2);
    G' 
    )





--  Sanity check that we're getting the right cohomology groups
--  Compares the cohomology groups computed by tateCompute and a direct
--  computation using the NormalToricVarieties package.
checkCohomGroups = method()
checkCohomGroups(ChainComplex) := String =>(F)->(
    T := tally degrees F_0;
    cor := 0;
    scan(keys T,k->(
	    if rank HH^(k#2)(X,sheaf S^{{k#0,k#1}}) == T#k then cor = cor +1;
	    --cor = cor+1;
	   ));
    out := toString(cor)|"/"|toString(#(keys T))|" cohom groups correct";
    out
    )

checkCohomGroups(Module,ChainComplex) := String =>(M,F)->(
    T := tally degrees F_0;
    cor := 0;
    scan(keys T,k->(
	    if rank HH^(k#2)(X,sheaf(M**S^{{k#0,k#1}})) == T#k then cor = cor +1;
	    --cor = cor+1;
	   ));
    out := toString(cor)|"/"|toString(#(keys T))|" cohom groups correct";
    out
    )



--  Used in debugging.
findErrorInTateCompute = (M,low,c,n1,n2)->(
    (F,phi) := hirzRowWMap(M,low,c);
    print checkCohomGroups(M,F);
    (G,psi) = multiResAndExtend(sum low,F,phi,n1);
    F' = chainComplex psi_0;
    print checkCohomGroups(M,F');
    G' = multiAltStepHirz(low_1,F',c,sum low - n1-1,n2);
    print checkCohomGroups(M,G');
    G' 
    )
--


    
end
--
restart
load "diffModules.m2"
X = hirzebruchSurface(1);
S = ring X;
E = dualRingToric S;


M = S^1;
G = tateCompute(M,{0,0},4,8,8)
--The output is a free differential module, represented by a complex.
--Here it's between free modules of rank 402.
--We check that it is square zero and homogeneous
G.dd_1^2 == 0
--tally degrees G_0
isHomogeneous G
--Regarding the input: the parameters ({0,0},4,8,8).
--    The {0,0} and the 4 are used in determining the starting
--    module RR(M).  We need {0,0} in the multigraded regularity or something.
--    And the "4" is roughly how many degrees we put into RR(M).
--The first "8" is how far we resolve horizontally.
--The second "8" is how far we resolve vertically.

--You can see the degrees of the Tate module we computed:
tally degrees G_0
--Here is how to interpret this.  The sheaf of M is OO.
--The output {a,b,c} => d means "rank H^c(OO(a,b)) = d"
--For instance the third line is  {-1, -4, 2} => 6.  We can check:
HH^2(X,OO_X(-1,-4))
--So you can see that we really computed a lot of cohomology groups.
--I also wrote a simple code to checks correctness:
checkCohomGroups(S^1,G)

--Here is the same example M = S^1, but starting the 
--resolution at a different degree.
G = tateCompute(M,{1,1},4,8,8)
tally degrees G_0
checkCohomGroups(S^1,G)


--Here we let M be the structure sheaf of a point.
(M,low,c,n1,n2) = (S^1/ideal((x_0-x_2,x_0*x_1+x_3)),{1,1},3,8,8)
G = tateCompute(M,low,c,n1,n2)
checkCohomGroups(M,G)
tally degrees G_0
--You can see that it's just a bunch of H^0 = QQ^1, as expected.

--Here's a curve which has genus 1.  
M = S^1/ideal(random({1,2},S));
G = tateCompute(M,{1,2},6,4,4)
tally degrees G_0
--You can see its genus by seeing {0,0,1} => 1 in the above.
checkCohomGroups(M,G)
                  
--There are still some bugs around the boundaries, though.
--The issue seems to be if you push the parameters too far, or something.
--In this sequence, all I'm doing is changing the starting degree
--and the number of steps used to resolve.
M = S^1/ideal(random({1,1},S));
G = tateCompute(M,{1,1},2,4,3)
checkCohomGroups(M,G)
G = tateCompute(M,{1,1},2,5,3)
checkCohomGroups(M,G)
T = tally degrees G_0
scan(keys T,k-> if rank HH^(k#2)(X,sheaf(M**S^{{k#0,k#1}})) != T#k then print k)
--so we get an error in degree {0,-2} and {-1,-1}
--But we can correct that by increasing the parameters
G = tateCompute(M,{2,2},2,7,4)
checkCohomGroups(M,G)
T = tally degrees G_0
--Note that this now correctly computes in degrees {0,-2} and {-1,-1}.
--But pushing too far still causes issues:
G = tateCompute(M,{2,2},2,8,5)
checkCohomGroups(M,G)
--Anyways, not sure exactly what is happening there.






--  Generalize DM-cover algorithm

--  Input:  a differential module (expressed as a complex M<--M)
--  Output: one step of the minimal free cover 
oneStepCover = (F) -> (
    --r := max apply(degrees F_0,i-> i_1+1);
    --G := res(coker F.dd_1,LengthLimit => 2);
    F' = chainComplex(F.dd_1,F.dd_1);
    G := res HH_1 F';
    psi := map(F_0,G_0,gens (HH_1 F'));
--    psi := map(F_0,source pm,pm);
--    G := res ker F.dd_1;
--    psi := map(F_0,G_0,gens ker F.dd_1);
    newD = map(F_0++G_0,F_0++G_0,matrix{{F.dd_1,psi},{map(G_0,F_0,0),map(G_0,G_0,0)}});
    assert (newD^2 == 0);
    chainComplex newD
)
--F0 = F
F1 = oneStepCover(F)
F2 = oneStepCover(F1)
F3 = oneStepCover(F2)
F4 = oneStepCover(F3)

betti F4_0
F4.dd_1

F' = chainComplex(F.dd_1,F.dd_1)


F = F2
newD
S = ZZ/101[x]
M = S^1/(x^3)
phi = map(M,M,matrix{{x^2}})
phi^2
F = chainComplex({phi})
--betti res HH_1 F
