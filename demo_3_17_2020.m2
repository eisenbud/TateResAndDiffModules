--  On weighted projective space, this converts a free diff module to 
--  a cohomology table, presented as column vector.
tallyToCohomWeighted = N ->(
    L := degrees N;
    T := tally degrees(N);
    topX := max apply(degrees N, d-> d_0);
    botX := min apply(degrees N, d-> d_0);
    transpose matrix{apply(toList(-8..8),i->(
		  sum apply(max apply(L,d-> d_1)+1,k->(
			  if T#?{-i,k} then t^k*(T#{-i,k}) else 0  
	    ))))}
)


--  From a polynomial ring S creates the dual ring E (with the "extra" grading).
dualRingToric = method();
dualRingToric(PolynomialRing) := (S) ->(
    kk := coefficientRing S;
    degs := apply(degrees S,d-> (-d)|{1});
    ee := apply(#gens S, i-> e_i);
    kk[ee,Degrees=>degs,SkewCommutative=> not isSkewCommutative S]    
    );



--
--  EDITED on 3/17/2020: fixed positive/negative grading and
--                       made the output a chain complex instead of a matrix
--                       otherwise identical to old code.
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
    df0 = apply(flatten (degrees f0)#1,i-> {-i,0});
    df1 = apply(flatten (degrees f0)#1,i-> {-i,-1});
    SE := S**E;
    tr = sum(dim S, i-> SE_i*SE_(dim S+i));
    newf0 = sub(f0,SE)*tr;
    newg = contract(transpose sub(f0,SE),newf0);
    g' = sub(newg,E);
    chainComplex map(E^df0,E^df1, g')
    )


--This ``resolves'' a free differential module one degree at a time.
--Input: A free differential module G which is exact up in degrees \geq bot
--Output: A larger free differential module G' which is exact in
--        degrees \geq bot - 1.
oneStep = (bot,F) -> (
    G := res(coker F.dd_1,LengthLimit => 2);
    newSpots = {};
    D = degrees G_2;
    scan(#D, i->(if (D#i)_0 == bot-1 then  newSpots = newSpots|{i};));
    Gpre = E^(apply(newSpots,i-> -D#i + {0,1}));
    phi = map(G_0,Gpre,(G.dd_2)_(newSpots));
    psi = gens trim image(phi % (matrix G.dd_1));
    Gnew = source psi;
    d1 = psi|G.dd_1;    
    d2 = map(Gnew**E^{{0,1}},Gnew++G_1, (i,j)->0);
    d = (d2||d1);
    chainComplex d 
)


--This ``resolves'' a free differential module one degree at a time.
--Input: A free differential module G which is exact up in degrees \geq bot
--Output: A larger free differential module G' which is exact in
--        degrees \geq bot - 1.
oneStepNonMin = (bot,F) -> (
    G := res(coker F.dd_1,LengthLimit => 2);
    newSpots = {};
    D = degrees G_2;
    scan(#D, i->(if (D#i)_0 <= bot-1 then  newSpots = newSpots|{i};));
    Gpre = E^(apply(newSpots,i-> -D#i + {0,1}));
    phi = map(G_0,Gpre,(G.dd_2)_(newSpots));
    psi = gens trim image(phi % (matrix G.dd_1));
    Gnew = source psi;
    d1 = psi|G.dd_1;    
    d2 = map(Gnew**E^{{0,1}},Gnew++G_1, (i,j)->0);
    d = (d2||d1);
    chainComplex d 
)


--This just iterates the oneStep code, adjusting the bottom
--degree accordingly.
multiStep = (bot,G,n)->(
    scan(n, i-> G = oneStep(bot-i,G));
    G
    )

multiStepNonMin = (bot,G,n)->(
    scan(n, i-> G = oneStepNonMin(bot-i,G));
    G
    )

--Hacky code for producing the a cohom table from a non-minimal free DM
nonMinCohom = G ->(
    barD := G.dd_1 %( ideal gens E);
    Gbar := chainComplex(barD**E^{{0,1}}, barD);
    rbar := res(prune HH_1(Gbar), LengthLimit => 0);
    tallyToCohomWeighted(rbar_0)
)

end;



--
restart
load "demo_3_17_2020.m2"
--  Before diving into these examples, it's probably worth skimming over the code above.
--  There are only 5 functions.

--  Setup for P(1,1,2)
S = ZZ/101[x_0,x_1,x_2, Degrees => {1,1,2}];
E = dualRingToric S;

--  bggWeighted is the RR functor.
M = S^1;
L = toList(2..5);
F = bggWeighted(L,M,E)
--  If you want to see the degrees of the gens:
betti (F_0)

--  Or in the format which will encode cohomology groups
--  columns go from degree -8 to degree 8
R = QQ[t];
tallyToCohomWeighted(F_0)
--  

--  oneStep "resolves" F for one extra degree.
--  The following assumes F is exact in degree 2 and then proceeds 10 steps.
G = oneStep(2,F)
tallyToCohomWeighted(G_0)
--  so we added 2 generators of degree 2.
--  But we threw out some of the other homology of G.  Let's lookt it by hand.
H = res(coker F.dd_1,LengthLimit => 2);
T = tally degrees(H_2)


--  multiStep iterates over oneStep
H = multiStep(2,F,10)
tallyToCohomWeighted(H_0)

--  now we try the nonminimal code:
G = multiStepNonMin(2,F,10)
--  noMinCohom computes the Betti table of the minimization (but not the minimization_
nonMinCohom(G)
--  checking that they give the same thing.
nonMinCohom(G) == tallyToCohomWeighted(H_0)
--  Woo hoo!



--Let's do a degree 10 curve in P(1,1,2), which has genus 16.
--We make sure that L encompasses degree 10.
L = toList(7..14);
M = S^1/(random(10,S));
F = bggWeighted(L,M,E);
betti (F_0)
--  the range of tallyToCohomWeighted is hardcoded as -8 .. 8
tallyToCohomWeighted(F_0)

G = multiStep(L_0,F,20);
--Here we've extended the differential module 20 steps
--But you can see how Betti numbers correspond to cohom groups
betti(G_0)
--To see the cohomology groups we do:
tallyToCohomWeighted(G_0)

--  goes slower with the non-minimal code.
H = multiStepNonMin(L_0,F,20);
CT = nonMinCohom(H)
CT == tallyToCohomWeighted(G_0)

--For instance, let's check that H^1(M) = QQ^16 (the genus of the curve):
T = tally degrees G_0;
T#{0,1}


--  New example.
--  Let's do a smooth point on P(1,1,2):
M = S^1/ideal(x_0,x_2);
L = toList(4..8);
F = bggWeighted(L,M,E);
G = multiStep(L_0,F,12);
tallyToCohomWeighted(G_0)
H = multiStepNonMin(L_0,F,12);
nonMinCohom(H)

--  Or the stacky point on P(1,1,2):
M = S^1/ideal(x_0,x_1);
L = toList(4..8);
F = bggWeighted(L,M,E);
G = multiStep(L_0,F,12);
tallyToCohomWeighted(G_0)
H = multiStepNonMin(L_0,F,12);
nonMinCohom(H)


--
--  Finally let's do a crazy curve on P(1,2,3,4):
S = ZZ/101[x_0..x_3, Degrees =>{1,2,3,4}];
E = dualRingToric S;
M = S^1/(random(8,S),random(6,S));
L = toList(10..20);
F = bggWeighted(L,M,E);
G = multiStep(L_0,F,18);
tallyToCohomWeighted(G_0)
--  Woah!  Don't know what to make of that...
--  At least there's no H^2 (it's a curve).
--  Let's check the genus:
T = tally degrees G_0;
T#{0,1}
--  So genus 5.  Which:  omega_C = OO_C(-1-2-3-4+8+6) = OO_C(4).
--  Which has 5 global sections because
hilbertFunction(4,S)


