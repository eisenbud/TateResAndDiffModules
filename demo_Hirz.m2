restart
load "diffModules.m2"

X = hirzebruchSurface(1);
S = ring X;
E = dualRingToric S;
M = S^1
low = {0,0}
(c,r) = (1,1)
F = RRfunctor(M,low,c,r)
tally degrees F_0

--  this code defines a bunch of degrees to use for the RR-functors:
L = degreeSetup(low,c,r)

--  A variant of the RRfunctor lets you compute RR with respect any subset
--  of variables.  We showed in Tate_DM.pdf that each of these extends to
--  an everywhere exact Tate resolution.
F02 = RRfunctor(M,L,{0,2})
F02.dd_1
F13 = RRfunctor(M,L,{1,3})
F13.dd_1

--  We start with the a 02-module.  But we want the 13-map to also
--  be present, as an endomorphism of F02 (as a diff module).
--  hirzRowWMap produces the 02-complex along with that endomorphism.
--  It is hardcode to only ivolve two rows
(F,d13) = hirzRowWMap(M,low,c);
F
tally degrees F_0
d13
--  Checking that d13 commutes with the differential of F:
F.dd_1*(d13_0) + (d13_1)*F.dd_1 == 0

--  We now resolve horizontally, adding degree by degree. 
--  We have everything in total degree 0.  But there is nothing
--  new in total degree -1:
oneStepHirz(0,F) == F
--  So let's add in degree -2:
G = oneStepHirz(-1,F)
tally degrees G_0
--  The new generators have degree {-2,0} and {-3,1}
--  and correspond to H^1 groups.
QQ[t]
tallyToCohom G_0

--  We can continue along the rows:
G = resHirz(0,F,8);
tallyToCohom G_0


-- Of course, doing this we could produce an upper-half plane complex.
-- If we want a bigger bite of the Tate resolution, we need to add rows.
-- Each row is itself a free diff module.  
-- And d13 is a morphism of diff modules, but only on the righthand portion.
-- By our lifting lemma, we can extend d13 to a morphism on the whole rows.
-- We do this:
(G,psi) = resAndExtend(-1,F,d13);
tallyToCohom G_0
G.dd_1*(psi_0) + (psi_1)*G.dd_1 == 0
-- Potential issue in code.  I think {0,0} wasn't positive enough?
-- Because it wants to lift d13 to a map involving more than just e_1,e_3.
G.dd_1*(psi_0) + (psi_1)*G.dd_1

-- Regardless, by starting with a more ample degree, we can avoid it:
low = {1,1};
L = degreeSetup(low,c,r);
(F,d13) = hirzRowWMap(M,low,c);
--  F is exact in total degrees >=2.  So we do:
(G,psi) = multiResAndExtend(2,F,d13,10);
tallyToCohom G_0
G.dd_1*(psi_0) + (psi_1)*G.dd_1 == 0

--  Now we want to switch gears and start adding rows.
--  So we let F' be a new chain complex with differential psi.
F' = chainComplex psi_0;
--  We now resolve this free DM similarly:
G' = multiAltStepHirz(1,F',c,sum low - 10,10);
--  The parameters impose conditions on which homology generators are "valid"
--  and which are "boundary" effects.
--  We only add generators one row down; and we don't allow generators too 
--  far to the right or where x+y is too negative.  In other words,
--  we are filling in a right triangle of entries boundaries bounded by
--  x+y > A; x < B; and rows from 1,2 (where we started) on downwards.
tallyToCohom G'_0

--  For comparison:
cohomMat = matrix apply(toList(-6..5),i-> apply(toList(-6..5),j->
	sum apply(3,k-> t^k*(rank HH^k(X,sheaf S^{{j,-i}})))
	))
cohomMat - tallyToCohom G'_0 


--
--
-- Let's do some other examples.
--
--

--M is the structure sheaf of a point.
(M,low,c,n1,n2) = (S^1/ideal((x_0-x_2,x_0*x_1+x_3)),{1,1},3,8,8)
G = tateCompute(M,low,c,n1,n2)
tallyToCohom(G_0)

--Here's a curve which has genus 1.  
M = S^1/ideal(random({1,2},S));
G = tateCompute(M,{1,2},6,4,4)
tallyToCohom(G_0)
--You can see its genus by computing the number of gens
--of degrees {0,0,1} in G_0:
T = tally degrees G_0
T#{0,0,1}


G = tateCompute(M,{1,3},6,6,6)
tallyToCohom(G_0)
checkCohomGroups(M,G)

--There is still a very notable flaw: to get a big chunk of the cohomology table
--you seem need to start with a more positive chunk of RR(M).
--Computationally problematic.  Also not even clear you can reach arbitrarily
--negative portions of the cohomology table...
