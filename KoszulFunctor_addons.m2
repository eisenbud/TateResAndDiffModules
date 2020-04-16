--Input:  a free diff module for Beilinson window
--Output:  a hash table H where H#(i,j) is the chain complex
--         map corresponding to that entry
--Caveat:  might require monomial entries??
--In essence, this codes just takes the (i,j) entry of a matrix,
--spits out the corresponding map of chain complex (under the proposed U-functor)
--and then encodes that in a hash table (i,j) => (corresponding chain complex map)
--
diffModToChainComplexMaps = TB->(
    ijs := flatten apply(rank TB_0,i->apply(rank TB_1,j->(i,j)));
    zeroijs := select(ijs,ij->TB.dd_1_ij==0);
    nonzeroijs := select(ijs,ij->TB.dd_1_ij!=0);
--   allKeys := apply(ijs,ij-> {ij=> (i=ij_0;(-drop((degrees TB_0)_i,-1),TB.dd_1_ij))});
--   HT := hashTable flatten allKeys;
    degsTB = apply(degrees TB_0,d-> -drop(d,-1));
    zeroMaps := apply(zeroijs,ij->ij => map(S.complexes#(degsTB#(ij_0))[-1],S.complexes#(degsTB#(ij_1)),i-> 0));
    nzMaps := apply(nonzeroijs, ij->(
	    i=ij_0;
	    dm = (-drop((degrees TB_0)_i,-1),TB.dd_1_ij);
	    ij => S.phis#dm
	    ));
    hashTable(zeroMaps|nzMaps)
    )


--  Input:  the Beilinson window chain complex.  Might require
--           differential entries to be monomials(?)
--  Output:  the Beilinson monad (??)
--  In essence, this code just concatenates the chain complex maps from the HashTable
--  diffModToChainComplexMaps(TB).
bigChainMap = (TB)->(
    HT = diffModToChainComplexMaps(TB);
    rows = apply(rank TB_0,i->(
	    mm := HT#(i,0);
	    scan(rank TB_1-1,j-> mm = mm|HT#(i,j+1));
	    mm
	    ));
    nn = rows_0;
    scan(#rows -1,i-> nn = nn||rows_(i+1));
    nn    
    )

--  just a different name for same function
altDMonad = TB -> bigChainMap(TB)
--
end

restart
load "KoszulFunctor.m2"
load "KoszulFunctor_addons.m2"
load "TateDM.m2"


--SETUP
kk=ZZ/101
L = {1,1,2}
S=kk[x_0..x_(#L-1),Degrees=>L]

irr=ideal vars S
addTateData(S,irr)
E=S.exterior

--SIMPLE EXAMPLE:
F = E^{{0,0},{1,0},{2,0}};
phi = matrix{{0,e_0,0},{0,0,e_0},{0,0,0}};
betti F
TB = chainComplex map(F,F**E^{{0,-1}},phi)
TB.dd_1
altDMonad(TB)
--This is what I'd worked out by hand in a file!
--But this was an artificial example, it didn't come from a sheaf.

--NEXT SIMPLEST EXAMPLE:  S(1)
M= S^{{1}}
LL=apply(10,i->S.degOmega+{i})
elapsedTime betti(TM=RRfunctor(M,LL))
--RRfunctor screwed up
DTate=TM
betti TM
TM.dd
TB=beilinsonWindow(TM,-S.degs)
betti TB
degrees TB_0
TB.dd_1
degrees TB_1
DM = altDMonad(TB)
-- this also matches a computation I did by hand!
break



--NEW STUFF
altDMonad(TB)
M = S^1/ideal(x_0)**S^{{4}}
LL=apply(10,i->S.degOmega+{i})
elapsedTime betti(TM=RRfunctor(M,LL))
DTate=TM
TM.dd
TB = beilinsonWindow(TM,-S.degs)
betti TB
altDMonad(TB)
-- we get something....  no clue if it is correct.