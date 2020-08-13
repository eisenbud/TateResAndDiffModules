restart
needsPackage "NormalToricVarieties"
needsPackage "Polyhedra"

--  Input: a list L and an element d
--  Output:  whether or not d is an element of L.
--  Note:  surely there's a built-in M2 way to do this but I (daniel) didn't know it.
isElement = (L,d)->(
    not(set(L) - set({d}) === set(L))
    )

--
--  Attempt #1 at finiding resolutions of the diagonal
--  presentDeltaMod produces a presentation matrix.  We then resolve the coker
--  and hope that this is a resolution of the diagonal.
--  If L = {not irrelevant degrees in the Koszul complex}, then this worked very often, but not always...
--
--  Input:   a set of degrees L for a toric variety Y
--  Output:  a presentation matrix for a potential module supported on diagonal
--           of Y**Y.  The matrix is a particular submatrix of the infinite resolution
--           of the diagonal, obtained by restricting degrees.
presentDeltaMod = (L,Y,S)->(
    DEGS := degrees ring Y;
    m := #(DEGS#0);
    backHalf = toList(m..2*m-1);
    D0 := apply(L,l-> -l|l);
    D1 := {};
    scan(L,i->(
	    scan(#DEGS,j->(
		    if isElement(L,i+DEGS#j) then D1 = D1|{(-i|(i+DEGS#j))}
		    ))
	    ));
    keysD1 := {};
    scan(L,i->(
	    scan(#DEGS,j->(
		    if isElement(L,i+DEGS#j) then keysD1 = keysD1|{(i,j)}
		    ))
	    ));
    --  from a degree to a position
    backwardD0 := new HashTable from apply(#D0,i-> (i=> (D0#i)_backHalf));
    backwardD1 := new HashTable from apply(#keysD1, i-> (i=> keysD1 #i));
    entryCode = (i,j)->(
    	if backwardD0#i == (backwardD1#j)#0 then return y_((backwardD1#j)#1);
    	if backwardD0#i == (backwardD1#j)#0 + DEGS#((backwardD1#j)#1) then return -z_((backwardD1#j)#1);
    	return 0;
    	);
    map(S^(-D0),S^(-D1),(i,j) -> entryCode(i,j))    
    )
--  Input:  a set of lattice points L, usually multidegrees.
--  Output:  the set of lattice points in the convex hull.
makeConvex = L->(
    needsPackage "Polyhedra";
    P = convexHull transpose matrix L;
    LP = latticePoints P;
    flatten apply(#LP,i-> entries transpose (latticePoints P)_(i))
    )

--  Input:  a toric variety Y.
--  Output: the list of all degrees appearing in the koszul complex
allKoszulDegrees = Y->(
    K = koszul vars ring Y;
    unique flatten apply(dim ring Y+1,i-> degrees K_i)
    )

--outputs the sublist of all degrees appearing in the koszul complex
--where the corresponding truncated complex is **not** irrelevant
notIrrDegs = (Y)->(
    A := ring Y;
    irrY := ideal Y;    
    notIRR := {};
    m = dim A;
    scan(remove(subsets(m),0),D->(
	ID = ideal apply(D,i-> A_i);
	if saturate(ID,irrY) != ideal(1_(A))then notIRR = notIRR|{D};
	));
    notIRR = unique apply(notIRR, D-> degree product apply(D,i-> A_i));
    zz := apply(#(degree A_0),i-> 0);
    L := {zz}|notIRR;
    makeConvex L
    )

--
--The following are all subroutines for "diagComplex"
--
--
--Input: L is a list of degrees and E is a list of indices for exterior algebra
--and w is a degree.  This checks if all products from E + w are elements of L.
--In "diagComplex(L), the basis in homological degree j is in bijection with pairs (w,E) where
--w is in L, E is a monomial in the exterior algebra, and w + deg(e) is in L for all monomials e dividing E.
allSubElements = (L,E,w)->(
    OUT = true;
    scan(subsets(E),i-> if isElement(L,w+degH#i) == false then OUT = false);
    OUT
    )

-- Input: a list of degrees L and a ring R.
-- Output: the actual basis elements for diagComplex.
selectBasis = (L,R)->(
    preB :=  hashTable apply(dim R+1, j-> j=> flatten apply(L, w->( apply(subsets(dim R,j),i-> (w,i)))));
    degH = hashTable({{}=>degree(1_R)} | apply(remove(subsets(dim R),0),i-> i => degree product apply(i,j-> R_j)));
    hashTable apply(dim R+1,j-> j=> select(preB#j, D-> allSubElements(L,D#1,D#0)))
--    hashTable apply(dim R+1 - #degree(R_0),j-> j=> select(preB#j, D-> allSubElements(L,D#1,D#0)))
    )

--  Computes the difference of sets B \ A, assuming A is a subset of B.
--
setDiff = (A,B)->(
    if isSubset(A,B) == false then return "not a subset";
    toList(set(B) - set(A))
    )

--  Used in producing a sign convention for diagComplex.
extSign = (M,N)->(
    M = sort M;
    N = sort N;
    if isSubset(M,N) == false then return "not a subset";
    if #N - #M != 1 then return "not a one-element difference";
    (-1)^((select(#N,i-> isElement(M,N#i) == false))_0)
    )


--  Input:  lists A and B corresponding to basis elements of diagComplex.
--  Output:  the corresponding entry in the differential.
--  This is where we spend too much time because we are going through everything.
entryBB = (A,B)->(
    degH = hashTable({{}=>degree(1_R)} | apply(remove(subsets(dim R),0),i-> i => degree product apply(i,j-> R_j)));
    if isSubset(A#1,B#1) == false then return 0;
    if A#0 == B#0 then return product(setDiff(A#1,B#1),i->extSign(A#1,B#1)*y_i);
    if A#0 == B#0 + degH#(setDiff(A#1,B#1)) then return -product(setDiff(A#1,B#1),i-> extSign(A#1,B#1)*z_i);
    	return 0;
    	);


--  Packages the subroutines to build the i'th differential of diagComplex.
buildMap = (L,R,S,i,BB)->(
    --BB = selectBasis(L,R);
    --don't want to recompute BB each time
    F = S^(-apply(BB#(i-1),D-> -(D#0)|(D#0+degH#(D#1))));
    G = S^(-apply(BB#(i),D-> -(D#0)|(D#0+degH#(D#1))));
    --Instead of the following line, we want to make a mutable matrix, where given the column
    --index we simply 
    phi = mutableMatrix(S,rank F,rank G);
    scan(rank G,j->(
	D = (BB#i)_j;
    	D1 = D#1;
--these give the indices of the bases with -z entries
    	scan(#D1,k->(
		rowIndex = position(BB#(i-1), c -> c == (D#0+degree(x_(D1_k)),remove(D1,k)));
		columnIndex = j;
		phi_(rowIndex,columnIndex) = (-1)^k*z_(D1_k)
      		));
	scan(#D1,k->(
		rowIndex = position(BB#(i-1), c -> c == (D#0,remove(D1,k)));
		columnIndex = j;
		phi_(rowIndex,columnIndex) = (-1)^(k+1)*y_(D1_k)
      		));
    ));
    map(F,G, matrix phi)
    )


--
--  The key function!
--  Input:  list of degrees L and rings R (Cox ring of Y) and S (Cox ring of Y**Y).
--  Output:  the linear chain complex, based on degrees L, where each differential is a submatrix of the infinite res of diag
--
diagComplex = (L,R,S)->(
    BB = selectBasis(L,R);
    m = dim R;
    --m = dim R - #degree(R_0);
    chainComplex apply(m,j-> buildMap(L,R,S,j+1,BB))
    )
--
--  Just a shortcut for diagComplex.
--
--  Input:  a toric variety Y.
--  Output:  the diagComplex for Y, based on L = all Koszul degrees.
buildDiagonal = Y->(
    R = ZZ/101[gens ring Y, Degrees => degrees ring Y];
    S = coefficientRing(R)[y_0..y_(dim R-1),z_0..z_(dim R-1), Degrees => degrees ring(Y**Y)];
    --L = notIrrDegs(Y);
    L = allKoszulDegrees Y;    
    (R,S,diagComplex(L,R,S))
    )






--  Input:  a matrix psi on Y**Y.  irr is irrelevant ideal for Y**Y.
--  Output:  true/false whether coker psi is a resolution of diagonal for Y
--  The minimal primes part can be very slow.
diagonalCheck = (psi,Y)->(
    --first we check the codimension
    if codim coker psi != dim Y then return "Wrong codim";
    --checks that the rank is 1
    R := ZZ/101[x_0..x_(dim ring Y-1),Degrees => degrees ring Y];
    rho := map(R,ring psi,vars R|vars R);
    M := coker rho(psi);
    if isFreeModule prune Hom(M,R) != true then return "Doesn't restrict to free module";
    if rank M != 1 then return "Wrong rank";
    -- Simplify via:
    -- prune Hom(M,R) == R^1
    --
    -- Since codim = pdim it is equidimensional.  If it has only one minimal prime then we are done.
    MP := minimalPrimes ann coker psi;
    -- add an equidimensional check
    if #MP == 1 then return "WooHoo!  coker psi is a resolution of the diagonal";
    --If it has multiple minimal primes, then we check that all but one of the minimal
    --primes are irrelevant. For this we need the irrelevant ideal, which we must define.
    --Or check that cokernel (or kernel) is irrelevant...
    S := ring psi;
    X := Y**Y;
    phi := map(S,ring X, gens S);
    irrX := phi(ideal X);
    if #select(MP, I-> saturate(I,irrX) != ideal 1_(ring irrX)) != 1 then return "Some funky minimal prime";
    return "WooHoo!  coker psi is a resolution of the diagonal (with an irrelevant component)";
    )




end;

---
---
---
---
---Sandbox
---
---
---
---

restart
load "resDiagonal.m2";
Y = hirzebruchSurface(3);
X = Y**Y;
R = ring Y;
S = ZZ/101[z_0..z_(dim ring Y-1),y_0..y_(dim ring Y-1),Degrees => degrees ring X];

---Two main constructions.

---The first builds a linear submatrix of the infinite res of diagonal
---and the resolves the cokernel of that matrix.
L = notIrrDegs(Y);
psi = presentDeltaMod(L,Y,S);
psi
r = res coker psi
--This construction produces an Ulrich module resolving diagonal for weighted spaces,
--Hirzebruchs, and the full database of smooth Fano toric surfaces.
--But even for some surfaces, it fails to be linear.
--For smooth Fano threefolds, there are two examples where it only produces a virtual Ulrich module
--on the diagonal.  And for fourfolds/fivefolds, it sometimes fails to produce even a virtual resolution.


--Second main construction.
--We build a linear complex based on a specified set of degrees.
diagComplex(L,R,S)
--If L is the convex hull of the set of all Koszul degrees, 
--then this always appears to give a (virtual) resolution, though it's harder
--to check this for large examples.
L = makeConvex allKoszulDegrees Y;
r = diagComplex(L,R,S)
assert(r.dd^2 == 0)
apply(length r, i-> HH_i r == 0)
diagonalCheck(r.dd_1,Y)


--Another example
Y = smoothFanoToricVariety(2,3);
X = Y**Y;
R = ring Y;
--Y has Picard group ZZ^3
S = ZZ/101[z_0..z_(dim ring Y-1),y_0..y_(dim ring Y-1),Degrees => degrees ring X];
L = makeConvex allKoszulDegrees Y;
r = diagComplex(L,R,S)
apply(length r, i-> HH_i r == 0)
diagonalCheck(r.dd_1,Y)




--Another example
Y = smoothFanoToricVariety(2,4);
X = Y**Y;
R = ring Y;
--Y has Picard group ZZ^3
S = ZZ/101[z_0..z_(dim ring Y-1),y_0..y_(dim ring Y-1),Degrees => degrees ring X];
L = makeConvex allKoszulDegrees Y;
r = diagComplex(L,R,S)
apply(length r+1, i-> HH_i r == 0)



r.dd_5
codim coker r.dd_1
r.dd_1
r.dd_2
r
betti r

--But we can't even compute the resolution for smoothFanoToric(2,4)....

--Weighted Projective Space
Y = weightedProjectiveSpace({1,1,2})
X = Y**Y;
R = ring Y;
S = ZZ/101[z_0..z_(dim ring Y-1),y_0..y_(dim ring Y-1),Degrees => degrees ring X];
L = makeConvex allKoszulDegrees Y;
r = diagComplex(L,R,S)
--Note that's the resolution is "too long" to be Ulrich,
--but it's still a (virtual) resolution of the diagonal.
apply(length r, i-> HH_i r == 0)
diagonalCheck(r.dd_1,Y)


