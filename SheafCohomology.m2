needsPackage "NormalToricVarieties"
needsPackage "RandomIdeals"

dualRingToric = method();
dualRingToric(PolynomialRing) := (S) ->(
--  Input: a polynomial ring
--  Output:  the Koszul dual exterior algebra, but with an additional 
--           ZZ-degree, the ``standard grading'' where elements of \bigwedge^k
--           have degree k.
    kk := coefficientRing S;
    degs := apply(degrees S,d-> (-d)|{1});
    ee := apply(#gens S, i-> e_i);
    kk[ee,Degrees=>degs,SkewCommutative=>true]    
    );


multTest = (x, y, L) -> (
--Input: two matrices and a list of ring elements
--Output: if x * any element of L is y, return true. Else false. Note:
--we check equality entry-wise. So we're ignoring degrees of the maps.
    boolean := false;
    for i from 0 to #L - 1 do (
	if entries( x * L_i) == entries y then boolean = true;
	);
    boolean
    )

signedMultTest = (x, y, L) -> (
--Input: two matrices and a list of ring elements
--Output: if x * any element of L is y (up to a sign), return true. Else false. Note:
--we check equality entry-wise. So we're ignoring degrees of the maps.
    boolean := false;
    for i from 0 to #L - 1 do (
	if entries (x * L_i) == entries y or entries (x * L_i) == entries(-y) then boolean = true;
	);
    boolean
    )

weightSum = (S) -> (
--Input: polynomial ring
--Output: sum of the weights of the variables
    sum flatten apply(flatten entries vars S, v -> degree v)
    )


truncationDegree = (M) -> (
    --Input: S-module M
    --Output: An integer, the smallest i such that M_i != 0 and i > reg(M)
    reg := regularity(M);
    r := 0;
    for i from reg do (
	r = i;
	if hilbertFunction(i, M) != 0 then break
	);
    r
    )




Kdual = (M) -> (
    -- Input: an S-module M
    -- Output: a List with two entries. The first entry is the dual of the kernel of the 
    -- restriction of the differential of RR(M_{r)}), where r >> 0; see the definition of r in 
    -- comments in the code. The second entry is r.
    --NOTE: computing mapSource and mapTarget is unnecessary!
    r := truncationDegree(M);
    Bsource := new List;
    for i from 0 to numColumns basis(r,M) - 1 do (
	Bsource = append(Bsource, (basis(r,M))_{i});
	);--basis of M_r, encoded as column matrices
    mapSource := E^(#Bsource);--source of the map whose kernel we're computing
    Btarget := new List;
    mapTarget := E^0;
    degreeList := new List;
    for i from 0 to #(flatten entries vars S) - 1 do (
	if member(degree x_i, degreeList) == false then (
	    for j from 0 to numColumns basis((degree x_i)_0 + r, M) - 1 do (
    	  	Btarget = append(Btarget, (basis((degree x_i)_0 + r, M))_{j});
    	    	);	  
	    for j from 0 to numColumns basis((degree x_i)_0 + r, M) - 1 do (
	    	mapTarget = mapTarget ++ E^{degree e_i};
	    	);
	    degreeList = append(degreeList, degree x_i);
	    );
	);
    --now Btarget is a basis of M_{r + |x_0|} + ... + M_{r + |x_n|}, but with no repetitions
    --(so, for instance, if all the |x_i| are 1, there will be just one summand).
    --and mapTarget is the target of the map whose kernel we're computing
    columnList := new List;	
    for i from 0 to #Bsource - 1 do (
	column := new List;
	for j from 0 to #Btarget - 1 do (
	    if multTest(Bsource_i, Btarget_j, flatten entries vars S) == false then (
		column = append(column, {0});
	    	);
	    if multTest(Bsource_i, Btarget_j, flatten entries vars S) == true then (
	      	for k from 0 to #(flatten entries vars S) - 1 do (   
		    if entries (x_k * Bsource_i) == entries (Btarget_j) then (
		    	column = append(column, {e_k});
		     	);
		    );
		);
	    );
	columnList = append(columnList, column);
	);
    theMatrix := matrix columnList_0;
    for i from 1 to #Bsource - 1 do (
	theMatrix = theMatrix | matrix columnList_i;
	);
    K := kernel theMatrix;--this is the module K appearing in the description of the algorithm
    --in the notes.
    dual(K)
    )
-*
--Test
L = {1,1}
L = {1, 1, 1}
L = {1,2}
L = {1,2,3}
kk=ZZ/101;
S=kk[x_0..x_(#L-1),Degrees=>L];
E = S.exterior = dualRingToric S;
M = E^1
Kdual(S^1)--should always be 1-dimensional, irrespective of weights.
M = E^1/ideal(e_0)
*-

LFunctor = (M, r) -> (
--Input: A submodule M of a direct sum of copies of E and an integer r. I really 
--want M to be a quotient of Hom_E(\omega(-r, 0), E) = E(w + r, -n-1), so there are 
--two grading shifts in the code, labeled with *: one by -(w + r) and the other by 2(n + 1).
--Output: the complex L(M).
--In practice, M will be (up to a twist) the dual of the kernel of the restriction of 
--the differential of 
--RR(N_{\ge r}) to N_r \otimes \omega(-r, 0), where N is an S-module and r = reg(N).
    B := new List;
    for i from 0 to (numColumns basis M) - 1 do (
	B = append(B, (basis M)_{i});
	);
    --B is a basis of E, recorded as column matrices.
    w := weightSum(S);
    Bdegrees = new List;
    for i from 0 to #B - 1 do (
	d := 0;
	for j from 0 to #(entries B_i) - 1 do (
	    if (flatten entries B_i)_j != 0 then d = degree (flatten entries B_i)_j;
	    );
	Bdegrees = append(Bdegrees, d);
	);
    --Bdegrees is a list of the degrees of the (unique) nonzero entries in the elements of B 
    --(recall the elements of B are column matrices).
    mindeg := min apply(Bdegrees, b -> b_1);--mindeg is the smallest "auxiliary degree" in M
    maxdeg := max apply(Bdegrees, b -> b_1);--similarly for maxdeg
    --appearing in M.
    L := new List;
    for i from -maxdeg to -mindeg do (
	F := S^0;
	for j from 0 to #B - 1 do (
	    if (Bdegrees_j)_1 == -i then (
		F = F ++ S^{-(Bdegrees_j)_0 + w + r};--*
		);
	    );
	L = append(L, F);
	);
    --the i^th element of L is the (i - maxdeg)^th term of L(M).
    --if there is only one element in L, then the code below won't work, because
    --the chainComplex(List) will be receiving an empty list. So, we need the following:
     if #L == 1 then (
	 return chainComplex({map(L_0, S^0, 0)})[maxdeg + #(flatten entries vars S)]
	 );
    --now let's make the differentials and form the complex.
    C := new List; --this is the list we will use to make the complex
    for i from -maxdeg to -mindeg - 1 do (
	--in this routine we make the matrix L(M)_{i + 1} --> L(M)_{i}
	diffList:= new List; --this is the list we will make the matrix out of
	for j from 0 to #B - 1 do (
	    if (Bdegrees_j)_1 == -i  then (
		R := new List; --this is the row of the matrix corresponding to B_j
		for k from 0 to #B - 1 do (
		    if (Bdegrees_k)_1 == -i -1  then (
		--	print signedMultTest(B_k, B_j, flatten entries vars E);
			if signedMultTest(B_k, B_j, flatten entries vars E) == false then R = append(R, 0);
			if signedMultTest(B_k, B_j, flatten entries vars E) == true then (
			    for l from 0 to #(flatten entries vars S) - 1 do (
			    	if (entries (e_l * B_k)) == entries(B_j) then R = append(R, x_l);
			    	if (entries (e_l * B_k)) == entries(-B_j) then R = append(R, -x_l);
			    	);
			    );
			);
		    );
		diffList = append(diffList, R);
		);
	    );
	A := map(L_(i + maxdeg), L_(i + 1 + maxdeg), matrix diffList);
	C = append(C, A);
	);
    chainComplex(C)[maxdeg + #(flatten entries vars S)]--*
    )

--Tests
-*
L = {1,1,1,3}
kk=ZZ/101;
S=kk[x_0..x_(#L-1),Degrees=>L];
E = S.exterior = dualRingToric S;
M = E^1
r = 1
LFunctor(M, 1)--should return the Koszul complex with final term in homological degree -2(n+1)
*-

higherSheafCohomology = (M, l, d) -> (
    --if sheaf(X, M) == sheaf(X, S^0) then return 0 else (
    --Input: an S-module M, a twist l, and a positive integer d.
    --Output: the d^th cohomology of \widetilde{M}(l).
  	w := weightSum(S);
    	n := #(flatten entries vars S) - 1;
    	hilbertFunction(- l - 2*w, HH_(d - 2*(n+1) + 1)(LFunctor(Kdual(M),truncationDegree(M))))
--	);
    )

-*
sheafCohomologyTest = (M, l, d) -> (
    --Input: An S-module M, a twist l, and a positive integer d.
    --Output: true if the algorithm computed H^d(\widetilde{M}(l)) correctly. Else, false. 
    F := sheaf(X, S^1)** sheaf(X,S^{l});
    HH^d(X, F)
    higherSheafCohomology(M, l, d) == 
    )
*-
end;
restart
load "SheafCohomology.m2"
--The algorithm works in some cases. For instance, it seems to always work for the
--structure sheaf. Here's an example:
L = {2,3,5,7};
kk = ZZ/101;
X = weightedProjectiveSpace L;
S = ring X;
E = S.exterior = dualRingToric S;
M = S^1
regularity M
for i from -30 to -18 do (
   print (rank HH^3(X, sheaf(X, M**S^{i})) ,higherSheafCohomology(M, i, 3));
   );

--And it seems to work in full generality over ordinary projective space.
--But, it doesn't always work. Here is a simple example.
L = {1,1,2}
kk = ZZ/101;
X = weightedProjectiveSpace L;
S = ring X;
E = S.exterior = dualRingToric S;
M = (S^1)/ideal(x_0*x_1);
regularity M
for i from -10 to 0 do (
   print (rank HH^1(X, sheaf(X, M**S^{i})) ,higherSheafCohomology(M, i, 1));
   );

--Notice: the algorithm is overcounting. When there is a discrepancy, this
--has always been the problem in every example I've tried. The problem isn't with the code;
--I tried this example by hand and got the same answer: H^1(X, M(-2)) is rank 1, but the algorithm
--says it's rank 2. The problem seems to be with how we're truncating.