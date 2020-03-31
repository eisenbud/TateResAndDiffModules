

--- Input: a nonpositive integer l
--- Output: a List of all variables of degree at most -l. 



variableList = (l) -> (
    L := new List;
    variables := flatten entries vars S;
    for i from 0 to #variables-1 do (
	if (degree variables_i)_0 <= -l then L = append(L, variables_i);
	);
    L
)


-*
--Test
S = ZZ/101[x_1, x_2, Degrees => {1,2}, MonomialOrder => Lex];
variableList(0) --should give {}
variableList(-1) --should give {x_1}
variableList(-2) --should give {x_1, x_2}

--Test
S = ZZ/101[x_1, x_2, x_3, Degrees => {1, 1, 2}, MonomialOrder => Lex];
variableList(0) --should give {}
variableList(-1) --should give {x_1, x_2}
variableList(-2) --should give {x_1, x_2, x_3}
*-


--- Input: a nonpositive integer l and a List L of square free monomials of 
---        degree at most -l, ordered lexicographically.
--- Output: a List of all of the square free monomials of degree at most -l 
---         given by products of one of the variables with elements of L,
---    	    ordered lexicographically.

addAVariable = (L, l) -> (
    L' := new List;
    variables := flatten entries vars S;
    for i from 0 to #variables - 1 do (
    	for j from 0 to #L -1 do (
	    if L_j % variables_i != 0 and member(variables_i * L_j, L') == false and (degree (variables_i * L_j))_0 <= -l then 
	    L' = append(L', variables_i * L_j);
	    );
    	);
    L'
)





--Test

--S = ZZ/101[x_1, x_2, Degrees => {1,2}, MonomialOrder => Lex];
--variables := flatten entries vars S;
--addAVariable(variables, -1) --should return {}
--addAVariable(variables, -2) --should return {}
--addAVariable(variables, -3) --should return {x_1x_2}
--addAVariable(oo, -4)        --should return {}

--S = ZZ/101[x_1, x_2, x_3, Degrees => {1, 1, 2}, MonomialOrder => Lex];
--variables := flatten entries vars S;
--addAVariable(variables, -1) --should return {}
--addAVariable(variables, -2) --should return {x_1x_2}
--addAVariable(variables, -3) --should return {x_1x_2, x_1x_3, x_2x_3}
--addAVariable(oo, -4)        --should return {x_1x_2x_3x_4}
--addAVariable(oo, -5)	    --should return {}



--- Input: Nonpositive integers l and j
--- Output: A List of all squarefree monomials containing -j variables of degree at
---         most -l, ordered lexicographically.

squareFreeMonomialList = (l, j) -> (
    L := variableList(l);
    if j == 0 then L = {1} else (
    	for i from 1 to -j - 1 do (
	    L = addAVariable(L, l);
    	    );
	);
    L
)


-*
--Test
S = ZZ/101[x_1, x_2, Degrees => {1,2}, MonomialOrder => Lex];
squareFreeMonomialList(-1, -1)  --should return {x_1}
squareFreeMonomialList(-1, -2)  --should return {}
squareFreeMonomialList(-2, -1)  --should return {x_1, x_2}
squareFreeMonomialList(-2, -2)  --should return {}
squareFreeMonomialList(-3, -2)  --should return {x_1x_2}
squareFreeMonomialList(-3, -3)  --should return {}
squareFreeMonomialList(-4, -2)  --should return {x_1x_2}


S = ZZ/101[x_1, x_2, x_3, Degrees => {1, 1, 2}, MonomialOrder => Lex];
squareFreeMonomialList(-1, -1)  --should return {x_1, x_2}
squareFreeMonomialList(-1, -2)  --should return {}
squareFreeMonomialList(-2, -1)  --should return {x_1, x_2, x_3}
squareFreeMonomialList(-2, -2)  --should return {x_1x_2}
squareFreeMonomialList(-3, -2)  --should return {x_1x_2, x_1x_3, x_2x_3}
squareFreeMonomialList(-3, -3)  --should return {}
squareFreeMonomialList(-4, -3)  --should return {x_1x_2x_3}
squareFreeMonomialList(-4, -2)  --should return {x_1x_2, x_1x_3, x_2x_3}
*-


--- Input: A monomial m and a variable v
--- Output: A monomial, the contraction of m by v. 
contraction = (m, v) -> (
    p := 0;
    if m % v == 0 then (
    	counter := 0;
    	L := new List;
    	variables := flatten entries vars S;
    	for i from 0 to  #variables-1 do (
	    if m % variables_i == 0 and variables_i != v then (
		L = append(L,variables_i);
		if variables_i > v then (
	    	    counter = counter + 1;
		    );
	    	);
	    );
    	p = 1;
    	for i from 0 to #L-1 do p = L_i * p;
    	p = (-1)^(counter) *p
	);
    p
)
-*
--Test
S = ZZ/101[x_1, x_2, x_3, Degrees => {1, 1, 2}, MonomialOrder => Lex];
contraction(x_1*x_2*x_3, x_1) --should give x_2x_3
contraction(x_1*x_2*x_3, x_2) --should give -x_1x_3
contraction(x_1*x_2*x_3, x_3) --should give x_1x_2
contraction(x_1*x_3, x_1) --should give x_3
contraction(x_1*x_3, x_3) --should give -x_1
contraction(x_1*x_2, x_1)
contraction(x_2, x_2) --should give 1
*-

--- Input: A monomial m and a variable v
--- Output: The sign on the contraction of m by v (assuming v | m).
koszulSign = (m, v) -> (
    n := 0;
    variables := flatten entries vars S;
    for i from 0 to  #variables-1 do (
    	if m % variables_i == 0 and variables_i > v then (
	    n = n + 1;
	    );
    	);
    (-1)^n
)

-*
--Test
S = ZZ/101[x_1, x_2, x_3, Degrees => {1, 1, 2}, MonomialOrder => Lex];
koszulSign(x_1*x_2*x_3, x_1) --should give 1
koszulSign(x_1*x_2*x_3, x_2) --should give -1
koszulSign(x_1*x_2*x_3, x_3) --should give 1
koszulSign(x_1*x_3, x_1) --should give 1
koszulSign(x_1*x_3, x_3) --should give -1
koszulSign(x_2, x_2) --should give 1
*-



--Input: a Z-graded polynomial ring
--Output: the tensor product of S with itself, with the natural Z x Z grading. 
--This might be stupid, but the reason I don't just take S**S is because the variables 
--in, say, k[x_1, x_2] tensor itself are {x_1, x_2, x_1, x_2}. But I want the variables 
--in different tensor factors to have different names...
bigradedTensor = (S) -> (
    n := # flatten entries vars S;
    variables := flatten entries vars S;
    deg := flatten apply(variables, i -> degree i);
    bigradedDegs := new List;
    for i from 0 to n - 1 do (
    	bigradedDegs = append(bigradedDegs, {deg_i, 0});
       	);
    for i from 0 to n-1 do (
     	bigradedDegs = append(bigradedDegs, {0, deg_i});
        );
    tensor(S, S, Variables => {x_1..x_n, y_1..y_n}, Degrees => bigradedDegs)
    )
    


--- Input: A PolynomialRing R, the tensor product of some other polynomial ring S with itself,
--         equipped with the natural bigrading coming from the grading on S. 
--         A nonpositive integer k and a monomial m involving -j variables
--- Output: A Matrix, the column corresponding to m of the j^th differential of 
--          OO(k) \boxtimes the truncated Koszul complex M_k.
-- 

truncatedKoszulColumn = (R,k,j, m) -> (
   M := R^{{k, -k - (degree m)_0}};
   --M is the source of our column matrix. We now build the target, N.
   N := R^0;
   L := squareFreeMonomialList(k, j + 1);
   if L_0 == 1 then N = N ++ R^{{k, -k}} else (
       for i from 0 to #L -1 do (
       	   N = N ++ R^{{k, -k - (degree L_i)_0  }}; 
       	   );
       );
   variables := flatten entries vars S;
   n := #variables;
   columnEntries := new List;
       for i from 0 to #L-1 do (
       	   if m % L_i != 0 then columnEntries = append(columnEntries, 0) else (
	       variables := flatten entries vars S;
	       bigradedVariables := flatten entries vars R;
	       v := 0;
	       bigradedv := 0;
	       for s from 0 to #variables - 1 do (
		   if variables_s * L_i == m then (
		       v = variables_s;
		       bigradedv = bigradedVariables_(n + s);
		   );
	       );
	       columnEntries = append(columnEntries, (koszulSign(m, v) * bigradedv));
    	   );
       );
   --Need to "unflatten" columnEntries, so we can turn it into a matrix.
   unflattenedList := new List;
   for i from 0 to #L - 1 do (
       unflattenedList = append(unflattenedList, {columnEntries_i});
       );
   map(N, M, matrix unflattenedList)
)


--- Input: A PolynomialRing R, the tensor product of some other polynomial ring S with itself,
--         equipped with the natural bigrading coming from the grading on S. 
--         A nonpositive integer k and a negative integer j (if j = 0, the
--         differential is 0).
--- Output: a Matrix, the j^th differential in the complex O(k) \boxtimes M_l from 
--          Canonaco-Karp. 


koszulMatrix = (R,k, j) -> (
    L := squareFreeMonomialList(k, j);
    M := truncatedKoszulColumn(R, k, j, L_0);
    for i from 1 to #L - 1 do (
	M = M | truncatedKoszulColumn(R,k, j, L_i);
	);
    M
 )
-*
--Test
S = ZZ/101[e_1, e_2, Degrees => {1,2}, MonomialOrder => Lex]
R = bigradedTensor(S);
--Let's check that we can compute the matrices in M_{-1} and M_{-2} over P(1,2):
koszulMatrix(R,-1, -1)
isHomogeneous oo
koszulMatrix(R, -2, -1)
isHomogeneous oo
koszulMatrix(R, -3, -2)
truncatedKoszulColumn(R, -3, -2, e_1*e_2)
--Now let's check that we get the right matrices for M_{-1}, M_{-2}, and M_{-3} over
--P(1,1,2):
S = ZZ/101[x_1, x_2, x_3, Degrees => {1, 1, 2}, MonomialOrder => Lex]
R = bigradedTensor(S);
koszulMatrix(R, -1, -1)
isHomogeneous oo
koszulMatrix(R, -2, -1)
isHomogeneous oo
koszulMatrix(R, -2, -2)
isHomogeneous oo
koszulMatrix(R, -3, -1)
isHomogeneous oo
koszulMatrix(R, -3, -2)
isHomogeneous oo
*-

--Input: a nonpositive integer l and a positive integer w. w is the sum of the weights of
--       the variables.
--Output: the index of the smallest nonzero component of the Koszul complex truncated by l.
lastComponent = (l) -> (
    w:= sum flatten degrees S;
    component := 0;
    for j from -w to 0 do (
	if squareFreeMonomialList(l, j) == {} then component = j +1;
	);
    component
)
--- Input: A PolynomialRing R, the tensor product of some other polynomial ring S with itself,
--         equipped with the natural bigrading coming from the grading on S. 
--         Also a negative integer k.
--- Output: A ChainComplex, the complex O(k) \boxtimes M_k from 
--          Canonaco-Karp. 
koszulComplex = (R, k) -> (
    mapList := {};
    for j from 1 to -lastComponent(k) do (
	mapList = append(mapList, koszulMatrix(R, k, -j));
	);
    chainComplex(mapList)
)

-*
--Test
S = ZZ/101[x_1, x_2, Degrees => {1,2}, MonomialOrder => Lex]
R = bigradedTensor(S);
koszulComplex(R, -1)
oo.dd
koszulComplex(R, -2)
oo.dd
koszulComplex(R, -3)
oo.dd
S = ZZ/101[x_1, x_2, x_3, Degrees => {1, 1, 2}, MonomialOrder => Lex]
R = bigradedTensor(S);
koszulComplex(R, -1)
oo.dd
koszulComplex(R, -2)
oo.dd
koszulComplex(R, -3)
oo.dd
koszulComplex(R, -4)
oo.dd
*-
-- Input: A PolynomialRing R, the tensor product of some other polynomial ring S with itself,
--        equipped with the natural bigrading coming from the grading on S. Nonnegative 
--        integers k and j and a squarefree monomial m in S involving 1-j variables, 
--        with degree at most -k.
-- Output: a Matrix, the column of Canonaco's map \alpha_k^j corresponding to the monomial m. 


alphaMatrix = (R, k, j) -> (
    bigradedVariables := flatten entries vars R;
    alphaColumn = (k, j, m) -> (
    	M := R^{{k,-k - (degree(m))_0 }};
    	N := R^0;
    	for l from k + 1 to 0 do (
     	    if j == 0 then (
	    	N = N ++ R^{{l, -l}};
	    	);
	    if j != 0 then (
	    	for i from 0 to #squareFreeMonomialList(l,j) - 1 do (
	    	    N = N ++ R^{{l, -l - (degree (squareFreeMonomialList(l,j))_i)_0}};
            	    );
	    	);
    	    );
    	    columnEntries := new List;
    	    for l from k + 1 to 0 do (
	    	for i from 0 to #squareFreeMonomialList(l,j) - 1 do (
	    	    variables := flatten entries vars S;
	    	    indicator := 0;
	    	    v := 0;
	    	    bigradedv := 0;
	    	    for t from 0 to #variables - 1 do (
		    	if variables_t * (squareFreeMonomialList(l,j))_i == m and l == k + (degree variables_t)_0 then (
		    	    v = variables_t;
		    	    bigradedv = bigradedVariables_t;
		    	    indicator = 1;
		    	    );
	    	    	);	
	     	    if indicator == 1 then (
	       	    	p := (-1)*koszulSign(m, v) * bigradedv;
	            	columnEntries = append(columnEntries, p);
	       	    	);
	     	    if indicator == 0 then (
	     	    	columnEntries = append(columnEntries, 0);
	       	    	);
	     	    indicator = 0;
	     	    );
       	    	);
     	    unflattenedList := new List;
     	    for i from 0 to #columnEntries - 1 do (
       	    	unflattenedList = append(unflattenedList, {columnEntries_i});
	    	);
	    map(N, M, matrix unflattenedList)
    	);
     L := squareFreeMonomialList(k, j-1);
     M := alphaColumn(k, j, L_0);
     for i from 1 to #L - 1 do (
	 M = M | alphaColumn(k, j, L_i);
	 );
     M    
)



-*
--Test
S = ZZ/101[x_1, x_2, Degrees => {1,2}, MonomialOrder => Lex];
R = bigradedTensor(S)


--We recover all of the \alpha_k^j matrices computed in the 
--``Resolution of the diagonal examples" pdf.

alphaMatrix(R, -1, 0)
isHomogeneous oo
alphaMatrix(R, -2, 0)
isHomogeneous oo

S = ZZ/101[x_1, x_2, x_3, Degrees => {1, 1, 2}, MonomialOrder => Lex];
R = bigradedTensor(S);
alphaMatrix(R, -1, 0)
isHomogeneous oo
alphaMatrix(R, -2, 0)
isHomogeneous oo
alphaMatrix(R, -2, -1)
isHomogeneous oo
alphaMatrix(R, -3, 0)
isHomogeneous oo
alphaMatrix(R, -3, -1)
isHomogeneous oo
*-
--Input: A PolynomialRing R, the tensor product of some other polynomial ring S with itself,
--       equipped with the natural bigrading coming from the grading on S. 
--     
--Output: the complex R_0 from Canonaco-Karp. Notice I tack on a 0 in degree -1. 
RZero = (R) -> (
    D := new ChainComplex;
    D_0 = R^1;
    D_1 = R^0;
    D
)


--Input: A PolynomialRing R, the tensor product of some other polynomial ring S with itself,
--       equipped with the natural bigrading coming from the grading on S. 
--       A nonpositive integer k and a ChainComplex C of R-modules. C should be R_{k + 1}.
--Output: a ChainComplex, R_k.
rComplex = (R, k, D) -> (
    C := koszulComplex(R, k)[1];
    alpha := map(D, C, i -> alphaMatrix(R, k, -i));
    mappingCone(alpha) 
)

--Input: ChainComplexMap
--Output: the mapping cone of alpha. I didn't use M2's mapping cone function, because it
--        returns the components of the mapping cone as D_i ++ C_(i-1), and I want them
--        to be C_(i-1) ++ D_i. 
mappingCone = (alpha) -> (
    C := source alpha;
    D := target alpha;
    l := length C;
    if length D < l then D_l = R^0;--tacked an extra 0 on the end of D. Necessary for 
    --rComplex code to run. This is sort of hacky, I realize.
    mcone := new ChainComplex;
    for i from 0 to l do (
	mcone_i = C_(i -1) ++ D_i;
	);
    for i from 1 to l do (
	mcone.dd_i = -C.dd_(i-1);
	mcone.dd_i = mcone.dd_i | map(C_(i - 2), D_i, 0);
	N := alpha_(i-1) | D.dd_i;
	mcone.dd_i = mcone.dd_i || N;
	);
    mcone
    )




--Input: A PolynomialRing R, the tensor product of some other polynomial ring S with itself,
--       equipped with the natural bigrading coming from the grading on S. Also a List 
--       W = {w_1, ..., w_n} of positive integers, the weights of the variables. 
--Output: A ChainComplex, Canonaco-Karp's resolution of the diagonal for P(w_1, ..., w_n).

resDiag = (R, W) -> (
    n := #W;
    w := sum W;
    resDiag := RZero(R);
    for i from 1 to w - 1 do (
	resDiag = rComplex(R, -i, resDiag);
	);
    resDiag
    )


end;
restart
load "WeightedResolutionOfDiagonal.m2"


--Test:
S = ZZ/101[x_1, x_2, Degrees => {1,2}, MonomialOrder => Lex];
R = bigradedTensor(S);
resDiag(R, {1,2})
oo.dd_1
kernel oo
--This recovers the first calculation in the ``Resolutions of the diagonal examples" pdf.


S = ZZ/101[x_1, x_2, Degrees => {1,3}, MonomialOrder => Lex];
R = bigradedTensor(S);
resDiag(R, {1,3})
oo.dd_1
kernel oo

S = ZZ/101[x_1, x_2, Degrees => {1,4}, MonomialOrder => Lex];
R = bigradedTensor(S);
resDiag(R, {1,4})
oo.dd_1
kernel oo


S = ZZ/101[x_1, x_2, x_3, Degrees => {1, 1, 2}, MonomialOrder => Lex]
R = bigradedTensor(S);
resDiag(R, {1,1,2})
oo.dd
oo_1 * oo_2
HH_1 resDiag(R, {1,1,2});
oo == 0
--This recovers the other calculation in the ``Resolutions of the diagonal examples" pdf.

S = ZZ/101[x_1, x_2, x_3, Degrees => {1, 1, 1}, MonomialOrder => Lex]
R = bigradedTensor(S);
resDiag(R, {1,1,1})
oo.dd
r = resDiag(R, {1,1,1})
sub(r.dd_1, {y_1 => x_1, y_2 => x_2, y_3 => x_3})
prune coker oo



S = ZZ/101[x_1, x_2, x_3, x_4,  Degrees => {1, 1, 2, 2}, MonomialOrder => Lex]
R = bigradedTensor(S);
resDiag(R, {1,1,2,2})
oo.dd
HH_1 resDiag(R, {1,1,2,2});
oo == 0
HH_2 resDiag(R, {1,1,2,2});
oo == 0



