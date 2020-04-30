isIsoWithMap = (A,B)->(
    S := ring A;
    H := Hom(A,B);
    Hp := prune H;
    pmap := Hp.cache.pruningMap;
    f := homomorphism(pmap*map(Hp,S^1, random(target presentation Hp,S^1)));
    t := if prune coker f == 0 then true else false;
    (t,f))

isHomogeneousIso = (A,B)->(
        if not isHomogeneous A and isHomogeneous B then error"inputs not homogeneous";
    	S := ring A;
	A1 := prune A;
	B1 := prune B;

	--handle the cases where one of A,B is 0
	isZA1 = A1==0;
	isZB1 = B1==0;	
    	if isZA1 =!= isZB1 then return false;
	if isZA1 and isZB1 then return true;

	-- from now on, A1 and B1 are nonzero
	dA := degree A1_*_0;
	dB := degree B1_*_0;
	df := dB-dA;
        H := Hom(A1,B1);       
	kk := ultimate(coefficientRing, ring A);
	sH := select(H_*, f-> degree f == df);
	if #sH ==0 then return false;
	g := sum(sH, f-> random(kk)*homomorphism matrix f);
	kmodule := coker vars S;
	gbar := kmodule ** g;
	if gbar==0  then return false;
--	error();
	(prune coker gbar) == 0 and prune ker g == 0
	)
isIso = isHomogeneousIso	

isLocalIso = (A,B)->(
    if isHomogeneous A and isHomogeneous B and
            all(A_*, a->degree a == degree(A_*_0)) and 
	    all(B_*, a->degree a == degree(B_*_0)) then
	return isHomogeneousIso(A,B);

	S := ring A; 
	kk := ultimate(coefficientRing, S);
	kmod := coker vars S;
	A1 := prune A;
	B1 := prune B;

--handle the cases where one of A,B is 0
	isZA1 = A1==0;
	isZB1 = B1==0;	
    	if isZA1 =!= isZB1 then return false;
	if isZA1 and isZB1 then return true;

--now we can assume both are nonzero
        H1 := Hom(A1,B1);      
	if #H1_* == 0 then return false;
	g1 := sum(H1_*, f-> random(kk)*(kmod**homomorphism matrix f));
	t1 = (prune coker g1 == 0);
	if t1 == false then return false else(
	    <<"there is a surjection arg1 -> arg2"<<endl;
            H2 := Hom(B1,A1);      
	    if #H2_* == 0 then return false;	    
	    g2 := sum(H2_*, f-> random(kk)*(kmod**homomorphism matrix f));
	    prune coker g2 == 0)
	)
end--
restart
load "IsIsomorphic.m2"
n = 3
S = ZZ/32003[x_1..x_n]
m = random(S^3, S^{4:-2})
A = random(target m, target m)
B = random(source m, source m)
m' = A*m*B
time isIso (coker m, coker m')
time isLocalIso(coker m, coker m')
