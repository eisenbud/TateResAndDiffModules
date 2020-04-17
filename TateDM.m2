--  This contains the necessary for a general RR-functor
--  both with and without the "extra grading".
--



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
--  Input: a polynomial ring and a boolean value
--  Output:  if boolean = false then you get the Koszul dual exterior algebra
--           but without the extra grading.
dualRingToric(PolynomialRing,Boolean) := (S,x) ->(
    if x == true then return dualRingToric(S);
    kk := coefficientRing S;
    degs := apply(degrees S,d-> (-d));
    ee := apply(#gens S, i-> e_i);
    kk[ee,Degrees=>degs,SkewCommutative=> not isSkewCommutative S]    
    );


--  The RR functor with variants.
RRfunctor = method();
--Input: (M,L) M a (multi)-graded S-module.
--             L a list of degrees.
--Question:  should E be part of the input??
--Output:  The differenial module RR(M) in degrees from L.
RRfunctor(Module,List) := (M,L) ->(
    S := ring(M);
    --E := dualRingToric S;
    relationsM := gens image presentation M;
    numvarsE := rank source vars E;
    ev := map(E,S,vars E);
    --L := degreeSetup(low,c,r);
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
    g' := transpose sub(newg,E);
    chainComplex map(E^df0,E^df1, g')
    )

--  The RR functor with variants.
RRfunctor = method();
--Input: (M,L) M a (multi)-graded S-module.
--             L a list of degrees.
--Question:  should E be part of the input??
--Output:  The differenial module RR(M) in degrees from L.
RRfunctor(Module,List) := (M,L) ->(
    S := ring(M);
    --E := dualRingToric S;
    relationsM := gens image presentation M;
    numvarsE := rank source vars E;
    ev := map(E,S,vars E);
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




RRfunctor(Module,List,Boolean) := (M,L,bbb) ->(
    if bbb == true then return RRfunctor(M,L);
    S := ring(M);
    --E := dualRingToric S;
    relationsM := gens image presentation M;
    numvarsE := rank source vars E;
    ev := map(E,S,vars E);
    f0 := gens image basis(L_0,M);
    scan(#L-1,i-> f0 = f0 | gens image basis(L_(i+1),M));
    --f0 is the basis for M in degrees given by L
    df0 := apply(degrees source f0,i-> (-1)*i);
    df1 := apply(degrees source f0,i-> (-1)*i);   
    SE := S**E;
    tr := sum(dim S, i-> SE_i*SE_(dim S+i));
    newf0 := sub(f0,SE)*tr;
    relationsMinSE := sub(relationsM,SE);
    newf0 = newf0 % relationsMinSE;
    newg := contract(transpose sub(f0,SE),newf0);
    g' := sub(newg,E);
    chainComplex map(E^df0,E^df1, g')
    )

end;
--
--
--
restart
load "TateDM.m2"
needsPackage "NormalToricVarieties"

--  RRfunctor of a module
S = ZZ/101[x_0,x_1,x_2,Degrees =>{1,1,2}];
E = dualRingToric(S);
M = S^1;
F = RRfunctor(M,{0,1,2})
F.dd_1
isHomogeneous F.dd_1
F.dd_1^2 == 0

--  RRfunctor of a module, without the extra grading
--  "false" gives it without the extra grading.
E = dualRingToric(S,false);
M = S^1;
F = RRfunctor(M,{0,1,2},false)
isHomogeneous F


--  Example on a Hirzebruch
S = ring hirzebruchSurface(2);
E = dualRingToric(S);
M = S^1;
L = {{0,0},{1,0},{2,0},{-2,1},{-1,1},{0,1}}
F = RRfunctor(M,L)
isHomogeneous F
F.dd_1^2 == 0

--  And same example without the extra grading.
S = ring hirzebruchSurface(2);
E = dualRingToric(S,false);
M = S^1;
L = {{0,0},{1,0},{2,0},{-2,1},{-1,1},{0,1}}
F = RRfunctor(M,L,false)
isHomogeneous F
F.dd_1^2 == 0
