--code to create a 1-step Cartan-Eilenberg resolution of a 3-term complex C;
-- that is, a free complex surjecting to C such that the induced map on homology is surjective,
--and the induced map on cycles and boundaries are also surjective.


CE = C ->(
    K := ker C.dd_1;
    inc := inducedMap(C_1,K);
    H := coker map(K,C_2,C.dd_2//inc);
    PH := prune H;
    HtoPH := (PH.cache#pruningMap)^-1;
    KtoPH := HtoPH *map(H,K,1);
    B := image C.dd_1;
    C1toB := map(B,C_1,1);
    BtoC0 := map(C_0, B, C.dd_1);
    
    eB := map(B, cover B, 1);
    FB := source eB;
    e0 := map(C_0, cover C_0, 1);
    F0 := source e0;
    FBtoF0 := map(F0,FB, (BtoC0*eB)//e0);
        
    e2 := map(C_2,cover C_2, 1);
    F2 := source e2;
    ePH := map(PH, cover PH, 1);
    FPH := source ePH;
        
    FK := F2++FPH;
    eK := (C.dd_2*e2*FK^[0])//inc + ((ePH*FK^[1])//KtoPH);
        
    F1:= (F2++FPH)++FB;
    F1':= F2++(FPH++FB);
    d2 := F1'_[0];
    d1 := FBtoF0*F1^[1];
    e1 := inc * eK *(F1^[0]) + (eB*F1^[1])//C1toB;
    e := {e0,e1,e2};
    F := chainComplex(d1,d2);

    assert (F.dd^2==0);
    assert(e_1*F.dd_2 == C.dd_2*e_2);
    assert(e_0*F.dd_1 == C.dd_1*e_1);

    map(C,F,i->e_i)
)
    
    
Ures = method()
Ures ChainComplex := C -> (
    --C is a right exact chain complex C_2 -> C_1 -> C_0 -> 0 of modules. 
--construct the diagram
--     F_2 --> F_1     -->   F_0
--     |e_2 d' |e_1     d''  |e_0
--    C_2 --> C_1 -->        C_0
--with F_1 = F_2++F_0 free modules
    e2 := map(C_2, source gens C_2, 1);
    e0:= map(C_0, source gens C_0, 1);
    Ures0(C,{e0,e2})
)


Ures0 = (C, e) ->(
    --C is a right exact chain complex N' -> N -> N'' -> 0 of modules. Output is a 
    --split exact sequence of free modules
    --with a surjective ChainComplexMap to MM
    --construct the diagram
    --     F_2 -->F_1     -->   F_0
    --     |e_2 d_2 |e_1  d_1   |e_0
    --    C_2 --> C_1     -->   C_0 --> 0
    --with FN = FN'++FN'' free modules
    --from the complex
    --C: C_2 --> C_1 --> C_0 -->0
    --
    --e = {e_0,e_2}, maps from free modules are given
    (e0,e2) := (e_0,e_1);
    e1 := map(C_1, source e0 ++ source e2, matrix{{e0//C.dd_1 , C.dd_2*e2}});
    e' := {e0,e1,e2};
    dF1 := map(source e'_0, source e'_1, (C.dd_1*e'_1)//e'_0);
    dF2 := (source (e'_1))_[1];
    F := chainComplex{dF1,dF2};
    assert (F.dd^2==0);
    assert(e'_1*F.dd_2 == C.dd_2*e'_2);
    assert(e'_0*F.dd_1 == C.dd_1*e'_1);
    map(C,F,i->e'_i)
    )

cplxToDM = method()
cplxToDM ChainComplex := F -> (
    --F is a 3-term complex
    minF := min F;
    maxF := max F;
    evens := positions (toList(minF..maxF), i->i%2==0);
    odds := positions (toList(minF..maxF), i->i%2!=0);
    F0 := directSum apply(evens, i-> F_i);
    F1 := directSum apply(odds, i-> F_i);
    D1 := F0_[0]*F.dd_1;
    D0 := map(F1,F0,F.dd_2*F0^[1]);
    map(F0++F1,F0++F1, matrix{{0*id_F0,D1},{D0,0*id_F1}})
	)
cplxToDM ChainComplex := F -> (
    --F is a 3-term complex
    minF := min F;
    maxF := max F;
    evens := positions (toList(minF..maxF), i->i%2==0);
    odds := positions (toList(minF..maxF), i->i%2!=0);
    F0 := directSum apply(evens, i-> F_i);
    F1 := directSum apply(odds, i-> F_i);
    D1 := F0_[0]*F.dd_1;
    D0 := map(F1,F0,F.dd_2*F0^[1]);
    map(F0++F1,F0++F1, matrix{{0*id_F0,D1},{D0,0*id_F1}})
	)
cplxToDM ChainComplexMap := e -> (
    --e: F -->C  is a map of complexes
    --assumes that C is the unfolding of a DM, ie the terms of C are
    --all the same
    S := ring e;
    F := source e;
    C := target e;
    minF := min F;
    maxF := max F;
    DC := cplxToDM C;
    DF := cplxToDM F;    
esum := directSum apply(toList(minF..maxF), i -> e_i);
etot0 := map(source DC, source DF,esum);
etot1 := map(target DC, target DF,esum);
assert(etot0*DF == DC*etot1);
(etot0, etot1)
)

DMToCplx = (M,d) -> (
    d2 = map(source d, , matrix d);
    chainComplex(d,d2))

end--
restart
load "CartanEilenberg.m2"
S = ZZ/101[a,b,c]
m1 = map(S^2, S^{3:-1}, matrix{{a,b,c},{b,c,a}})
m2 = map(S^{3:-1},S^{-2},matrix{{c},{b},{a}})
I = ideal(m1*m2)
R = S^1/I
C = chainComplex(R**m1, R**m2)
prune HH_1 C
Ures C
e = CE C
etot = cplxToDM e
F = source e
Ftot = cplxToDM F
Ctot = cplxToDM C
needsPackage "PruneComplex"
pF = prune F
pTot = prune Ftot
F.dd
pF.dd 
Ftot == source etot
Ftot
assert(prune coker HH_1 e == 0)

cplxToDM C
cplxToDM F



TEST///
S = ZZ/101[x]
M = S^1/x^3
d = map(M, M**S^{-1}, x^2)
C=chainComplex{d**S^{1},d}
C.dd^2==0
e = CE C
F = source e
assert (F.dd^2==0);
assert(e_1*F.dd_2 == C.dd_2*e_2)
assert(e_0*F.dd_1 == C.dd_1*e_1)
assert(prune coker HH_1 e == 0)
///


