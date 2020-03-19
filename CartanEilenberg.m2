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
F = source e
assert(prune coker HH_1 e == 0)

F = source CE C



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


