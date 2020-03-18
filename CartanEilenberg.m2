--code to lift a complex to a double complex 


CE = C -> (
    --C is a 2-step chain complex. Output is a split  chain complex F of free modules, together with a 
    --chainComplexMap to C, such that the homology of F is a free module mapping
    --onto the homology of C.
N' := C_2;
N := ker C.dd_1;
inc := map(C_1 , N, gens N);
d' := map(N,N',C.dd_2//inc);
N'' := coker d';
d'' := map(N'', N, 1);
assert(prune N'' == prune HH_1 C);
C1 := chainComplex{d'',d'};
e1 := Ures C1;

N1' = N;
N1 = C_1;
N1'' = coker C.dd_2;
d1' = map(N1, N1', matrix C.dd_2);
d1'' = map(N1'', N1,1);
C2 = chainComplex{d1'',d1'};
assert(C2.dd^2 ==0);
e2 = Ures (C2, e1_1, map(N1'', source gens N1'', 1));

map(C_0, N1'', matrix C.dd_1);
eC0 = map(C_0, source gens C_0, 1);
eC1 = e2_1;
eC2 = e1_2;
e' = e1_0;
e = e2_1;
e'' = map(C_0, source gens C_0, 1);
(source e1_0, source e2_1,source e'')
)

Ures = method()
Ures ChainComplex := C -> (
    --C is a right exact chain complex N' -> N -> N'' -> 0 of modules. Output is a 
    --split exact sequence of free modules
    --with a ChainComplexMap to MM.
--construct the diagram
--     FN' -->FN     -->          FN''
--     |eN' d' |eN           d''  |eN''
--N' = C_2 --> N = ker C.dd_1 --> N'' = HH_1 C --> 0
--with FN = FN'++FN'' free modules
--from the complex
--C: C_2 --> C_1 --> C_0
    N' = C_2;N = C_1;N'' = C_0;
    eN' := map(N', source gens N', 1);
    eN'':= map(N'', source gens N'', 1);
    eN := map(N, source eN'++source eN'', matrix{{C.dd_2*eN', eN''//C.dd_1}});
    F := chainComplex{(source eN)^[1],(source eN)_[0]};
    map(C,F, i-> {eN'', eN, eN'}_i)
)

Ures(ChainComplex, Matrix, Matrix) :=  (C, e',e'') ->(
    N' = C_2;N = C_1;N'' = C_0;
    eN' := e';
    eN'':= e'';
    eN := map(N, source eN'++source eN'', matrix{{C.dd_2*eN', eN''//C.dd_1}});
    F := chainComplex{(source eN)^[1],(source eN)_[0]};
    map(C,F, i-> {eN'', eN, eN'}_i)
)
    
end--
restart
load "CartanEilenberg.m2"
S = ZZ/101[x]
M = S^1/x^3
d = map(M, M**S^{-1}, x^2)
C=chainComplex{d**S^{1},d}
C.dd^2==0
CE C

N' = C_2
N = ker C.dd_1
inc = map(C_1 , N, gens N)
d' = map(N,N',C.dd_2//inc)
N'' = coker d'
d'' = map(N'', N, 1)
assert(prune N'' == prune HH_1 C)
eN'' = map(coker d', source gens coker d', 1)
eN' = map(N', source gens N', 1)
C.dd_2*eN' ++ eN''//d''


C = chainComplex{d'',d'}
e = Ures C
F = source e
prune HH_1 F
(ker e).dd^2
Ures ker e
