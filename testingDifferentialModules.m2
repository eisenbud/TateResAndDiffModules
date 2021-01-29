
--
restart
load "DifferentialModules.m2";
R = QQ[x]/(x^2)
M = R^1/ideal(x);
phi = map(M,M,0)
D = differentialModule(phi)
r = resDM(D,LengthLimit => 3)
r.dd_1
r.dd_1^2
--check that we actually have a map in DM
eps = map(D_0,r_0,matrix{{x,0,0,1,0,0}})
D.dd_0*eps - eps*r.dd_1
--how to check that its a qis?
betti res prune homology D
betti res prune homology r
--the difference seems to be a truncation effect.
r = resDM(D,LengthLimit => 6)
betti res prune homology r


restart
load "DifferentialModules.m2";
R = QQ[x]/(x^3)
M = R^1;
phi = map(M,M**R^{-2},matrix{{x^2}})
D = differentialModule(phi)
r = resDM(D,LengthLimit => 3)
r.dd_1
r.dd_1^2
--check that we actually have a map in DM
eps = map(D_0,r_0,matrix{{x,0,0,1,0,0}})
D.dd_0*eps - eps*r.dd_1
--how to check that its a qis?
betti res prune homology D
betti res prune homology r
--the difference seems to be a truncation effect.
r = resDM(D,LengthLimit => 6)
betti res prune homology r

restart
load "ToricTate.m2";
R = QQ[x,y]
M = R^2;
phi = map(M,M**R^{-2},matrix{{x*y, -x^2},{y^2,-x*y}})
D = differentialModule(phi)
r = resDM D
assert(r.dd_1^2 == 0)
r.dd_1
(r,eps) = resDMwMap D
D.dd_0*eps - eps*r.dd_1
betti res homology D
betti res prune homology r


restart
load "ToricTate.m2";
R = QQ[x]/(x^2)
M = R^1;
phi = map(M,M**R^{-1},matrix{{x}})
D = differentialModule(phi)
(r,eps) = resDMwMap(D,LengthLimit => 3);
r
r.dd_1
r.dd_1^2
--check that we actually have a map in DM
D.dd_0*eps - eps*r.dd_1
--how to check that its a qis?
betti res prune homology D
betti res prune homology r
--no homology.
degrees source r.dd_1
degrees target r.dd_1
isHomogeneous r.dd_1
r.dd_1^2
r = resDM(D,LengthLimit => 6)
r.dd_1
r.dd_1^2
rank(r.dd_1 % ideal(x))
--
restart
load "ToricTate.m2";
R = QQ[x]/(x^2)
M = R^2;
phi = map(M,M**R^{-1},matrix{{0,x},{0,0}})
D = differentialModule(phi)
r = resDM(D,LengthLimit => 3)
r.dd_1
r.dd_1^2
--check that we actually have a map in DM
eps = map(D_0,r_0,matrix{{x,0,0,0,1,0,0,0}})
D.dd_0*eps - eps*r.dd_1
--how to check that its a qis?
betti res prune homology D
betti res prune homology r
degrees source r.dd_1
degrees target r.dd_1
isHomogeneous r.dd_1
r.dd_1^2
r = resDM(D,LengthLimit => 6)
r.dd_1
r.dd_1^2
rank(r.dd_1 % ideal(x))
(r,eps) = resDMwMap(D)
---


R = QQ[x,y,z]
M = R^1/ideal(x^2,y^2,z^2)
phi = map(M,M**R^{-3},x*y*z)
D = differentialModule phi
r = resDM D
--resDM free and flag and qis to the original
r.dd_1
r.dd_1^2


--
R = QQ[x,y]
M = R^1/ideal(x^2,y^2)
phi = map(M,M**R^{-2},x*y)
D = differentialModule phi
r = resDM D
--resDM free and flag and qis to the original
r.dd_1
mingens minors(5,r.dd_1)
betti res homology D
--homology of D is annihilated by (x,y)


--Examples:  M = R^1/(x^n) and the map *x^m  where 2m\geq n.


S = ZZ/101[x,y]
phi = random(S^2,S^{5:-2})
r =res coker phi
betti r
viewHelp submatrix
det submatrix(r.dd_1,{0,1})
(det transpose submatrix(transpose r.dd_2, {2,3,4}))*((1/40)_S)
S = QQ[x]
M = matrix{{1,0,0},{x,1,0},{0,x,1}}
transpose M
(transpose M)^(-1)
M^(-1)
M*M^(-1)


S = ZZ/101[x,y]/ideal(x*y)
load "DifferentialModules.m2"
phi = map(S^2,S^{2:-1}, matrix{{0,x},{y,0}})
M = coker phi
psi = map(M,M,0)
D = differentialModule(psi)
r = resDM(D,LengthLimit=>6)
r.dd_1
d = map(S^(20),S^(20), (i,j) -> if i == j-1 then S_(i%2) else 0)
D = differentialModule(d)
M = id_(S^(20)) + map(S^(20),S^(20), (i,j) -> if i == j-1 then x else 0)
(M^(-1)*d*M)
D' = differentialModule((M^(-1)*d*M))
betti res prune homology D
betti res 
minimalPresentation prune homology D
minimalPresentation prune homology D'

restart
load "DifferentialModules.m2"
S = ZZ/101[x,y]/ideal(x*y)
M = S^1/ideal(x)
f = map(M,M,0)
D = differentialModule f
r = resDM(D,LengthLimit => 17)
d = r.dd_1
isHomogeneous D
M = id_(S^(20)) + map(S^(20),S^(20), (i,j) -> if i == j-1 then x else 0)
(M^(-1)*d*M)
degrees r_0
