
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
