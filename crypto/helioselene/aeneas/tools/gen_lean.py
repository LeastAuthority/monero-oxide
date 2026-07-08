"""Emit the unit-z certificate lemmas as Lean source."""
from poly import *
import poly as PP

PP.NAMES = ['x1', 'y1', 'x2', 'y2', '(Bcurve : F)']

X3, Y3, Z3 = addCoords(x1, y1, one, x2, y2, one)
d = psub(x1, x2)
d2 = pmul(d, d); d3 = pmul(d2, d); d4 = pmul(d2, d2); d6 = pmul(d3, d3)
u = padd(y1, y2)
v = psub(y1, y2)
sx = padd(x1, x2)
tx = padd(pscale(x1, 2), x2)

N4 = psub(pmul(u, psub(pmul(tx, d2), pmul(u, u))), pmul(y1, d3))
R2 = psub(pmul(u, u), pmul(sx, d2))
Nx = psub(pmul(v, v), pmul(sx, d2))
Ny = psub(pmul(v, psub(pmul(tx, d2), pmul(v, v))), pmul(y1, d3))

def cof(p):
    nfp, c1, c2 = reduce_mod(p)
    assert is_zero(nfp)
    return lean(c1), lean(c2)

out = []

# CERT1 as used: prove  N4 = 0  from  hZ : Z3 = 0.
# linear_combination (-1) * hZ + c1 * hE1 + c2 * hE2 proves N4 = 0 iff
# N4 - 0 - [(-1)(Z3 - 0) + c1*E1 + c2*E2] == 0 iff N4 + Z3 = c1 E1 + c2 E2.
c1, c2 = cof(padd(Z3, N4))
out.append(("CERT1  (N4 = 0 from Z3 = 0):  linear_combination (-1) * hZ + (%s) * hE1 + (%s) * hE2" % (c1, c2)))

# CERT2: prove R2^3 - 3 R2 d^4 + B d^6 = 0 from hN4 : N4 = 0:
# goal - [N4 * hN4 + c1 hE1 + c2 hE2] == 0 iff (R2^3 - ...) - N4^2 = c1 E1 + c2 E2
c1, c2 = cof(psub(padd(psub(ppow(R2, 3), pscale(pmul(R2, d4), 3)), pmul(B, d6)), pmul(N4, N4)))
out.append("CERT2  (hom cubic from N4 = 0): linear_combination (%s) * hN4 + (%s) * hE1 + (%s) * hE2" % (lean(N4), c1, c2))

# CERT3: X3 * d^2 = Nx * Z3
c1, c2 = cof(psub(pmul(X3, d2), pmul(Nx, Z3)))
out.append("CERT3  (X3 d2 = Nx Z3): linear_combination (%s) * hE1 + (%s) * hE2" % (c1, c2))

# CERT4: Y3 * d^3 = Ny * Z3
c1, c2 = cof(psub(pmul(Y3, d3), pmul(Ny, Z3)))
out.append("CERT4  (Y3 d3 = Ny Z3): linear_combination (%s) * hE1 + (%s) * hE2" % (c1, c2))

# print the reference polynomials for statements
for nm, p in [('N4', N4), ('R2', R2), ('Nx', Nx), ('Ny', Ny)]:
    out.append("POLY %s = %s" % (nm, lean(p)))

# one-point certificates (vars x1 y1 only)
def subst_diag(p, ysign):
    r = {}
    for m, c in p.items():
        mm = list(m)
        cc = c * (ysign ** m[Y2])
        mm[X1] += m[X2]; mm[X2] = 0
        mm[Y1] += m[Y2]; mm[Y2] = 0
        key = tuple(mm)
        nc = r.get(key, 0) + cc
        if nc: r[key] = nc
        elif key in r: del r[key]
    return r

st = psub(pscale(ppow(x1, 2), 3), const(3))
D = pscale(y1, 2)
D2 = pmul(D, D); D3 = pmul(D2, D); D4 = pmul(D2, D2); D6 = pmul(D3, D3)
M = psub(pmul(st, st), pscale(pmul(x1, D2), 2))
Ndbl = psub(pmul(st, psub(pmul(x1, D2), M)), pmul(y1, D3))

Y3a = subst_diag(Y3, -1)
X3d = subst_diag(X3, +1); Y3d = subst_diag(Y3, +1); Z3d = subst_diag(Z3, +1)

c1, c2 = cof(psub(Y3a, Ndbl))
out.append("CERT5  (Y3anti = Ndbl): linear_combination (%s) * hE1" % c1)
c1, c2 = cof(psub(padd(psub(ppow(M, 3), pscale(pmul(M, D4), 3)), pmul(B, D6)), pmul(Ndbl, Ndbl)))
out.append("CERT6  (hom cubic from Ndbl = 0): linear_combination (%s) * hN + (%s) * hE1" % (lean(Ndbl), c1))
c1, c2 = cof(psub(X3d, pmul(M, D)))
out.append("CERT7X (X3diag = M*D): linear_combination (%s) * hE1" % c1)
c1, c2 = cof(psub(Y3d, Ndbl))
out.append("CERT7Y (Y3diag = Ndbl): linear_combination (%s) * hE1" % c1)
c1, c2 = cof(psub(Z3d, D3))
out.append("CERT7Z (Z3diag = D^3): linear_combination (%s) * hE1" % c1)
out.append("POLY M = %s" % lean(M))
out.append("POLY Ndbl = %s" % lean(Ndbl))

print('\n\n'.join(out))
