"""Emit the unit-z RCB certificate lemmas for the HELIOS group law as Lean source.

Helios port of `gen_lean.py` (the Selene certificate generator). Self-contained:
the tiny multivariate polynomial engine (originally `phase-d/poly.py`, ephemeral
scratchpad) is inlined below.

Curve: y^2 = x^3 - 3x + B over ZMod q with
  q = 2^255 - 19,
  B = 0x26bdec0884fe05f20cb42071569fab6432be360d07da8c5b460b82b980fd8c60.

The cofactor extraction runs over ZZ[x1, y1, x2, y2, B] with B SYMBOLIC, so the
certificates are integer-coefficient polynomial identities valid over ANY
commutative ring and ANY value of B: they are expected to agree with the Selene
certificates (`lean_certs.txt`) up to the field spelling `(Bcurve : Fq)` vs
`(Bcurve : F)`. This script re-derives them from scratch anyway (independent
regeneration for the (q, B_helios) instance) and then NUMERICALLY re-verifies
every emitted identity at pseudo-random points modulo the concrete
(q, B_helios) pair, so a silent porting mistake in either the engine or the RCB
chain transcription would be caught.

Usage:  python3 gen_lean_helios.py > lean_certs_helios.txt
"""

# ---------------------------------------------------------------------------
# Tiny multivariate polynomial engine over ZZ (inlined from phase-d/poly.py).
# Variables (fixed order): x1, y1, x2, y2, B  -> exponent 5-tuples.
# Poly = dict{exp-tuple: int coeff}.
# Reduction mod E1 = y1^2 - (x1^3 - 3x1 + B), E2 = y2^2 - (x2^3 - 3x2 + B)
# with cofactor tracking: p = nf + c1*E1 + c2*E2.
# ---------------------------------------------------------------------------

NV = 5
X1, Y1, X2, Y2, BB = range(NV)
NAMES = ['x1', 'y1', 'x2', 'y2', '(Bcurve : Fq)']
VARKEYS = ['x1', 'y1', 'x2', 'y2', 'B']  # keyword names for P(**kw)

def P(**kw):
    e = [0] * NV
    for k, v in kw.items():
        e[VARKEYS.index(k)] = v
    return {tuple(e): 1}

def const(c):
    return {(0,) * NV: c} if c else {}

def padd(a, b):
    r = dict(a)
    for m, c in b.items():
        nc = r.get(m, 0) + c
        if nc:
            r[m] = nc
        elif m in r:
            del r[m]
    return r

def pneg(a):
    return {m: -c for m, c in a.items()}

def psub(a, b):
    return padd(a, pneg(b))

def pmul(a, b):
    r = {}
    for m1, c1 in a.items():
        for m2, c2 in b.items():
            m = tuple(i + j for i, j in zip(m1, m2))
            nc = r.get(m, 0) + c1 * c2
            if nc:
                r[m] = nc
            elif m in r:
                del r[m]
    return r

def pscale(a, k):
    if not k:
        return {}
    return {m: c * k for m, c in a.items()}

def ppow(a, n):
    r = const(1)
    for _ in range(n):
        r = pmul(r, a)
    return r

# curve rhs f(x) = x^3 - 3x + B (variable slot)
def fx(xkey):
    return padd(psub(P(**{xkey: 3}), pscale(P(**{xkey: 1}), 3)), P(B=1))

E1 = psub(P(y1=2), fx('x1'))   # y1^2 - f(x1)
E2 = psub(P(y2=2), fx('x2'))

def reduce_mod(p):
    """return (nf, c1, c2) with p = nf + c1*E1 + c2*E2, nf y-degrees <= 1."""
    c1, c2 = {}, {}
    p = dict(p)
    changed = True
    while changed:
        changed = False
        for m in list(p.keys()):
            c = p.get(m, 0)
            if not c:
                continue
            if m[Y1] >= 2:
                qq = list(m); qq[Y1] -= 2
                qm = {tuple(qq): c}
                p = psub(p, pmul(qm, E1))
                c1 = padd(c1, qm)
                changed = True
                break
            if m[Y2] >= 2:
                qq = list(m); qq[Y2] -= 2
                qm = {tuple(qq): c}
                p = psub(p, pmul(qm, E2))
                c2 = padd(c2, qm)
                changed = True
                break
    return p, c1, c2

def is_zero(p):
    return not p

def lean(p):
    """Lean expression (variables x1 y1 x2 y2 (Bcurve : Fq) assumed in scope)."""
    if not p:
        return "0"
    terms = sorted(p.items(), key=lambda kv: (-sum(kv[0]), kv[0]))
    out = []
    for m, c in terms:
        parts = []
        for i, e in enumerate(m):
            if e == 1:
                parts.append(NAMES[i])
            elif e > 1:
                parts.append(f"{NAMES[i]} ^ {e}")
        if not parts:
            out.append(f"({c} : Fq)" if c >= 0 else f"(({c}) : Fq)")
            continue
        body = ' * '.join(parts)
        if c == 1:
            out.append(body)
        elif c == -1:
            out.append(f"(-1) * {body}")
        else:
            out.append(f"({c}) * {body}" if c >= 0 else f"(({c})) * {body}")
    return ' + '.join(out)

# ---------------------------------------------------------------------------
# RCB addCoords mirror (identical chain to HelioseleneCore/Spec/Helios/Ops.lean's
# `addCoords`, which itself mirrors the translated `HeliosPoint::add`).
# ---------------------------------------------------------------------------

x1, y1, x2, y2, B = P(x1=1), P(y1=1), P(x2=1), P(y2=1), P(B=1)
one = const(1)

def addCoords(px, py, pz, qx, qy, qz):
    t0 = pmul(px, qx)
    t1 = pmul(py, qy)
    t2 = pmul(pz, qz)
    t3 = psub(pmul(padd(px, py), padd(qx, qy)), padd(t0, t1))
    t4 = psub(pmul(padd(py, pz), padd(qy, qz)), padd(t1, t2))
    t5 = psub(pmul(padd(px, pz), padd(qx, qz)), padd(t0, t2))
    u = psub(t5, pmul(B, t2))
    v = padd(u, pscale(u, 2))
    zc = psub(t1, v)
    xc = padd(t1, v)
    w = psub(psub(pmul(B, t5), padd(pscale(t2, 2), t2)), t0)
    ww = padd(pscale(w, 2), w)
    s = psub(padd(pscale(t0, 2), t0), padd(pscale(t2, 2), t2))
    X3 = psub(pmul(t3, xc), pmul(t4, ww))
    Y3 = padd(pmul(xc, zc), pmul(s, ww))
    Z3 = padd(pmul(t4, zc), pmul(t3, s))
    return X3, Y3, Z3

# ---------------------------------------------------------------------------
# Certificate derivation (identical logic to gen_lean.py).
# ---------------------------------------------------------------------------

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
    assert is_zero(nfp), "not in the ideal (E1, E2) over ZZ!"
    return c1, c2

# Every emitted certificate is recorded here as (target, [(cofactor, base)...])
# meaning: target == sum(cofactor * base) as polynomials over ZZ — re-verified
# numerically mod (q, B_helios) at the end.
CHECKS = []
out = []

# CERT1 as used: prove  N4 = 0  from  hZ : Z3 = 0.
# linear_combination (-1) * hZ + c1 * hE1 + c2 * hE2 proves N4 = 0 iff
# N4 + Z3 = c1 E1 + c2 E2.
c1, c2 = cof(padd(Z3, N4))
CHECKS.append((padd(Z3, N4), [(c1, E1), (c2, E2)]))
out.append("CERT1  (N4 = 0 from Z3 = 0):  linear_combination (-1) * hZ + (%s) * hE1 + (%s) * hE2"
           % (lean(c1), lean(c2)))

# CERT2: prove R2^3 - 3 R2 d^4 + B d^6 = 0 from hN4 : N4 = 0:
# (R2^3 - 3 R2 d^4 + B d^6) - N4^2 = c1 E1 + c2 E2
tgt2 = psub(padd(psub(ppow(R2, 3), pscale(pmul(R2, d4), 3)), pmul(B, d6)), pmul(N4, N4))
c1, c2 = cof(tgt2)
CHECKS.append((tgt2, [(c1, E1), (c2, E2)]))
out.append("CERT2  (hom cubic from N4 = 0): linear_combination (%s) * hN4 + (%s) * hE1 + (%s) * hE2"
           % (lean(N4), lean(c1), lean(c2)))

# CERT3: X3 * d^2 = Nx * Z3
tgt3 = psub(pmul(X3, d2), pmul(Nx, Z3))
c1, c2 = cof(tgt3)
CHECKS.append((tgt3, [(c1, E1), (c2, E2)]))
out.append("CERT3  (X3 d2 = Nx Z3): linear_combination (%s) * hE1 + (%s) * hE2"
           % (lean(c1), lean(c2)))

# CERT4: Y3 * d^3 = Ny * Z3
tgt4 = psub(pmul(Y3, d3), pmul(Ny, Z3))
c1, c2 = cof(tgt4)
CHECKS.append((tgt4, [(c1, E1), (c2, E2)]))
out.append("CERT4  (Y3 d3 = Ny Z3): linear_combination (%s) * hE1 + (%s) * hE2"
           % (lean(c1), lean(c2)))

# print the reference polynomials for statements
for nm, pp in [('N4', N4), ('R2', R2), ('Nx', Nx), ('Ny', Ny)]:
    out.append("POLY %s = %s" % (nm, lean(pp)))

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
        if nc:
            r[key] = nc
        elif key in r:
            del r[key]
    return r

st = psub(pscale(ppow(x1, 2), 3), const(3))
D = pscale(y1, 2)
D2 = pmul(D, D); D3 = pmul(D2, D); D4 = pmul(D2, D2); D6 = pmul(D3, D3)
M = psub(pmul(st, st), pscale(pmul(x1, D2), 2))
Ndbl = psub(pmul(st, psub(pmul(x1, D2), M)), pmul(y1, D3))

Y3a = subst_diag(Y3, -1)
X3d = subst_diag(X3, +1); Y3d = subst_diag(Y3, +1); Z3d = subst_diag(Z3, +1)

tgt5 = psub(Y3a, Ndbl)
c1, c2 = cof(tgt5)
assert is_zero(c2)
CHECKS.append((tgt5, [(c1, E1)]))
out.append("CERT5  (Y3anti = Ndbl): linear_combination (%s) * hE1" % lean(c1))

tgt6 = psub(padd(psub(ppow(M, 3), pscale(pmul(M, D4), 3)), pmul(B, D6)), pmul(Ndbl, Ndbl))
c1, c2 = cof(tgt6)
assert is_zero(c2)
CHECKS.append((tgt6, [(c1, E1)]))
out.append("CERT6  (hom cubic from Ndbl = 0): linear_combination (%s) * hN + (%s) * hE1"
           % (lean(Ndbl), lean(c1)))

tgt7x = psub(X3d, pmul(M, D))
c1, c2 = cof(tgt7x)
assert is_zero(c2)
CHECKS.append((tgt7x, [(c1, E1)]))
out.append("CERT7X (X3diag = M*D): linear_combination (%s) * hE1" % lean(c1))

tgt7y = psub(Y3d, Ndbl)
c1, c2 = cof(tgt7y)
assert is_zero(c2)
CHECKS.append((tgt7y, [(c1, E1)]))
out.append("CERT7Y (Y3diag = Ndbl): linear_combination (%s) * hE1" % lean(c1))

tgt7z = psub(Z3d, D3)
c1, c2 = cof(tgt7z)
assert is_zero(c2)
CHECKS.append((tgt7z, [(c1, E1)]))
out.append("CERT7Z (Z3diag = D^3): linear_combination (%s) * hE1" % lean(c1))

out.append("POLY M = %s" % lean(M))
out.append("POLY Ndbl = %s" % lean(Ndbl))

# ---------------------------------------------------------------------------
# Numeric re-verification of every certificate mod (q, B_helios), and of the
# transcribed RCB chain against the closed-form addCoords_x/y/z polynomials.
# ---------------------------------------------------------------------------

q = 2 ** 255 - 19
B_HELIOS = 0x26bdec0884fe05f20cb42071569fab6432be360d07da8c5b460b82b980fd8c60

def peval(p, vals):
    """Evaluate poly at vals = (x1, y1, x2, y2, B) mod q."""
    acc = 0
    for m, c in p.items():
        t = c % q
        for i, e in enumerate(m):
            t = (t * pow(vals[i], e, q)) % q
        acc = (acc + t) % q
    return acc

import random
rng = random.Random(20260709)
for trial in range(20):
    vals = (rng.randrange(q), rng.randrange(q), rng.randrange(q), rng.randrange(q), B_HELIOS)
    for idx, (tgt, combo) in enumerate(CHECKS):
        lhs = peval(tgt, vals)
        rhs = 0
        for cf, base in combo:
            rhs = (rhs + peval(cf, vals) * peval(base, vals)) % q
        assert lhs == rhs, ("numeric check failed", idx, trial)

# closed-form cross-check of the transcribed chain (matches Ops.lean addCoords_x/y/z)
for trial in range(20):
    vx1, vy1, vz1, vx2, vy2, vz2 = (rng.randrange(q) for _ in range(6))
    Bv = B_HELIOS
    # direct numeric chain evaluation
    t0 = vx1 * vx2 % q; t1 = vy1 * vy2 % q; t2 = vz1 * vz2 % q
    t3 = ((vx1 + vy1) * (vx2 + vy2) - (t0 + t1)) % q
    t4 = ((vy1 + vz1) * (vy2 + vz2) - (t1 + t2)) % q
    t5 = ((vx1 + vz1) * (vx2 + vz2) - (t0 + t2)) % q
    uu = (t5 - Bv * t2) % q
    vv = (uu + uu + uu) % q
    zc = (t1 - vv) % q
    xc = (t1 + vv) % q
    ww_ = (Bv * t5 - 3 * t2 - t0) % q
    www = 3 * ww_ % q
    ss = (3 * t0 - 3 * t2) % q
    cx = (t3 * xc - t4 * www) % q
    cy = (xc * zc + ss * www) % q
    cz = (t4 * zc + t3 * ss) % q
    # closed forms (Ops.lean addCoords_x/y/z)
    fx_ = ((vx1 * vy2 + vx2 * vy1) * (t1 + 3 * (vx1 * vz2 + vx2 * vz1) - 3 * Bv * t2)
           - 3 * (vy1 * vz2 + vy2 * vz1) * (Bv * (vx1 * vz2 + vx2 * vz1) - 3 * t2 - t0)) % q
    fy_ = ((t1 + 3 * (vx1 * vz2 + vx2 * vz1) - 3 * Bv * t2)
           * (t1 - 3 * (vx1 * vz2 + vx2 * vz1) + 3 * Bv * t2)
           + (3 * t0 - 3 * t2) * 3 * (Bv * (vx1 * vz2 + vx2 * vz1) - 3 * t2 - t0)) % q
    fz_ = ((vy1 * vz2 + vy2 * vz1) * (t1 - 3 * (vx1 * vz2 + vx2 * vz1) + 3 * Bv * t2)
           + (vx1 * vy2 + vx2 * vy1) * (3 * t0 - 3 * t2)) % q
    assert (cx, cy, cz) == (fx_, fy_, fz_), ("closed-form mismatch", trial)

import sys
print('\n\n'.join(out))
print("\n\n-- all symbolic cofactor extractions exact over ZZ;"
      "\n-- 20 random-point numeric re-checks mod (q, B_helios) passed;"
      "\n-- RCB chain transcription matches the Ops.lean closed forms (20 random checks).",
      file=sys.stderr)
