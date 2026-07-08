#!/usr/bin/env python3
"""Certificate generator for HelioseleneCore/Spec/Selene/Curve.lean.

Computes (and sanity-checks) every numeric literal used in Curve.lean:
  * B, G_Y decimal literals and the generator-on-curve congruence
  * Euler nonresidue exponentiation  B^((p-1)/2) mod p  (expected p-1)
  * discriminant  D = (-16*(4*(-3)^3 + 27*B^2)) mod p  and its slack k
    in  D + 432*B^2 = 1728 + k*p
  * the no-2-torsion certificate: g = X^p mod (f, p) for
    f = X^3 - 3X + B, h = g - X, and a Bezout identity
    u*F + v*h = 1  in F_p[X]  (F = X^3 + (p-3)X + B, the Nat spelling of f),
    together with the Nat-level slack polynomial s with
    u*F + v*h = 1 + p*s  coefficient-wise over N.

Also simulates the exact Lean `polyPowMod` recursion (fuel-based binary
powering with per-step coefficient reduction mod p) to confirm the kernel
computation in Curve.lean produces exactly the printed g triple.
"""

p = 57896044618658097711785492504343953926623305935230693509004809574567321395027
B = 0x38c40d10c226ef3bc597c2e1e25bc748e3401c3d031d14ca2265f309ba81efe4
GY = 0x39098c0a54bd9d2781c7d734720d5ca639ee79deeefcd74517fced93ad6635c0

assert B < p and GY < p

print("Bcurve :=", B)
print("gY     :=", GY)

# ---- deliverable 2: generator on curve ----
lhs = (GY * GY) % p
rhs = (1 + (p - 3) * 1 + B) % p
assert lhs == rhs, "generator not on curve?!"
print("generator_on_curve holds; common value =", lhs)

# ---- deliverable 3: Euler nonresidue ----
e = (p - 1) // 2
assert e == p // 2
r = pow(B, e, p)
assert r == p - 1, f"B is a QR?! B^e mod p = {r}"
print("p/2      =", e)
print("B^(p/2) mod p = p - 1   (nonresidue confirmed)")

# ---- deliverable 4: discriminant ----
D = (-16 * (4 * (-3) ** 3 + 27 * B * B)) % p
# D + 432*B^2 = 1728 + k*p over N
num = D + 432 * B * B - 1728
assert num % p == 0 and num >= 0
k = num // p
assert D + 432 * B * B == 1728 + k * p
assert D != 0 and D < p
print("deltaNat =", D)
print("delta slack k =", k)

# ---- deliverable 5: no 2-torsion / cubic has no roots ----

# 5a. exact simulation of the Lean polyMulMod / polyPowMod recursion
def polyMulMod(pp, BB, u0, u1, u2, v0, v1, v2):
    c0 = u0 * v0
    c1 = u0 * v1 + u1 * v0
    c2 = u0 * v2 + u1 * v1 + u2 * v0
    c3 = u1 * v2 + u2 * v1
    c4 = u2 * v2
    return ((c0 + (pp - BB) * c3) % pp,
            (c1 + 3 * c3 + (pp - BB) * c4) % pp,
            (c2 + 3 * c4) % pp)

def polyPowMod(pp, BB, fuel, a0, a1, a2, e):
    if fuel == 0:
        return (1 % pp, 0, 0)
    if e % 2 == 0:
        if e == 0:
            return (1 % pp, 0, 0)
        s0, s1, s2 = polyMulMod(pp, BB, a0, a1, a2, a0, a1, a2)
        return polyPowMod(pp, BB, fuel - 1, s0, s1, s2, e // 2)
    else:
        s0, s1, s2 = polyMulMod(pp, BB, a0, a1, a2, a0, a1, a2)
        r0, r1, r2 = polyPowMod(pp, BB, fuel - 1, s0, s1, s2, e // 2)
        return polyMulMod(pp, BB, r0, r1, r2, a0, a1, a2)

import sys
sys.setrecursionlimit(10000)
g0, g1, g2 = polyPowMod(p, B, 256, 0, 1, 0, p)
print("g (= X^p mod (f,p)) via Lean-recursion simulation:")
print("  g0 =", g0)
print("  g1 =", g1)
print("  g2 =", g2)

# 5b. independent check with generic poly modexp
def pmulmod(a, b, f, pp):
    # a, b lists little-endian; f monic little-endian
    res = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            res[i + j] = (res[i + j] + x * y) % pp
    d = len(f) - 1
    while len(res) > d:
        top = res.pop()
        for i in range(d):
            res[len(res) - d + i] = (res[len(res) - d + i] - top * f[i]) % pp
    while len(res) < d:
        res.append(0)
    return res

F = [B, (p - 3) % p, 0, 1]  # f = X^3 - 3X + B
def ppowmod(base, e, f, pp):
    result = [1, 0, 0]
    b = base[:]
    while e:
        if e & 1:
            result = pmulmod(result, b, f, pp)
        b = pmulmod(b, b, f, pp)
        e >>= 1
    return result

gg = ppowmod([0, 1, 0], p, F, p)
assert (g0, g1, g2) == tuple(gg), "simulation mismatch!"
print("independent modexp agrees")

# h = g - X mod p
h0, h1, h2 = g0, (g1 - 1) % p, g2
print("h0 =", h0)
print("h1 =", h1)
print("h2 =", h2)

# 5c. Bezout: extended Euclid over F_p[X] between F (deg 3) and H (deg <= 2)
def pdeg(a):
    d = len(a) - 1
    while d >= 0 and a[d] % p == 0:
        d -= 1
    return d

def ptrim(a):
    a = [x % p for x in a]
    while len(a) > 1 and a[-1] == 0:
        a.pop()
    return a

def padd(a, b):
    n = max(len(a), len(b))
    return ptrim([( (a[i] if i < len(a) else 0) + (b[i] if i < len(b) else 0)) % p
                  for i in range(n)])

def psub(a, b):
    n = max(len(a), len(b))
    return ptrim([( (a[i] if i < len(a) else 0) - (b[i] if i < len(b) else 0)) % p
                  for i in range(n)])

def pmul(a, b):
    res = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            res[i + j] = (res[i + j] + x * y) % p
    return ptrim(res)

def pdivmod(a, b):
    # a, b coefficient lists mod p, b != 0
    a = a[:]
    db, da = pdeg(b), pdeg(a)
    binv = pow(b[db], p - 2, p)
    q = [0] * (max(da - db + 1, 1))
    while pdeg(a) >= db and pdeg(a) >= 0:
        da = pdeg(a)
        c = (a[da] * binv) % p
        q[da - db] = c
        for i in range(db + 1):
            a[da - db + i] = (a[da - db + i] - c * b[i]) % p
    return ptrim(q), ptrim(a)

Fl = ptrim(F)
Hl = ptrim([h0, h1, h2])
assert pdeg(Hl) >= 0, "h is the zero polynomial (X^p == X mod f => f splits!)"

# extended euclid
r0l, r1l = Fl, Hl
s0l, s1l = [1], [0]
t0l, t1l = [0], [1]
while pdeg(r1l) > 0:
    q, r = pdivmod(r0l, r1l)
    r0l, r1l = r1l, r
    s0l, s1l = s1l, psub(s0l, pmul(q, s1l))
    t0l, t1l = t1l, psub(t0l, pmul(q, t1l))
assert pdeg(r1l) == 0, "gcd(f, g - X) is nonconstant: f HAS a root — abort!"
c = r1l[0]
cinv = pow(c, p - 2, p)
u = ptrim([x * cinv % p for x in s1l])   # multiplies F
v = ptrim([x * cinv % p for x in t1l])   # multiplies H
# check: u*F + v*H = 1
chk = padd(pmul(u, Fl), pmul(v, Hl))
assert chk == [1], f"bezout check failed: {chk}"
u = (u + [0, 0])[:2]
v = (v + [0, 0, 0])[:3]
u0, u1 = u
v0, v1, v2 = v
print("u0 =", u0)
print("u1 =", u1)
print("v0 =", v0)
print("v1 =", v1)
print("v2 =", v2)

# 5d. Nat-level slack polynomial: u*F + v*H - 1 = p * s over N (coefficient-wise)
# LHS coefficients over Z (all inputs in [0,p)):
UU = [u0, u1]
FF = [B, p - 3, 0, 1]
VV = [v0, v1, v2]
HH = [h0, h1, h2]

def zmul(a, b):
    res = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            res[i + j] += x * y
    return res

def zadd(a, b):
    n = max(len(a), len(b))
    return [(a[i] if i < len(a) else 0) + (b[i] if i < len(b) else 0) for i in range(n)]

lhsz = zadd(zmul(UU, FF), zmul(VV, HH))
lhsz[0] -= 1
s = []
for cz in lhsz:
    assert cz >= 0 and cz % p == 0, f"slack fail {cz}"
    s.append(cz // p)
while len(s) < 5:
    s.append(0)
assert len(s) == 5, f"unexpected slack degree {len(s) - 1}"
print("s0 =", s[0])
print("s1 =", s[1])
print("s2 =", s[2])
print("s3 =", s[3])
print("s4 =", s[4])

# final re-check of the N identity at a few points
import random
for _ in range(20):
    n = random.randrange(0, 4 * p)
    L = (u1 * n + u0) * (n ** 3 + (p - 3) * n + B) \
        + (v2 * n * n + v1 * n + v0) * (h2 * n * n + h1 * n + h0)
    R = 1 + p * (s[4] * n ** 4 + s[3] * n ** 3 + s[2] * n * n + s[1] * n + s[0])
    assert L == R, "N-identity failed!"
print("N-level Bezout identity verified on random points")

print()
print("=== Lean literal block ===")
print(f"p    = {p}")
print(f"pm1_half = {e}")
print(f"B    = {B}")
print(f"gY   = {GY}")
print(f"D    = {D}")
print(f"kD   = {k}")
print(f"g0   = {g0}")
print(f"g1   = {g1}")
print(f"g2   = {g2}")
print(f"h1   = {h1}")
print(f"u0   = {u0}")
print(f"u1   = {u1}")
print(f"v0   = {v0}")
print(f"v1   = {v1}")
print(f"v2   = {v2}")
print(f"s0   = {s[0]}")
print(f"s1   = {s[1]}")
print(f"s2   = {s[2]}")
print(f"s3   = {s[3]}")
print(f"s4   = {s[4]}")
print(f"pm3  = {p - 3}")
print(f"pm1  = {p - 1}")
