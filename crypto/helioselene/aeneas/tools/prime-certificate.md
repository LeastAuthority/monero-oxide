# Primality certificate data for the helioselene prime

Goal: everything needed to prove `p.Prime` in Lean 4 mathlib via
`Mathlib.NumberTheory.LucasPrimality.lucas_primality` (Pratt certificate):

```
theorem lucas_primality (p : ℕ) (a : ZMod p)
    (ha : a ^ (p - 1) = 1)
    (hd : ∀ q : ℕ, q.Prime → q ∣ (p - 1) → a ^ ((p - 1) / q) ≠ 1) :
    p.Prime
```

## The prime

```
p = 2^255 - 0x8cab7e2e6960ce8067af49720ee20ad
  = 0x7ffffffffffffffffffffffffffffffff735481d1969f317f9850b68df11df53
  = 57896044618658097711785492504343953926623305935230693509004809574567321395027   (decimal, 77 digits, 255 bits)
```

Identity of the constant confirmed: the hex string equals `2^255 - 0x8cab7e2e6960ce8067af49720ee20ad` exactly.
This is the base field of the Selene curve / scalar field (group order) of the Helios curve from
tevador's Helios/Selene tower-cycle for Curve25519 (gist `tevador/4524c2092178df08996487d4e272b096`,
CM discriminant D = -31750123). Neither tevador's gist, its comments, the monero-oxide repo, nor the
Veridise material publishes a factorization of p-1; factordb.com had only the partial factorization
`p-1 = 2 * 7451 * C73` with the 73-digit cofactor marked composite-unfactored (factordb ID 1100000008946027509).
The C73 was split here with msieve (SIQS, 32 threads, 83 seconds); everything below it was finished
with msieve + trial division. So the tree below is (as far as could be found) not published anywhere —
it was computed and verified from scratch for this task.

p passes strong-probable-prime tests to all bases 2..64 plus 40 random bases.

## Factorization of p - 1  —  STATUS: COMPLETE

```
p - 1 = 2 * 7451 * p36 * p37

p36 = 534841956073462850512095405427775209                (36 digits, 119 bits, prime)
p37 = 7264050700998174191624543895013716307               (37 digits, 123 bits, prime)
```

All four factors verified prime by Miller-Rabin (bases 2..65 + 40 random) and, for the tree, by the
recursive Pratt data below. Product re-verified: `2 * 7451 * p36 * p37 == p - 1` exactly.

## Pratt tree

Every node verified: (a) node passes MR; (b) the listed factorization of node-1 multiplies back
exactly; (c) every listed factor passes MR; (d) the witness a satisfies `a^(n-1) = 1 (mod n)` and
`a^((n-1)/q) != 1 (mod n)` for every distinct prime q | n-1.

Assumption used: norm_num certifies primes < 10^9 cheaply, so only nodes >= 10^9 get recursive
children spelled out as tree nodes; all other factors are norm_num leaves. (The full witness data
for every prime down to 2 is nevertheless included in the JSON for convenience.)

### Root: p (255 bits) — witness a = 2

```
p - 1 = 2 * 7451 * 534841956073462850512095405427775209 * 7264050700998174191624543895013716307
```
Distinct prime factors: {2, 7451, p36, p37}. 7451 is a norm_num leaf (7451-1 = 2 * 5^2 * 149).

### Node p36 = 534841956073462850512095405427775209 — witness a = 7

```
p36 - 1 = 2^3 * 3^2 * 320657 * 23004571 * 198921971 * 5062387142597
```
Leaves (< 10^9): 2, 3, 320657, 23004571, 198921971. Recursive child: 5062387142597.

### Node p37 = 7264050700998174191624543895013716307 — witness a = 5

```
p37 - 1 = 2 * 3^4 * 11 * 17 * 91812961 * 2611669708609136013927259
```
Leaves: 2, 3, 11, 17, 91812961. Recursive child: 2611669708609136013927259 (p25).

### Node 5062387142597 (~5.1e12) — witness a = 2

```
5062387142597 - 1 = 2^2 * 7 * 20269 * 8920003
```
All factors < 10^9 — all children are norm_num leaves. Subtree terminates.

### Node p25 = 2611669708609136013927259 (~2.6e24) — witness a = 2

```
p25 - 1 = 2 * 3^2 * 4508463343 * 32182309259467
```
Recursive children: 4508463343 (~4.5e9, just above the 10^9 leaf threshold) and 32182309259467 (~3.2e13).

### Node 4508463343 — witness a = 5

```
4508463343 - 1 = 2 * 3 * 17 * 673 * 65677
```
All factors < 10^9. Terminates. (This node itself is only 4.5e9; if norm_num comfortably handles
10-digit primes it can be made a leaf instead.)

### Node 32182309259467 — witness a = 2

```
32182309259467 - 1 = 2 * 3 * 15373 * 348905107
```
All factors < 10^9 (348905107 ≈ 3.5e8). Terminates.

### Tree shape summary (nodes needing `lucas_primality`, depth-first)

```
p (witness 2)
├─ 7451                                     [norm_num leaf]
├─ p36 = 534841956073462850512095405427775209 (witness 7)
│   ├─ 320657, 23004571, 198921971          [norm_num leaves]
│   └─ 5062387142597 (witness 2)
│       └─ 20269, 8920003                   [norm_num leaves]
└─ p37 = 7264050700998174191624543895013716307 (witness 5)
    ├─ 91812961                             [norm_num leaf]
    └─ 2611669708609136013927259 (witness 2)
        ├─ 4508463343 (witness 5)
        │   └─ 673, 65677                   [norm_num leaves]
        └─ 32182309259467 (witness 2)
            └─ 15373, 348905107             [norm_num leaves]
```

Only 7 `lucas_primality` applications are needed: p, p36, p37, 5062387142597,
2611669708609136013927259, 4508463343, 32182309259467. Everything else is norm_num.

## Machine-readable tree (verified)

Each entry: prime n, Lucas witness a (smallest working, found by scanning a = 2, 3, ...),
and the complete factorization of n-1 (prime -> multiplicity). Includes every prime in the
closure down to 2, not just the >= 10^9 nodes.

```json
{
 "root": "57896044618658097711785492504343953926623305935230693509004809574567321395027",
 "leaf_threshold_used": 1000000000,
 "nodes": {
  "57896044618658097711785492504343953926623305935230693509004809574567321395027": {"witness": 2, "p_minus_1": {"2": 1, "7451": 1, "534841956073462850512095405427775209": 1, "7264050700998174191624543895013716307": 1}},
  "534841956073462850512095405427775209": {"witness": 7, "p_minus_1": {"2": 3, "3": 2, "320657": 1, "23004571": 1, "198921971": 1, "5062387142597": 1}},
  "7264050700998174191624543895013716307": {"witness": 5, "p_minus_1": {"2": 1, "3": 4, "11": 1, "17": 1, "91812961": 1, "2611669708609136013927259": 1}},
  "2611669708609136013927259": {"witness": 2, "p_minus_1": {"2": 1, "3": 2, "4508463343": 1, "32182309259467": 1}},
  "32182309259467": {"witness": 2, "p_minus_1": {"2": 1, "3": 1, "15373": 1, "348905107": 1}},
  "5062387142597": {"witness": 2, "p_minus_1": {"2": 2, "7": 1, "20269": 1, "8920003": 1}},
  "4508463343": {"witness": 5, "p_minus_1": {"2": 1, "3": 1, "17": 1, "673": 1, "65677": 1}},
  "348905107": {"witness": 3, "p_minus_1": {"2": 1, "3": 2, "11": 1, "73": 1, "101": 1, "239": 1}},
  "198921971": {"witness": 2, "p_minus_1": {"2": 1, "5": 1, "13": 1, "1237": 2}},
  "91812961": {"witness": 13, "p_minus_1": {"2": 5, "3": 3, "5": 1, "53": 1, "401": 1}},
  "23004571": {"witness": 3, "p_minus_1": {"2": 1, "3": 1, "5": 1, "17": 1, "43": 1, "1049": 1}},
  "8920003": {"witness": 2, "p_minus_1": {"2": 1, "3": 1, "7": 1, "13": 1, "17": 1, "31": 2}},
  "320657": {"witness": 3, "p_minus_1": {"2": 4, "7": 2, "409": 1}},
  "65677": {"witness": 2, "p_minus_1": {"2": 2, "3": 1, "13": 1, "421": 1}},
  "20269": {"witness": 2, "p_minus_1": {"2": 2, "3": 2, "563": 1}},
  "15373": {"witness": 2, "p_minus_1": {"2": 2, "3": 2, "7": 1, "61": 1}},
  "7451": {"witness": 2, "p_minus_1": {"2": 1, "5": 2, "149": 1}},
  "1237": {"witness": 2, "p_minus_1": {"2": 2, "3": 1, "103": 1}},
  "1049": {"witness": 3, "p_minus_1": {"2": 3, "131": 1}},
  "673": {"witness": 5, "p_minus_1": {"2": 5, "3": 1, "7": 1}},
  "563": {"witness": 2, "p_minus_1": {"2": 1, "281": 1}},
  "421": {"witness": 2, "p_minus_1": {"2": 2, "3": 1, "5": 1, "7": 1}},
  "409": {"witness": 21, "p_minus_1": {"2": 3, "3": 1, "17": 1}},
  "401": {"witness": 3, "p_minus_1": {"2": 4, "5": 2}},
  "281": {"witness": 3, "p_minus_1": {"2": 3, "5": 1, "7": 1}},
  "239": {"witness": 7, "p_minus_1": {"2": 1, "7": 1, "17": 1}},
  "149": {"witness": 2, "p_minus_1": {"2": 2, "37": 1}},
  "131": {"witness": 2, "p_minus_1": {"2": 1, "5": 1, "13": 1}},
  "103": {"witness": 5, "p_minus_1": {"2": 1, "3": 1, "17": 1}},
  "101": {"witness": 2, "p_minus_1": {"2": 2, "5": 2}},
  "73": {"witness": 5, "p_minus_1": {"2": 3, "3": 2}},
  "61": {"witness": 2, "p_minus_1": {"2": 2, "3": 1, "5": 1}},
  "53": {"witness": 2, "p_minus_1": {"2": 2, "13": 1}},
  "43": {"witness": 3, "p_minus_1": {"2": 1, "3": 1, "7": 1}},
  "37": {"witness": 2, "p_minus_1": {"2": 2, "3": 2}},
  "31": {"witness": 3, "p_minus_1": {"2": 1, "3": 1, "5": 1}},
  "17": {"witness": 3, "p_minus_1": {"2": 4}},
  "13": {"witness": 2, "p_minus_1": {"2": 2, "3": 1}},
  "11": {"witness": 2, "p_minus_1": {"2": 1, "5": 1}},
  "7": {"witness": 3, "p_minus_1": {"2": 1, "3": 1}},
  "5": {"witness": 2, "p_minus_1": {"2": 2}},
  "3": {"witness": 2, "p_minus_1": {"2": 1}},
  "2": {"witness": 1, "p_minus_1": {}}
 }
}
```

A byte-identical machine-verified copy of this tree (produced directly by the verification run) is at
`/tmp/claude-1000/-home-user-monero-oxide/2d30c0df-f4e5-4a23-b0f8-bdcdc9628721/scratchpad/phase-a/pratt_verified.json`.

## Reproduction / verification

One-shot re-verification of the whole tree (pure Python, ~seconds):

```python
NODES = {  # prime: (witness, {factor: multiplicity})  — paste from JSON above
    ...
}
for n, (a, fac) in NODES.items():
    if n == 2: continue
    assert 1 == __import__("math").prod(q**e for q, e in fac.items()) // (n-1) * 1 or True
    prod = 1
    for q, e in fac.items(): prod *= q**e
    assert prod == n - 1
    assert pow(a, n-1, n) == 1
    for q in fac:
        assert pow(a, (n-1)//q, n) != 1
        assert q == 2 or q in NODES  # closure
```

Provenance of the factorizations:
- trial division (sieve to 10^7) and Miller-Rabin: custom Python (bases 2..65 + 40 random per test);
- C73 = p36 * p37 split: msieve SVN-r1030-era (github.com/radii/msieve) SIQS, `-t 32`, 83 s wall;
- (p36-1) cofactor 23166063741070107211829298277 = 23004571 * 198921971 * 5062387142597: msieve;
- (p37-1) cofactor 239785129101411969090398887403899 = 91812961 * 2611669708609136013927259: msieve;
- (p25-1) cofactor 145092761589396445218181 = 4508463343 * 32182309259467: msieve;
- gmp-ecm 7.0.5 (Ubuntu package, extracted without install) ran ~3800 curves at B1 in {50k, 250k, 1M}
  on the C73 with no factor found (consistent with smallest factor being 36 digits) before SIQS won.

## Notes for the Lean encoding

- Root hypothesis `ha`: `(2 : ZMod p) ^ (p - 1) = 1`; `hd` needs the four cases
  q ∈ {2, 7451, p36, p37} — the "for all prime q ∣ p-1" quantifier is discharged by giving the
  factorization `p - 1 = 2 * 7451 * p36 * p37` and `Nat.Prime` proofs of the four factors
  (7451 by norm_num; p36, p37 recursively).
- The powers `a ^ ((p-1)/q) mod p` are 255-bit modexps; `decide`/`norm_num` on `ZMod p` power
  equalities of this size may need `Mathlib.Tactic.NormNum.Pow` kernel-friendly encodings or
  `Nat.ModEq` restated goals computed via `Nat.pow_mod` (binary powering reduces to ~255 squarings
  of 255-bit numbers — fine for `norm_num`-style reflection, potentially slow for `decide`).
- Mathlib's `Mathlib.Tactic.NormNum.Prime` already proves `Nat.Prime` for the < 10^9 leaves quickly;
  4508463343 (10 digits) was kept as a recursive node out of caution but is likely also fine as a
  norm_num leaf.
- Useful cross-check values: p-1 has 2-adic valuation 1 (p ≡ 3 mod 4);
  (p-1)/2 = 7451 * p36 * p37 is odd.
