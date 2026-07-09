# Primality certificate data for q = 2^255 - 19 (the Curve25519 field prime)

Goal: everything needed to prove `q.Prime` in Lean 4 mathlib via
`Mathlib.NumberTheory.LucasPrimality.lucas_primality` (Pratt certificate),
kernel-only, exactly as was done for the helioselene prime in
`HelioseleneCore/Spec/Prime.lean` / `tools/gen_prime.py`.

```
theorem lucas_primality (p : ℕ) (a : ZMod p)
    (ha : a ^ (p - 1) = 1)
    (hd : ∀ q : ℕ, q.Prime → q ∣ (p - 1) → a ^ ((p - 1) / q) ≠ 1) :
    p.Prime
```

## The prime

```
q = 2^255 - 19
  = 0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffed
  = 57896044618658097711785492504343953926634992332820282019728792003956564819949   (decimal, 77 digits, 255 bits)
```

This is the base field of Curve25519/Ed25519 and the field the Helios/Selene
tower cycle sits over (scalar field of Selene, base field of Helios).

q passes strong-probable-prime tests to all bases 2..65 plus 48 random bases.

## Factorization of q - 1  —  STATUS: COMPLETE

```
q - 1 = 2^2 * 3 * 65147 * p236

p236 = 74058212732561358302231226437062788676166966415465897661863160754340907   (71 digits, 236 bits, prime)
```

The factorization of q - 1 (and of p236 - 1) is well known from the
Curve25519 literature / factordb; here it was reconstructed and then
**fully re-verified locally**: every listed factor passes Miller-Rabin
(bases 2..65 + 48 random) and every factorization multiplies back exactly
to n - 1. The one piece that needed actual factoring work locally was the
27-digit cofactor of p35 - 1 (see below), split instantly by the msieve
binary already built for the helioselene certificate.

## Pratt tree

Every node verified: (a) node passes MR; (b) the listed factorization of
node-1 multiplies back exactly; (c) every listed factor passes MR; (d) the
witness a satisfies `a^(n-1) = 1 (mod n)` and `a^((n-1)/q) != 1 (mod n)` for
every distinct prime q | n-1. (This verification is re-run by
`gen_prime25519.py` every time the Lean file is generated.)

Convention (same as the helioselene certificate): norm_num certifies primes
< 10^9 cheaply, so only nodes >= 10^9 get recursive children spelled out as
tree nodes; all other factors are norm_num leaves. This gives 7 Lucas nodes.

### Root: q (255 bits) — witness a = 2

```
q - 1 = 2^2 * 3 * 65147 * 74058212732561358302231226437062788676166966415465897661863160754340907
```
Leaves (< 10^9): 2, 3, 65147. Recursive child: p236.

### Node p236 = 74058212732561358302231226437062788676166966415465897661863160754340907 — witness a = 2

```
p236 - 1 = 2 * 3 * 353 * 57467 * 132049 * 1923133 * 31757755568855353 * 75445702479781427272750846543864801
```
Leaves: 2, 3, 353, 57467, 132049, 1923133.
Recursive children: p17 = 31757755568855353, p35 = 75445702479781427272750846543864801.

### Node p35 = 75445702479781427272750846543864801 (~7.5e34) — witness a = 7

```
p35 - 1 = 2^5 * 3^2 * 5^2 * 75707 * 72106336199 * 1919519569386763
```
Trial division left the 27-digit composite 138409523410761641138333837; msieve
split it as `72106336199 * 1919519569386763` (both prime).
Leaves: 2, 3, 5, 75707. Recursive children: 72106336199, 1919519569386763.

### Node p17 = 31757755568855353 (~3.2e16) — witness a = 10

```
p17 - 1 = 2^3 * 3 * 31 * 107 * 223 * 4153 * 430751
```
All factors are leaves.

### Node 1919519569386763 (~1.9e15) — witness a = 2

```
1919519569386763 - 1 = 2 * 3 * 7 * 19 * 47^2 * 127 * 8574133
```
All factors are leaves.

### Node 72106336199 (~7.2e10) — witness a = 7

```
72106336199 - 1 = 2 * 13 * 2773320623
```
Leaves: 2, 13. Recursive child: 2773320623 (just above the 10^9 leaf bound).

### Node 2773320623 (~2.8e9) — witness a = 5

```
2773320623 - 1 = 2 * 2437 * 569003
```
All factors are leaves.

## Machine-checkable data

The full tree (witnesses + factorizations) lives in `tools/pratt_25519.json`.
`tools/gen_prime25519.py` re-verifies it (Fermat + primitivity of each
witness, exact product reconstruction, closure of the tree) and emits
`HelioseleneCore/Spec/Helios/Prime25519.lean`.

## Lean result

```
theorem q_prime :
    Nat.Prime 57896044618658097711785492504343953926634992332820282019728792003956564819949

instance fact_q_prime : Fact (Nat.Prime 5789...9949)
```

in namespace-free scope (Pratt machinery under `Helios25519Pratt`), proved
with `lucas_primality` at the 7 nodes above; all modular exponentiations are
kernel-reduced through the fuel-based `powMod`.

- `#print axioms q_prime` = `[propext, Classical.choice, Quot.sound]` (kernel-only,
  no `native_decide`, no `sorry`; same for `fact_q_prime`).
- Elaboration benchmark: `lake env lean HelioseleneCore/Spec/Helios/Prime25519.lean`
  completes in ~8.4 s wall (~7.5 s user) on this machine; `lake build` of the
  module takes ~7 s and the whole `HelioseleneCore` tree stays green.
