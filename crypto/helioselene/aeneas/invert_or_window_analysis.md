# The `invert` top-bit `OR`: correctness window, why it is unprovable locally, and the fix

**Resolution (2026-07-10).** The recommended source-level fix has been applied:
the high-half loop now includes `add_two_modulus` in the carry chain and the
top-bit OR is gone. `HelioseleneSpec.Invert.step_congruence` and `invert_ok`
are proved without `UVWindow`. The analysis below is retained to document the
original operation, its exact correctness window, and why changing the source
was preferable to adding a trace-global assumption.

Constants used below:
- `p` = the helioselene prime = `2^255 − γ`, where `γ = 2^255 − p = 0x8cab…20ad ≈ 2^123`.
- `C := 2p − 2^255 = p − γ` (the correctness threshold; `≈ 2^255`).

---

## 1. What the code does (invert.rs, lines ~138–165)

One GCD `step` updates the Bézout cofactor `u` to the integer that should equal

```
u_new  =  ±(u − v_masked) + k·p        with sign and k ∈ {0,1,2} chosen by masks
```

so that `u_new ≥ 0` and `u_new` is even (the following `u ← u/2` is then exact).
Adding `2p` is the awkward case: `p` is a 255-bit number (bit 255 clear) but
`2p` is 256-bit (bit 255 **set**). The implementation adds the `p`-or-`2p`
correction through a carry chain over the low limbs, then injects the one top
bit that distinguishes `2p` from `p` with an **OR**, not an add:

```rust
// line 164-165 — `add_two_modulus` is 0 or all-ones; `<< 63` is 0 or 2^255
u.as_limbs_mut()[3] = u.as_limbs()[3] | (add_two_modulus << (Limb::BITS - 1));
```

This saves a carry propagation through the top limb.

## 2. Why the OR is only conditionally correct

For any integer `x`:

```
x | 2^255  =  x + 2^255      IF bit 255 of x is 0
x | 2^255  =  x              IF bit 255 of x is 1   (the OR does nothing)
```

So the instruction computes the intended `+2^255` **iff bit 255 of the pre-OR
accumulator is clear**. Reducing that condition through the chain arithmetic
gives a sharp window on the driving difference:

```
correct  ⇔  |u − v_masked| ≤ C = 2p − 2^255 = p − γ
```

Verified bit-exactly against the extracted code: correct at `C`, **wrong at
`C + 2`** (the OR silently drops the `+2^255`, so `u'` comes out too small by
`2^255`, `u' > p`, and the congruence `a' ≡ u'·y (mod p)` breaks).

## 3. Why `UVWindow` preservation is not provable by a local invariant

The Lean obligation is inductive: *in-window input ⇒ in-window output*. It fails
locally for a structural reason.

- **A single `step` can produce an out-of-window state on its own terms.** A
  correction can push `u'` up near `p` while `v'` stays small, so `|u' − v'|`
  can exceed `C`. Whether it does depends on the *actual* `(u, v)` values.
- **The reachable `(u, v)` are constrained by a trace-global relation**, not a
  local one: `u, v` are cofactors with `a·v − b·u ≡ 0 (mod p)` and a tightly
  bounded integer coupling `J = (a·v − b·u)/p` (`|J| ≤ a + b − 1`, empirically
  tight). This relation is what keeps every state reachable from the initial
  `(y, p, 1, 0)` inside the window.

Consequently any candidate invariant `P(a,b,u,v)` is squeezed:

| If `P` is … | then … |
|---|---|
| too weak | it admits states the real trace never reaches, on which `step` genuinely violates the window — the two counterexamples below |
| strong enough | it must encode "reachable from the start," which is not a finite condition on four numbers — essentially the trace itself |

**Two verified counterexamples** (each satisfies every stated conjunct, yet
executes to a wrong `u'`):
- `(y,a,b,u,v) = (2, p+2, p, 1, p)` — breaks the original invariant (`u,v ≤ p`).
- `(y,a,b,u,v) = (w, w, p−2w, 1, p−2)` for odd `w ∈ [p/3, p/2)` — breaks the
  `a,b ≤ p`-strengthened invariant too. Its violating region has measure
  `≈ γ/p ≈ 2^−132` among random invariant-respecting states, which is why
  1.25M-state fuzzing never hit it; it was found by targeted analysis.

**This is not just a hard proof — the construction is genuinely non-generic.**
Exhaustively over **all** primes with `2^(m−2) < q < 2^(m−1)`, `m = 8..11`, and
all inputs, the OR trick **fails for most primes**. The real `p` is safe only
because `γ ≈ 2^123` lies ~132 bits below `p`, so any true invariant must
quantitatively use this prime's structure — which a prime-agnostic local
invariant cannot.

**Honest status for the shipped `p`:** correct on all 2016 full 510-step traces
tested (incl. adversarial edge values), all 500 random inversions, and the
first-order danger family `u = 2^−k mod p, v = 0` for `k ≤ 1200` (≥115 bits of
margin everywhere). The heuristic danger measure is `≈ 1` expected bad
`(y, step)` pair over all `2^255` inputs — so "correct for literally every
input" is **plausible but not certain**, and settling it is research-grade
(formalize `J` and count the `γ`-sized danger windows against the reachable
`(u,v)` structure). Veridise's Dafny artifact does **not** cover this: it
replaced the fused chain with branching exact-mod-`p` code and asserted, without
proof, that the Rust "produces the same value modulo p".

## 4. The fix: replace the `OR` with a real add

Change line 164-165 from an OR to a genuine carry-propagating addition of
`2^255` into the top limb — equivalently, route the `2p`-correction's top bit
through the same `overflowing_add` carry chain the other limbs already use,
instead of special-casing it. Then

```
u_pre + 2^255  (mod 2^256)
```

is computed correctly **whether or not bit 255 was already set**: the carry
propagates out and is dropped mod `2^256`, which is harmless because the true
intended value `±(u − v_masked) + k·p` is always `< 3p < 2^256` and `u` is
reduced mod `p` at the end of `invert` anyway.

Consequences:
- **The window disappears.** The update equals the mathematically intended
  value for *all* inputs satisfying the cheap local invariant (`u, v ≤ p`).
- **`step_congruence` closes** with the local machinery already in the Lean
  file — no reachability argument, no `γ`-margin, no research program. The
  entire package becomes `sorry`-free.
- **Cost:** a few extra 64-bit adds per step. The code's own comment
  (invert.rs lines 145–149) already contemplates alternative top-limb handling,
  so this spot is a deliberate micro-optimization, not a load-bearing design
  choice.

**The trade in one line:** the `OR` buys a tiny constant-time speedup at the
price of a correctness property that is unfalsifiable without a `2^255` search;
a real add returns that speedup and makes correctness provable and
prime-independent. For consensus-critical inversion that is the right trade, and
it is the recommendation independent of whether the Lean proof of the *current*
code is ever completed.

---

*Cross-references: `human_audit_assumptions.txt` §I.1 (full ledger entry);
`HelioseleneCore/Spec/Invert.lean` (the `UVWindow` def + `step_congruence`
docstring); counterexample simulators archived under the session scratchpad
`sorry-final/` (sim_uchain.py, diag.py, reach.py, sim_full_invert.py).*
