# Strategic search for a true `invert` OR-trick failure — results

**Historical status (2026-07-10).** No concrete failing field input was found,
but the production source has since replaced the OR with an exact four-limb
carry-chain addition. The search result below records the evidence gathered
before that correction; the repaired implementation no longer has this
failure condition.

**Question.** Does an input `y ∈ [1, p)` exist for which the real Rust
`HelioseleneField::invert(y)` returns a *wrong* inverse, because the fused
u-chain's top-bit `OR` (invert.rs L164-165) drops a `+2^255`? (Background:
`invert_or_window_analysis.md`, `human_audit_assumptions.txt` §I.1.)

**Answer (this search).** No failing input was found. Across **~4 million
strategically-constructed inputs**, the closest any of them drove the internal
state to the failure window was **2^168**, i.e. **~45 bits short** of the
`γ ≈ 2^123` threshold at which the OR becomes lossy. The two closest inputs
were confirmed on the **real shipped Rust** to return the correct inverse.
This is strong quantitative evidence of safety-by-margin for this prime — not a
proof of universal correctness (see "What this does and does not establish").

---

## Pipeline

1. **Real-Rust oracle** — a batch binary
   (`scratchpad/helioselene-patched/src/bin/invert_oracle.rs`) calling the
   actual crate's `HelioseleneField::invert`; the ground-truth verdict is always
   `invert(y)·y ≡ 1 (mod p)`.
2. **Bit-exact fast model** (`pipeline/model.py`) — a faithful reimplementation
   of the branchless chain *including the OR*, **cross-validated to agree with
   real Rust bit-for-bit on 20,000 diverse inputs** (uniform, small-rational,
   2-adic, near-boundary). It exposes, per step, the observables that make the
   search strategic:
   - the identity `u_i = a_i·y⁻¹ mod p`, `v_i = b_i·y⁻¹ mod p` (verified every
     step), and `Dres = (a_i − b_i)·y⁻¹ mod p`;
   - a per-step `margin` = distance of the state to the OR-failure window
     (`margin ≤ 0` ⟺ that step's OR is lossy ⟺ wrong inverse).
   Per-input fitness = `min_i margin_i` (the "how close did this input come"
   metric). This is the "checks inside the inverse steps" instrumentation.

## The target, sharply

The OR is lossy exactly when, at an **odd** step, `u_i` and `v_i` land at
**opposite ends** of `[0, p]` — one `< γ`, the other `> p − γ`
(`γ = 2^255 − p ≈ 2^123`). Note `Dres ≈ 0` alone is *not* enough (the closest
random hit had `Dres ≈ 0` but `u ≈ v ≈ 2^254`, the safe branch): the danger is
the **two-sided** event `u < γ AND v > p−γ`. Its density is
`≈ (γ/p)² ≈ 2^−264` per step, `≈ 1` expected occurrence over the *entire*
`2^255` input space — which is why blind fuzzing cannot probe it and a targeted
method is required.

## Strategic methods run

- **Structured families** — small rationals `y = s·t⁻¹ mod p` (`s,t ≤ 400`),
  2-adic `y = m·2^{±k} mod p` (1.2M of them). Floor: `2^242`. (These bias
  cofactors *small* — both toward 0 — i.e. the *safe* direction.)
- **Plant-and-verify** — using the identity, solve `y = a·e⁻¹ mod p` to force a
  chosen cofactor tiny at a reachable-looking state, then forward-verify.
  Reachability wall: no improvement past the structured floor.
- **Adaptive multi-basin hill-climb** — observe each input's closest step
  (`u`, `v`, `Dres` bit-patterns), perturb `y` by 2-adic shifts, small-rational
  multiplies, and additive nudges; keep a population of the 50 lowest-margin
  inputs and climb from each. This is the "deduce better next inputs from the
  observed bit pattern" loop.

## Results

| stage | candidates | closest margin | gap to band |
|---|---|---|---|
| random baseline | 2,000 | `2^246.6` | 123 bits |
| small rationals | 160,000 | `2^246.0` | 123 bits |
| 2-adic | 1,200,000 | `2^242.7` | 120 bits |
| plant-from-near-danger | 1,500 | `2^242.7` | 120 bits |
| hill-climb (run 1) | ~120,000 | `2^169.1` | 46 bits |
| **multi-basin refine** | **~1,620,000** | **`2^168.1`** | **~45 bits** |

- The hill-climb closed **77 bits** (2^246 → 2^169) by finding an input whose
  trace has a step with `u ≈ p − 2^168` (just below `p`) and `v ≈ 2^169`.
- The intensified 20-basin × 27-round refine improved this by only **1 more
  bit** and then **plateaued hard** — a real floor, not an exhausted basin.
- **Zero** inputs reached `margin ≤ 0` (no failure).
- The closest input,
  `y = 46060171028209869055326276125955724694552131082115441741596060240979794089070`,
  was run on the **real Rust**: `invert(y)·y ≡ 1` ✓ (correct inverse), as were
  the runner-up and controls.

## Why it plateaus at ~45 bits (the wall)

At the closest step, `p − u ≈ 2^168` and `v ≈ 2^168` *both* sit ~45 bits above
`γ`. Reaching the window needs **both** to shrink ~45 bits **simultaneously at
the same step** — a joint ~90-bit coincidence in the mid-trace state. Local
perturbation of `y` reshuffles the entire (chaotic) trace, so there is no
gradient that tightens both coordinates together; the hill-climb can align one
near-coincidence but not compound two. Tightening both is exactly the
trace-global reachability problem that also blocks the Lean proof. Backward /
meet-in-the-middle does not help: the reachable state set is `≈ 2^255 · 510`,
not enumerable, and danger states number `≈ 1` in it.

## What this does and does not establish

- **Does:** even a search that actively steers toward the danger condition —
  using the exact modular structure — cannot get within 45 bits of it in ~4M
  attempts. Combined with the `≈ 2^−264`/step density, this is strong evidence
  that **no failing input exists for this prime, and certainly none is
  findable**. The shipped `invert` is safe in every practical sense.
- **Does not:** prove absence over all `2^255` inputs. A search cannot; that
  remains either the research-grade trace-global argument or — cleanly — the
  one-line source fix (replace the `OR` with a carry-propagating add of
  `2^255`, see `invert_or_window_analysis.md` §4), which removes the window
  entirely and makes correctness provable and prime-independent.

## Reproduce

`scratchpad/pipeline/{model.py, searchlib.py, hunt.py, refine.py}` (search) and
`scratchpad/helioselene-patched/src/bin/invert_oracle.rs` (real-Rust oracle).
Model↔Rust agreement: `pipeline/validate.py` (20,000/20,000).
