# Reproducibility artifacts

Generator scripts and certificate data referenced by the Spec tree (copied out
of the ephemeral session scratchpad on 2026-07-08):

- `prime-certificate.md`, `pratt_verified.json` — the Pratt primality
  certificate for p (p−1 = 2·7451·p36·p37; factorization obtained via msieve
  SIQS, double-verified). Input to `gen_prime.py`.
- `gen_prime.py` — generates `HelioseleneCore/Spec/Prime.lean` (re-verifies the
  certificate with Python `pow()` before emitting).
- `gen_curve.py` — generates the no-2-torsion polynomial certificate data in
  `HelioseleneCore/Spec/Selene/Curve.lean` (X^p mod cubic + Bézout identity;
  cross-checked against an independent polynomial modexp).
- `test_vectors.json` (964 field vectors), `selene_vectors.json` (100 curve
  vectors) — independent ground truth, generated with Python big-int
  arithmetic; consumed by `gen_validation.py` / `gen_validation_selene.py`
  which emit `HelioseleneCore/Validation.lean` / `ValidationSelene.lean`.
- `gen_lean.py`, `lean_certs.txt` — the linear_combination certificate
  generator for the RCB↔mathlib group-law correspondence in
  `HelioseleneCore/Spec/Selene/GroupLaw.lean`.

Helios-stage artifacts (third run, 2026-07-08; copied out of the session
scratchpad on 2026-07-09):

- `prime25519-certificate.md`, `pratt_25519.json` — the 7-node Pratt primality
  certificate for q = 2^255 − 19 (the Helios coordinate field / 25519 base
  field). The factorization of q−1 is well known from the Curve25519
  literature/factordb and was fully re-verified locally; one 27-digit interior
  cofactor was split with msieve. Input to `gen_prime25519.py`.
- `gen_prime25519.py` — generates `HelioseleneCore/Spec/Helios/Prime25519.lean`
  (`q_prime`, kernel-only Pratt certificate; re-verifies the certificate with
  Python `pow()` before emitting).
- `gen_curve_helios.py` — generates the Helios curve-constant and
  number-theory certificate data in `HelioseleneCore/Spec/Helios/Curve.lean`
  (B-nonresidue, no-2-torsion `X^q mod (X³−3X+B)` + Bézout identity, Δ ≠ 0;
  same technique as `gen_curve.py`, instantiated at (q, B_helios)).
- `gen_lean_helios.py`, `lean_certs_helios.txt` — the linear_combination
  certificate generator for the RCB↔mathlib correspondence in
  `HelioseleneCore/Spec/Helios/GroupLaw.lean`. The integer cofactors are
  identical to `lean_certs.txt` (the extraction runs over ℤ with B symbolic);
  the printed files differ only in the `Fq`-vs-`F` spelling of the type
  ascriptions, so a literal `diff` shows 10 differing lines.
- `helios_vectors.json` (75 curve vectors: 35 add, 15 double, 5 neg, 12 ct_eq,
  8 from_xy) — independent ground truth for the Helios group law, generated
  with Python big-int arithmetic; consumed by `gen_validation_helios.py`,
  which emits `HelioseleneCore/ValidationHelios.lean`. NOTE the weaker-signal
  caveat in that file's header: the Helios coordinate field is idealized
  (`ZMod (2^255−19)` by definition), so these vectors validate the translated
  group-law formulas and model plumbing, not any field-arithmetic
  implementation.

Note: some Lean file headers cite the original `/tmp/...` scratchpad paths of
these scripts; those paths are ephemeral — these copies are the durable ones.
