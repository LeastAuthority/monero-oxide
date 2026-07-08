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

Note: some Lean file headers cite the original `/tmp/...` scratchpad paths of
these scripts; those paths are ephemeral — these copies are the durable ones.
