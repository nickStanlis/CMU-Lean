# CMU-Lean

Lean 4 / Mathlib formalizations from my CMU coursework.

| File | Contents |
|---|---|
| [`CMULean/IntegerVersions.lean`](CMULean/IntegerVersions.lean) | Well-ordering for ℕ (`wellOr`) and for bounded-below subsets of ℤ (`wellOrInt`, `wellOrUnique_int`); the division algorithm over ℤ (`divalgoint`). |
| [`CMULean/Partitions.lean`](CMULean/Partitions.lean) | Conjugate partitions: conjugation is an involution swapping number of parts and largest part, so #partitions of `n` into `k` parts = #partitions of `n` with largest part `k` (`PartitionProof.Partition.card_eq`). |
| [`CMULean/FTC.lean`](CMULean/FTC.lean) | Fundamental Theorem of Calculus, part (i), for strictly monotone functions, built from a hand-rolled Riemann integral (`FTC.ftc_strictMono`, `FTC.ftc_strictAnti`). **Two lemmas remain `sorry`:** `lowerSum_le_upperSum` (A5) and `hasDerivWithinAt_of_eps`. |

## Building

Requires [elan](https://github.com/leanprover/elan).

```bash
lake exe cache get   # download prebuilt Mathlib
lake build
```

## Adding a new project

1. Put the new file in `CMULean/`, starting with `import Mathlib`.
2. Add `import CMULean.<FileName>` to `CMULean.lean`.
3. `lake build`, then commit and push.
