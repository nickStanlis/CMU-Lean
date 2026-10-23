# IntegerVersions

Lean 4 / Mathlib formalizations of:

| Theorem | Statement |
|---|---|
| `wellOr` | Every nonempty set of natural numbers has a least element. |
| `wellOrInt` | Every nonempty set of integers that is bounded below has a least element. |
| `divalgoint` | For `d > 0`, there exist `q r : ℤ` with `a = d*q + r` and `0 ≤ r < d`. |
| `wellOrUnique_int` | The least element in `wellOrInt` is unique. |

All proofs are in [`IntegerVersions/Basic.lean`](IntegerVersions/Basic.lean).

## Building

Requires [elan](https://github.com/leanprover/elan).

```bash
lake exe cache get   # download prebuilt Mathlib (saves hours)
lake build
```
