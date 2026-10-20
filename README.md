# Supplemental Material

This supplemental material contains the Lean formalization for Appendix B.

## Theorem correspondence

| Result | Lean declarations |
| --- | --- |
| Lemma 1 | `lemma1` |
| Lemma 2 | `lemma2` |
| Lemma 3 | `lemma3` |
| Theorem 1(1) | `theorem1_part1` |
| Theorem 1(2) | `theorem1_part2`, `theorem1_part2_capped` |
| Theorem 1(3) | `theorem1_part3` |
| Corollary 1.1 | `corollary11` |
| Theorem 2 | `theorem2`, `theorem2_capped` |
| Corollary 2.1 | `corollary21`, `corollary21_capped` |
| Corollary 2.2 | `corollary22`, `corollary22_capped` |
| Corollary 2.3 | `corollary23`, `corollary23_capped` |
| Lemma 4 | `lemma4` |
| Theorem 3 | `theorem3`, `theorem3_capped` |
| Theorem 4 | `theorem4`, `theorem4_capped` |

## Prerequisite

Install Lean 4 and Lake. Lake is included with Lean when Lean is installed through `elan`.

## Verification

Run:

```sh
lake build
lake env lean MCTS.lean
```
