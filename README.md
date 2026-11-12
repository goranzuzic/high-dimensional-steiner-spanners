# Constant-Stretch High-Dimensional Spanners Require Super-Linear Size

Lean 4 (`v4.27.0` / Mathlib `v4.27.0`) formal verification accompanying *Constant-Stretch High-Dimensional Spanners Require Super-Linear Size*.

## Layout

- `Challenge.lean` — problem definitions (27) and target theorem/lemma statements (15, `sorry` stubs).
- `Solution.lean`, `Solution/*.lean` — complete `sorry`-free proofs (standard axioms `[propext, Classical.choice, Quot.sound]` only).
- `config.json` — [`comparator`](https://github.com/leanprover/comparator) specification checking `Solution` against `Challenge`.
- `papers/` — accompanying manuscript (`main_v1.pdf`, `main_v1.tex`, `references.bib`).

## Build

```bash
lake exe cache get
lake build Challenge Solution
```
