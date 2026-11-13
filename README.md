# Constant-Stretch High-Dimensional Spanners Require Super-Linear Size

**Authors:** Rajesh Jayaram, Vahab Mirrokni, Erik Waingarten, David P. Woodruff, and Goran Žužić

Manuscript and complete Lean 4 (`v4.27.0` / Mathlib `v4.27.0`) formal verification proving that for every $p \in [1, \infty)$ and constant stretch $C \ge 1$, high-dimensional $\ell_p$ point sets require $\Omega\bigl(n^{1 + c(C, p)}\bigr)$ edges ($c(C, p) = 2^{-O(C^{3p}\log(C^p + 1))}$) in every undirected non-metric Steiner $C$-spanner.

- **Paper (PDF):** [`papers/main_v1.pdf`](papers/main_v1.pdf) (LaTeX source: [`papers/main_v1.tex`](papers/main_v1.tex), [`papers/references.bib`](papers/references.bib))
- **Specification (`705` lines):** [`Challenge.lean`](Challenge.lean) — 27 definitions and 15 target theorem/lemma statements
- **Proofs (`14,769` lines, `0 sorry`):** [`Solution.lean`](Solution.lean) and [`Solution/`](Solution/) — standard axioms `[propext, Classical.choice, Quot.sound]` only
- **Kernel Comparator Spec:** [`config.json`](config.json) ([`leanprover/comparator`](https://github.com/leanprover/comparator))

## Paper ↔ Lean 4 Correspondence

| Section | Paper Statements | Lean 4 Declarations & Modules |
| :--- | :--- | :--- |
| **§1** | Definition 1.1, Theorems 1.2 & 1.3, Corollary 1.4 | `lpDist_eq_toLp_dist`, `thm_1_2_geometric_spanner_lower_bound`, `thm_1_3_non_metric_steiner_spanner_lower_bound`, `cor_1_4_lp_dvoretzky_lower_bound` ([`Solution/Glue.lean`](Solution/Glue.lean), [`Solution/Dvoretzky.lean`](Solution/Dvoretzky.lean)) |
| **§2 & §4** | Theorems 2.1(a)–(b), 2.2(a)–(b), 2.3 | `thm_2_1a_metric_nearest_terminal_projection`, `thm_2_1b_hypercube_lp_reduction`, `thm_2_2a_last_hit_edge_charging`, `thm_2_2b_biclique_bottleneck`, `thm_2_3_locally_list_bounded_csp_codes` ([`Solution/Projection.lean`](Solution/Projection.lean), [`Solution/Combinatorics.lean`](Solution/Combinatorics.lean), [`Solution/CSP.lean`](Solution/CSP.lean)) |
| **§3** | Propositions 3.1, 3.2, 3.4; Lemma 3.3 | `prop_3_1_diameter_bounded_bucketing`, `prop_3_2_simplex_separation`, `lem_3_3_blockwise_hamming_hubs`, `prop_3_4_three_hop_hypercube_collapse` ([`Solution/Bucketing.lean`](Solution/Bucketing.lean), [`Solution/Hamming.lean`](Solution/Hamming.lean)) |
| **§5 & §6** | Lemma 5.1, Definition 6.1, Lemmas 6.3–6.5 | `lem_5_1_interval_crossing`, `bicliqueWitnessList`, `lem_6_3_biclique_list_hit` ([`Solution/Glue.lean`](Solution/Glue.lean), [`Solution/CSP.lean`](Solution/CSP.lean)) |

`Solution` does not import `Challenge`.

## Build & Verify

```bash
lake exe cache get
lake build Challenge Solution
lake env comparator config.json
```
