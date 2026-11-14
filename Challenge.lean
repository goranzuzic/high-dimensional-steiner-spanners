import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 200000

open scoped ENNReal Classical

/-!
# Constant-Stretch High-Dimensional Spanners Require Polynomial Overhead

Self-contained Lean 4 (`v4.27.0` / Mathlib `v4.27.0`) challenge file formalizing all main theorems,
corollaries, three-step interfaces, Section 3 constructions, and core combinatorial/CSP lemmas
of *Constant-Stretch High-Dimensional Spanners Require Polynomial Overhead* (`papers/main_v1.tex`):

* **Section 1 (Definitions & Main Results)**:
  - `lpDist_eq_toLp_dist`: compatibility of `lpDist` with Mathlib's `PiLp` (`WithLp`) metric.
  - `thm_1_2_geometric_spanner_lower_bound` (**Theorem 1.2**): `n^(1 + c)` edge lower bound with
    singly-exponential `c(C, p) = 2^(-O(C^(3p) log(C^p + 1))) = 2^(-O(C^(4p)))` for geometric
    `C`-spanners on Boolean hypercube point sets `P_n ⊂ {0, 1}^d`, `d = Θ_{C, p}(log n)`,
    `Δ_p(P_n) = O_{C, p}(1)`.
  - `thm_1_3_non_metric_steiner_spanner_lower_bound` (**Theorem 1.3**, Main Theorem): `n^(1 + c(C₁))`
    edge lower bound (`C₁ = max(3, ⌈C^p⌉)`, `c(C₁) = 2^(-O(C₁^3 log C₁)) = 2^(-O(C^(3p) log(C^p + 1)))`
    `= 2^(-O(C^(4p)))`) against unrestricted-hop undirected non-metric Steiner `C`-spanners across
    all `p ∈ [1, ∞)` and `C ≥ 1`.
  - `cor_1_4_lp_dvoretzky_lower_bound` (**Corollary 1.4**): `p`-independent exponent
    `c(C) = 2^(-O(C^6 log(C + 1)))` for `p > 2` in dimension `d(n) = Θ_{C, p}((log n)^(p/2))`
    with `Δ_p(P_n) = O_C(1)`.
* **Section 2 (The Three Steps of the Proof)**:
  - `thm_2_1a_metric_nearest_terminal_projection` (**Theorem 2.1(a)**): nearest-terminal projection
    removing Steiner vertices and weights on arbitrary finite metric spaces `(P, d_P)`.
  - `thm_2_1b_hypercube_lp_reduction` (**Theorem 2.1(b)**): unscaled one-hot embedding
    `ι : [q]^N → {0, 1}^(N q)` and `(C₁, rStar)`-local connector reduction across all `ℓ_p`.
  - `thm_2_2a_last_hit_edge_charging` (**Theorem 2.2(a)**): charging argument
    (`|E_{rStar}(X)| ≤ 2 K^2 |Ê|` from `(List-Size)`, `(Overlap)`, and `(List-Hit)`).
  - `thm_2_2b_biclique_bottleneck` (**Theorem 2.2(b)**): set-sequence lemma peeling `F_{s-1} ∩ F_s`
    into `k ≤ 8 C₁` disjoint pieces `A₁, ..., A_k` and remainder `|I_k| ≤ rStar / 2`.
  - `thm_2_3_locally_list_bounded_csp_codes` (**Theorem 2.3**): existence of hard `2`-CSP codes
    with `L = O(C₁^3 log C₁)`, `K = 20 C₁^2`, and `c(C₁) = 2^(-(2L + 5))`.
* **Section 3 (Warm-Ups & Three-Hop Hypercube Collapse)**:
  - `prop_3_1_diameter_bounded_bucketing` (**Proposition 3.1**): diameter-bounded bucketings as
    `2`-hop non-metric Steiner spanners.
  - `prop_3_2_simplex_separation` (**Proposition 3.2**): equidistant points (`C < 2` geometric
    `C(n, 2)` edges vs `2`-hop Steiner `1`-spanner with `n` edges) and `(N / r₀)^(1/p)` bound.
  - `lem_3_3_blockwise_hamming_hubs` (**Lemma 3.3**): single-scale blockwise Hamming-code hubs
    (`3` hops, stretch `387`, at most `2|P|` edges).
  - `prop_3_4_three_hop_hypercube_collapse` (**Proposition 3.4**): `3`-hop collapse on dense
    subsets `|P| ≥ 2^((1 - ε(ρ)) d)` (`5760`-stretch, `2|P| log₂(2/ρ)` edges) and `{0, 1}^d`.
* **Sections 5–6 (Combinatorial & Hybrid-Constraint List Core)**:
  - `lem_5_1_interval_crossing` (**Lemma 5.1**): Interval Crossing Lemma.
  - `lem_6_3_biclique_list_hit` (**Lemma 6.3**): verification of Condition `(List-Hit)` (`η₀ = 1/80`)
    for the lists `L_R(a, b)` (**Definition 6.1**).
-/

namespace HighDimSteinerSpanners

/-!
================================================================================
1. Core Spanner and Metric Definitions (Definition 1.1)
================================================================================
-/

/-- The `ℓ_p` distance `‖x - y‖_p = (∑_{i=1}^d |x_i - y_i|^p)^(1 / p)` on `ℝ^d` (`Fin d → ℝ`). -/
noncomputable def lpDist (p : ℝ) {d : ℕ} (x y : Fin d → ℝ) : ℝ :=
  (∑ i : Fin d, |x i - y i| ^ p) ^ (1 / p)

/-- Maximum pairwise `ℓ_p` distance `max_{i, j} ‖P_i - P_j‖_p` of `P : Fin n → (Fin d → ℝ)`. -/
noncomputable def maxPairwiseDist (p : ℝ) {n d : ℕ} (P : Fin n → (Fin d → ℝ)) : ℝ :=
  if hn : 0 < n then
    haveI : Nonempty (Fin n × Fin n) := ⟨(⟨0, hn⟩, ⟨0, hn⟩)⟩
    Finset.univ.sup' Finset.univ_nonempty (fun ij : Fin n × Fin n => lpDist p (P ij.1) (P ij.2))
  else 0

/-- Minimum distinct-pair `ℓ_p` distance `min_{i ≠ j} ‖P_i - P_j‖_p` of `P : Fin n → (Fin d → ℝ)`. -/
noncomputable def minDistinctPairwiseDist (p : ℝ) {n d : ℕ} (P : Fin n → (Fin d → ℝ)) : ℝ :=
  let offDiag := Finset.univ.filter (fun ij : Fin n × Fin n => ij.1 ≠ ij.2)
  if hne : offDiag.Nonempty then
    offDiag.inf' hne (fun ij => lpDist p (P ij.1) (P ij.2))
  else 0

/-- Aspect ratio `Δ_p(P) = max_{i, j} ‖P_i - P_j‖_p / min_{i ≠ j} ‖P_i - P_j‖_p`. -/
noncomputable def aspectRatio (p : ℝ) {n d : ℕ} (P : Fin n → (Fin d → ℝ)) : ℝ :=
  maxPairwiseDist p P / minDistinctPairwiseDist p P

/-- Total edge weight `∑_{i=1}^k w({v_{i-1}, v_i})` of a finite walk in `H : SimpleGraph V`. -/
def walkWeight {V : Type} {H : SimpleGraph V} (w : Sym2 V → ℝ) :
    ∀ {u v : V}, H.Walk u v → ℝ
  | _, _, .nil => 0
  | u, _, @SimpleGraph.Walk.cons _ _ _ b _ _ q => w s(u, b) + walkWeight w q

/-- Unrestricted-hop shortest-path distance `d_H(u, v) ∈ ℝ≥0∞` (`⊤` when disconnected). -/
noncomputable def graphDist {V : Type} (H : SimpleGraph V) (w : Sym2 V → ℝ) (u v : V) : ℝ≥0∞ :=
  ⨅ p : H.Walk u v, ENNReal.ofReal (walkWeight w p)

/-- Definition 1.1 for `(P, ‖·‖_p)` in `ℝ^d`: `H = (Fin n ⊕ S, E, w)` is an undirected non-metric
Steiner `C`-spanner of `(P, ‖·‖_p)` with unrestricted hop count. -/
structure IsNonMetricSteinerSpanner (p : ℝ) {n d : ℕ} (P : Fin n → (Fin d → ℝ)) (C : ℝ)
    {S : Type} [Fintype S] (H : SimpleGraph (Fin n ⊕ S)) (w : Sym2 (Fin n ⊕ S) → ℝ) : Prop where
  weight_nonneg : ∀ e ∈ H.edgeSet, 0 ≤ w e
  noncontracting : ∀ i j : Fin n,
    ENNReal.ofReal (lpDist p (P i) (P j)) ≤ graphDist H w (.inl i) (.inl j)
  stretch : ∀ i j : Fin n,
    graphDist H w (.inl i) (.inl j) ≤ ENNReal.ofReal (C * lpDist p (P i) (P j))

/-- Definition 1.1 (`S = ∅` geometric case): `G` is a geometric `C`-spanner of `(P, ‖·‖_p)`. -/
def IsGeometricSpanner (p : ℝ) {n d : ℕ} (P : Fin n → (Fin d → ℝ)) (C : ℝ)
    (G : SimpleGraph (Fin n)) : Prop :=
  ∀ i j : Fin n,
    graphDist G
      (Sym2.lift ⟨fun u v => lpDist p (P u) (P v), fun u v => by
        simp only [lpDist, abs_sub_comm]⟩)
      i j ≤ ENNReal.ofReal (C * lpDist p (P i) (P j))

/-- Definition 1.1 for an arbitrary finite metric space `(P, dist)`: `H = (P ⊕ S, E, w)` is an
undirected non-metric Steiner `C`-spanner of `(P, dist)`. -/
structure IsGeneralNonMetricSteinerSpanner {P : Type} [MetricSpace P] [Fintype P]
    (C : ℝ) {S : Type} [Fintype S] (H : SimpleGraph (P ⊕ S)) (w : Sym2 (P ⊕ S) → ℝ) : Prop where
  weight_nonneg : ∀ e ∈ H.edgeSet, 0 ≤ w e
  noncontracting : ∀ x y : P,
    ENNReal.ofReal (dist x y) ≤ graphDist H w (.inl x) (.inl y)
  stretch : ∀ x y : P,
    graphDist H w (.inl x) (.inl y) ≤ ENNReal.ofReal (C * dist x y)

/-!
================================================================================
2. Module 1–3 & Section 3–6 Definitions
================================================================================
-/

/-- Unscaled one-hot map `ι : [q]^N → {0, 1}^{N q} ⊂ ℝ^{N q}` (`ι(x)_{v, c} = 1[x_v = c]`)
from Theorem 2.1(b). -/
def oneHotEmbed {N q : ℕ} (x : Fin N → Fin q) : Fin (N * q) → ℝ :=
  fun k =>
    let vc := finProdFinEquiv.symm k
    if x vc.1 = vc.2 then 1 else 0

/-- Disagreement coordinate set `Δ(x, y) = {v ∈ [N] : x_v ≠ y_v}`. -/
def disagreeSet {N q : ℕ} (x y : Fin N → Fin q) : Finset (Fin N) :=
  Finset.univ.filter (fun v => x v ≠ y v)

/-- Ordered pairs `E_{rStar}(X) = {(x, y) ∈ X × X : d_Ham(x, y) = rStar}` at exact Hamming distance `rStar`. -/
def exactDistPairs {N q : ℕ} (X : Finset (Fin N → Fin q)) (rStar : ℕ) :
    Finset ((Fin N → Fin q) × (Fin N → Fin q)) :=
  (X ×ˢ X).filter (fun xy => hammingDist xy.1 xy.2 = rStar)

/-- Condition **(List-Size)** of Theorem 2.2(a): `|L(a, b)| < K` for `0 < d_Ham(a, b) ≤ C₁ rStar`. -/
def ListSizeCond {N q : ℕ} (C₁ rStar K : ℕ) (X : Finset (Fin N → Fin q))
    (L : ↥X → ↥X → Finset ↥X) : Prop :=
  ∀ a b : ↥X,
    0 < hammingDist a.val b.val →
    hammingDist a.val b.val ≤ C₁ * rStar →
    (L a b).card < K

/-- Condition **(Overlap)** of Theorem 2.2(a): for every `(x, w₀) ∈ X²` with `0 < d_Ham(x, w₀) ≤ C₁ rStar`,
fewer than `K` points `y ∈ X \ {x, w₀}` satisfy `d_Ham(x, y) = rStar` and `|Δ(x, w₀) ∩ Δ(x, y)| > rStar / 4`. -/
noncomputable def OverlapCond {N q : ℕ} (C₁ rStar K : ℕ) (X : Finset (Fin N → Fin q)) : Prop :=
  ∀ x w₀ : ↥X,
    0 < hammingDist x.val w₀.val →
    hammingDist x.val w₀.val ≤ C₁ * rStar →
    (Finset.univ.filter (fun y : ↥X =>
      y ≠ x ∧ y ≠ w₀ ∧
      hammingDist x.val y.val = rStar ∧
      (rStar : ℝ) / 4 < ((disagreeSet x.val w₀.val ∩ disagreeSet x.val y.val).card : ℝ))).card < K

/-- Condition **(List-Hit)** of Theorem 2.2(a): along any sequence `w₀, ..., w_ℓ ∈ B_X(x, C₁ rStar) \ {x}`
(`ℓ ≥ 1`) with step lengths in `(0, C₁ rStar]`, `d_Ham(x, w_ℓ) = rStar`, and `|Δ(x, w₀) ∩ Δ(x, w_ℓ)| ≤ rStar / 4`,
some step `s` satisfies `x ∈ L(w_{s-1}, w_s)`. -/
def ListHitCond {N q : ℕ} (C₁ rStar : ℕ) (X : Finset (Fin N → Fin q))
    (L : ↥X → ↥X → Finset ↥X) : Prop :=
  ∀ (x : ↥X) (ℓ : ℕ), 1 ≤ ℓ →
    ∀ (w : Fin (ℓ + 1) → ↥X),
      (∀ t : Fin (ℓ + 1), w t ≠ x ∧ hammingDist x.val (w t).val ≤ C₁ * rStar) →
      (∀ s : Fin ℓ,
        0 < hammingDist (w s.castSucc).val (w s.succ).val ∧
        hammingDist (w s.castSucc).val (w s.succ).val ≤ C₁ * rStar) →
      hammingDist x.val (w (Fin.last ℓ)).val = rStar →
      ((disagreeSet x.val (w 0).val ∩ disagreeSet x.val (w (Fin.last ℓ)).val).card : ℝ) ≤
        (rStar : ℝ) / 4 →
      ∃ s : Fin ℓ, x ∈ L (w s.castSucc) (w s.succ)

/-- Diameter `D_i = max_{u, v ∈ B} dist(u, v)` of a finite subset `B ⊆ P` (Proposition 3.1). -/
noncomputable def bucketDiam {P : Type} [MetricSpace P] (B : Finset P) : ℝ :=
  if hne : B.Nonempty then
    B.sup' hne (fun u => B.sup' hne (fun v => dist u v))
  else 0

/-- Bipartite bucket-hub graph `H = (P ⊔ I, E)` with `E = {{x, i} : x ∈ B_i}` (Proposition 3.1). -/
def bucketingGraph {P I : Type} (B : I → Finset P) : SimpleGraph (P ⊕ I) where
  Adj u v :=
    match u, v with
    | .inl x, .inr i => x ∈ B i
    | .inr i, .inl x => x ∈ B i
    | _, _ => False
  symm u v h := by
    cases u <;> cases v <;> exact h
  loopless u h := by
    cases u <;> exact h

/-- Edge weights `w({x, i}) = D_i / 2` on `bucketingGraph B` (Proposition 3.1). -/
noncomputable def bucketingWeight {P I : Type} [MetricSpace P] (B : I → Finset P) :
    Sym2 (P ⊕ I) → ℝ :=
  Sym2.lift ⟨fun u v =>
    match u, v with
    | .inl _, .inr i => bucketDiam (B i) / 2
    | .inr i, .inl _ => bucketDiam (B i) / 2
    | _, _ => 0,
    fun u v => by cases u <;> cases v <;> rfl⟩

/-- Standard basis `P = {e_1, ..., e_n} ⊂ {0, 1}^n` (Proposition 3.2(a)). -/
def stdBasis (n : ℕ) : Fin n → (Fin n → ℝ) :=
  fun i j => if i = j then 1 else 0

/-- Inclusion of `{0, 1}^d` (`Fin d → Bool`) into `ℝ^d` (`false ↦ 0`, `true ↦ 1`). -/
def boolVecToReal {d : ℕ} (x : Fin d → Bool) : Fin d → ℝ :=
  fun i => if x i then 1 else 0

/-- Ambient `ℓ_p` distance `‖x - y‖_p` on `{0, 1}^d` (`Fin d → Bool`). -/
noncomputable def cubeLpDist (p : ℝ) {d : ℕ} (x y : Fin d → Bool) : ℝ :=
  lpDist p (boolVecToReal x) (boolVecToReal y)

/-- Ambient `ℓ_p` edge weight `w({u, v}) = ‖u - v‖_p` on any vertex subset `V ⊆ {0, 1}^d`. -/
noncomputable def cubeSubgraphWeight (p : ℝ) {d : ℕ} (V : Finset (Fin d → Bool)) :
    Sym2 ↥V → ℝ :=
  Sym2.lift ⟨fun u v => cubeLpDist p u.val v.val, fun u v => by
    simp only [cubeLpDist, lpDist, abs_sub_comm]⟩

/-- Symmetric binary `2`-CSP constraint family `R` on `K_N` over alphabet `[q]` (Section 6.1). -/
def Symmetric2CSP {N q : ℕ} (R : Fin N → Fin N → Fin q → Fin q → Prop) : Prop :=
  ∀ u v : Fin N, ∀ c₁ c₂ : Fin q, R u v c₁ c₂ ↔ R v u c₂ c₁

/-- Satisfying assignments `Ω(R) = {x ∈ [q]^N : ∀ u < v, (x_u, x_v) ∈ R_{u, v}}` (Section 6.1). -/
noncomputable def satisfyingSet {N q : ℕ} (R : Fin N → Fin N → Fin q → Fin q → Prop) :
    Finset (Fin N → Fin q) :=
  Finset.univ.filter (fun x => ∀ u v : Fin N, u < v → R u v (x u) (x v))

/-- Three-way disagreement set `D_3(x, y, z) = {v ∈ [N] : |{x_v, y_v, z_v}| = 3}` (Section 6.1). -/
def threeWayDisagree {N q : ℕ} (x y z : Fin N → Fin q) : Finset (Fin N) :=
  Finset.univ.filter (fun v => x v ≠ y v ∧ x v ≠ z v ∧ y v ≠ z v)

/-- Active alternative color `c_v(x, a, b) = a_v` if `a_v ≠ x_v`, else `b_v` (Section 6.1). -/
def activeColor {N q : ℕ} (x a b : Fin N → Fin q) (v : Fin N) : Fin q :=
  if a v ≠ x v then a v else b v

/-- **Definition 6.1 (The Lists `L_R(a, b)`)**:
Set of `x ∈ Ω(R) \ {a, b}` within Hamming distance `C₁ rStar` of `a` and `b` admitting `0 ≤ k ≤ 8 C₁`,
a partition `Δ(x, a) ∩ Δ(x, b) = A₁ ⊔ ... ⊔ A_k ⊔ I_k` with `|I_k| ≤ rStar / 2`, and (setting
`I_rem(r) = (⊔_{j > r} A_j) ⊔ I_k`) sets `B_fut(r) ⊆ I_rem(r)` and
`B_out(r) ⊆ W(x, a, b) \ (A_r ⊔ I_rem(r))` satisfying:
(1) `(x_u, c_v(x, a, b)) ∈ R_{u, v}` for all `u ∈ A_r` and `v ∈ B_fut(r) ∪ B_out(r)`; and
(2) `|I_rem(r) \ B_fut(r)| ≤ rStar / 80` and `|B_out(r)| ≥ |A_r| - (11 / 40) rStar`. -/
noncomputable def bicliqueWitnessList {N q : ℕ}
    (R : Fin N → Fin N → Fin q → Fin q → Prop) (C₁ rStar : ℕ)
    (a b : Fin N → Fin q) : Finset (Fin N → Fin q) :=
  let W := fun x => disagreeSet x a ∪ disagreeSet x b
  let I := fun x => disagreeSet x a ∩ disagreeSet x b
  (satisfyingSet R).filter (fun x =>
    x ≠ a ∧ x ≠ b ∧
    hammingDist x a ≤ C₁ * rStar ∧
    hammingDist x b ≤ C₁ * rStar ∧
    ∃ k : ℕ, k ≤ 8 * C₁ ∧
      ∃ (A B_fut B_out : Fin k → Finset (Fin N)) (I_k : Finset (Fin N)),
        Pairwise (fun i j => Disjoint (A i) (A j)) ∧
        (∀ r : Fin k, Disjoint (A r) I_k) ∧
        Finset.univ.biUnion A ∪ I_k = I x ∧
        (I_k.card : ℝ) ≤ (rStar : ℝ) / 2 ∧
        ∀ r : Fin k,
          let I_rem := (Finset.univ.filter (fun j : Fin k => r < j)).biUnion A ∪ I_k
          B_fut r ⊆ I_rem ∧
          B_out r ⊆ W x \ (A r ∪ I_rem) ∧
          (∀ u ∈ A r, ∀ v ∈ B_fut r ∪ B_out r, R u v (x u) (activeColor x a b v)) ∧
          (((I_rem \ B_fut r).card : ℝ) ≤ (rStar : ℝ) / 80 ∧
           ((A r).card : ℝ) - (11 : ℝ) / 40 * (rStar : ℝ) ≤ ((B_out r).card : ℝ)))

end HighDimSteinerSpanners

open HighDimSteinerSpanners

/-!
================================================================================
3. Challenge Theorems, Corollaries, Propositions, and Lemmas
================================================================================
-/

/-- **Metric Compatibility (`lpDist` = Mathlib `PiLp` `dist`)**:
For every real `p ≥ 1`, `lpDist p` agrees identically with Mathlib's `WithLp` (`PiLp`) distance. -/
theorem lpDist_eq_toLp_dist :
    ∀ (p : ℝ), 1 ≤ p →
      ∀ {d : ℕ} (x y : Fin d → ℝ),
        lpDist p x y =
          dist (WithLp.toLp (ENNReal.ofReal p) x) (WithLp.toLp (ENNReal.ofReal p) y) := by
  sorry

/-- **Theorem 1.2 (Lower Bound for Geometric Spanners)**:
There exists an absolute constant `M > 0` such that for every real `p ≥ 1` and every constant `C ≥ 1`,
there exist constants `c ≥ 2^(-M C^(3p) log₂(C^p + 1)) ≥ 2^(-M C^(4p)) > 0`, `c₀ > 0`, `0 < β₁ ≤ β₂`,
and `A > 0` and a strictly increasing sequence `nSeq : ℕ → ℕ` (`nSeq j ≥ 2`) such that for every `j`,
there is an `nSeq j`-point subset `P ⊂ {0, 1}^d` in dimension `β₁ log₂ n ≤ d ≤ β₂ log₂ n` with
`Δ_p(P) ≤ A` on which every geometric `C`-spanner of `(P, ‖·‖_p)` has at least `c₀ · n^(1 + c)` edges. -/
theorem thm_1_2_geometric_spanner_lower_bound :
    ∃ M : ℝ, 0 < M ∧
      ∀ (p : ℝ), 1 ≤ p →
        ∀ (C : ℝ), 1 ≤ C →
          ∃ (c c₀ A β₁ β₂ : ℝ),
            (2 : ℝ) ^ (-M * C ^ (4 * p)) ≤ (2 : ℝ) ^ (-M * C ^ (3 * p) * Real.logb 2 (C ^ p + 1)) ∧
            (2 : ℝ) ^ (-M * C ^ (3 * p) * Real.logb 2 (C ^ p + 1)) ≤ c ∧
            0 < c₀ ∧ 0 < A ∧ 0 < β₁ ∧ β₁ ≤ β₂ ∧
            ∃ nSeq : ℕ → ℕ, StrictMono nSeq ∧ (∀ j : ℕ, 2 ≤ nSeq j) ∧
              ∀ j : ℕ,
                ∃ (d : ℕ) (P : Fin (nSeq j) → (Fin d → ℝ)),
                  1 ≤ d ∧
                  β₁ * Real.logb 2 (nSeq j : ℝ) ≤ (d : ℝ) ∧
                  (d : ℝ) ≤ β₂ * Real.logb 2 (nSeq j : ℝ) ∧
                  (∀ i : Fin (nSeq j), ∀ k : Fin d, P i k = 0 ∨ P i k = 1) ∧
                  Function.Injective P ∧
                  aspectRatio p P ≤ A ∧
                  ∀ (G : SimpleGraph (Fin (nSeq j))),
                    IsGeometricSpanner p P C G →
                    c₀ * (nSeq j : ℝ) ^ (1 + c) ≤ (Nat.card G.edgeSet : ℝ) := by
  sorry

/-- **Theorem 1.3 (Main Theorem: Lower Bound for Steiner Spanners)**:
There exist an absolute constant `M > 0` and functions `c, c₀, β₁, β₂, A : ℕ → ℝ` (depending only on
`C₁ = max(3, ⌈C^p⌉)`) with `c(C₁) ≥ 2^(-M C₁^3 log₂ C₁)` such that for every real `p ≥ 1` and `C ≥ 1`
(giving `c(C₁) ≥ 2^(-(81 M) C^(3p) log₂(C^p + 1)) ≥ 2^(-(81 M) C^(4p))`), there exists a strictly
increasing sequence `nSeq : ℕ → ℕ` (`nSeq j ≥ 2`) of Boolean-hypercube point sets `P_n ⊂ {0, 1}^{d(n)}`
with `β₁(C₁) log₂ n ≤ d(n) ≤ β₂(C₁) log₂ n` and `Δ_p(P_n) ≤ A(C₁)` on which every undirected
non-metric Steiner `C`-spanner `H = (P_n ⊔ S, E, w)` has at least `c₀(C₁) · n^(1 + c(C₁))` edges. -/
theorem thm_1_3_non_metric_steiner_spanner_lower_bound :
    ∃ (M : ℝ) (c c₀ β₁ β₂ A : ℕ → ℝ),
      0 < M ∧
      (∀ C₁ : ℕ, 3 ≤ C₁ →
        (2 : ℝ) ^ (-M * (C₁ : ℝ) ^ 3 * Real.logb 2 (C₁ : ℝ)) ≤ c C₁ ∧
        0 < c₀ C₁ ∧ 0 < β₁ C₁ ∧ β₁ C₁ ≤ β₂ C₁ ∧ 0 < A C₁) ∧
      ∀ (p : ℝ), 1 ≤ p →
        ∀ (C : ℝ), 1 ≤ C →
          let C₁ : ℕ := max 3 ⌈C ^ p⌉₊
          (2 : ℝ) ^ (-(81 * M) * C ^ (4 * p)) ≤
            (2 : ℝ) ^ (-(81 * M) * C ^ (3 * p) * Real.logb 2 (C ^ p + 1)) ∧
          (2 : ℝ) ^ (-(81 * M) * C ^ (3 * p) * Real.logb 2 (C ^ p + 1)) ≤ c C₁ ∧
          ∃ nSeq : ℕ → ℕ, StrictMono nSeq ∧ (∀ j : ℕ, 2 ≤ nSeq j) ∧
            ∀ j : ℕ,
              ∃ (d : ℕ) (P : Fin (nSeq j) → (Fin d → ℝ)),
                1 ≤ d ∧
                β₁ C₁ * Real.logb 2 (nSeq j : ℝ) ≤ (d : ℝ) ∧
                (d : ℝ) ≤ β₂ C₁ * Real.logb 2 (nSeq j : ℝ) ∧
                (∀ i : Fin (nSeq j), ∀ k : Fin d, P i k = 0 ∨ P i k = 1) ∧
                Function.Injective P ∧
                aspectRatio p P ≤ A C₁ ∧
                ∀ (S : Type) [Fintype S]
                  (H : SimpleGraph (Fin (nSeq j) ⊕ S))
                  (w : Sym2 (Fin (nSeq j) ⊕ S) → ℝ),
                  IsNonMetricSteinerSpanner p P C H w →
                  c₀ C₁ * (nSeq j : ℝ) ^ (1 + c C₁) ≤ (Nat.card H.edgeSet : ℝ) := by
  sorry

/-- **Corollary 1.4 (`p`-Independent Exponent for `p > 2` via Dvoretzky Embedding)**:
There exist an absolute constant `M > 0` and functions `c, c₀, A : ℝ → ℝ` (depending only on `C`)
with `c(C) ≥ 2^(-M C^6 log₂(C + 1)) > 0`, `c₀(C) > 0`, and `A(C) > 0` for all `C ≥ 1`, such that for
every real `p > 2` and `C ≥ 1`, there exist `0 < β₁ ≤ β₂` and a strictly increasing sequence
`nSeq : ℕ → ℕ` (`nSeq j ≥ 2`) of `nSeq j`-point sets `P_n ⊂ ℝ^{d(n)}` in dimension
`β₁ (log₂ n)^(p/2) ≤ d(n) ≤ β₂ (log₂ n)^(p/2)` with `Δ_p(P_n) ≤ A(C)` on which every undirected
non-metric Steiner `C`-spanner (and every geometric `C`-spanner) has at least `c₀(C) · n^(1 + c(C))`
edges. -/
theorem cor_1_4_lp_dvoretzky_lower_bound :
    ∃ (M : ℝ) (c c₀ A : ℝ → ℝ),
      0 < M ∧
      (∀ C : ℝ, 1 ≤ C →
        (2 : ℝ) ^ (-M * C ^ (6 : ℕ) * Real.logb 2 (C + 1)) ≤ c C ∧ 0 < c₀ C ∧ 0 < A C) ∧
      ∀ (p : ℝ), 2 < p →
        ∀ (C : ℝ), 1 ≤ C →
          ∃ (β₁ β₂ : ℝ), 0 < β₁ ∧ β₁ ≤ β₂ ∧
            ∃ nSeq : ℕ → ℕ, StrictMono nSeq ∧ (∀ j : ℕ, 2 ≤ nSeq j) ∧
              ∀ j : ℕ,
                ∃ (d : ℕ) (P : Fin (nSeq j) → (Fin d → ℝ)),
                  1 ≤ d ∧
                  β₁ * (Real.logb 2 (nSeq j : ℝ)) ^ (p / 2) ≤ (d : ℝ) ∧
                  (d : ℝ) ≤ β₂ * (Real.logb 2 (nSeq j : ℝ)) ^ (p / 2) ∧
                  Function.Injective P ∧
                  aspectRatio p P ≤ A C ∧
                  (∀ (S : Type) [Fintype S]
                    (H : SimpleGraph (Fin (nSeq j) ⊕ S))
                    (w : Sym2 (Fin (nSeq j) ⊕ S) → ℝ),
                    IsNonMetricSteinerSpanner p P C H w →
                    c₀ C * (nSeq j : ℝ) ^ (1 + c C) ≤ (Nat.card H.edgeSet : ℝ)) ∧
                  (∀ (G : SimpleGraph (Fin (nSeq j))),
                    IsGeometricSpanner p P C G →
                    c₀ C * (nSeq j : ℝ) ^ (1 + c C) ≤ (Nat.card G.edgeSet : ℝ)) := by
  sorry

/-- **Theorem 2.1(a) (Metric Nearest-Terminal Projection, Module 1)**:
For any finite metric space `(P, dist)` (`|P| ≥ 2`), `C ≥ 1`, `r > 0`, and undirected non-metric
Steiner `C`-spanner `H = (P ⊔ S, E, w)`, there exists an unweighted simple graph `Ĝ = (P, Ê)` with
`|Ê| ≤ |E|` whose edges satisfy `0 < dist(a, b) ≤ C r` and in which every pair `x, y ∈ P` with
`0 < dist(x, y) ≤ r` is connected by a simple path inside `B_P(x, C r)`. -/
theorem thm_2_1a_metric_nearest_terminal_projection :
    ∀ (P : Type) [MetricSpace P] [Fintype P],
      2 ≤ Fintype.card P →
      ∀ (C r : ℝ), 1 ≤ C → 0 < r →
        ∀ (S : Type) [Fintype S]
          (H : SimpleGraph (P ⊕ S)) (w : Sym2 (P ⊕ S) → ℝ),
          IsGeneralNonMetricSteinerSpanner C H w →
          ∃ G_hat : SimpleGraph P,
            Nat.card G_hat.edgeSet ≤ Nat.card H.edgeSet ∧
            (∀ a b : P, G_hat.Adj a b → 0 < dist a b ∧ dist a b ≤ C * r) ∧
            (∀ x y : P, 0 < dist x y → dist x y ≤ r →
              ∃ q : G_hat.Walk x y, q.IsPath ∧ ∀ z ∈ q.support, dist x z ≤ C * r) := by
  sorry

/-- **Theorem 2.1(b) (Boolean-Hypercube Reduction Across `ℓ_p`, Module 1)**:
For `N = 2^L rStar` (`N, q ≥ 2`, `rStar ≥ 1`), `p ≥ 1`, `C ≥ 1`, and `C₁ ≥ ⌈C^p⌉`:
(1) `‖ι(x) - ι(y)‖_p = (2 d_Ham(x, y))^(1/p)` for all `x, y ∈ [q]^N`; and
(2) for any `X ⊆ [q]^N` (`|X| ≥ 2`) with minimum Hamming distance `≥ rStar / 2`, `ι(X) ⊂ {0, 1}^{N q}`
has `|X|` distinct points, `Δ_p(ι(X)) ≤ 2^(L + 1)`, and every undirected non-metric Steiner
`C`-spanner of `(ι(X), ‖·‖_p)` projects to an unweighted simple graph `Ĝ` on `X` (`|Ê| ≤ |E|`)
with edge lengths in `(0, C₁ rStar]` and simple paths inside `B_X(x, C₁ rStar)` for all `(x, y) ∈ E_{rStar}(X)`. -/
theorem thm_2_1b_hypercube_lp_reduction :
    ∀ (N q L rStar C₁ : ℕ), 2 ≤ N → 2 ≤ q → 1 ≤ rStar → N = 2 ^ L * rStar →
      ∀ (p C : ℝ), 1 ≤ p → 1 ≤ C → ⌈C ^ p⌉₊ ≤ C₁ →
        (∀ x y : Fin N → Fin q,
          lpDist p (oneHotEmbed x) (oneHotEmbed y) = (2 * (hammingDist x y : ℝ)) ^ (1 / p)) ∧
        (∀ (X : Finset (Fin N → Fin q)),
          2 ≤ X.card →
          (∀ x ∈ X, ∀ y ∈ X, x ≠ y → (rStar : ℝ) / 2 ≤ (hammingDist x y : ℝ)) →
          ∀ (e : Fin X.card ≃ ↥X),
            let P : Fin X.card → (Fin (N * q) → ℝ) := fun i => oneHotEmbed (e i).val
            (∀ i : Fin X.card, ∀ k : Fin (N * q), P i k = 0 ∨ P i k = 1) ∧
            Function.Injective P ∧
            aspectRatio p P ≤ (2 : ℝ) ^ (L + 1) ∧
            ∀ (S : Type) [Fintype S]
              (H : SimpleGraph (Fin X.card ⊕ S))
              (w : Sym2 (Fin X.card ⊕ S) → ℝ),
              IsNonMetricSteinerSpanner p P C H w →
              ∃ G_hat : SimpleGraph ↥X,
                Nat.card G_hat.edgeSet ≤ Nat.card H.edgeSet ∧
                (∀ a b : ↥X, G_hat.Adj a b →
                  0 < hammingDist a.val b.val ∧ hammingDist a.val b.val ≤ C₁ * rStar) ∧
                (∀ x y : ↥X, hammingDist x.val y.val = rStar →
                  ∃ q_walk : G_hat.Walk x y,
                    q_walk.IsPath ∧
                    ∀ z ∈ q_walk.support, hammingDist x.val z.val ≤ C₁ * rStar)) := by
  sorry

/-- **Theorem 2.2(a) (Last-Hit Edge Charging, Module 2)**:
Under single-scale `C₁ rStar`-ball connectivity of `E_{rStar}(X)` in `Ĝ = (X, Ê)` and Conditions
**(List-Size)**, **(Overlap)**, and **(List-Hit)** with parameter `K ≥ 1`,
`|E_{rStar}(X)| ≤ 2 K^2 |Ê|`. -/
theorem thm_2_2a_last_hit_edge_charging :
    ∀ (C₁ rStar N q K : ℕ), 2 ≤ C₁ → 1 ≤ rStar → 2 ≤ N → 2 ≤ q → 1 ≤ K →
      ∀ (X : Finset (Fin N → Fin q)) (G_hat : SimpleGraph ↥X)
        (L : ↥X → ↥X → Finset ↥X),
        (∀ a b : ↥X, G_hat.Adj a b →
          0 < hammingDist a.val b.val ∧ hammingDist a.val b.val ≤ C₁ * rStar) →
        (∀ x y : ↥X, hammingDist x.val y.val = rStar →
          ∃ q_walk : G_hat.Walk x y,
            q_walk.IsPath ∧ ∀ z ∈ q_walk.support, hammingDist x.val z.val ≤ C₁ * rStar) →
        ListSizeCond C₁ rStar K X L →
        OverlapCond C₁ rStar K X →
        ListHitCond C₁ rStar X L →
        (exactDistPairs X rStar).card ≤ 2 * K ^ 2 * Nat.card G_hat.edgeSet := by
  sorry

/-- **Theorem 2.2(b) (Set-Sequence Lemma, Step 2)**:
For `C₁ ≥ 2`, `rStar ≥ 1`, `N ≥ 1`, `ℓ ≥ 1`, and any set sequence `F₀, ..., F_ℓ ⊆ [N]` with
`|F_i| ≤ C₁ rStar` and `|F₀ ∩ F_ℓ| ≤ rStar / 4`, there exist `s ∈ {1, ..., ℓ}`, `0 ≤ k ≤ 8 C₁`,
indices `t₁, ..., t_k ∈ {0, ..., ℓ}`, and a partition `F_{s-1} ∩ F_s = A₁ ⊔ ... ⊔ A_k ⊔ I_k` with
`|I_k| ≤ rStar / 2` such that (writing `I_rem(r) = (⊔_{j > r} A_j) ⊔ I_k` and `W_s = F_{s-1} ∪ F_s`)
every `r` satisfies `A_r ∩ F_{t_r} = ∅`, `I_rem(r) ⊆ F_{t_r}`, and
`|(W_s ∩ F_{t_r}) \ (A_r ⊔ I_rem(r))| ≥ |A_r| - rStar / 4`. -/
theorem thm_2_2b_biclique_bottleneck :
    ∀ (C₁ rStar N ℓ : ℕ), 2 ≤ C₁ → 1 ≤ rStar → 1 ≤ N → 1 ≤ ℓ →
      ∀ (F : Fin (ℓ + 1) → Finset (Fin N)),
        (∀ i : Fin (ℓ + 1), (F i).card ≤ C₁ * rStar) →
        ((F 0 ∩ F (Fin.last ℓ)).card : ℝ) ≤ (rStar : ℝ) / 4 →
        ∃ (s : Fin ℓ) (k : ℕ), k ≤ 8 * C₁ ∧
          ∃ (t : Fin k → Fin (ℓ + 1)) (A : Fin k → Finset (Fin N)) (I_k : Finset (Fin N)),
            Pairwise (fun i j => Disjoint (A i) (A j)) ∧
            (∀ r : Fin k, Disjoint (A r) I_k) ∧
            Finset.univ.biUnion A ∪ I_k = F s.castSucc ∩ F s.succ ∧
            (I_k.card : ℝ) ≤ (rStar : ℝ) / 2 ∧
            ∀ r : Fin k,
              let I_rem := (Finset.univ.filter (fun j : Fin k => r < j)).biUnion A ∪ I_k
              Disjoint (A r) (F (t r)) ∧
              I_rem ⊆ F (t r) ∧
              ((A r).card : ℝ) - (rStar : ℝ) / 4 ≤
                ((((F s.castSucc ∪ F s.succ) ∩ F (t r)) \ (A r ∪ I_rem)).card : ℝ) := by
  sorry

/-- **Theorem 2.3 (Existence of Hard Codes, Step 3)**:
There exists an absolute constant `M_L > 0` such that for every integer `C₁ ≥ 3`, there exist
integers `L, q, K ≥ 2` and `R₀ > 160 C₁` with `L ≤ M_L C₁^3 log₂ C₁` and `K = 20 C₁^2`, and real
`μ₀ > 0`, such that setting `c := 2^(-(2L + 5))`, for every `rStar ≥ R₀` and `N := 2^L rStar`,
there exist `X ⊆ [q]^N` of size `n := |X| ≥ 2` and `L_X : X² → 2^X` satisfying:
(1) `(2/5) μ₀ rStar ≤ log₂ n ≤ (3/2) μ₀ rStar` and `|E_{rStar}(X)| ≥ (1/192) n^(1 + c)`;
(2) `d_Ham(x, y) ≥ rStar / 2` for all distinct `x, y ∈ X`; and
(3) Conditions **(List-Size)**, **(Overlap)**, and **(List-Hit)** with parameters `(C₁, rStar, K)`. -/
theorem thm_2_3_locally_list_bounded_csp_codes :
    ∃ M_L : ℝ, 0 < M_L ∧
      ∀ C₁ : ℕ, 3 ≤ C₁ →
        ∃ (L q K R₀ : ℕ) (μ₀ : ℝ),
          2 ≤ L ∧ (L : ℝ) ≤ M_L * (C₁ : ℝ) ^ 3 * Real.logb 2 (C₁ : ℝ) ∧
          2 ≤ q ∧ K = 20 * C₁ ^ 2 ∧ 160 * C₁ < R₀ ∧ 0 < μ₀ ∧
          let c : ℝ := (2 : ℝ) ^ (-((2 * L + 5 : ℕ) : ℝ))
          ∀ rStar : ℕ, R₀ ≤ rStar →
            let N : ℕ := 2 ^ L * rStar
            ∃ (X : Finset (Fin N → Fin q)) (L_X : ↥X → ↥X → Finset ↥X),
              2 ≤ X.card ∧
              (2 : ℝ) / 5 * μ₀ * (rStar : ℝ) ≤ Real.logb 2 (X.card : ℝ) ∧
              Real.logb 2 (X.card : ℝ) ≤ (3 : ℝ) / 2 * μ₀ * (rStar : ℝ) ∧
              (1 : ℝ) / 192 * (X.card : ℝ) ^ (1 + c) ≤ ((exactDistPairs X rStar).card : ℝ) ∧
              (∀ x ∈ X, ∀ y ∈ X, x ≠ y → (rStar : ℝ) / 2 ≤ (hammingDist x y : ℝ)) ∧
              ListSizeCond C₁ rStar K X L_X ∧
              OverlapCond C₁ rStar K X ∧
              ListHitCond C₁ rStar X L_X := by
  sorry

/-- **Proposition 3.1 (Diameter-Bounded Bucketings as `2`-Hop Non-Metric Steiner Spanners)**:
For any finite metric space `(P, dist)` (`|P| ≥ 2`), `C ≥ 1`, and finite family `(B_i)_{i ∈ I}`
of subsets `B_i ⊆ P` with `|B_i| ≥ 2`:
(a) `|E(H)| = ∑_{i ∈ I} |B_i|` and `d_H(x, y) ≥ dist(x, y)` for all `x, y ∈ P`; and
(b) if every `x ≠ y` in `P` lies in some `B_i` with `diam(B_i) ≤ C · dist(x, y)`, then `H` is a
`2`-hop undirected non-metric Steiner `C`-spanner of `(P, dist)`. -/
theorem prop_3_1_diameter_bounded_bucketing :
    ∀ (P : Type) [MetricSpace P] [Fintype P],
      2 ≤ Fintype.card P →
      ∀ (C : ℝ), 1 ≤ C →
        ∀ (I : Type) [Fintype I] (B : I → Finset P),
          (∀ i : I, 2 ≤ (B i).card) →
          (Nat.card (bucketingGraph B).edgeSet = ∑ i : I, (B i).card ∧
            ∀ x y : P,
              ENNReal.ofReal (dist x y) ≤
                graphDist (bucketingGraph B) (bucketingWeight B) (.inl x) (.inl y)) ∧
          ((∀ x y : P, x ≠ y → ∃ i : I, x ∈ B i ∧ y ∈ B i ∧ bucketDiam (B i) ≤ C * dist x y) →
            IsGeneralNonMetricSteinerSpanner C (bucketingGraph B) (bucketingWeight B) ∧
            ∀ x y : P, x ≠ y →
              ∃ q : (bucketingGraph B).Walk (.inl x) (.inl y),
                q.IsPath ∧ q.length ≤ 2 ∧
                walkWeight (bucketingWeight B) q ≤ C * dist x y) := by
  sorry

/-- **Proposition 3.2 (Simplex Separation and Necessity of `N ≫ rStar`)**:
For every real `p ≥ 1`:
(a) On the standard basis `P = {e_1, ..., e_n} ⊂ {0, 1}^n` (`n ≥ 3`), every geometric `C`-spanner
with `1 ≤ C < 2` has `C(n, 2)` edges, whereas `(P, ‖·‖_p)` admits a `2`-hop undirected non-metric
Steiner `1`-spanner with `n` edges; and
(b) For any `N, q ≥ 2`, `r₀ ≥ 1`, and `X ⊆ [q]^N` (`|X| ≥ 2`) with minimum Hamming distance `≥ r₀`,
`ι(X) ⊂ {0, 1}^{N q}` admits a `2`-hop undirected non-metric Steiner `(N / r₀)^(1/p)`-spanner with
`|X|` edges. -/
theorem prop_3_2_simplex_separation :
    ∀ (p : ℝ), 1 ≤ p →
      (∀ n : ℕ, 3 ≤ n →
        (∀ (C : ℝ), 1 ≤ C → C < 2 →
          ∀ G : SimpleGraph (Fin n),
            IsGeometricSpanner p (stdBasis n) C G →
            Nat.card G.edgeSet = Nat.choose n 2) ∧
        (∃ (S : Type) (_ : Fintype S)
            (H : SimpleGraph (Fin n ⊕ S)) (w : Sym2 (Fin n ⊕ S) → ℝ),
          IsNonMetricSteinerSpanner p (stdBasis n) 1 H w ∧
          Nat.card H.edgeSet = n ∧
          ∀ i j : Fin n, i ≠ j →
            ∃ q : H.Walk (.inl i) (.inl j),
              q.IsPath ∧ q.length ≤ 2 ∧
              walkWeight w q ≤ 1 * lpDist p (stdBasis n i) (stdBasis n j))) ∧
      (∀ (N q r₀ : ℕ), 2 ≤ N → 2 ≤ q → 1 ≤ r₀ →
        ∀ (X : Finset (Fin N → Fin q)),
          2 ≤ X.card →
          (∀ x ∈ X, ∀ y ∈ X, x ≠ y → r₀ ≤ hammingDist x y) →
          ∀ (e : Fin X.card ≃ ↥X),
            let P : Fin X.card → (Fin (N * q) → ℝ) := fun i => oneHotEmbed (e i).val
            let stretch : ℝ := ((N : ℝ) / (r₀ : ℝ)) ^ (1 / p)
            ∃ (S : Type) (_ : Fintype S)
              (H : SimpleGraph (Fin X.card ⊕ S)) (w : Sym2 (Fin X.card ⊕ S) → ℝ),
              IsNonMetricSteinerSpanner p P stretch H w ∧
              Nat.card H.edgeSet = X.card ∧
              ∀ i j : Fin X.card, i ≠ j →
                ∃ q : H.Walk (.inl i) (.inl j),
                  q.IsPath ∧ q.length ≤ 2 ∧
                  walkWeight w q ≤ stretch * lpDist p (P i) (P j)) := by
  sorry

/-- **Lemma 3.3 (Single-Scale Blockwise Hamming-Code Hubs)**:
For integers `r ≥ 4`, `d ≥ 1`, real `p ≥ 1`, `b_r = 2^r - 1`, `ρ_r = 1 / (64 b_r)`, and every
`P ⊆ {0, 1}^d` (`|P| ≥ 2`) with `|P| ≥ 2^((1 - r / (2 b_r)) d)`, there exist `S_r ⊆ {0, 1}^d \ P`
and a simple graph `H_r` on `P ∪ S_r` weighted by `‖·‖_p` with `|E_r| ≤ 2|P|`, non-contraction on
`P`, and simple `≤ 3`-edge paths of weight `≤ 387 ‖x - y‖_p` for all `x, y ∈ P` with
`(1/3) ρ_r d ≤ d_Ham(x, y) ≤ (9/4) ρ_r d`. -/
lemma lem_3_3_blockwise_hamming_hubs :
    ∀ (r d : ℕ), 4 ≤ r → 1 ≤ d →
      ∀ (p : ℝ), 1 ≤ p →
        let b_r : ℝ := (2 : ℝ) ^ r - 1
        let ρ_r : ℝ := 1 / (64 * b_r)
        ∀ (P : Finset (Fin d → Bool)),
          2 ≤ P.card →
          (2 : ℝ) ^ ((1 - (r : ℝ) / (2 * b_r)) * (d : ℝ)) ≤ (P.card : ℝ) →
          ∃ (S_r : Finset (Fin d → Bool)),
            Disjoint P S_r ∧
            ∃ (H_r : SimpleGraph ↥(P ∪ S_r)),
              let w := cubeSubgraphWeight p (P ∪ S_r)
              Nat.card H_r.edgeSet ≤ 2 * P.card ∧
              (∀ (x y : Fin d → Bool) (hx : x ∈ P) (hy : y ∈ P),
                ENNReal.ofReal (cubeLpDist p x y) ≤
                  graphDist H_r w ⟨x, Finset.mem_union_left S_r hx⟩
                    ⟨y, Finset.mem_union_left S_r hy⟩) ∧
              (∀ (x y : Fin d → Bool) (hx : x ∈ P) (hy : y ∈ P),
                (1 : ℝ) / 3 * ρ_r * (d : ℝ) ≤ (hammingDist x y : ℝ) →
                (hammingDist x y : ℝ) ≤ (9 : ℝ) / 4 * ρ_r * (d : ℝ) →
                ∃ q : H_r.Walk ⟨x, Finset.mem_union_left S_r hx⟩
                    ⟨y, Finset.mem_union_left S_r hy⟩,
                  q.IsPath ∧ q.length ≤ 3 ∧ walkWeight w q ≤ 387 * cubeLpDist p x y) := by
  sorry

/-- **Proposition 3.4 (Three-Hop Collapse on High-Rate Hypercube Subsets)**:
For `p ≥ 1` and `ρ ∈ (0, 1)`, there exists `ε > 0` such that for every `d ≥ 1` and `P ⊆ {0, 1}^d`
(`|P| ≥ 2`) with `|P| ≥ 2^((1 - ε) d)`:
(a) some metric Steiner graph `H` in `{0, 1}^d` with `|E| ≤ 2|P|` spans all pairs in
`[(1/3) ρ d, ρ d]` in `≤ 3` hops with stretch `5760`; and
(b) if `min_{x ≠ y ∈ P} d_Ham(x, y) ≥ (1/3) ρ d`, `(P, ‖·‖_p)` admits a `3`-hop metric Steiner
`5760`-spanner in `{0, 1}^d` with at most `2|P| log₂(2 / ρ)` edges (and for `d ≥ 2` and
`P = {0, 1}^d`, a `3`-hop geometric `5760`-spanner with `S = ∅` and `≤ 4 · 2^d log₂ d` edges). -/
theorem prop_3_4_three_hop_hypercube_collapse :
    ∀ (p : ℝ), 1 ≤ p →
      ((∀ ρ : ℝ, 0 < ρ → ρ < 1 →
        ∃ ε : ℝ, 0 < ε ∧
          ∀ d : ℕ, 1 ≤ d →
            ∀ P : Finset (Fin d → Bool),
              2 ≤ P.card →
              (2 : ℝ) ^ ((1 - ε) * (d : ℝ)) ≤ (P.card : ℝ) →
              (∃ (S : Finset (Fin d → Bool)),
                Disjoint P S ∧
                ∃ H : SimpleGraph ↥(P ∪ S),
                  let w := cubeSubgraphWeight p (P ∪ S)
                  Nat.card H.edgeSet ≤ 2 * P.card ∧
                  (∀ (x y : Fin d → Bool) (hx : x ∈ P) (hy : y ∈ P),
                    ENNReal.ofReal (cubeLpDist p x y) ≤
                      graphDist H w ⟨x, Finset.mem_union_left S hx⟩
                        ⟨y, Finset.mem_union_left S hy⟩) ∧
                  (∀ (x y : Fin d → Bool) (hx : x ∈ P) (hy : y ∈ P),
                    (1 : ℝ) / 3 * ρ * (d : ℝ) ≤ (hammingDist x y : ℝ) →
                    (hammingDist x y : ℝ) ≤ ρ * (d : ℝ) →
                    ∃ q : H.Walk ⟨x, Finset.mem_union_left S hx⟩
                        ⟨y, Finset.mem_union_left S hy⟩,
                      q.IsPath ∧ q.length ≤ 3 ∧
                      walkWeight w q ≤ 5760 * cubeLpDist p x y)) ∧
              ((∀ x ∈ P, ∀ y ∈ P, x ≠ y →
                  (1 : ℝ) / 3 * ρ * (d : ℝ) ≤ (hammingDist x y : ℝ)) →
                ∃ (S : Finset (Fin d → Bool)),
                  Disjoint P S ∧
                  ∃ H : SimpleGraph ↥(P ∪ S),
                    let w := cubeSubgraphWeight p (P ∪ S)
                    (Nat.card H.edgeSet : ℝ) ≤ 2 * (P.card : ℝ) * Real.logb 2 (2 / ρ) ∧
                    (∀ (x y : Fin d → Bool) (hx : x ∈ P) (hy : y ∈ P),
                      ENNReal.ofReal (cubeLpDist p x y) ≤
                        graphDist H w ⟨x, Finset.mem_union_left S hx⟩
                          ⟨y, Finset.mem_union_left S hy⟩) ∧
                    (∀ (x y : Fin d → Bool) (hx : x ∈ P) (hy : y ∈ P), x ≠ y →
                      ∃ q : H.Walk ⟨x, Finset.mem_union_left S hx⟩
                          ⟨y, Finset.mem_union_left S hy⟩,
                        q.IsPath ∧ q.length ≤ 3 ∧
                        walkWeight w q ≤ 5760 * cubeLpDist p x y))) ∧
      (∀ d : ℕ, 2 ≤ d →
        ∃ H : SimpleGraph (Fin d → Bool),
          let w : Sym2 (Fin d → Bool) → ℝ :=
            Sym2.lift ⟨fun u v => cubeLpDist p u v, fun u v => by
              simp only [cubeLpDist, lpDist, abs_sub_comm]⟩
          (Nat.card H.edgeSet : ℝ) ≤ 4 * (2 : ℝ) ^ d * Real.logb 2 (d : ℝ) ∧
          (∀ x y : Fin d → Bool, ENNReal.ofReal (cubeLpDist p x y) ≤ graphDist H w x y) ∧
          (∀ x y : Fin d → Bool, x ≠ y →
            ∃ q : H.Walk x y,
              q.IsPath ∧ q.length ≤ 3 ∧ walkWeight w q ≤ 5760 * cubeLpDist p x y))) := by
  sorry

/-- **Lemma 5.1 (Interval Crossing Lemma)**:
For integers `1 ≤ α ≤ β` and intervals `[L_s, R_s]` (`s ∈ [α, β]`) satisfying
`α - 1 ≤ L_s ≤ s - 1 < s ≤ R_s ≤ β` and `(L_s, R_s) ≠ (α - 1, β)`, there exist `s < t` in `[α, β]`
with `L_s < L_t ≤ s < t ≤ R_s + 1 ≤ R_t`. -/
lemma lem_5_1_interval_crossing :
    ∀ (α β : ℤ), 1 ≤ α → α ≤ β →
      ∀ (L R : ℤ → ℤ),
        (∀ s : ℤ, α ≤ s → s ≤ β →
          α - 1 ≤ L s ∧ L s ≤ s - 1 ∧ s ≤ R s ∧ R s ≤ β ∧ (L s, R s) ≠ (α - 1, β)) →
        ∃ s t : ℤ,
          α ≤ s ∧ s < t ∧ t ≤ β ∧
          L s < L t ∧ L t ≤ s ∧ t ≤ R s + 1 ∧ R s + 1 ≤ R t := by
  sorry

/-- **Lemma 6.3 (Verification of Condition `(List-Hit)`)**:
If `R` is a symmetric `2`-CSP on `K_N` over `[q]`, `X ⊆ Ω(R)`, and `|D_3(x, u, z)| ≤ η₀ rStar`
(`η₀ = 1 / 80`) for all `x, u ∈ X` and `z ∈ Ω(R)` within Hamming distance `C₁ rStar` of `x`, then
`L_X(a, b) := L_R(a, b) ∩ X` (for `0 < d_Ham(a, b) ≤ C₁ rStar`, and `∅` otherwise) satisfies
Condition **(List-Hit)** of Theorem 2.2(a). -/
lemma lem_6_3_biclique_list_hit :
    ∀ (N q C₁ rStar : ℕ), 2 ≤ N → 2 ≤ q → 3 ≤ C₁ → 1 ≤ rStar →
      ∀ (R : Fin N → Fin N → Fin q → Fin q → Prop),
        Symmetric2CSP R →
        ∀ (X : Finset (Fin N → Fin q)),
          X ⊆ satisfyingSet R →
          let η₀ : ℝ := 1 / 80
          (∀ x ∈ X, ∀ u ∈ X, ∀ z ∈ satisfyingSet R,
            hammingDist x u ≤ C₁ * rStar →
            hammingDist x z ≤ C₁ * rStar →
            ((threeWayDisagree x u z).card : ℝ) ≤ η₀ * (rStar : ℝ)) →
          let L_X : ↥X → ↥X → Finset ↥X := fun a b =>
            if 0 < hammingDist a.val b.val ∧ hammingDist a.val b.val ≤ C₁ * rStar then
              Finset.univ.filter (fun x : ↥X => x.val ∈ bicliqueWitnessList R C₁ rStar a.val b.val)
            else ∅
          ListHitCond C₁ rStar X L_X := by
  sorry
