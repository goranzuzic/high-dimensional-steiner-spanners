import Solution.Glue
import Solution.Projection
import Solution.Combinatorics
import Solution.CSP

/-!
Proofs of the three theorems of `MinimalChallenge.lean` (Appendix A.1 of the paper), derived from
the proofs in `Solution/`. Definitions and theorem statements are verbatim from
`MinimalChallenge.lean`.
-/

open scoped ENNReal

-- Core metric, aspect-ratio, and spanner definitions (Definition 1.1)
noncomputable def lpDist (p : ℝ) {d : ℕ} (x y : Fin d → ℝ) : ℝ :=
  (∑ i : Fin d, |x i - y i| ^ p) ^ (1 / p)

noncomputable def aspectRatio (p : ℝ) {n d : ℕ} (P : Fin n → (Fin d → ℝ)) : ℝ :=
  let offDiag := Finset.univ.filter (fun ij : Fin n × Fin n => ij.1 ≠ ij.2)
  if hne : offDiag.Nonempty then
    offDiag.sup' hne (fun ij => lpDist p (P ij.1) (P ij.2)) /
      offDiag.inf' hne (fun ij => lpDist p (P ij.1) (P ij.2))
  else 0

def walkWeight {V : Type} {H : SimpleGraph V} (w : Sym2 V → ℝ) :
    ∀ {u v : V}, H.Walk u v → ℝ
  | _, _, .nil => 0
  | u, _, .cons (v := b) _ q => w s(u, b) + walkWeight w q

noncomputable def graphDist {V : Type} (H : SimpleGraph V) (w : Sym2 V → ℝ)
    (u v : V) : ℝ≥0∞ := ⨅ q : H.Walk u v, ENNReal.ofReal (walkWeight w q)

structure IsNonMetricSteinerSpanner (p : ℝ) {n d : ℕ} (P : Fin n → (Fin d → ℝ))
    (C : ℝ) {S : Type} [Fintype S] (H : SimpleGraph (Fin n ⊕ S))
    (w : Sym2 (Fin n ⊕ S) → ℝ) : Prop where
  weight_nonneg : ∀ e ∈ H.edgeSet, 0 ≤ w e
  noncontracting : ∀ i j : Fin n,
    ENNReal.ofReal (lpDist p (P i) (P j)) ≤ graphDist H w (.inl i) (.inl j)
  stretch : ∀ i j : Fin n,
    graphDist H w (.inl i) (.inl j) ≤ ENNReal.ofReal (C * lpDist p (P i) (P j))

def IsGeometricSpanner (p : ℝ) {n d : ℕ} (P : Fin n → (Fin d → ℝ)) (C : ℝ)
    (G : SimpleGraph (Fin n)) : Prop := ∀ i j : Fin n,
  graphDist G (Sym2.lift ⟨fun u v => lpDist p (P u) (P v),
    fun u v => by simp only [lpDist, abs_sub_comm]⟩) i j ≤
    ENNReal.ofReal (C * lpDist p (P i) (P j))

namespace MinimalSolution

/-! Comparison with the definitions of `Challenge.lean` (namespace `HighDimSteinerSpanners`). -/

theorem walkWeight_eq {V : Type} {H : SimpleGraph V} (w : Sym2 V → ℝ) {u v : V}
    (q : H.Walk u v) : walkWeight w q = HighDimSteinerSpanners.walkWeight w q := by
  induction q with
  | nil => rfl
  | cons _ _ ih => simp [walkWeight, HighDimSteinerSpanners.walkWeight, ih]

theorem graphDist_eq {V : Type} (H : SimpleGraph V) (w : Sym2 V → ℝ) (u v : V) :
    graphDist H w u v = HighDimSteinerSpanners.graphDist H w u v := by
  simp only [graphDist, HighDimSteinerSpanners.graphDist, walkWeight_eq]

theorem steiner {p : ℝ} {n d : ℕ} {P : Fin n → (Fin d → ℝ)} {C : ℝ} {S : Type} [Fintype S]
    {H : SimpleGraph (Fin n ⊕ S)} {w : Sym2 (Fin n ⊕ S) → ℝ}
    (h : IsNonMetricSteinerSpanner p P C H w) :
    HighDimSteinerSpanners.IsNonMetricSteinerSpanner p P C H w :=
  ⟨h.weight_nonneg,
    fun i j => by simpa only [graphDist_eq] using h.noncontracting i j,
    fun i j => by simpa only [graphDist_eq] using h.stretch i j⟩

theorem geometric {p : ℝ} {n d : ℕ} {P : Fin n → (Fin d → ℝ)} {C : ℝ}
    {G : SimpleGraph (Fin n)} (h : IsGeometricSpanner p P C G) :
    HighDimSteinerSpanners.IsGeometricSpanner p P C G := by
  intro i j
  simpa only [IsGeometricSpanner, HighDimSteinerSpanners.IsGeometricSpanner, graphDist_eq]
    using h i j

theorem aspectRatio_le {n d : ℕ} (hn : 0 < n) (p : ℝ) (P : Fin n → (Fin d → ℝ)) :
    aspectRatio p P ≤ HighDimSteinerSpanners.aspectRatio p P := by
  simp only [aspectRatio, HighDimSteinerSpanners.aspectRatio,
    HighDimSteinerSpanners.maxPairwiseDist, HighDimSteinerSpanners.minDistinctPairwiseDist,
    hn, dite_true]
  split_ifs with h
  · apply div_le_div_of_nonneg_right
    · apply Finset.sup'_le h
      intro ij _
      exact Finset.le_sup' (fun ij : Fin n × Fin n =>
        HighDimSteinerSpanners.lpDist p (P ij.1) (P ij.2)) (Finset.mem_univ ij)
    · rw [Finset.le_inf'_iff]
      intro ij _
      exact Real.rpow_nonneg (Finset.sum_nonneg fun _ _ => Real.rpow_nonneg (abs_nonneg _) _) _
  · simp

/-- Theorem 1.3 for the definitions of `Challenge.lean`, assembled as in `Solution.lean`. -/
def thm_1_3_full :=
  Solution.Glue.thm_1_3_from_modules Solution.Projection.thm_2_1b_proof
    Solution.Combinatorics.thm_2_2a_proof
    (Solution.CSP.thm_2_3_from_6_3
      (Solution.Glue.lem_6_3_from_2_2b Solution.Combinatorics.thm_2_2b_proof))

/-- Theorem 1.2 for the definitions of `Challenge.lean`, assembled as in `Solution.lean`. -/
def thm_1_2_full :=
  Solution.Projection.thm_1_2_from_1_3 Solution.Glue.lpDist_eq_toLp_dist_proof thm_1_3_full

end MinimalSolution

-- Equivalence of lpDist with Mathlib's WithLp (PiLp) metric
theorem lpDist_eq_toLp_dist :
    ∀ (p : ℝ), 1 ≤ p → ∀ {d : ℕ} (x y : Fin d → ℝ),
      let p' := ENNReal.ofReal p
      lpDist p x y = dist (WithLp.toLp p' x) (WithLp.toLp p' y) :=
  Solution.Glue.lpDist_eq_toLp_dist_proof

-- Theorem 1.2: Lower bound for geometric spanners
theorem thm_1_2_geometric_spanner_lower_bound :
    ∃ M : ℝ, 0 < M ∧ ∀ (p : ℝ), 1 ≤ p → ∀ (C : ℝ), 1 ≤ C →
      ∃ (c c₀ A β₁ β₂ : ℝ),
        (2 : ℝ) ^ (-M * C ^ (3 * p) * Real.logb 2 (C ^ p + 1)) ≤ c ∧
        0 < c₀ ∧ 0 < A ∧ 0 < β₁ ∧ β₁ ≤ β₂ ∧
        ∃ nSeq : ℕ → ℕ, StrictMono nSeq ∧ (∀ j : ℕ, 2 ≤ nSeq j) ∧ ∀ j : ℕ,
          ∃ (d : ℕ) (P : Fin (nSeq j) → (Fin d → ℝ)),
            1 ≤ d ∧ β₁ * Real.logb 2 (nSeq j : ℝ) ≤ (d : ℝ) ∧
            (d : ℝ) ≤ β₂ * Real.logb 2 (nSeq j : ℝ) ∧
            (∀ i : Fin (nSeq j), ∀ k : Fin d, P i k = 0 ∨ P i k = 1) ∧
            Function.Injective P ∧ aspectRatio p P ≤ A ∧
            ∀ (G : SimpleGraph (Fin (nSeq j))), IsGeometricSpanner p P C G →
              c₀ * (nSeq j : ℝ) ^ (1 + c) ≤ (Nat.card G.edgeSet : ℝ) := by
  obtain ⟨M, hM, hmain⟩ := MinimalSolution.thm_1_2_full
  refine ⟨M, hM, fun p hp C hC => ?_⟩
  obtain ⟨c, c₀, A, β₁, β₂, _, hc, hc₀, hA, hβ₁, hβ₂, nSeq, hmono, hn, hP⟩ := hmain p hp C hC
  refine ⟨c, c₀, A, β₁, β₂, hc, hc₀, hA, hβ₁, hβ₂, nSeq, hmono, hn, fun j => ?_⟩
  obtain ⟨d, P, hd, hd₁, hd₂, h01, hinj, hΔ, hspan⟩ := hP j
  exact ⟨d, P, hd, hd₁, hd₂, h01, hinj,
    (MinimalSolution.aspectRatio_le (Nat.zero_lt_two.trans_le (hn j)) p P).trans hΔ,
    fun G hG => hspan G (MinimalSolution.geometric hG)⟩

-- Theorem 1.3: Main lower bound for undirected non-metric Steiner spanners
theorem thm_1_3_non_metric_steiner_spanner_lower_bound :
    ∃ (M : ℝ) (c c₀ β₁ β₂ A : ℕ → ℝ), 0 < M ∧
      (∀ C₁ : ℕ, 3 ≤ C₁ →
        (2 : ℝ) ^ (-M * (C₁ : ℝ) ^ 3 * Real.logb 2 (C₁ : ℝ)) ≤ c C₁ ∧
        0 < c₀ C₁ ∧ 0 < β₁ C₁ ∧ β₁ C₁ ≤ β₂ C₁ ∧ 0 < A C₁) ∧
      ∀ (p : ℝ), 1 ≤ p → ∀ (C : ℝ), 1 ≤ C →
        let C₁ : ℕ := max 3 ⌈C ^ p⌉₊
        (2 : ℝ) ^ (-(81 * M) * C ^ (3 * p) * Real.logb 2 (C ^ p + 1)) ≤ c C₁ ∧
        ∃ nSeq : ℕ → ℕ, StrictMono nSeq ∧ (∀ j : ℕ, 2 ≤ nSeq j) ∧ ∀ j : ℕ,
          ∃ (d : ℕ) (P : Fin (nSeq j) → (Fin d → ℝ)),
            1 ≤ d ∧ β₁ C₁ * Real.logb 2 (nSeq j : ℝ) ≤ (d : ℝ) ∧
            (d : ℝ) ≤ β₂ C₁ * Real.logb 2 (nSeq j : ℝ) ∧
            (∀ i : Fin (nSeq j), ∀ k : Fin d, P i k = 0 ∨ P i k = 1) ∧
            Function.Injective P ∧ aspectRatio p P ≤ A C₁ ∧
            ∀ (S : Type) [Fintype S] (H : SimpleGraph (Fin (nSeq j) ⊕ S))
              (w : Sym2 (Fin (nSeq j) ⊕ S) → ℝ),
              IsNonMetricSteinerSpanner p P C H w →
              c₀ C₁ * (nSeq j : ℝ) ^ (1 + c C₁) ≤ (Nat.card H.edgeSet : ℝ) := by
  obtain ⟨M, c, c₀, β₁, β₂, A, hM, hc₁, hmain⟩ := MinimalSolution.thm_1_3_full
  refine ⟨M, c, c₀, β₁, β₂, A, hM, hc₁, fun p hp C hC => ?_⟩
  obtain ⟨_, hc, nSeq, hmono, hn, hP⟩ := hmain p hp C hC
  refine ⟨hc, nSeq, hmono, hn, fun j => ?_⟩
  obtain ⟨d, P, hd, hd₁, hd₂, h01, hinj, hΔ, hspan⟩ := hP j
  exact ⟨d, P, hd, hd₁, hd₂, h01, hinj,
    (MinimalSolution.aspectRatio_le (Nat.zero_lt_two.trans_le (hn j)) p P).trans hΔ,
    fun S _ H w hH => hspan S H w (MinimalSolution.steiner hH)⟩
