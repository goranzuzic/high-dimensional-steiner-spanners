import Mathlib
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

-- Equivalence of lpDist with Mathlib's WithLp (PiLp) metric
theorem lpDist_eq_toLp_dist :
    ∀ (p : ℝ), 1 ≤ p → ∀ {d : ℕ} (x y : Fin d → ℝ),
      let p' := ENNReal.ofReal p
      lpDist p x y = dist (WithLp.toLp p' x) (WithLp.toLp p' y) := by sorry

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
              c₀ * (nSeq j : ℝ) ^ (1 + c) ≤ (Nat.card G.edgeSet : ℝ) := by sorry

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
              c₀ C₁ * (nSeq j : ℝ) ^ (1 + c C₁) ≤ (Nat.card H.edgeSet : ℝ) := by sorry
