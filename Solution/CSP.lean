import Solution.Defs

set_option maxHeartbeats 4000000

open scoped ENNReal Classical
open HighDimSteinerSpanners

namespace Solution.CSP

noncomputable section Helpers

set_option synthInstance.maxHeartbeats 200000

private def diffCoords {N q : ℕ} (x y : Fin N → Fin q) : Finset (Fin N) :=
  Finset.univ.filter (fun v : Fin N => x v ≠ y v)

private abbrev dHam {N q : ℕ} (x y : Fin N → Fin q) : ℕ :=
  (diffCoords x y).card

private def d3Coords {N q : ℕ} (x y z : Fin N → Fin q) : Finset (Fin N) :=
  Finset.univ.filter (fun v : Fin N => x v ≠ y v ∧ x v ≠ z v ∧ y v ≠ z v)

private def cspKMax (C₁ : ℕ) : ℕ := 8 * C₁

private def cspKCh (C₁ : ℕ) : ℕ := 20 * C₁ ^ 2

private def cspKMom (C₁ : ℕ) : ℕ := 20 * C₁ ^ 2

private def cspInvEta0 (_C₁ : ℕ) : ℕ := 80

private def cspLam0 (C₁ : ℕ) : ℕ := 100 * C₁ * (2 * Nat.clog 2 C₁ + 6)

private def cspBeta0 (C₁ : ℕ) : ℕ := 6 * cspLam0 C₁

private def cspGamma0 (C₁ : ℕ) : ℕ := 5 * cspLam0 C₁

private def cspL (C₁ : ℕ) : ℕ := 20 + 20 * C₁ ^ 2 * cspInvEta0 C₁ * cspLam0 C₁

private def cspEq (C₁ : ℕ) : ℕ := 2 * cspBeta0 C₁ * 2 ^ cspL C₁

private def cspQ (C₁ : ℕ) : ℕ := 2 ^ cspEq C₁ + 1

private abbrev cspIota (N q : ℕ) : Type :=
  (Fin N × Fin N × Fin q × Fin q) ⊕ (Fin N → Fin q)

private def homQueries {N q : ℕ} (z : Fin N → Fin q) : Finset (Fin N × Fin N × Fin q × Fin q) :=
  (Finset.univ.filter (fun uv : Fin N × Fin N => uv.1 < uv.2)).image
    (fun uv => (uv.1, uv.2, z uv.1, z uv.2))

private noncomputable def bernWeight {ι : Type*} [Fintype ι] (p : ι → ℝ) (ω : ι → Bool) : ℝ :=
  ∏ i : ι, if ω i = true then p i else 1 - p i

private noncomputable def cspSigmaEdge (C₁ r_star : ℕ) : ℝ :=
  ((cspEq C₁ + cspL C₁ + cspGamma0 C₁ + 2 : ℕ) : ℝ) / ((2 ^ cspL C₁ * r_star - 1 : ℕ) : ℝ)

private noncomputable def cspPEdge (C₁ r_star : ℕ) : ℝ :=
  (2 : ℝ) ^ (- cspSigmaEdge C₁ r_star)

private noncomputable def cspDOmega (C₁ r_star s : ℕ) : ℝ :=
  ((2 ^ cspL C₁ * r_star).choose s : ℝ) * ((cspQ C₁ - 1 : ℕ) : ℝ) ^ s *
    (cspPEdge C₁ r_star) ^ (s * (2 ^ cspL C₁ * r_star - 1) - s.choose 2)

private noncomputable def cspDStar (C₁ r_star : ℕ) : ℝ :=
  (2 : ℝ) ^ ((1 / 4 : ℝ) * (cspLam0 C₁ : ℝ) * (r_star : ℝ))

private noncomputable def cspPKeep (C₁ r_star : ℕ) : ℝ :=
  cspDStar C₁ r_star / cspDOmega C₁ r_star r_star

private noncomputable def cspN0 (C₁ r_star : ℕ) : ℝ :=
  cspPKeep C₁ r_star * ((cspQ C₁ : ℝ) ^ (2 ^ cspL C₁ * r_star)) *
    (cspPEdge C₁ r_star) ^ ((2 ^ cspL C₁ * r_star).choose 2)

private noncomputable def cspPIota (C₁ r_star : ℕ) : cspIota (2 ^ cspL C₁ * r_star) (cspQ C₁) → ℝ :=
  Sum.elim (fun _ => cspPEdge C₁ r_star) (fun _ => cspPKeep C₁ r_star)

private noncomputable def cspGamma (r_star : ℕ) : ℝ :=
  (2 : ℝ) ^ ((r_star : ℝ) / ((2 : ℝ) ^ (998 : ℕ)))

private noncomputable def cspDeltaBad (C₁ r_star : ℕ) : ℝ :=
  (2 : ℝ) ^ (- (6 / 10 : ℝ) * (cspLam0 C₁ : ℝ) * (r_star : ℝ))

private def cspPoolCand {N q : ℕ} (C₁ r_star : ℕ) (a b : Fin N → Fin q) : Finset (Fin N → Fin q) :=
  Finset.univ.filter (fun x : Fin N → Fin q =>
    x ≠ a ∧ x ≠ b ∧ dHam x a ≤ C₁ * r_star ∧ dHam x b ≤ C₁ * r_star)

private def cspRvc {N q : ℕ} (a b : Fin N → Fin q) (m : ℕ)
    (z_prev : Fin m → (Fin N → Fin q)) : Finset (Fin N × Fin q) :=
  Finset.univ.image (fun v : Fin N => (v, a v)) ∪
    Finset.univ.image (fun v : Fin N => (v, b v)) ∪
    Finset.univ.biUnion (fun t : Fin m => Finset.univ.image (fun v : Fin N => (v, z_prev t v)))

private def cspUCand {N q : ℕ} (a b : Fin N → Fin q) (m : ℕ)
    (z_prev : Fin m → (Fin N → Fin q)) : Finset (cspIota N q) :=
  ({a, b} : Finset (Fin N → Fin q)).image Sum.inr ∪
    Finset.univ.image (fun t : Fin m => (Sum.inr (z_prev t) : cspIota N q)) ∪
    (Finset.univ.filter (fun t : Fin N × Fin N × Fin q × Fin q =>
      t.1 < t.2.1 ∧ (t.1, t.2.2.1) ∈ cspRvc a b m z_prev ∧
      (t.2.1, t.2.2.2) ∈ cspRvc a b m z_prev)).image Sum.inl

private def cspPoolCh {N q : ℕ} (C₁ r_star : ℕ) (x w₀ : Fin N → Fin q) : Finset (Fin N → Fin q) :=
  Finset.univ.filter (fun y : Fin N → Fin q =>
    y ≠ x ∧ y ≠ w₀ ∧ dHam x y = r_star ∧
    r_star < 4 * (diffCoords x w₀ ∩ diffCoords x y).card ∧
    cspInvEta0 C₁ * (d3Coords x w₀ y).card ≤ r_star)

private def cspUCh {N q : ℕ} (x w₀ : Fin N → Fin q) (m : ℕ)
    (y_prev : Fin m → (Fin N → Fin q)) : Finset (cspIota N q) :=
  ({x, w₀} : Finset (Fin N → Fin q)).image Sum.inr ∪
    Finset.univ.image (fun t : Fin m => (Sum.inr (y_prev t) : cspIota N q)) ∪
    (homQueries x ∪ homQueries w₀ ∪
      Finset.univ.biUnion (fun t : Fin m => homQueries (y_prev t))).image Sum.inl

private def symROf {N q : ℕ} (ω : cspIota N q → Bool) : Fin N → Fin N → Fin q → Fin q → Prop :=
  fun u v c₁ c₂ =>
    if u < v then ω (Sum.inl (u, v, c₁, c₂)) = true
    else if v < u then ω (Sum.inl (v, u, c₂, c₁)) = true
    else False

private def cspPRaw {N q : ℕ} (ω : cspIota N q → Bool) : Finset (Fin N → Fin q) :=
  Finset.univ.filter (fun x : Fin N → Fin q =>
    ω (Sum.inr x) = true ∧ ∀ t ∈ homQueries x, ω (Sum.inl t) = true)

private def cspBD3 {N q : ℕ} (C₁ r_star : ℕ) (ω : cspIota N q → Bool) : Finset (Fin N → Fin q) :=
  (cspPRaw ω).filter (fun x =>
    ∃ u ∈ cspPRaw ω, ∃ z : Fin N → Fin q,
      (∀ t ∈ homQueries z, ω (Sum.inl t) = true) ∧
      dHam x u ≤ C₁ * r_star ∧ dHam x z ≤ C₁ * r_star ∧
      r_star < cspInvEta0 C₁ * (d3Coords x u z).card)

private def cspBCh {N q : ℕ} (C₁ r_star : ℕ) (ω : cspIota N q → Bool) : Finset (Fin N → Fin q) :=
  (cspPRaw ω).filter (fun x =>
    ∃ w₀ ∈ cspPRaw ω, x ≠ w₀ ∧ dHam x w₀ ≤ C₁ * r_star ∧
      cspKCh C₁ ≤ ((cspPoolCh C₁ r_star x w₀).filter (fun y => y ∈ cspPRaw ω)).card)

private noncomputable def cspBCand {N q : ℕ} (C₁ r_star : ℕ) (ω : cspIota N q → Bool) :
    Finset (Fin N → Fin q) :=
  (cspPRaw ω).filter (fun a =>
    ∃ b ∈ cspPRaw ω, a ≠ b ∧ dHam a b ≤ C₁ * r_star ∧
      cspKMom C₁ ≤ ((cspPRaw ω).filter (fun x => x ∈ bicliqueWitnessList (symROf ω) C₁ r_star a b)).card)

private def cspBDist {N q : ℕ} (r_star : ℕ) (ω : cspIota N q → Bool) : Finset (Fin N → Fin q) :=
  (cspPRaw ω).filter (fun x =>
    ∃ y ∈ cspPRaw ω, x ≠ y ∧ 2 * dHam x y < r_star)

private noncomputable def cspBBad {N q : ℕ} (C₁ r_star : ℕ) (ω : cspIota N q → Bool) :
    Finset (Fin N → Fin q) :=
  cspBD3 C₁ r_star ω ∪ cspBCh C₁ r_star ω ∪ cspBCand C₁ r_star ω ∪ cspBDist r_star ω

private def candCStar {N q : ℕ} (a b x : Fin N → Fin q) (v : Fin N) : Fin q :=
  if a v ≠ x v then a v else b v

private def candMFresh {N q : ℕ} (a b : Fin N → Fin q) (m : ℕ)
    (z_prev : Fin m → (Fin N → Fin q)) (x : Fin N → Fin q) : Finset (Fin N) :=
  Finset.univ.filter (fun v : Fin N => (v, x v) ∉ cspRvc a b m z_prev)

private def candA1 {N : ℕ} (S : Finset (Fin N)) : Finset (Fin N × Fin N) :=
  Finset.univ.filter (fun uv : Fin N × Fin N => uv.1 < uv.2 ∧ (uv.1 ∈ S ∨ uv.2 ∈ S))

private abbrev candWitType (N C₁ : ℕ) : Type :=
  Fin (cspKMax C₁ + 1) ×
  (Fin N → Fin (cspKMax C₁ + 1)) ×
  (Fin (cspKMax C₁) → Finset (Fin N)) ×
  Finset (Fin (cspKMax C₁) × Fin N)

private def candA2 {N q : ℕ} (C₁ : ℕ) (a b x : Fin N → Fin q) (M : Finset (Fin N))
    (w : candWitType N C₁) : Finset (Fin N × Fin N) :=
  (M ×ˢ (diffCoords x a ∪ diffCoords x b)).filter
    (fun uv => ∃ r : Fin (cspKMax C₁),
      r.1 < w.1.1 ∧ w.2.1 uv.1 = r.succ ∧ (uv.2 ∈ w.2.2.1 r ∨ (r, uv.2) ∈ w.2.2.2))

private def candPhi1 {N q : ℕ} (x : Fin N → Fin q) (uv : Fin N × Fin N) :
    Fin N × Fin N × Fin q × Fin q :=
  (uv.1, uv.2, x uv.1, x uv.2)

private def candPhi2 {N q : ℕ} (a b x : Fin N → Fin q) (uv : Fin N × Fin N) :
    Fin N × Fin N × Fin q × Fin q :=
  if uv.1 < uv.2 then (uv.1, uv.2, x uv.1, candCStar a b x uv.2)
  else (uv.2, uv.1, candCStar a b x uv.2, x uv.1)

private def candMWit {N q : ℕ} (C₁ r_star : ℕ) (a b : Fin N → Fin q) (m : ℕ)
    (z_prev : Fin m → (Fin N → Fin q)) (x : Fin N → Fin q) :
    Finset (candWitType N C₁) :=
  let K_max := cspKMax C₁
  let M := candMFresh a b m z_prev x
  let W_ab := diffCoords x a ∪ diffCoords x b
  let base := (Finset.univ : Finset (Fin (K_max + 1))) ×ˢ
    (Fintype.piFinset (fun u : Fin N =>
      if u ∈ M then Finset.univ else ({0} : Finset (Fin (K_max + 1)))) ×ˢ
      Fintype.piFinset (fun _ : Fin K_max => M.powerset))
  let s_hat := fun (k : Fin (K_max + 1)) (τ : Fin N → Fin (K_max + 1)) (r : Fin K_max) =>
    if r.1 < k.1 then (M.filter (fun u => τ u = r.succ)).card - (11 * r_star) / 40 else 0
  (base.biUnion (fun ktB =>
    (((Finset.univ : Finset (Fin K_max)) ×ˢ W_ab).powersetCard
      (∑ r : Fin K_max, s_hat ktB.1 ktB.2.1 r)).image
      (fun U_out => (ktB.1, ktB.2.1, ktB.2.2, U_out)))).filter
    (fun w =>
      let k := w.1
      let τ := w.2.1
      let B_fut := w.2.2.1
      let U_out := w.2.2.2
      (∀ u ∈ M, (τ u).1 ≤ k.1) ∧
      2 * (M.filter (fun u => τ u = 0)).card ≤ r_star ∧
      ∀ r : Fin K_max, r.1 < k.1 →
        let M_r := M.filter (fun u => τ u = r.succ)
        let I_t := M.filter (fun u => τ u = 0 ∨ r.1 + 1 < (τ u).1)
        let B_o := W_ab.filter (fun v => (r, v) ∈ U_out)
        B_fut r ⊆ I_t ∧
        80 * (I_t \ B_fut r).card ≤ r_star ∧
        Disjoint B_o (M_r ∪ I_t) ∧
        B_o.card = M_r.card - (11 * r_star) / 40)

private def candQCand {N q : ℕ} (C₁ : ℕ) (a b : Fin N → Fin q) (m : ℕ)
    (z_prev : Fin m → (Fin N → Fin q)) (x : Fin N → Fin q)
    (w : candWitType N C₁) : Finset (cspIota N q) :=
  ({x} : Finset (Fin N → Fin q)).image Sum.inr ∪
    ((candA1 (candMFresh a b m z_prev x)).image (candPhi1 x) ∪
      (candA2 C₁ a b x (candMFresh a b m z_prev x) w).image (candPhi2 a b x)).image Sum.inl

private lemma lam0_ge_1000_C1 (C₁ : ℕ) (hC₁ : 3 ≤ C₁) :
    2 ≤ Nat.clog 2 C₁ ∧ 1000 * C₁ ≤ cspLam0 C₁ ∧
    (cspL C₁ : ℝ) ≤ (2000000 : ℝ) * (C₁ : ℝ) ^ 3 * Real.logb 2 (C₁ : ℝ) := by
  have hclog_ge2 : 2 ≤ Nat.clog 2 C₁ := by
    by_contra hlt
    have hle1 : Nat.clog 2 C₁ ≤ 1 := by omega
    have hC_le : C₁ ≤ 2 ^ 1 := (Nat.clog_le_iff_le_pow (by decide : 1 < 2)).mp hle1
    omega
  have hlam_ge : 1000 * C₁ ≤ cspLam0 C₁ := by
    unfold cspLam0
    have h10 : 10 ≤ 2 * Nat.clog 2 C₁ + 6 := by omega
    nlinarith
  refine ⟨hclog_ge2, hlam_ge, ?_⟩
  set t := Nat.clog 2 C₁
  have ht_pos : 1 ≤ t := by omega
  have hpow_lt : 2 ^ (t - 1) < C₁ := by
    by_contra hge
    push_neg at hge
    have hle : Nat.clog 2 C₁ ≤ t - 1 :=
      (Nat.clog_le_iff_le_pow (by decide : 1 < 2)).mpr hge
    omega
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hlogb_mono : ∀ x y : ℝ, 0 < x → x ≤ y → Real.logb 2 x ≤ Real.logb 2 y := by
    intro x y hx hxy
    unfold Real.logb
    exact div_le_div_of_nonneg_right (Real.log_le_log hx hxy) (le_of_lt hlog2_pos)
  have hlogb_pow : ∀ k : ℕ, Real.logb 2 ((2 : ℝ) ^ k) = (k : ℝ) := by
    intro k
    unfold Real.logb
    rw [Real.log_pow, mul_div_cancel_right₀ _ (ne_of_gt hlog2_pos)]
  have hC1_real_ge3 : (3 : ℝ) ≤ (C₁ : ℝ) := by exact_mod_cast hC₁
  have hlog_ge1 : 1 ≤ Real.logb 2 (C₁ : ℝ) := by
    have h := hlogb_mono 2 (C₁ : ℝ) (by norm_num) (by linarith)
    simpa [hlogb_pow 1] using h
  have ht1_le : ((t - 1 : ℕ) : ℝ) ≤ Real.logb 2 (C₁ : ℝ) := by
    have hle_real : ((2 : ℝ) ^ (t - 1)) ≤ (C₁ : ℝ) := by
      exact_mod_cast (le_of_lt hpow_lt)
    have h := hlogb_mono ((2 : ℝ) ^ (t - 1)) (C₁ : ℝ) (by positivity) hle_real
    rwa [hlogb_pow (t - 1)] at h
  have ht_le : (t : ℝ) ≤ 2 * Real.logb 2 (C₁ : ℝ) := by
    rw [Nat.cast_sub ht_pos, Nat.cast_one] at ht1_le
    linarith
  have h2t6_le : 2 * (t : ℝ) + 6 ≤ 10 * Real.logb 2 (C₁ : ℝ) := by linarith
  have hlam_real : (cspLam0 C₁ : ℝ) ≤ 1000 * (C₁ : ℝ) * Real.logb 2 (C₁ : ℝ) := by
    have heq : (cspLam0 C₁ : ℝ) = 100 * (C₁ : ℝ) * (2 * (t : ℝ) + 6) := by
      dsimp [cspLam0, t]
      push_cast
      ring
    rw [heq]
    have h100C : 0 ≤ 100 * (C₁ : ℝ) := by positivity
    have hm := mul_le_mul_of_nonneg_left h2t6_le h100C
    linarith
  have hL_eq : (cspL C₁ : ℝ) = 1600 * (C₁ : ℝ) ^ 2 * (cspLam0 C₁ : ℝ) + 20 := by
    unfold cspL cspInvEta0
    push_cast
    ring
  have hC3_ge27 : (27 : ℝ) ≤ (C₁ : ℝ) ^ 3 := by nlinarith
  have hC3log_ge27 : (27 : ℝ) ≤ (C₁ : ℝ) ^ 3 * Real.logb 2 (C₁ : ℝ) := by
    nlinarith
  have hm_L : 1600 * (C₁ : ℝ) ^ 2 * (cspLam0 C₁ : ℝ) ≤
      1600000 * (C₁ : ℝ) ^ 3 * Real.logb 2 (C₁ : ℝ) := by
    have hm := mul_le_mul_of_nonneg_left hlam_real (by positivity : (0 : ℝ) ≤ 1600 * (C₁ : ℝ) ^ 2)
    linarith [hm,
      show 1600 * (C₁ : ℝ) ^ 2 * (1000 * (C₁ : ℝ) * Real.logb 2 (C₁ : ℝ)) =
        1600000 * (C₁ : ℝ) ^ 3 * Real.logb 2 (C₁ : ℝ) by ring]
  linarith

private lemma choose_bound_exp4 (U S m_sz r B : ℕ) (hB : 1 ≤ B) (hU : U ≤ B * r) (hS : S ≤ m_sz) :
    (U.choose S : ℝ) ≤ (B : ℝ) ^ m_sz * (4 : ℝ) ^ r := by
  have hexp4 : Real.exp (r : ℝ) ≤ (4 : ℝ) ^ r := by
    have h1 : Real.exp (r : ℝ) = (Real.exp 1) ^ r := by simp
    have he4 : Real.exp 1 ≤ 4 := by linarith [Real.exp_one_lt_d9]
    rw [h1]
    exact pow_le_pow_left₀ (le_of_lt (Real.exp_pos 1)) he4 r
  have h1 : (U.choose S : ℝ) ≤ (U : ℝ) ^ S / (S.factorial : ℝ) := Nat.choose_le_pow_div S U
  have hU_r : (U : ℝ) ≤ (B : ℝ) * (r : ℝ) := by exact_mod_cast hU
  have h2 : (U : ℝ) ^ S / (S.factorial : ℝ) ≤
      ((B : ℝ) * (r : ℝ)) ^ S / (S.factorial : ℝ) :=
    div_le_div_of_nonneg_right (pow_le_pow_left₀ (Nat.cast_nonneg U) hU_r S) (Nat.cast_nonneg _)
  have h3 : ((B : ℝ) * (r : ℝ)) ^ S / (S.factorial : ℝ) =
      (B : ℝ) ^ S * ((r : ℝ) ^ S / (S.factorial : ℝ)) := by
    rw [mul_pow, mul_div_assoc]
  have hB1 : (1 : ℝ) ≤ (B : ℝ) := by exact_mod_cast hB
  have hBs : (B : ℝ) ^ S ≤ (B : ℝ) ^ m_sz := pow_le_pow_right₀ hB1 hS
  have hrs : (r : ℝ) ^ S / (S.factorial : ℝ) ≤ (4 : ℝ) ^ r :=
    le_trans (Real.pow_div_factorial_le_exp (r : ℝ) (Nat.cast_nonneg r) S) hexp4
  have h4 : (B : ℝ) ^ S * ((r : ℝ) ^ S / (S.factorial : ℝ)) ≤ (B : ℝ) ^ m_sz * (4 : ℝ) ^ r :=
    mul_le_mul hBs hrs (by positivity) (by positivity)
  linarith

private lemma powerset_card_le_bound {α : Type*} [DecidableEq α] (R_set : Finset α)
    (C₁ A b : ℕ) (hC₁ : 3 ≤ C₁) (hA : A ≤ 21) (hcard : R_set.card ≤ A * C₁ ^ 2 * b) :
    ((R_set.powerset.filter (fun G => G.card ≤ b)).card : ℝ) ≤
      ((b + 1 : ℕ) : ℝ) * (2 : ℝ) ^ (((2 * Nat.clog 2 C₁ + 6) * b : ℕ) : ℝ) := by
  let M : ℕ := 21 * C₁ ^ 2 * b
  have hR_le_M : R_set.card ≤ M := by
    have hAC : A * C₁ ^ 2 ≤ 21 * C₁ ^ 2 := Nat.mul_le_mul_right _ hA
    exact le_trans hcard (Nat.mul_le_mul_right b hAC)
  have h2b_le_M : 2 * b ≤ M := by
    dsimp [M]
    have hC2 : 9 ≤ C₁ ^ 2 := by nlinarith
    nlinarith
  have hchoose_mono : ∀ (N0 t0 b0 : ℕ), 2 * b0 ≤ N0 → t0 ≤ b0 → N0.choose t0 ≤ N0.choose b0 := by
    intro N0 t0 b0 h2b htb
    have hstep : ∀ k : ℕ, 2 * (k + 1) ≤ N0 → N0.choose k ≤ N0.choose (k + 1) := by
      intro k hk
      have hid := (Nat.choose_succ_right_eq N0 k).symm
      have hkle : k + 1 ≤ N0 - k := by omega
      have hmul : N0.choose k * (k + 1) ≤ N0.choose (k + 1) * (k + 1) := by
        calc
          N0.choose k * (k + 1) ≤ N0.choose k * (N0 - k) := Nat.mul_le_mul_left _ hkle
          _ = N0.choose (k + 1) * (k + 1) := hid
      exact Nat.le_of_mul_le_mul_right hmul (by omega)
    have hm : ∀ x : ℕ, t0 ≤ x → 2 * x ≤ N0 → N0.choose t0 ≤ N0.choose x :=
      Nat.le_induction (fun _ => le_refl _) (fun k _ ih hk1 =>
        le_trans (ih (by omega)) (hstep k hk1))
    exact hm b0 htb h2b
  have hMb_le : (M.choose b : ℝ) ≤ (2 : ℝ) ^ (((2 * Nat.clog 2 C₁ + 6) * b : ℕ) : ℝ) := by
    have h1 : (M.choose b : ℝ) ≤ (M : ℝ) ^ b / (b.factorial : ℝ) := Nat.choose_le_pow_div b M
    have hM_cast : (M : ℝ) = (21 * (C₁ : ℝ) ^ 2) * (b : ℝ) := by dsimp [M]; push_cast; ring
    have h2 : (M : ℝ) ^ b / (b.factorial : ℝ) =
        (21 * (C₁ : ℝ) ^ 2) ^ b * ((b : ℝ) ^ b / (b.factorial : ℝ)) := by
      rw [hM_cast, mul_pow, mul_div_assoc]
    have hexp3 : (b : ℝ) ^ b / (b.factorial : ℝ) ≤ (3 : ℝ) ^ b := by
      have he : Real.exp (b : ℝ) ≤ (3 : ℝ) ^ b := by
        have heb : Real.exp (b : ℝ) = (Real.exp 1) ^ b := by simp
        have he3 : Real.exp 1 ≤ 3 := by linarith [Real.exp_one_lt_d9]
        rw [heb]
        exact pow_le_pow_left₀ (le_of_lt (Real.exp_pos 1)) he3 b
      exact le_trans (Real.pow_div_factorial_le_exp (b : ℝ) (Nat.cast_nonneg b) b) he
    have hC_pow : C₁ ≤ 2 ^ Nat.clog 2 C₁ := Nat.le_pow_clog (by decide : 1 < 2) C₁
    have hC_r : (C₁ : ℝ) ≤ (2 : ℝ) ^ Nat.clog 2 C₁ := by exact_mod_cast hC_pow
    have hbase : 63 * (C₁ : ℝ) ^ 2 ≤ (2 : ℝ) ^ (2 * Nat.clog 2 C₁ + 6) := by
      calc
        63 * (C₁ : ℝ) ^ 2 ≤ 64 * ((2 : ℝ) ^ Nat.clog 2 C₁) ^ 2 := by
          have hsq : (C₁ : ℝ) ^ 2 ≤ ((2 : ℝ) ^ Nat.clog 2 C₁) ^ 2 :=
            pow_le_pow_left₀ (Nat.cast_nonneg C₁) hC_r 2
          nlinarith [show (0 : ℝ) ≤ ((2 : ℝ) ^ Nat.clog 2 C₁) ^ 2 by positivity]
        _ = (2 : ℝ) ^ (2 * Nat.clog 2 C₁ + 6) := by
          rw [show (64 : ℝ) = (2 : ℝ) ^ 6 by norm_num, ← pow_mul, ← pow_add]
          congr 1; omega
    have h12 : (M.choose b : ℝ) ≤ (21 * (C₁ : ℝ) ^ 2) ^ b * (3 : ℝ) ^ b := by
      calc
        (M.choose b : ℝ) ≤ (M : ℝ) ^ b / (b.factorial : ℝ) := h1
        _ = (21 * (C₁ : ℝ) ^ 2) ^ b * ((b : ℝ) ^ b / (b.factorial : ℝ)) := h2
        _ ≤ (21 * (C₁ : ℝ) ^ 2) ^ b * (3 : ℝ) ^ b :=
            mul_le_mul_of_nonneg_left hexp3 (by positivity)
    calc
      (M.choose b : ℝ) ≤ (21 * (C₁ : ℝ) ^ 2) ^ b * (3 : ℝ) ^ b := h12
      _ = (63 * (C₁ : ℝ) ^ 2) ^ b := by rw [← mul_pow]; congr 1; ring
      _ ≤ ((2 : ℝ) ^ (2 * Nat.clog 2 C₁ + 6)) ^ b := pow_le_pow_left₀ (by positivity) hbase b
      _ = (2 : ℝ) ^ (((2 * Nat.clog 2 C₁ + 6) * b : ℕ) : ℝ) := by
        rw [← pow_mul, ← Real.rpow_natCast]
  have hsub : R_set.powerset.filter (fun G => G.card ≤ b) ⊆
      (Finset.range (b + 1)).biUnion (fun t => R_set.powersetCard t) := by
    intro G hG
    simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_biUnion,
      Finset.mem_range, Finset.mem_powersetCard] at hG ⊢
    exact ⟨G.card, Nat.lt_succ_of_le hG.2, hG.1, rfl⟩
  have hcard_nat : (R_set.powerset.filter (fun G => G.card ≤ b)).card ≤ (b + 1) * M.choose b := by
    calc
      (R_set.powerset.filter (fun G => G.card ≤ b)).card
        ≤ ((Finset.range (b + 1)).biUnion (fun t => R_set.powersetCard t)).card :=
          Finset.card_le_card hsub
      _ ≤ ∑ t ∈ Finset.range (b + 1), (R_set.powersetCard t).card := Finset.card_biUnion_le
      _ ≤ ∑ _t ∈ Finset.range (b + 1), M.choose b := by
          refine Finset.sum_le_sum (fun t ht => ?_)
          rw [Finset.card_powersetCard]
          exact le_trans (Nat.choose_le_choose t hR_le_M)
            (hchoose_mono M t b h2b_le_M (Nat.lt_succ_iff.mp (Finset.mem_range.mp ht)))
      _ = (b + 1) * M.choose b := by rw [Finset.sum_const, Finset.card_range, smul_eq_mul]
  calc
    ((R_set.powerset.filter (fun G => G.card ≤ b)).card : ℝ)
      ≤ ((b + 1 : ℕ) : ℝ) * (M.choose b : ℝ) := by exact_mod_cast hcard_nat
    _ ≤ ((b + 1 : ℕ) : ℝ) * (2 : ℝ) ^ (((2 * Nat.clog 2 C₁ + 6) * b : ℕ) : ℝ) :=
      mul_le_mul_of_nonneg_left hMb_le (Nat.cast_nonneg _)

private lemma candMWit_card_and_quad {N q : ℕ} (C₁ r_star m : ℕ)
    (hC₁ : 3 ≤ C₁) (hr : 1000 * C₁ < r_star)
    (a b : Fin N → Fin q) (z_prev : Fin m → (Fin N → Fin q)) (x : Fin N → Fin q)
    (hd_xa : dHam x a ≤ C₁ * r_star) (hd_xb : dHam x b ≤ C₁ * r_star) :
    let M := candMFresh a b m z_prev x
    ((candMWit C₁ r_star a b m z_prev x).card : ℝ) ≤
      (2 : ℝ) ^ (3 * (r_star : ℝ) + (1 / 10 : ℝ) * (cspLam0 C₁ : ℝ) * (M.card : ℝ)) ∧
    ∀ w ∈ candMWit C₁ r_star a b m z_prev x,
      (∀ uv ∈ candA2 C₁ a b x M w, uv.1 ≠ uv.2) ∧
      40 * ((M.card : ℤ) ^ 2 - 2 * ((candA2 C₁ a b x M w).card : ℤ)) ≤
        23 * (r_star : ℤ) * (M.card : ℤ) := by
  intro M
  let K_max := cspKMax C₁
  let W_ab := diffCoords x a ∪ diffCoords x b
  have hM_sub_W : M ⊆ W_ab := by
    intro v hv
    simp only [M, candMFresh, cspRvc, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_union, Finset.mem_image] at hv
    simp only [W_ab, diffCoords, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
    refine Or.inl (fun hxa => hv (Or.inl (Or.inl ⟨v, hxa.symm ▸ rfl⟩)))
  have hW_card : W_ab.card ≤ 2 * C₁ * r_star := by
    have h1 := Finset.card_union_le (diffCoords x a) (diffCoords x b)
    have h2 : (diffCoords x a).card ≤ C₁ * r_star := hd_xa
    have h3 : (diffCoords x b).card ≤ C₁ * r_star := hd_xb
    calc
      W_ab.card ≤ C₁ * r_star + C₁ * r_star := le_trans h1 (Nat.add_le_add h2 h3)
      _ = 2 * C₁ * r_star := by ring
  constructor
  · -- Witness cardinality bound
    let base := (Finset.univ : Finset (Fin (K_max + 1))) ×ˢ
      (Fintype.piFinset (fun u : Fin N =>
        if u ∈ M then Finset.univ else ({0} : Finset (Fin (K_max + 1)))) ×ˢ
        Fintype.piFinset (fun _ : Fin K_max => M.powerset))
    let s_hat := fun (k : Fin (K_max + 1)) (τ : Fin N → Fin (K_max + 1)) (r : Fin K_max) =>
      if r.1 < k.1 then (M.filter (fun u => τ u = r.succ)).card - (11 * r_star) / 40 else 0
    have hcard_le1 : (candMWit C₁ r_star a b m z_prev x).card ≤
        ∑ ktB ∈ base, (((Finset.univ : Finset (Fin K_max)) ×ˢ W_ab).card).choose
          (∑ r : Fin K_max, s_hat ktB.1 ktB.2.1 r) := by
      have h1 : (candMWit C₁ r_star a b m z_prev x).card ≤
          (base.biUnion (fun ktB =>
            (((Finset.univ : Finset (Fin K_max)) ×ˢ W_ab).powersetCard
              (∑ r : Fin K_max, s_hat ktB.1 ktB.2.1 r)).image
              (fun U_out => (ktB.1, ktB.2.1, ktB.2.2, U_out)))).card :=
        Finset.card_filter_le _ _
      refine le_trans h1 (le_trans Finset.card_biUnion_le (Finset.sum_le_sum (fun ktB _ => ?_)))
      exact le_trans Finset.card_image_le (le_of_eq (Finset.card_powersetCard _ _))
    have hU_card : ((Finset.univ : Finset (Fin K_max)) ×ˢ W_ab).card ≤ 16 * C₁ ^ 2 * r_star := by
      rw [Finset.card_product, Finset.card_univ, Fintype.card_fin]
      calc
        K_max * W_ab.card ≤ (8 * C₁) * (2 * C₁ * r_star) :=
          Nat.mul_le_mul_left K_max hW_card
        _ = 16 * C₁ ^ 2 * r_star := by ring
    have hS_le : ∀ ktB : Fin (K_max + 1) × (Fin N → Fin (K_max + 1)) × (Fin K_max → Finset (Fin N)),
        ∑ r : Fin K_max, s_hat ktB.1 ktB.2.1 r ≤ M.card := by
      intro ktB
      have hle1 : ∑ r : Fin K_max, s_hat ktB.1 ktB.2.1 r ≤
          ∑ r : Fin K_max, (M.filter (fun u => ktB.2.1 u = r.succ)).card := by
        refine Finset.sum_le_sum (fun r _ => ?_)
        dsimp [s_hat]
        split_ifs
        · exact Nat.sub_le _ _
        · exact Nat.zero_le _
      have hdisj : ((Finset.univ : Finset (Fin K_max)) : Set (Fin K_max)).PairwiseDisjoint
          (fun r => M.filter (fun u => ktB.2.1 u = r.succ)) := by
        intro r₁ _ r₂ _ hne
        rw [Function.onFun, Finset.disjoint_left]
        intro u hu₁ hu₂
        simp only [Finset.mem_filter] at hu₁ hu₂
        exact hne (Fin.succ_injective _ (hu₁.2.symm.trans hu₂.2))
      have hsub : (Finset.univ : Finset (Fin K_max)).biUnion
          (fun r => M.filter (fun u => ktB.2.1 u = r.succ)) ⊆ M := by
        intro u hu
        rcases Finset.mem_biUnion.mp hu with ⟨_, _, huM⟩
        exact (Finset.mem_filter.mp huM).1
      rw [← Finset.card_biUnion hdisj] at hle1
      exact le_trans hle1 (Finset.card_le_card hsub)
    have hbase_card : base.card =
        (K_max + 1) * ((K_max + 1) ^ M.card * (2 ^ M.card) ^ K_max) := by
      dsimp [base]
      rw [Finset.card_product, Finset.card_product, Finset.card_univ, Fintype.card_fin,
        Fintype.card_piFinset, Fintype.card_piFinset]
      have htau : ∀ u : Fin N,
          (if u ∈ M then Finset.univ else ({0} : Finset (Fin (K_max + 1)))).card =
            if u ∈ M then K_max + 1 else 1 := by
        intro u
        split_ifs
        · rw [Finset.card_univ, Fintype.card_fin]
        · exact Finset.card_singleton 0
      simp_rw [htau, Finset.card_powerset]
      rw [Finset.prod_ite_mem, Finset.univ_inter, Finset.prod_const,
        Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    have hsum_r : ((candMWit C₁ r_star a b m z_prev x).card : ℝ) ≤
        (base.card : ℝ) * ((16 * (C₁ : ℝ) ^ 2) ^ M.card * (4 : ℝ) ^ r_star) := by
      have hc : ((candMWit C₁ r_star a b m z_prev x).card : ℝ) ≤
          ∑ ktB ∈ base, ((((Finset.univ : Finset (Fin K_max)) ×ˢ W_ab).card).choose
            (∑ r : Fin K_max, s_hat ktB.1 ktB.2.1 r) : ℝ) := by
        exact_mod_cast hcard_le1
      calc
        ((candMWit C₁ r_star a b m z_prev x).card : ℝ)
          ≤ ∑ ktB ∈ base, ((((Finset.univ : Finset (Fin K_max)) ×ˢ W_ab).card).choose
              (∑ r : Fin K_max, s_hat ktB.1 ktB.2.1 r) : ℝ) := hc
        _ ≤ ∑ _ktB ∈ base, ((16 * (C₁ : ℝ) ^ 2) ^ M.card * (4 : ℝ) ^ r_star) := by
            refine Finset.sum_le_sum (fun ktB _ => ?_)
            have hch := choose_bound_exp4 (((Finset.univ : Finset (Fin K_max)) ×ˢ W_ab).card)
              (∑ r : Fin K_max, s_hat ktB.1 ktB.2.1 r) M.card r_star (16 * C₁ ^ 2)
              (by nlinarith) hU_card (hS_le ktB)
            simpa using hch
        _ = (base.card : ℝ) * ((16 * (C₁ : ℝ) ^ 2) ^ M.card * (4 : ℝ) ^ r_star) := by
            rw [Finset.sum_const, nsmul_eq_mul]
    have hconst_r : ((K_max + 1 : ℕ) : ℝ) * (4 : ℝ) ^ r_star ≤ (2 : ℝ) ^ (3 * (r_star : ℝ)) := by
      have hk_r : K_max + 1 ≤ 2 ^ r_star := by
        have hk1 : K_max + 1 ≤ r_star := by dsimp [K_max, cspKMax]; omega
        exact le_trans hk1 (le_of_lt Nat.lt_two_pow_self)
      have hk_real : ((K_max + 1 : ℕ) : ℝ) ≤ (2 : ℝ) ^ (r_star : ℝ) := by
        have hc : ((K_max + 1 : ℕ) : ℝ) ≤ ((2 ^ r_star : ℕ) : ℝ) := by exact_mod_cast hk_r
        rwa [Nat.cast_pow, Nat.cast_ofNat, ← Real.rpow_natCast] at hc
      have h4_eq : (4 : ℝ) ^ r_star = (2 : ℝ) ^ (2 * (r_star : ℝ)) := by
        rw [show (4 : ℝ) = (2 : ℝ) ^ (2 : ℕ) by norm_num, ← pow_mul, ← Real.rpow_natCast]
        push_cast; rfl
      calc
        ((K_max + 1 : ℕ) : ℝ) * (4 : ℝ) ^ r_star
          ≤ (2 : ℝ) ^ (r_star : ℝ) * (2 : ℝ) ^ (2 * (r_star : ℝ)) := by
            rw [h4_eq]; exact mul_le_mul_of_nonneg_right hk_real (by positivity)
        _ = (2 : ℝ) ^ (3 * (r_star : ℝ)) := by
            rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]; congr 1; ring
    have hper_s : ((K_max + 1 : ℕ) : ℝ) * (2 : ℝ) ^ K_max * (16 * (C₁ : ℝ) ^ 2) ≤
        (2 : ℝ) ^ ((1 / 10 : ℝ) * (cspLam0 C₁ : ℝ)) := by
      have hk_pow : K_max + 1 ≤ 2 ^ K_max := Nat.lt_two_pow_self
      have hC_pow : C₁ ≤ 2 ^ Nat.clog 2 C₁ := Nat.le_pow_clog (by decide : 1 < 2) C₁
      have hnat : (K_max + 1) * 2 ^ K_max * (16 * C₁ ^ 2) ≤
          2 ^ (10 * C₁ * (2 * Nat.clog 2 C₁ + 6)) := by
        have h1 : (K_max + 1) * 2 ^ K_max * (16 * C₁ ^ 2) ≤
            2 ^ K_max * 2 ^ K_max * (2 ^ 4 * (2 ^ Nat.clog 2 C₁) ^ 2) := by
          have hC2 : C₁ ^ 2 ≤ (2 ^ Nat.clog 2 C₁) ^ 2 := Nat.pow_le_pow_left hC_pow 2
          have h16 : 16 * C₁ ^ 2 ≤ 2 ^ 4 * (2 ^ Nat.clog 2 C₁) ^ 2 := by
            simpa using Nat.mul_le_mul_left 16 hC2
          exact Nat.mul_le_mul (Nat.mul_le_mul_right _ hk_pow) h16
        have h2 : 2 ^ K_max * 2 ^ K_max * (2 ^ 4 * (2 ^ Nat.clog 2 C₁) ^ 2) =
            2 ^ (2 * K_max + 4 + 2 * Nat.clog 2 C₁) := by
          rw [← pow_mul (2 : ℕ) (Nat.clog 2 C₁) 2,
            show Nat.clog 2 C₁ * 2 = 2 * Nat.clog 2 C₁ by ring,
            ← pow_add, ← pow_add, ← pow_add]
          congr 1; omega
        have hclog_ge2 := (lam0_ge_1000_C1 C₁ hC₁).1
        have hexp : 2 * K_max + 4 + 2 * Nat.clog 2 C₁ ≤ 10 * C₁ * (2 * Nat.clog 2 C₁ + 6) := by
          dsimp [K_max, cspKMax]
          have h10 : 10 ≤ 2 * Nat.clog 2 C₁ + 6 := by omega
          nlinarith
        rw [h2] at h1
        exact le_trans h1 (Nat.pow_le_pow_right (by norm_num) hexp)
      have hcast : ((K_max + 1 : ℕ) : ℝ) * (2 : ℝ) ^ K_max * (16 * (C₁ : ℝ) ^ 2) ≤
          ((2 ^ (10 * C₁ * (2 * Nat.clog 2 C₁ + 6)) : ℕ) : ℝ) := by
        exact_mod_cast hnat
      refine le_trans hcast (le_of_eq ?_)
      rw [Nat.cast_pow, Nat.cast_ofNat, ← Real.rpow_natCast]
      congr 1
      dsimp [cspLam0]
      push_cast
      ring
    have hrew_base : (base.card : ℝ) * ((16 * (C₁ : ℝ) ^ 2) ^ M.card * (4 : ℝ) ^ r_star) =
        (((K_max + 1 : ℕ) : ℝ) * (4 : ℝ) ^ r_star) *
          (((K_max + 1 : ℕ) : ℝ) * (2 : ℝ) ^ K_max * (16 * (C₁ : ℝ) ^ 2)) ^ M.card := by
      rw [hbase_card]
      push_cast
      rw [pow_right_comm (2 : ℝ) M.card K_max]
      repeat rw [mul_pow]
      ring
    calc
      ((candMWit C₁ r_star a b m z_prev x).card : ℝ)
        ≤ (((K_max + 1 : ℕ) : ℝ) * (4 : ℝ) ^ r_star) *
            (((K_max + 1 : ℕ) : ℝ) * (2 : ℝ) ^ K_max * (16 * (C₁ : ℝ) ^ 2)) ^ M.card := by
          rwa [hrew_base] at hsum_r
      _ ≤ (2 : ℝ) ^ (3 * (r_star : ℝ)) *
            ((2 : ℝ) ^ ((1 / 10 : ℝ) * (cspLam0 C₁ : ℝ))) ^ M.card :=
          mul_le_mul hconst_r (pow_le_pow_left₀ (by positivity) hper_s M.card)
            (by positivity) (by positivity)
      _ = (2 : ℝ) ^ (3 * (r_star : ℝ) + (1 / 10 : ℝ) * (cspLam0 C₁ : ℝ) * (M.card : ℝ)) := by
          rw [← Real.rpow_natCast ((2 : ℝ) ^ _) M.card,
            ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),
            ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
  · -- Disjointness (uv.1 ≠ uv.2) and quadratic residual bound
    intro w hw
    have hw_filt := (Finset.mem_filter.mp hw).2
    let k := w.1
    let τ := w.2.1
    let B_fut := w.2.2.1
    let U_out := w.2.2.2
    rcases hw_filt with ⟨hτ_le, htail_le, hr_props⟩
    let M_piece := fun r : Fin K_max => M.filter (fun u => τ u = r.succ)
    let I_tilde := fun r : Fin K_max => M.filter (fun u => τ u = 0 ∨ r.1 + 1 < (τ u).1)
    let B_out := fun r : Fin K_max => W_ab.filter (fun v => (r, v) ∈ U_out)
    refine ⟨?_, ?_⟩
    · rintro ⟨u, v⟩ huv
      simp only [candA2, Finset.mem_filter, Finset.mem_product] at huv
      rcases huv with ⟨⟨huM, hvW⟩, r, hrk, hτu, hvB⟩
      obtain ⟨hBf_sub, _, hBo_disj, _⟩ := hr_props r hrk
      dsimp only
      intro heq
      subst heq
      rcases hvB with hvf | hvo
      · have huI := (Finset.mem_filter.mp (hBf_sub hvf)).2
        rw [hτu] at huI
        rcases huI with h0 | hlt
        · exact Fin.succ_ne_zero r h0
        · simp at hlt
      · have huBo : u ∈ B_out r := Finset.mem_filter.mpr ⟨hvW, hvo⟩
        have huMr : u ∈ M_piece r := Finset.mem_filter.mpr ⟨huM, hτu⟩
        exact Finset.disjoint_left.mp hBo_disj huBo (Finset.mem_union_left _ huMr)
    · -- Exact card of candA2
      let R_lt := (Finset.univ : Finset (Fin K_max)).filter (fun r => r.1 < k.1)
      have hA2_eq : candA2 C₁ a b x M w =
          R_lt.biUnion (fun r => M_piece r ×ˢ (B_fut r ∪ B_out r)) := by
        ext ⟨u, v⟩
        simp only [candA2, R_lt, M_piece, B_out, Finset.mem_filter, Finset.mem_product,
          Finset.mem_biUnion, Finset.mem_univ, true_and]
        constructor
        · rintro ⟨⟨huM, hvW⟩, r, hrk, hτu, hvf | hvo⟩
          · exact ⟨r, hrk, ⟨huM, hτu⟩, Finset.mem_union_left _ hvf⟩
          · exact ⟨r, hrk, ⟨huM, hτu⟩, Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hvW, hvo⟩)⟩
        · rintro ⟨r, hrk, ⟨huM, hτu⟩, hv⟩
          rcases Finset.mem_union.mp hv with hvf | hvo
          · have hvfM : v ∈ M := (Finset.mem_filter.mp ((hr_props r hrk).1 hvf)).1
            exact ⟨⟨huM, hM_sub_W hvfM⟩, r, hrk, hτu, Or.inl hvf⟩
          · rcases Finset.mem_filter.mp hvo with ⟨hvW, hvoU⟩
            exact ⟨⟨huM, hvW⟩, r, hrk, hτu, Or.inr hvoU⟩
      have hA2_disj : (R_lt : Set (Fin K_max)).PairwiseDisjoint
          (fun r => M_piece r ×ˢ (B_fut r ∪ B_out r)) := by
        intro r₁ _ r₂ _ hne
        rw [Function.onFun, Finset.disjoint_left]
        rintro ⟨u, v⟩ h₁ h₂
        simp only [M_piece, Finset.mem_product, Finset.mem_filter] at h₁ h₂
        exact hne (Fin.succ_injective _ (h₁.1.2.symm.trans h₂.1.2))
      have hA2_card : (candA2 C₁ a b x M w).card =
          ∑ r ∈ R_lt, (M_piece r).card * ((B_fut r).card + (B_out r).card) := by
        rw [hA2_eq, Finset.card_biUnion hA2_disj]
        refine Finset.sum_congr rfl (fun r hr => ?_)
        have hrk : r.1 < k.1 := (Finset.mem_filter.mp hr).2
        obtain ⟨hBf_sub, _, hBo_disj, _⟩ := hr_props r hrk
        have hdisj_f_o : Disjoint (B_fut r) (B_out r) := by
          rw [Finset.disjoint_left]
          intro z hzf hzo
          exact Finset.disjoint_left.mp hBo_disj hzo (Finset.mem_union_right _ (hBf_sub hzf))
        rw [Finset.card_product, Finset.card_union_of_disjoint hdisj_f_o]
      -- Backward induction on suffix j = k.1 - d
      let Suf := fun j : ℕ => M.filter (fun u => τ u = 0 ∨ j < (τ u).1)
      let A2_suf := fun j : ℕ =>
        ∑ r ∈ R_lt.filter (fun r => j ≤ r.1),
          (M_piece r).card * ((B_fut r).card + (B_out r).card)
      have h_ind : ∀ d : ℕ, d ≤ k.1 →
          40 * (((Suf (k.1 - d)).card : ℤ) ^ 2 - 2 * (A2_suf (k.1 - d) : ℤ)) ≤
            23 * (r_star : ℤ) * ((Suf (k.1 - d)).card : ℤ) := by
        intro d
        induction d with
        | zero =>
          intro _
          simp only [Nat.sub_zero]
          have hSuf_k : Suf k.1 = M.filter (fun u => τ u = 0) := by
            ext u
            simp only [Suf, Finset.mem_filter]
            constructor
            · rintro ⟨huM, h0 | hgt⟩
              · exact ⟨huM, h0⟩
              · exact absurd (hτ_le u huM) (not_le_of_gt hgt)
            · rintro ⟨huM, h0⟩
              exact ⟨huM, Or.inl h0⟩
          have hA2_k : A2_suf k.1 = 0 := by
            apply Finset.sum_eq_zero
            intro r hr
            simp only [R_lt, Finset.mem_filter, Finset.mem_univ, true_and] at hr
            omega
          rw [hSuf_k, hA2_k]
          have ht_int : 2 * (((M.filter (fun u => τ u = 0)).card : ℤ)) ≤ (r_star : ℤ) := by
            exact_mod_cast htail_le
          have ht_nn : (0 : ℤ) ≤ ((M.filter (fun u => τ u = 0)).card : ℤ) := Nat.cast_nonneg _
          nlinarith
        | succ d ih =>
          intro hd1
          let j := k.1 - (d + 1)
          have hjk : j < k.1 := by omega
          have hkd_eq : k.1 - d = j + 1 := by omega
          have hih := ih (by omega)
          rw [hkd_eq] at hih
          have hjK : j < K_max := lt_of_lt_of_le hjk (Nat.le_of_lt_succ k.2)
          let r0 : Fin K_max := ⟨j, hjK⟩
          have hr0_val : r0.1 = j := rfl
          have hr0_lt : r0.1 < k.1 := hjk
          obtain ⟨hBf_sub, hmiss_le, _, hBo_card⟩ := hr_props r0 hr0_lt
          have hSuf_split : Suf j = M_piece r0 ∪ Suf (j + 1) := by
            ext u
            simp only [Suf, M_piece, Finset.mem_union, Finset.mem_filter, Fin.ext_iff,
              Fin.val_succ, Fin.val_zero]
            rw [hr0_val]
            by_cases hu : u ∈ M
            · simp only [hu, true_and]
              omega
            · simp [hu]
          have hSuf_disj : Disjoint (M_piece r0) (Suf (j + 1)) := by
            rw [Finset.disjoint_left]
            intro u hu1 hu2
            simp only [M_piece, Suf, Finset.mem_filter, Fin.ext_iff,
              Fin.val_succ, Fin.val_zero] at hu1 hu2
            rw [hr0_val] at hu1
            omega
          have hSuf_card : (Suf j).card = (M_piece r0).card + (Suf (j + 1)).card := by
            rw [hSuf_split, Finset.card_union_of_disjoint hSuf_disj]
          have hA2_split : A2_suf j =
              (M_piece r0).card * ((B_fut r0).card + (B_out r0).card) + A2_suf (j + 1) := by
            have hset : R_lt.filter (fun r => j ≤ r.1) =
                insert r0 (R_lt.filter (fun r => j + 1 ≤ r.1)) := by
              ext r
              simp only [R_lt, Finset.mem_insert, Finset.mem_filter, Finset.mem_univ,
                true_and, Fin.ext_iff]
              rw [hr0_val]
              omega
            have hnot : r0 ∉ R_lt.filter (fun r => j + 1 ≤ r.1) := by
              simp [r0]
            dsimp [A2_suf]
            rw [hset, Finset.sum_insert hnot]
          have hIt_eq : I_tilde r0 = Suf (j + 1) := rfl
          have hsdiff_card : (Suf (j + 1)).card =
              (I_tilde r0 \ B_fut r0).card + (B_fut r0).card := by
            rw [← hIt_eq, Finset.card_sdiff_add_card_eq_card hBf_sub]
          have hBo_card' : (B_out r0).card = (M_piece r0).card - (11 * r_star) / 40 := hBo_card
          have hBo_ineq : 40 * (M_piece r0).card ≤ 40 * (B_out r0).card + 11 * r_star := by
            rw [hBo_card']
            omega
          -- Finish step in ℤ
          set a_c : ℤ := ((M_piece r0).card : ℤ)
          set b_c : ℤ := ((Suf (j + 1)).card : ℤ)
          set f_c : ℤ := ((B_fut r0).card : ℤ)
          set m_c : ℤ := ((I_tilde r0 \ B_fut r0).card : ℤ)
          set o_c : ℤ := ((B_out r0).card : ℤ)
          have ha_nn : 0 ≤ a_c := Nat.cast_nonneg _
          have hbmf : b_c = m_c + f_c := by
            dsimp only [b_c, m_c, f_c]
            exact_mod_cast hsdiff_card
          have hmiss_le' : 80 * (I_tilde r0 \ B_fut r0).card ≤ r_star := hmiss_le
          have hm80 : 80 * m_c ≤ (r_star : ℤ) := by
            dsimp only [m_c]
            exact_mod_cast hmiss_le'
          have ho40 : 40 * a_c ≤ 40 * o_c + 11 * (r_star : ℤ) := by
            have hc : ((40 * (M_piece r0).card : ℕ) : ℤ) ≤
                ((40 * (B_out r0).card + 11 * r_star : ℕ) : ℤ) := by exact_mod_cast hBo_ineq
            push_cast at hc
            exact hc
          change 40 * (((Suf j).card : ℤ) ^ 2 - 2 * (A2_suf j : ℤ)) ≤
            23 * (r_star : ℤ) * ((Suf j).card : ℤ)
          rw [hSuf_card, hA2_split]
          push_cast
          change 40 * ((a_c + b_c) ^ 2 - 2 * (a_c * (f_c + o_c) + (A2_suf (j + 1) : ℤ))) ≤
            23 * (r_star : ℤ) * (a_c + b_c)
          have hterm_miss : 80 * a_c * (b_c - f_c) ≤ (r_star : ℤ) * a_c := by
            have hbf : b_c - f_c = m_c := by linarith
            rw [hbf]
            nlinarith
          have hterm_out : 40 * (a_c ^ 2 - 2 * a_c * o_c) ≤ 22 * (r_star : ℤ) * a_c := by
            have hsq_nn : 0 ≤ 40 * a_c ^ 2 := by positivity
            nlinarith
          nlinarith
      have h0 := h_ind k.1 (le_refl k.1)
      simp only [Nat.sub_self] at h0
      have hSuf0 : Suf 0 = M := by
        ext u
        simp only [Suf, Finset.mem_filter, Fin.ext_iff, Fin.val_zero]
        constructor
        · exact fun h => h.1
        · intro hu; exact ⟨hu, by omega⟩
      have hA2_0 : A2_suf 0 = (candA2 C₁ a b x M w).card := by
        rw [hA2_card]
        dsimp [A2_suf]
        congr 1
        ext r
        simp
      rwa [hSuf0, hA2_0] at h0

private lemma candMWit_proj {N q : ℕ} (C₁ r_star m : ℕ)
    (a b : Fin N → Fin q) (z_prev : Fin m → (Fin N → Fin q)) (x : Fin N → Fin q)
    (ω : cspIota N q → Bool) (hω_keep : ω (Sum.inr x) = true)
    (hx_wit : x ∈ bicliqueWitnessList (symROf ω) C₁ r_star a b) :
    ∃ w ∈ candMWit C₁ r_star a b m z_prev x,
      ∀ i ∈ candQCand C₁ a b m z_prev x w, ω i = true := by
  let K_max := cspKMax C₁
  let M := candMFresh a b m z_prev x
  let W_ab := diffCoords x a ∪ diffCoords x b
  have hdiff_eq : ∀ y z : Fin N → Fin q, diffCoords y z = disagreeSet y z := fun _ _ => rfl
  have hM_sub_I : M ⊆ disagreeSet x a ∩ disagreeSet x b := by
    intro v hv
    simp only [M, candMFresh, cspRvc, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_union, Finset.mem_image] at hv
    simp only [disagreeSet, Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun h => hv (Or.inl (Or.inl ⟨v, h ▸ rfl⟩)),
           fun h => hv (Or.inl (Or.inr ⟨v, h ▸ rfl⟩))⟩
  simp only [bicliqueWitnessList, satisfyingSet, Finset.mem_filter, Finset.mem_univ,
    true_and] at hx_wit
  rcases hx_wit with ⟨hx_hom, _, _, _, _, k, hk_le, A, B_fut₀, B_out₀, I_k,
    hA_disj, hAIk_disj, hpart, hIk_card, hr_all⟩
  have hk_Kmax : k ≤ K_max := hk_le
  let k_fin : Fin (K_max + 1) := ⟨k, Nat.lt_succ_of_le hk_Kmax⟩
  let τ : Fin N → Fin (K_max + 1) := fun u =>
    if u ∈ M then
      if h : ∃ r : Fin k, u ∈ A r then
        (⟨(Classical.choose h).1, lt_of_lt_of_le (Classical.choose h).2 hk_Kmax⟩ : Fin K_max).succ
      else 0
    else 0
  have hτ_zero_iff : ∀ u ∈ M, τ u = 0 ↔ u ∈ I_k := by
    intro u huM
    dsimp [τ]
    rw [if_pos huM]
    have huI : u ∈ Finset.univ.biUnion A ∪ I_k := hpart.symm ▸ hM_sub_I huM
    by_cases hex : ∃ r : Fin k, u ∈ A r
    · rw [dif_pos hex]
      have hne0 :
          (⟨(Classical.choose hex).1,
            lt_of_lt_of_le (Classical.choose hex).2 hk_Kmax⟩ : Fin K_max).succ ≠ 0 :=
        Fin.succ_ne_zero _
      obtain ⟨r, hur⟩ := hex
      have hnotIk : u ∉ I_k := Finset.disjoint_left.mp (hAIk_disj r) hur
      exact iff_of_false hne0 hnotIk
    · rw [dif_neg hex]
      simp only [Finset.mem_union, Finset.mem_biUnion, Finset.mem_univ, true_and] at huI
      rcases huI with ⟨r, hur⟩ | huIk
      · exact absurd ⟨r, hur⟩ hex
      · exact iff_of_true rfl huIk
  have hτ_succ_iff : ∀ (r : Fin K_max) (hr : r.1 < k), ∀ u ∈ M,
      τ u = r.succ ↔ u ∈ A ⟨r.1, hr⟩ := by
    intro r hr u huM
    dsimp only [τ]
    rw [if_pos huM]
    constructor
    · intro hτ
      by_cases hex : ∃ j : Fin k, u ∈ A j
      · rw [dif_pos hex] at hτ
        have hval : (Classical.choose hex).1 + 1 = r.1 + 1 := by
          simpa [Fin.ext_iff, Fin.val_succ] using hτ
        have hj_eq : Classical.choose hex = ⟨r.1, hr⟩ :=
          Fin.ext (by change (Classical.choose hex).1 = r.1; omega)
        exact hj_eq ▸ Classical.choose_spec hex
      · rw [dif_neg hex] at hτ
        exact absurd hτ.symm (Fin.succ_ne_zero r)
    · intro huA
      have hex : ∃ j : Fin k, u ∈ A j := ⟨⟨r.1, hr⟩, huA⟩
      rw [dif_pos hex]
      have hch_eq : Classical.choose hex = ⟨r.1, hr⟩ := by
        by_contra hne
        exact Finset.disjoint_left.mp (hA_disj hne) (Classical.choose_spec hex) huA
      ext
      simp [hch_eq]
  have hτ_le_k : ∀ u ∈ M, (τ u).1 ≤ k := by
    intro u huM
    dsimp [τ]
    rw [if_pos huM]
    split_ifs with hex
    · exact (Classical.choose hex).2
    · exact Nat.zero_le k
  have hIt_eq : ∀ (r : Fin K_max) (hr : r.1 < k),
      M.filter (fun u => τ u = 0 ∨ r.1 + 1 < (τ u).1) =
        M ∩ ((Finset.univ.filter (fun j : Fin k => (⟨r.1, hr⟩ : Fin k) < j)).biUnion A ∪ I_k) := by
    intro r hr
    ext u
    simp only [Finset.mem_filter, Finset.mem_inter, Finset.mem_union, Finset.mem_biUnion,
      Finset.mem_univ, true_and]
    constructor
    · rintro ⟨huM, h0 | hgt⟩
      · exact ⟨huM, Or.inr ((hτ_zero_iff u huM).mp h0)⟩
      · have hne0 : τ u ≠ 0 := by intro h; simp [h] at hgt
        have hle : (τ u).1 ≤ k := hτ_le_k u huM
        let j0 : Fin K_max := ⟨(τ u).1 - 1, lt_of_lt_of_le (by omega) hk_Kmax⟩
        have hj0_lt : j0.1 < k := by dsimp [j0]; omega
        have hτ_j0 : τ u = j0.succ := by ext; dsimp [j0]; omega
        have huAj0 : u ∈ A ⟨j0.1, hj0_lt⟩ := (hτ_succ_iff j0 hj0_lt u huM).mp hτ_j0
        refine ⟨huM, Or.inl ⟨⟨j0.1, hj0_lt⟩, ?_, huAj0⟩⟩
        simp only [Fin.lt_def, j0]; omega
    · rintro ⟨huM, ⟨j, hrj, huAj⟩ | huIk⟩
      · have hjK : j.1 < K_max := lt_of_lt_of_le j.2 hk_Kmax
        have hτj : τ u = (⟨j.1, hjK⟩ : Fin K_max).succ :=
          (hτ_succ_iff ⟨j.1, hjK⟩ j.2 u huM).mpr huAj
        refine ⟨huM, Or.inr ?_⟩
        rw [hτj, Fin.val_succ]
        dsimp only
        simp only [Fin.lt_def] at hrj
        omega
      · exact ⟨huM, Or.inl ((hτ_zero_iff u huM).mpr huIk)⟩
  let B_fut : Fin K_max → Finset (Fin N) := fun r =>
    if hr : r.1 < k then M ∩ B_fut₀ ⟨r.1, hr⟩ else ∅
  -- Choose exact-size subset B_sub r' ⊆ B_out₀ r' for each r' : Fin k
  let s_target : Fin k → ℕ := fun r' => (M ∩ A r').card - (11 * r_star) / 40
  have hs_le_Bo : ∀ r' : Fin k, s_target r' ≤ (B_out₀ r').card := by
    intro r'
    have hbo_real := (hr_all r').2.2.2.2
    have h40_r : (40 : ℝ) * ((A r').card : ℝ) ≤
        40 * ((B_out₀ r').card : ℝ) + 11 * (r_star : ℝ) := by linarith
    have h40_nat : 40 * (A r').card ≤ 40 * (B_out₀ r').card + 11 * r_star := by
      exact_mod_cast h40_r
    have hMA : (M ∩ A r').card ≤ (A r').card := Finset.card_le_card Finset.inter_subset_right
    dsimp [s_target]
    omega
  let B_sub : Fin k → Finset (Fin N) := fun r' =>
    Classical.choose (Finset.exists_subset_card_eq (hs_le_Bo r'))
  have hB_sub_spec : ∀ r' : Fin k, B_sub r' ⊆ B_out₀ r' ∧ (B_sub r').card = s_target r' :=
    fun r' => Classical.choose_spec (Finset.exists_subset_card_eq (hs_le_Bo r'))
  let U_out : Finset (Fin K_max × Fin N) :=
    (Finset.univ : Finset (Fin K_max)).biUnion (fun r =>
      if hr : r.1 < k then (B_sub ⟨r.1, hr⟩).image (fun v => (r, v)) else ∅)
  have hMr_eq : ∀ (r : Fin K_max) (hr : r.1 < k),
      M.filter (fun u => τ u = r.succ) = M ∩ A ⟨r.1, hr⟩ := by
    intro r hr
    ext u
    simp only [Finset.mem_filter, Finset.mem_inter]
    exact ⟨fun ⟨huM, h⟩ => ⟨huM, (hτ_succ_iff r hr u huM).mp h⟩,
           fun ⟨huM, h⟩ => ⟨huM, (hτ_succ_iff r hr u huM).mpr h⟩⟩
  have hBo_slice : ∀ (r : Fin K_max) (hr : r.1 < k),
      W_ab.filter (fun v => (r, v) ∈ U_out) = B_sub ⟨r.1, hr⟩ := by
    intro r hr
    ext v
    simp only [U_out, Finset.mem_filter, Finset.mem_biUnion, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨_, r', hmem⟩
      split_ifs at hmem with hr'
      · rcases Finset.mem_image.mp hmem with ⟨v', hv', hp⟩
        rcases Prod.mk.inj hp with ⟨rfl, rfl⟩
        exact hv'
      · simp at hmem
    · intro hv
      have hvW : v ∈ W_ab := by
        have hv0 : v ∈ B_out₀ ⟨r.1, hr⟩ := (hB_sub_spec ⟨r.1, hr⟩).1 hv
        have hv1 := (hr_all ⟨r.1, hr⟩).2.1 hv0
        exact (Finset.mem_sdiff.mp hv1).1
      refine ⟨hvW, r, ?_⟩
      rw [dif_pos hr]
      exact Finset.mem_image.mpr ⟨v, hv, rfl⟩
  let w : candWitType N C₁ := (k_fin, τ, B_fut, U_out)
  refine ⟨w, ?_, ?_⟩
  · -- w ∈ candMWit
    simp only [candMWit, Finset.mem_filter]
    refine ⟨?_, ?_, ?_, ?_⟩
    · -- w ∈ ambient biUnion
      rw [Finset.mem_biUnion]
      refine ⟨(k_fin, τ, B_fut), ?_, ?_⟩
      · simp only [Finset.mem_product, Finset.mem_univ, true_and,
          Fintype.mem_piFinset, Finset.mem_powerset]
        refine ⟨fun u => ?_, fun r => ?_⟩
        · split_ifs with huM
          · exact Finset.mem_univ _
          · dsimp only [τ]
            rw [if_neg huM]
            exact Finset.mem_singleton_self 0
        · dsimp [B_fut]
          split_ifs with hr
          · exact Finset.inter_subset_left
          · exact Finset.empty_subset _
      · rw [Finset.mem_image]
        refine ⟨U_out, ?_, rfl⟩
        rw [Finset.mem_powersetCard]
        refine ⟨?_, ?_⟩
        · intro rv hrv
          rcases Finset.mem_biUnion.mp hrv with ⟨r, _, hm⟩
          split_ifs at hm with hr
          · rcases Finset.mem_image.mp hm with ⟨v, hv, rfl⟩
            rw [Finset.mem_product]
            refine ⟨Finset.mem_univ r, ?_⟩
            have hv0 := (hB_sub_spec ⟨r.1, hr⟩).1 hv
            exact (Finset.mem_sdiff.mp ((hr_all ⟨r.1, hr⟩).2.1 hv0)).1
          · simp at hm
        · have hdisj : ((Finset.univ : Finset (Fin K_max)) : Set (Fin K_max)).PairwiseDisjoint
              (fun r : Fin K_max =>
                if hr : r.1 < k then (B_sub ⟨r.1, hr⟩).image (fun v => (r, v)) else ∅) := by
            intro r₁ _ r₂ _ hne
            rw [Function.onFun, Finset.disjoint_left]
            intro p hp1 hp2
            split_ifs at hp1 hp2 with hr1 hr2 hr2
            · rcases Finset.mem_image.mp hp1 with ⟨_, _, rfl⟩
              rcases Finset.mem_image.mp hp2 with ⟨_, _, hp⟩
              exact hne (Prod.mk.inj hp).1.symm
            · simp at hp2
            · simp at hp1
            · simp at hp1
          dsimp [U_out]
          rw [Finset.card_biUnion hdisj]
          refine Finset.sum_congr rfl (fun r _ => ?_)
          split_ifs with hr
          · rw [Finset.card_image_of_injective _ (fun _ _ h => (Prod.mk.inj h).2),
              (hB_sub_spec ⟨r.1, hr⟩).2, hMr_eq r hr]
          · simp
    · exact hτ_le_k
    · have htail_sub : M.filter (fun u => τ u = 0) ⊆ I_k := by
        intro u hu
        rcases Finset.mem_filter.mp hu with ⟨huM, h0⟩
        exact (hτ_zero_iff u huM).mp h0
      have h2Ik_r : (2 : ℝ) * (I_k.card : ℝ) ≤ (r_star : ℝ) := by linarith
      have h2Ik : 2 * I_k.card ≤ r_star := by exact_mod_cast h2Ik_r
      exact le_trans (Nat.mul_le_mul_left 2 (Finset.card_le_card htail_sub)) h2Ik
    · intro r hrk
      have hr : r.1 < k := hrk
      obtain ⟨hBf0_sub, hBo0_sub, _, hmiss0, _⟩ := hr_all ⟨r.1, hr⟩
      refine ⟨?_, ?_, ?_, ?_⟩
      · -- B_fut r ⊆ I_tilde r
        rw [hIt_eq r hr]
        dsimp [w, B_fut]
        rw [dif_pos hr]
        exact Finset.inter_subset_inter_left hBf0_sub
      · -- 80 * (I_tilde r \ B_fut r).card ≤ r_star
        have hsdiff_sub : M.filter (fun u => τ u = 0 ∨ r.1 + 1 < (τ u).1) \ B_fut r ⊆
            ((Finset.univ.filter (fun j : Fin k => (⟨r.1, hr⟩ : Fin k) < j)).biUnion A ∪ I_k) \
              B_fut₀ ⟨r.1, hr⟩ := by
          rw [hIt_eq r hr]
          dsimp [B_fut]
          rw [dif_pos hr]
          intro u hu
          simp only [Finset.mem_sdiff, Finset.mem_inter] at hu ⊢
          exact ⟨hu.1.2, fun h => hu.2 ⟨hu.1.1, h⟩⟩
        have h80_r : (80 : ℝ) *
            ((((Finset.univ.filter (fun j : Fin k => (⟨r.1, hr⟩ : Fin k) < j)).biUnion A ∪ I_k) \
              B_fut₀ ⟨r.1, hr⟩).card : ℝ) ≤ (r_star : ℝ) := by linarith
        have h80_nat : 80 *
            (((Finset.univ.filter (fun j : Fin k => (⟨r.1, hr⟩ : Fin k) < j)).biUnion A ∪ I_k) \
              B_fut₀ ⟨r.1, hr⟩).card ≤ r_star := by exact_mod_cast h80_r
        exact le_trans (Nat.mul_le_mul_left 80 (Finset.card_le_card hsdiff_sub)) h80_nat
      · -- Disjoint (B_out r) (M_r ∪ I_tilde r)
        change Disjoint (W_ab.filter (fun v => (r, v) ∈ U_out)) _
        rw [hBo_slice r hr, hMr_eq r hr, hIt_eq r hr, Finset.disjoint_left]
        intro v hv hmem
        have hv0 := hBo0_sub ((hB_sub_spec ⟨r.1, hr⟩).1 hv)
        rw [Finset.mem_sdiff] at hv0
        apply hv0.2
        rcases Finset.mem_union.mp hmem with h1 | h2
        · exact Finset.mem_union_left _ (Finset.mem_inter.mp h1).2
        · exact Finset.mem_union_right _ (Finset.mem_inter.mp h2).2
      · -- (B_out r).card = M_r.card - (11 * r_star) / 40
        change (W_ab.filter (fun v => (r, v) ∈ U_out)).card = _
        rw [hBo_slice r hr, hMr_eq r hr, (hB_sub_spec ⟨r.1, hr⟩).2]
  · -- ∀ i ∈ candQCand, ω i = true
    intro i hi
    simp only [candQCand, Finset.mem_union, Finset.mem_image, Finset.mem_singleton] at hi
    rcases hi with ⟨_, rfl, rfl⟩ | ⟨t, ht | ht, rfl⟩
    · exact hω_keep
    · rcases ht with ⟨⟨u, v⟩, huv, rfl⟩
      simp only [candA1, Finset.mem_filter, Finset.mem_univ, true_and] at huv
      simpa [symROf, if_pos huv.1] using hx_hom u v huv.1
    · rcases ht with ⟨⟨u, v⟩, huv, rfl⟩
      simp only [candA2, w, k_fin, Finset.mem_filter, Finset.mem_product] at huv
      rcases huv with ⟨⟨huM, hvW⟩, r, hrk, hτu, hvf | hvo⟩
      · have huA : u ∈ A ⟨r.1, hrk⟩ := (hτ_succ_iff r hrk u huM).mp hτu
        dsimp [B_fut] at hvf
        rw [dif_pos hrk] at hvf
        have hvBf0 : v ∈ B_fut₀ ⟨r.1, hrk⟩ := (Finset.mem_inter.mp hvf).2
        have hne_uv : u ≠ v := by
          intro heq; subst heq
          have huI := (Finset.mem_filter.mp
            ((hIt_eq r hrk).symm ▸ Finset.mem_inter.mpr ⟨huM, (hr_all ⟨r.1, hrk⟩).1 hvBf0⟩)).2
          rw [hτu] at huI
          rcases huI with h0 | hlt
          · exact Fin.succ_ne_zero r h0
          · simp at hlt
        have hrel := (hr_all ⟨r.1, hrk⟩).2.2.1 u huA v (Finset.mem_union_left _ hvBf0)
        dsimp [candPhi2]
        split_ifs with hlt
        · simpa [symROf, if_pos hlt, candCStar, activeColor] using hrel
        · have hgt : v < u := lt_of_le_of_ne (not_lt.mp hlt) (Ne.symm hne_uv)
          simpa [symROf, if_neg hlt, if_pos hgt, candCStar, activeColor] using hrel
      · have huA : u ∈ A ⟨r.1, hrk⟩ := (hτ_succ_iff r hrk u huM).mp hτu
        have hvBsub : v ∈ B_sub ⟨r.1, hrk⟩ := by
          rw [← hBo_slice r hrk]
          exact Finset.mem_filter.mpr ⟨hvW, hvo⟩
        have hvBo0 : v ∈ B_out₀ ⟨r.1, hrk⟩ := (hB_sub_spec ⟨r.1, hrk⟩).1 hvBsub
        have hne_uv : u ≠ v := by
          intro heq; subst heq
          have hv_sdiff := (hr_all ⟨r.1, hrk⟩).2.1 hvBo0
          exact (Finset.mem_sdiff.mp hv_sdiff).2 (Finset.mem_union_left _ huA)
        have hrel := (hr_all ⟨r.1, hrk⟩).2.2.1 u huA v (Finset.mem_union_right _ hvBo0)
        dsimp [candPhi2]
        split_ifs with hlt
        · simpa [symROf, if_pos hlt, candCStar, activeColor] using hrel
        · have hgt : v < u := lt_of_le_of_ne (not_lt.mp hlt) (Ne.symm hne_uv)
          simpa [symROf, if_neg hlt, if_pos hgt, candCStar, activeColor] using hrel


private theorem finite_bernoulli_cylinder_and_sequential_moment {ι : Type} [Fintype ι] [DecidableEq ι]
    (p : ι → ℝ) (hp : ∀ i : ι, 0 ≤ p i ∧ p i ≤ 1) :
    (∀ ω : ι → Bool, 0 ≤ bernWeight p ω) ∧
    (∑ ω : ι → Bool, bernWeight p ω = 1) ∧
    (∀ S : Finset ι,
      ∑ ω : ι → Bool, (if ∀ i ∈ S, ω i = true then bernWeight p ω else 0) = ∏ i ∈ S, p i) ∧
    (∀ (β γ : Type) [DecidableEq β] [DecidableEq γ]
      (Pool : Finset β) (K : ℕ) (α_step : ℝ),
      0 ≤ α_step →
      ∀ (Base : (ι → Bool) → Prop) [DecidablePred Base]
        (A : (ι → Bool) → Finset β),
        (∀ ω : ι → Bool, A ω ⊆ Pool) →
        ∀ (S₀ : Finset ι)
          (U : (m : ℕ) → (Fin m → β) → Finset ι)
          (M_wit : (m : ℕ) → (Fin m → β) → β → Finset γ)
          (Q : (m : ℕ) → (Fin m → β) → β → γ → Finset ι),
          (∀ z₀ : Fin 0 → β, S₀ ⊆ U 0 z₀) →
          (∀ m < K, ∀ (z_prev : Fin m → β) (b : β),
            U m z_prev ⊆ U (m + 1) (Fin.snoc z_prev b)) →
          (∀ m < K, ∀ z_prev : Fin m → β,
            Function.Injective z_prev → (∀ t : Fin m, z_prev t ∈ Pool) →
            ∀ b ∈ Pool \ Finset.univ.image z_prev, ∀ w ∈ M_wit m z_prev b,
              Q m z_prev b w ⊆ U (m + 1) (Fin.snoc z_prev b) \ U m z_prev) →
          (∀ ω : ι → Bool, Base ω →
            (∀ i ∈ S₀, ω i = true) ∧
            (∀ z : Fin K → β, Function.Injective z → (∀ m : Fin K, z m ∈ A ω) →
              ∀ m : Fin K,
                ∃ w ∈ M_wit m.1 (fun t : Fin m.1 => z (t.castLE (Nat.le_of_lt m.isLt))) (z m),
                  ∀ i ∈ Q m.1 (fun t : Fin m.1 => z (t.castLE (Nat.le_of_lt m.isLt))) (z m) w,
                    ω i = true)) →
          (∀ m < K, ∀ z_prev : Fin m → β,
            Function.Injective z_prev → (∀ t : Fin m, z_prev t ∈ Pool) →
            ∑ b ∈ Pool \ Finset.univ.image z_prev,
              ∑ w ∈ M_wit m z_prev b, (∏ i ∈ Q m z_prev b w, p i) ≤ α_step) →
          ∑ ω : ι → Bool, (if Base ω ∧ K ≤ (A ω).card then bernWeight p ω else 0) ≤
            (∏ i ∈ S₀, p i) * α_step ^ K) :=
by
  have hW_nn : ∀ ω : ι → Bool, 0 ≤ bernWeight p ω := by
    intro ω
    unfold bernWeight
    refine Finset.prod_nonneg (fun i _ => ?_)
    split_ifs
    · exact (hp i).1
    · exact sub_nonneg.mpr (hp i).2
  have hp_prod_nn : ∀ T : Finset ι, 0 ≤ ∏ i ∈ T, p i :=
    fun T => Finset.prod_nonneg (fun i _ => (hp i).1)
  have h_cyl : ∀ S : Finset ι,
      ∑ ω : ι → Bool, (if ∀ i ∈ S, ω i = true then bernWeight p ω else 0) = ∏ i ∈ S, p i := by
    intro S
    let T : ι → Finset Bool := fun i => if i ∈ S then {true} else Finset.univ
    let g : ι → Bool → ℝ := fun i b => if b = true then p i else 1 - p i
    have hfilt : Finset.univ.filter (fun ω : ι → Bool => ∀ i ∈ S, ω i = true) =
        Fintype.piFinset T := by
      ext ω
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset, T]
      constructor
      · intro h i
        by_cases hi : i ∈ S
        · rw [if_pos hi, h i hi]
          exact Finset.mem_singleton_self true
        · rw [if_neg hi]
          exact Finset.mem_univ (ω i)
      · intro h i hi
        have hi' := h i
        rw [if_pos hi] at hi'
        exact Finset.mem_singleton.mp hi'
    have hsum1 : ∑ ω : ι → Bool, (if ∀ i ∈ S, ω i = true then bernWeight p ω else 0) =
        ∑ ω ∈ Fintype.piFinset T, ∏ i : ι, g i (ω i) := by
      rw [← Finset.sum_filter, hfilt]
      rfl
    rw [hsum1, ← Finset.prod_univ_sum T g]
    have hfiber : ∀ i : ι, ∑ b ∈ T i, g i b = if i ∈ S then p i else 1 := by
      intro i
      by_cases hi : i ∈ S
      · simp only [T, if_pos hi, Finset.sum_singleton, g, ↓reduceIte]
      · simp only [T, if_neg hi]
        rw [Fintype.sum_bool]
        dsimp [g]
        ring
    have hprod : (∏ i : ι, ∑ b ∈ T i, g i b) = ∏ i ∈ Finset.univ, if i ∈ S then p i else 1 :=
      Finset.prod_congr rfl (fun i _ => hfiber i)
    rw [hprod, Finset.prod_ite_mem Finset.univ S p, Finset.univ_inter]
  have hW_sum : ∑ ω : ι → Bool, bernWeight p ω = 1 := by
    simpa using h_cyl ∅
  refine ⟨hW_nn, hW_sum, h_cyl, ?_⟩
  intro β γ _ _ Pool K α_step hα_nn Base _ A hA_sub S₀ U M_wit Q
    hU0 hU_mono hQ_sub hBase_wit hStep_sum
  have snoc_inj : ∀ (m : ℕ) (z_prev : Fin m → β),
      Function.Injective z_prev →
      ∀ b ∈ Pool \ Finset.univ.image z_prev,
      Function.Injective (Fin.snoc z_prev b) := by
    intro m z_prev hinj b hb u₁ u₂ heq
    have hb_fresh : b ∉ Finset.univ.image z_prev := (Finset.mem_sdiff.mp hb).2
    revert heq
    refine Fin.lastCases ?_ (fun i₁ => ?_) u₁
    · refine Fin.lastCases ?_ (fun i₂ => ?_) u₂
      · intro _
        rfl
      · intro heq
        rw [Fin.snoc_last, Fin.snoc_castSucc] at heq
        exact absurd (Finset.mem_image.mpr ⟨i₂, Finset.mem_univ i₂, heq.symm⟩) hb_fresh
    · refine Fin.lastCases ?_ (fun i₂ => ?_) u₂
      · intro heq
        rw [Fin.snoc_castSucc, Fin.snoc_last] at heq
        exact absurd (Finset.mem_image.mpr ⟨i₁, Finset.mem_univ i₁, heq⟩) hb_fresh
      · intro heq
        rw [Fin.snoc_castSucc, Fin.snoc_castSucc] at heq
        exact congr_arg Fin.castSucc (hinj heq)
  have snoc_mem_pool : ∀ (m : ℕ) (z_prev : Fin m → β),
      (∀ t : Fin m, z_prev t ∈ Pool) →
      ∀ b ∈ Pool, ∀ u : Fin (m + 1), (Fin.snoc z_prev b : Fin (m + 1) → β) u ∈ Pool := by
    intro m z_prev hz_pool b hb
    refine Fin.lastCases ?_ (fun i => ?_)
    · simpa [Fin.snoc_last] using hb
    · simpa [Fin.snoc_castSucc] using hz_pool i
  let tailInd : ℕ → (m : ℕ) → (Fin m → β) → Finset ι → (ι → Bool) → ℝ :=
    fun r => Nat.rec
      (motive := fun _ => (m : ℕ) → (Fin m → β) → Finset ι → (ι → Bool) → ℝ)
      (fun _ _ Acc ω => if ∀ i ∈ Acc, ω i = true then bernWeight p ω else 0)
      (fun _ ih m z_prev Acc ω =>
        ∑ b ∈ Pool \ Finset.univ.image z_prev,
          ∑ w ∈ M_wit m z_prev b,
            ih (m + 1) (Fin.snoc z_prev b) (Acc ∪ Q m z_prev b w) ω)
      r
  have tailInd_nonneg : ∀ (r m : ℕ) (z_prev : Fin m → β) (Acc : Finset ι) (ω : ι → Bool),
      0 ≤ tailInd r m z_prev Acc ω := by
    intro r
    induction r with
    | zero =>
      intro m z_prev Acc ω
      dsimp [tailInd]
      split_ifs
      · exact hW_nn ω
      · exact le_rfl
    | succ r ih =>
      intro m z_prev Acc ω
      dsimp [tailInd]
      exact Finset.sum_nonneg (fun b _ =>
        Finset.sum_nonneg (fun w _ => ih (m + 1) (Fin.snoc z_prev b) (Acc ∪ Q m z_prev b w) ω))
  have sum_tailInd_le : ∀ (r m : ℕ), m + r ≤ K →
      ∀ (z_prev : Fin m → β), Function.Injective z_prev → (∀ t : Fin m, z_prev t ∈ Pool) →
      ∀ (Acc : Finset ι), Acc ⊆ U m z_prev →
      ∑ ω : ι → Bool, tailInd r m z_prev Acc ω ≤ (∏ i ∈ Acc, p i) * α_step ^ r := by
    intro r
    induction r with
    | zero =>
      intro m _ z_prev _ _ Acc _
      dsimp [tailInd]
      rw [h_cyl Acc, pow_zero, mul_one]
    | succ r ih =>
      intro m hmr z_prev hinj hz_pool Acc hAcc
      have hm : m < K := by omega
      have hmr' : (m + 1) + r ≤ K := by omega
      let B_rem : Finset β := Pool \ Finset.univ.image z_prev
      have hswap : ∑ ω : ι → Bool, tailInd (r + 1) m z_prev Acc ω =
          ∑ b ∈ B_rem, ∑ w ∈ M_wit m z_prev b,
            ∑ ω : ι → Bool,
              tailInd r (m + 1) (Fin.snoc z_prev b) (Acc ∪ Q m z_prev b w) ω := by
        dsimp [tailInd]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl (fun b _ => Finset.sum_comm)
      rw [hswap]
      have hterm : ∀ b ∈ B_rem, ∀ w ∈ M_wit m z_prev b,
          ∑ ω : ι → Bool,
            tailInd r (m + 1) (Fin.snoc z_prev b) (Acc ∪ Q m z_prev b w) ω ≤
          (∏ i ∈ Acc, p i) * (∏ i ∈ Q m z_prev b w, p i) * α_step ^ r := by
        intro b hb w hw
        have hinj' : Function.Injective (Fin.snoc z_prev b) := snoc_inj m z_prev hinj b hb
        have hz_pool' : ∀ u : Fin (m + 1), (Fin.snoc z_prev b : Fin (m + 1) → β) u ∈ Pool :=
          snoc_mem_pool m z_prev hz_pool b (Finset.mem_sdiff.mp hb).1
        have hQ_bw : Q m z_prev b w ⊆ U (m + 1) (Fin.snoc z_prev b) \ U m z_prev :=
          hQ_sub m hm z_prev hinj hz_pool b hb w hw
        have hAcc' : Acc ∪ Q m z_prev b w ⊆ U (m + 1) (Fin.snoc z_prev b) :=
          Finset.union_subset
            (Finset.Subset.trans hAcc (hU_mono m hm z_prev b))
            (Finset.Subset.trans hQ_bw Finset.sdiff_subset)
        have hDisj : Disjoint Acc (Q m z_prev b w) := by
          rw [Finset.disjoint_left]
          intro i hiAcc hiQ
          exact (Finset.mem_sdiff.mp (hQ_bw hiQ)).2 (hAcc hiAcc)
        have h_ih := ih (m + 1) hmr' (Fin.snoc z_prev b) hinj' hz_pool' (Acc ∪ Q m z_prev b w) hAcc'
        rwa [Finset.prod_union hDisj] at h_ih
      have hsum_le : ∑ b ∈ B_rem, ∑ w ∈ M_wit m z_prev b,
          ∑ ω : ι → Bool,
            tailInd r (m + 1) (Fin.snoc z_prev b) (Acc ∪ Q m z_prev b w) ω ≤
          ∑ b ∈ B_rem, ∑ w ∈ M_wit m z_prev b,
            ((∏ i ∈ Acc, p i) * (∏ i ∈ Q m z_prev b w, p i) * α_step ^ r) :=
        Finset.sum_le_sum (fun b hb => Finset.sum_le_sum (fun w hw => hterm b hb w hw))
      have hfactor : ∑ b ∈ B_rem, ∑ w ∈ M_wit m z_prev b,
          ((∏ i ∈ Acc, p i) * (∏ i ∈ Q m z_prev b w, p i) * α_step ^ r) =
          (∏ i ∈ Acc, p i) *
            (∑ b ∈ B_rem, ∑ w ∈ M_wit m z_prev b, (∏ i ∈ Q m z_prev b w, p i)) *
            α_step ^ r := by
        rw [Finset.mul_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl (fun b _ => ?_)
        rw [Finset.mul_sum, Finset.sum_mul]
      have hstep := hStep_sum m hm z_prev hinj hz_pool
      have hmul1 : (∏ i ∈ Acc, p i) *
          (∑ b ∈ B_rem, ∑ w ∈ M_wit m z_prev b, (∏ i ∈ Q m z_prev b w, p i)) ≤
          (∏ i ∈ Acc, p i) * α_step :=
        mul_le_mul_of_nonneg_left hstep (hp_prod_nn Acc)
      have hmul2 : (∏ i ∈ Acc, p i) *
          (∑ b ∈ B_rem, ∑ w ∈ M_wit m z_prev b, (∏ i ∈ Q m z_prev b w, p i)) * α_step ^ r ≤
          (∏ i ∈ Acc, p i) * α_step * α_step ^ r :=
        mul_le_mul_of_nonneg_right hmul1 (pow_nonneg hα_nn r)
      calc
        ∑ b ∈ B_rem, ∑ w ∈ M_wit m z_prev b,
            ∑ ω : ι → Bool,
              tailInd r (m + 1) (Fin.snoc z_prev b) (Acc ∪ Q m z_prev b w) ω
          ≤ (∏ i ∈ Acc, p i) *
              (∑ b ∈ B_rem, ∑ w ∈ M_wit m z_prev b, (∏ i ∈ Q m z_prev b w, p i)) *
              α_step ^ r := by rwa [hfactor] at hsum_le
        _ ≤ (∏ i ∈ Acc, p i) * α_step * α_step ^ r := hmul2
        _ = (∏ i ∈ Acc, p i) * α_step ^ (r + 1) := by rw [mul_assoc, ← pow_succ']
  have bernWeight_le_tailInd : ∀ (ω : ι → Bool) (z : Fin K → β),
      Function.Injective z →
      (∀ s : Fin K, z s ∈ Pool) →
      (∀ s : Fin K,
        ∃ w ∈ M_wit s.1 (fun t : Fin s.1 => z (t.castLE (Nat.le_of_lt s.isLt))) (z s),
          ∀ i ∈ Q s.1 (fun t : Fin s.1 => z (t.castLE (Nat.le_of_lt s.isLt))) (z s) w,
            ω i = true) →
      ∀ (r m : ℕ) (hmr : m + r = K) (Acc : Finset ι),
        (∀ i ∈ Acc, ω i = true) →
        bernWeight p ω ≤
          tailInd r m (fun t : Fin m => z (t.castLE (Nat.le.intro hmr))) Acc ω := by
    intro ω z hz_inj hz_pool hwit r
    induction r with
    | zero =>
      intro m hmr Acc hω_Acc
      dsimp [tailInd]
      rw [if_pos hω_Acc]
    | succ r ih =>
      intro m hmr Acc hω_Acc
      have hm : m < K := by omega
      have hmr' : (m + 1) + r = K := by omega
      let s : Fin K := ⟨m, hm⟩
      let z_m : Fin m → β := fun t => z (t.castLE (Nat.le_of_lt hm))
      let b₀ : β := z s
      have hb₀ : b₀ ∈ Pool \ Finset.univ.image z_m := by
        rw [Finset.mem_sdiff]
        refine ⟨hz_pool s, ?_⟩
        intro himg
        rcases Finset.mem_image.mp himg with ⟨t, _, ht_eq⟩
        have hval := congr_arg Fin.val (hz_inj ht_eq)
        simp only [s, Fin.val_castLE] at hval
        exact absurd hval (Nat.ne_of_lt t.isLt)
      obtain ⟨w₀, hw₀_mem, hw₀_true⟩ := hwit s
      have hω_union : ∀ i ∈ Acc ∪ Q m z_m b₀ w₀, ω i = true := by
        intro i hi
        rcases Finset.mem_union.mp hi with hi | hi
        · exact hω_Acc i hi
        · exact hw₀_true i hi
      have hsnoc : Fin.snoc z_m b₀ =
          (fun t : Fin (m + 1) => z (t.castLE (Nat.le.intro hmr'))) := by
        funext u
        refine Fin.lastCases ?_ (fun t => ?_) u
        · simp only [Fin.snoc_last, b₀, s]
          congr 1
        · simp only [Fin.snoc_castSucc, z_m]
          congr 1
      have h1 : bernWeight p ω ≤
          tailInd r (m + 1) (Fin.snoc z_m b₀) (Acc ∪ Q m z_m b₀ w₀) ω := by
        have h_ih := ih (m + 1) hmr' (Acc ∪ Q m z_m b₀ w₀) hω_union
        rwa [← hsnoc] at h_ih
      have h2 : tailInd r (m + 1) (Fin.snoc z_m b₀) (Acc ∪ Q m z_m b₀ w₀) ω ≤
          ∑ w ∈ M_wit m z_m b₀,
            tailInd r (m + 1) (Fin.snoc z_m b₀) (Acc ∪ Q m z_m b₀ w) ω :=
        Finset.single_le_sum
          (fun w _ => tailInd_nonneg r (m + 1) (Fin.snoc z_m b₀) (Acc ∪ Q m z_m b₀ w) ω)
          hw₀_mem
      have h3 : ∑ w ∈ M_wit m z_m b₀,
          tailInd r (m + 1) (Fin.snoc z_m b₀) (Acc ∪ Q m z_m b₀ w) ω ≤
          tailInd (r + 1) m (fun t : Fin m => z (t.castLE (Nat.le.intro hmr))) Acc ω := by
        change ∑ w ∈ M_wit m z_m b₀,
            tailInd r (m + 1) (Fin.snoc z_m b₀) (Acc ∪ Q m z_m b₀ w) ω ≤
          ∑ b ∈ Pool \ Finset.univ.image z_m,
            ∑ w ∈ M_wit m z_m b,
              tailInd r (m + 1) (Fin.snoc z_m b) (Acc ∪ Q m z_m b w) ω
        exact Finset.single_le_sum
          (fun b _ => Finset.sum_nonneg (fun w _ =>
            tailInd_nonneg r (m + 1) (Fin.snoc z_m b) (Acc ∪ Q m z_m b w) ω))
          hb₀
      exact le_trans h1 (le_trans h2 h3)
  have hpt_ω : ∀ ω : ι → Bool,
      (if Base ω ∧ K ≤ (A ω).card then bernWeight p ω else 0) ≤
        tailInd K 0 Fin.elim0 S₀ ω := by
    intro ω
    by_cases h : Base ω ∧ K ≤ (A ω).card
    · rw [if_pos h]
      obtain ⟨T₀, hT₀_sub, hT₀_card⟩ := Finset.exists_subset_card_eq h.2
      let e : Fin K ≃ ↥T₀ := (finCongr hT₀_card.symm).trans T₀.equivFin.symm
      let z : Fin K → β := fun s => (e s).1
      have hz_inj : Function.Injective z := Subtype.val_injective.comp e.injective
      have hz_A : ∀ s : Fin K, z s ∈ A ω := fun s => hT₀_sub (e s).2
      have hz_pool : ∀ s : Fin K, z s ∈ Pool := fun s => hA_sub ω (hz_A s)
      obtain ⟨hω_S₀, hwit_all⟩ := hBase_wit ω h.1
      have hdom := bernWeight_le_tailInd ω z hz_inj hz_pool (hwit_all z hz_inj hz_A)
        K 0 (Nat.zero_add K) S₀ hω_S₀
      have hz0 : (fun t : Fin 0 => z (t.castLE (Nat.le.intro (Nat.zero_add K)))) = Fin.elim0 :=
        Subsingleton.elim _ _
      rwa [hz0] at hdom
    · rw [if_neg h]
      exact tailInd_nonneg K 0 Fin.elim0 S₀ ω
  calc
    ∑ ω : ι → Bool, (if Base ω ∧ K ≤ (A ω).card then bernWeight p ω else 0)
      ≤ ∑ ω : ι → Bool, tailInd K 0 Fin.elim0 S₀ ω :=
        Finset.sum_le_sum (fun ω _ => hpt_ω ω)
    _ ≤ (∏ i ∈ S₀, p i) * α_step ^ K :=
        sum_tailInd_le K 0 (Nat.zero_add K).le Fin.elim0
          (fun t => Fin.elim0 t) (fun t => Fin.elim0 t) S₀ (hU0 Fin.elim0)

private theorem paley_zygmund_markov_expurgation {Ω V : Type} [Fintype Ω] [DecidableEq Ω] [Fintype V] [DecidableEq V]
    (W : Ω → ℝ) (hW_nn : ∀ ω : Ω, 0 ≤ W ω) (hW_sum : ∑ ω : Ω, W ω = 1)
    (Rel : V → V → Prop) [DecidableRel Rel] (hRel_symm : Symmetric Rel)
    (P_raw B_bad : Ω → Finset V)
    (n_0 D_star γ δ_bad : ℝ)
    (hn0 : 0 < n_0) (hD : 0 < D_star) (hγ : 1 ≤ γ) (hδ : 0 < δ_bad)
    (h_margin : 72 * 144 * γ ^ 3 * δ_bad ≤ 1 / 256)
    (hM1 : ∑ ω : Ω, W ω * ((P_raw ω).card : ℝ) ≤ n_0)
    (hE1 : n_0 * D_star ≤ ∑ ω : Ω, W ω *
      (((P_raw ω ×ˢ P_raw ω).filter (fun xy => Rel xy.1 xy.2)).card : ℝ))
    (hE2 : ∑ ω : Ω, W ω *
      ((((P_raw ω ×ˢ P_raw ω).filter (fun xy => Rel xy.1 xy.2)).card : ℝ) ^ 2) ≤
        3 * γ * (n_0 * D_star) ^ 2)
    (hW2 : ∑ ω : Ω, W ω *
      (∑ x ∈ P_raw ω, (((P_raw ω).filter (fun y => Rel x y)).card : ℝ) ^ 2) ≤
        2 * γ * n_0 * D_star ^ 2)
    (hBad : ∑ ω : Ω, W ω * ((B_bad ω).card : ℝ) ≤ δ_bad * n_0) :
    ∃ ω₀ : Ω,
      (1 / 1024 : ℝ) * γ⁻¹ ^ 2 * n_0 ≤ ((P_raw ω₀ \ B_bad ω₀).card : ℝ) ∧
      ((P_raw ω₀ \ B_bad ω₀).card : ℝ) ≤ 72 * γ * n_0 ∧
      (D_star / γ) * ((P_raw ω₀ \ B_bad ω₀).card : ℝ) ≤
        192 * ((((P_raw ω₀ \ B_bad ω₀) ×ˢ (P_raw ω₀ \ B_bad ω₀)).filter
          (fun xy => Rel xy.1 xy.2)).card : ℝ) :=
by
  let E_set : Finset V → Finset (V × V) :=
    fun S => (S ×ˢ S).filter (fun xy => Rel xy.1 xy.2)
  let deg_set : Finset V → V → ℕ :=
    fun S x => (S.filter (fun y => Rel x y)).card
  let Z : Ω → ℝ := fun ω => ((E_set (P_raw ω)).card : ℝ)
  let W_2 : Ω → ℝ := fun ω => ∑ x ∈ P_raw ω, ((deg_set (P_raw ω) x : ℝ) ^ 2)
  let M_0 : ℝ := n_0 * D_star
  have hγ_pos : 0 < γ := lt_of_lt_of_le zero_lt_one hγ
  have hγ_ne : γ ≠ 0 := ne_of_gt hγ_pos
  have hM0_pos : 0 < M_0 := mul_pos hn0 hD
  have hM0_sq_pos : 0 < M_0 ^ 2 := pow_pos hM0_pos 2
  have hW2_nn : ∀ ω : Ω, 0 ≤ W_2 ω := fun _ =>
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  let p_good : Ω → Prop := fun ω => (1 / 2 : ℝ) * M_0 ≤ Z ω
  letI instDecGood : DecidablePred p_good := Classical.decPred p_good
  letI instDecNotGood : ∀ ω : Ω, Decidable (¬ p_good ω) := fun ω => Classical.dec (¬ p_good ω)
  let G : Finset Ω := Finset.univ.filter p_good
  let Gc : Finset Ω := Finset.univ.filter (fun ω => ¬ p_good ω)
  have h_part : (∑ ω ∈ G, W ω * Z ω) + (∑ ω ∈ Gc, W ω * Z ω) = ∑ ω : Ω, W ω * Z ω :=
    Finset.sum_filter_add_sum_filter_not Finset.univ p_good (fun ω => W ω * Z ω)
  have hGc_bound : ∑ ω ∈ Gc, W ω * Z ω ≤ (1 / 2 : ℝ) * M_0 := by
    have hpt : ∀ ω ∈ Gc, W ω * Z ω ≤ ((1 / 2 : ℝ) * M_0) * W ω := by
      intro ω hω
      have hnot : ¬ ((1 / 2 : ℝ) * M_0 ≤ Z ω) := (Finset.mem_filter.mp hω).2
      have hle : Z ω ≤ (1 / 2 : ℝ) * M_0 := le_of_not_ge hnot
      calc
        W ω * Z ω ≤ W ω * ((1 / 2 : ℝ) * M_0) := mul_le_mul_of_nonneg_left hle (hW_nn ω)
        _ = ((1 / 2 : ℝ) * M_0) * W ω := mul_comm _ _
    have hsum1 : ∑ ω ∈ Gc, W ω * Z ω ≤ ((1 / 2 : ℝ) * M_0) * ∑ ω ∈ Gc, W ω := by
      calc
        ∑ ω ∈ Gc, W ω * Z ω ≤ ∑ ω ∈ Gc, ((1 / 2 : ℝ) * M_0) * W ω := Finset.sum_le_sum hpt
        _ = ((1 / 2 : ℝ) * M_0) * ∑ ω ∈ Gc, W ω := (Finset.mul_sum Gc W ((1 / 2 : ℝ) * M_0)).symm
    have hsumW : ∑ ω ∈ Gc, W ω ≤ 1 := by
      calc
        ∑ ω ∈ Gc, W ω ≤ ∑ ω : Ω, W ω := Finset.sum_le_univ_sum_of_nonneg hW_nn
        _ = 1 := hW_sum
    have hhalf_nn : 0 ≤ (1 / 2 : ℝ) * M_0 := by positivity
    calc
      ∑ ω ∈ Gc, W ω * Z ω ≤ ((1 / 2 : ℝ) * M_0) * ∑ ω ∈ Gc, W ω := hsum1
      _ ≤ ((1 / 2 : ℝ) * M_0) * 1 := mul_le_mul_of_nonneg_left hsumW hhalf_nn
      _ = (1 / 2 : ℝ) * M_0 := mul_one _
  have hE1' : M_0 ≤ ∑ ω : Ω, W ω * Z ω := hE1
  have hG_E1 : (1 / 2 : ℝ) * M_0 ≤ ∑ ω ∈ G, W ω * Z ω := by
    linarith only [h_part, hGc_bound, hE1']
  have hCS_G : (∑ ω ∈ G, W ω * Z ω) ^ 2 ≤ (∑ ω ∈ G, W ω) * (∑ ω ∈ G, W ω * Z ω ^ 2) := by
    have hraw := Finset.sum_mul_sq_le_sq_mul_sq G
      (fun ω => Real.sqrt (W ω)) (fun ω => Real.sqrt (W ω) * Z ω)
    have h1 : ∑ ω ∈ G, Real.sqrt (W ω) * (Real.sqrt (W ω) * Z ω) = ∑ ω ∈ G, W ω * Z ω := by
      refine Finset.sum_congr rfl (fun ω _ => ?_)
      rw [← mul_assoc, Real.mul_self_sqrt (hW_nn ω)]
    have h2 : ∑ ω ∈ G, (Real.sqrt (W ω)) ^ 2 = ∑ ω ∈ G, W ω := by
      refine Finset.sum_congr rfl (fun ω _ => ?_)
      exact Real.sq_sqrt (hW_nn ω)
    have h3 : ∑ ω ∈ G, (Real.sqrt (W ω) * Z ω) ^ 2 = ∑ ω ∈ G, W ω * Z ω ^ 2 := by
      refine Finset.sum_congr rfl (fun ω _ => ?_)
      rw [mul_pow, Real.sq_sqrt (hW_nn ω)]
    rwa [h1, h2, h3] at hraw
  have hPZ : 1 ≤ ∑ ω ∈ G, W ω * (12 * γ) := by
    have hsq_low : (1 / 4 : ℝ) * M_0 ^ 2 ≤ (∑ ω ∈ G, W ω * Z ω) ^ 2 := by
      have hsq : ((1 / 2 : ℝ) * M_0) ^ 2 ≤ (∑ ω ∈ G, W ω * Z ω) ^ 2 := by
        nlinarith only [hG_E1, hM0_pos]
      linarith [hsq, show ((1 / 2 : ℝ) * M_0) ^ 2 = (1 / 4 : ℝ) * M_0 ^ 2 by ring]
    have hG_E2 : ∑ ω ∈ G, W ω * Z ω ^ 2 ≤ 3 * γ * M_0 ^ 2 := by
      calc
        ∑ ω ∈ G, W ω * Z ω ^ 2 ≤ ∑ ω : Ω, W ω * Z ω ^ 2 :=
          Finset.sum_le_univ_sum_of_nonneg (fun ω => mul_nonneg (hW_nn ω) (sq_nonneg (Z ω)))
        _ ≤ 3 * γ * M_0 ^ 2 := hE2
    have hGW_nn : 0 ≤ ∑ ω ∈ G, W ω := Finset.sum_nonneg (fun ω _ => hW_nn ω)
    have hcomb : (1 / 4 : ℝ) * M_0 ^ 2 ≤ (∑ ω ∈ G, W ω) * (3 * γ * M_0 ^ 2) :=
      le_trans hsq_low (le_trans hCS_G (mul_le_mul_of_nonneg_left hG_E2 hGW_nn))
    have hmul4 : 1 * M_0 ^ 2 ≤ ((∑ ω ∈ G, W ω) * (12 * γ)) * M_0 ^ 2 := by
      linarith [hcomb,
        show (∑ ω ∈ G, W ω) * (3 * γ * M_0 ^ 2) =
          (1 / 4 : ℝ) * (((∑ ω ∈ G, W ω) * (12 * γ)) * M_0 ^ 2) by ring]
    have h1 : 1 ≤ (∑ ω ∈ G, W ω) * (12 * γ) := le_of_mul_le_mul_right hmul4 hM0_sq_pos
    rwa [Finset.sum_mul] at h1
  let Phi : Ω → ℝ := fun ω =>
    ((P_raw ω).card : ℝ) / (6 * n_0) +
    W_2 ω / (12 * γ * n_0 * D_star ^ 2) +
    ((B_bad ω).card : ℝ) / (6 * δ_bad * n_0)
  have hPhi_t1_nn : ∀ ω : Ω, 0 ≤ ((P_raw ω).card : ℝ) / (6 * n_0) :=
    fun _ => div_nonneg (Nat.cast_nonneg _) (by positivity)
  have hPhi_t2_nn : ∀ ω : Ω, 0 ≤ W_2 ω / (12 * γ * n_0 * D_star ^ 2) :=
    fun ω => div_nonneg (hW2_nn ω) (by positivity)
  have hPhi_t3_nn : ∀ ω : Ω, 0 ≤ ((B_bad ω).card : ℝ) / (6 * δ_bad * n_0) :=
    fun _ => div_nonneg (Nat.cast_nonneg _) (by positivity)
  have hPhi_nn : ∀ ω : Ω, 0 ≤ Phi ω := fun ω => by
    dsimp only [Phi]
    linarith only [hPhi_t1_nn ω, hPhi_t2_nn ω, hPhi_t3_nn ω]
  have hPhi_sum1 : ∑ ω : Ω, W ω * (((P_raw ω).card : ℝ) / (6 * n_0)) ≤ 1 / 6 := by
    have heq : ∑ ω : Ω, W ω * (((P_raw ω).card : ℝ) / (6 * n_0)) =
        (∑ ω : Ω, W ω * ((P_raw ω).card : ℝ)) / (6 * n_0) := by
      simp_rw [← mul_div_assoc]
      exact (Finset.sum_div Finset.univ (fun ω => W ω * ((P_raw ω).card : ℝ)) (6 * n_0)).symm
    rw [heq]
    have hden : 0 < 6 * n_0 := by positivity
    rw [div_le_iff₀ hden]
    linarith only [hM1]
  have hPhi_sum2 : ∑ ω : Ω, W ω * (W_2 ω / (12 * γ * n_0 * D_star ^ 2)) ≤ 1 / 6 := by
    have heq : ∑ ω : Ω, W ω * (W_2 ω / (12 * γ * n_0 * D_star ^ 2)) =
        (∑ ω : Ω, W ω * W_2 ω) / (12 * γ * n_0 * D_star ^ 2) := by
      simp_rw [← mul_div_assoc]
      exact (Finset.sum_div Finset.univ (fun ω => W ω * W_2 ω) (12 * γ * n_0 * D_star ^ 2)).symm
    rw [heq]
    have hden : 0 < 12 * γ * n_0 * D_star ^ 2 := by positivity
    rw [div_le_iff₀ hden]
    have hW2' : ∑ ω : Ω, W ω * W_2 ω ≤ 2 * γ * n_0 * D_star ^ 2 := hW2
    linarith [hW2', show (1 / 6 : ℝ) * (12 * γ * n_0 * D_star ^ 2) = 2 * γ * n_0 * D_star ^ 2 by ring]
  have hPhi_sum3 : ∑ ω : Ω, W ω * (((B_bad ω).card : ℝ) / (6 * δ_bad * n_0)) ≤ 1 / 6 := by
    have heq : ∑ ω : Ω, W ω * (((B_bad ω).card : ℝ) / (6 * δ_bad * n_0)) =
        (∑ ω : Ω, W ω * ((B_bad ω).card : ℝ)) / (6 * δ_bad * n_0) := by
      simp_rw [← mul_div_assoc]
      exact (Finset.sum_div Finset.univ (fun ω => W ω * ((B_bad ω).card : ℝ)) (6 * δ_bad * n_0)).symm
    rw [heq]
    have hden : 0 < 6 * δ_bad * n_0 := by positivity
    rw [div_le_iff₀ hden]
    linarith [hBad, show (1 / 6 : ℝ) * (6 * δ_bad * n_0) = δ_bad * n_0 by ring]
  have hPhi_G_le : ∑ ω ∈ G, W ω * Phi ω ≤ 1 / 2 := by
    have huniv : ∑ ω ∈ G, W ω * Phi ω ≤ ∑ ω : Ω, W ω * Phi ω :=
      Finset.sum_le_univ_sum_of_nonneg (fun ω => mul_nonneg (hW_nn ω) (hPhi_nn ω))
    have hexp : ∑ ω : Ω, W ω * Phi ω =
        (∑ ω : Ω, W ω * (((P_raw ω).card : ℝ) / (6 * n_0))) +
        (∑ ω : Ω, W ω * (W_2 ω / (12 * γ * n_0 * D_star ^ 2))) +
        (∑ ω : Ω, W ω * (((B_bad ω).card : ℝ) / (6 * δ_bad * n_0))) := by
      have hdist : ∀ ω : Ω, W ω * Phi ω =
          W ω * (((P_raw ω).card : ℝ) / (6 * n_0)) +
          W ω * (W_2 ω / (12 * γ * n_0 * D_star ^ 2)) +
          W ω * (((B_bad ω).card : ℝ) / (6 * δ_bad * n_0)) := by
        intro ω
        dsimp only [Phi]
        ring
      simp_rw [hdist, Finset.sum_add_distrib]
    linarith only [huniv, hexp, hPhi_sum1, hPhi_sum2, hPhi_sum3]
  have hPhi_lt_PZ : ∑ ω ∈ G, W ω * Phi ω < ∑ ω ∈ G, W ω * (12 * γ) := by
    linarith only [hPhi_G_le, hPZ]
  obtain ⟨ω₀, hω₀_G, hω₀_lt⟩ := Finset.exists_lt_of_sum_lt hPhi_lt_PZ
  have hPhi_ω₀_le : Phi ω₀ ≤ 12 * γ :=
    le_of_lt (lt_of_mul_lt_mul_left hω₀_lt (hW_nn ω₀))
  have hZ_ω₀ : (1 / 2 : ℝ) * (n_0 * D_star) ≤ Z ω₀ := (Finset.mem_filter.mp hω₀_G).2
  have hP0_card : ((P_raw ω₀).card : ℝ) ≤ 72 * γ * n_0 := by
    have h1 : ((P_raw ω₀).card : ℝ) / (6 * n_0) ≤ 12 * γ := by
      have ht2 := hPhi_t2_nn ω₀
      have ht3 := hPhi_t3_nn ω₀
      dsimp only [Phi] at hPhi_ω₀_le
      linarith only [hPhi_ω₀_le, ht2, ht3]
    have hden : 0 < 6 * n_0 := by positivity
    rw [div_le_iff₀ hden] at h1
    linarith [h1, show (12 * γ) * (6 * n_0) = 72 * γ * n_0 by ring]
  have hW2_ω₀ : W_2 ω₀ ≤ 144 * γ ^ 2 * n_0 * D_star ^ 2 := by
    have h1 : W_2 ω₀ / (12 * γ * n_0 * D_star ^ 2) ≤ 12 * γ := by
      have ht1 := hPhi_t1_nn ω₀
      have ht3 := hPhi_t3_nn ω₀
      dsimp only [Phi] at hPhi_ω₀_le
      linarith only [hPhi_ω₀_le, ht1, ht3]
    have hden : 0 < 12 * γ * n_0 * D_star ^ 2 := by positivity
    rw [div_le_iff₀ hden] at h1
    linarith [h1, show (12 * γ) * (12 * γ * n_0 * D_star ^ 2) = 144 * γ ^ 2 * n_0 * D_star ^ 2 by ring]
  have hBad_ω₀ : ((B_bad ω₀).card : ℝ) ≤ 72 * γ * δ_bad * n_0 := by
    have h1 : ((B_bad ω₀).card : ℝ) / (6 * δ_bad * n_0) ≤ 12 * γ := by
      have ht1 := hPhi_t1_nn ω₀
      have ht2 := hPhi_t2_nn ω₀
      dsimp only [Phi] at hPhi_ω₀_le
      linarith only [hPhi_ω₀_le, ht1, ht2]
    have hden : 0 < 6 * δ_bad * n_0 := by positivity
    rw [div_le_iff₀ hden] at h1
    linarith [h1, show (12 * γ) * (6 * δ_bad * n_0) = 72 * γ * δ_bad * n_0 by ring]
  have h_fiber_left : ∀ A B : Finset V,
      ((A ×ˢ B).filter (fun xy => Rel xy.1 xy.2)).card = ∑ x ∈ A, deg_set B x := by
    intro A B
    rw [Finset.card_filter, Finset.sum_product]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    exact (Finset.card_filter (fun y => Rel x y) B).symm
  have h_fiber_right : ∀ A B : Finset V,
      ((A ×ˢ B).filter (fun xy => Rel xy.1 xy.2)).card = ∑ y ∈ B, deg_set A y := by
    intro A B
    rw [Finset.card_filter, Finset.sum_product, Finset.sum_comm]
    refine Finset.sum_congr rfl (fun y _ => ?_)
    have hsym : ∑ x ∈ A, (if Rel x y then 1 else 0) = ∑ x ∈ A, (if Rel y x then 1 else 0) := by
      refine Finset.sum_congr rfl (fun x _ => ?_)
      exact ite_congr (propext ⟨fun h => hRel_symm h, fun h => hRel_symm h⟩)
        (fun _ => rfl) (fun _ => rfl)
    rw [hsym]
    exact (Finset.card_filter (fun x => Rel y x) A).symm
  let P_0 : Finset V := P_raw ω₀
  let B_raw : Finset V := B_bad ω₀
  let B_0 : Finset V := P_0 ∩ B_raw
  let X : Finset V := P_0 \ B_raw
  let L_1 : Finset (V × V) := (B_0 ×ˢ P_0).filter (fun xy => Rel xy.1 xy.2)
  let L_2 : Finset (V × V) := (P_0 ×ˢ B_0).filter (fun xy => Rel xy.1 xy.2)
  have hE_sub : E_set P_0 ⊆ E_set X ∪ (L_1 ∪ L_2) := by
    intro xy hxy
    simp only [E_set, L_1, L_2, B_0, X, Finset.mem_union, Finset.mem_filter,
      Finset.mem_product, Finset.mem_inter, Finset.mem_sdiff] at hxy ⊢
    rcases hxy with ⟨⟨hxP, hyP⟩, hrel⟩
    by_cases hxB : xy.1 ∈ B_raw
    · exact Or.inr (Or.inl ⟨⟨⟨hxP, hxB⟩, hyP⟩, hrel⟩)
    · by_cases hyB : xy.2 ∈ B_raw
      · exact Or.inr (Or.inr ⟨⟨hxP, ⟨hyP, hyB⟩⟩, hrel⟩)
      · exact Or.inl ⟨⟨⟨hxP, hxB⟩, ⟨hyP, hyB⟩⟩, hrel⟩
  have hZ_del_nat : (E_set P_0).card ≤ (E_set X).card + 2 * ∑ x ∈ B_0, deg_set P_0 x := by
    have hc0 := Finset.card_le_card hE_sub
    have hc1 := Finset.card_union_le (E_set X) (L_1 ∪ L_2)
    have hc2 := Finset.card_union_le L_1 L_2
    have hL1 : L_1.card = ∑ x ∈ B_0, deg_set P_0 x := h_fiber_left B_0 P_0
    have hL2 : L_2.card = ∑ x ∈ B_0, deg_set P_0 x := h_fiber_right P_0 B_0
    omega
  have hZ_del : Z ω₀ ≤ ((E_set X).card : ℝ) + 2 * ∑ x ∈ B_0, (deg_set P_0 x : ℝ) := by
    have hcast : ((E_set P_0).card : ℝ) ≤
        (((E_set X).card + 2 * ∑ x ∈ B_0, deg_set P_0 x : ℕ) : ℝ) := by
      exact_mod_cast hZ_del_nat
    push_cast at hcast
    exact hcast
  have hX_up : (X.card : ℝ) ≤ 72 * γ * n_0 := by
    have hle_nat : X.card ≤ P_0.card := Finset.card_le_card Finset.sdiff_subset
    have hle_real : (X.card : ℝ) ≤ (P_0.card : ℝ) := by exact_mod_cast hle_nat
    exact le_trans hle_real hP0_card
  have hB0_deg_sum : ∑ x ∈ B_0, (deg_set P_0 x : ℝ) ≤ (1 / 16 : ℝ) * (n_0 * D_star) := by
    have hcs_raw := Finset.sum_mul_sq_le_sq_mul_sq B_0 (fun _ => (1 : ℝ)) (fun x => (deg_set P_0 x : ℝ))
    have hcs : (∑ x ∈ B_0, (deg_set P_0 x : ℝ)) ^ 2 ≤
        (B_0.card : ℝ) * ∑ x ∈ B_0, ((deg_set P_0 x : ℝ) ^ 2) := by
      have h1 : ∑ x ∈ B_0, (1 : ℝ) * (deg_set P_0 x : ℝ) = ∑ x ∈ B_0, (deg_set P_0 x : ℝ) := by
        simp only [one_mul]
      have h2 : ∑ _x ∈ B_0, (1 : ℝ) ^ 2 = (B_0.card : ℝ) := by
        simp only [one_pow, Finset.sum_const, nsmul_eq_mul, mul_one]
      rwa [h1, h2] at hcs_raw
    have hB0_card : (B_0.card : ℝ) ≤ 72 * γ * δ_bad * n_0 := by
      have hnat : B_0.card ≤ B_raw.card := Finset.card_le_card Finset.inter_subset_right
      have hreal : (B_0.card : ℝ) ≤ (B_raw.card : ℝ) := by exact_mod_cast hnat
      exact le_trans hreal hBad_ω₀
    have hB0_sq : ∑ x ∈ B_0, ((deg_set P_0 x : ℝ) ^ 2) ≤ 144 * γ ^ 2 * n_0 * D_star ^ 2 := by
      have hsub : ∑ x ∈ B_0, ((deg_set P_0 x : ℝ) ^ 2) ≤ W_2 ω₀ :=
        Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_left (fun _ _ _ => sq_nonneg _)
      exact le_trans hsub hW2_ω₀
    have hprod1 : (B_0.card : ℝ) * ∑ x ∈ B_0, ((deg_set P_0 x : ℝ) ^ 2) ≤
        (72 * γ * δ_bad * n_0) * (144 * γ ^ 2 * n_0 * D_star ^ 2) :=
      mul_le_mul hB0_card hB0_sq
        (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
        (by positivity)
    have hprod2 : (72 * γ * δ_bad * n_0) * (144 * γ ^ 2 * n_0 * D_star ^ 2) ≤
        ((1 / 16 : ℝ) * (n_0 * D_star)) ^ 2 := by
      have hmarg_mul : (72 * 144 * γ ^ 3 * δ_bad) * (n_0 * D_star) ^ 2 ≤
          (1 / 256 : ℝ) * (n_0 * D_star) ^ 2 :=
        mul_le_mul_of_nonneg_right h_margin (sq_nonneg _)
      linarith [hmarg_mul,
        show (72 * γ * δ_bad * n_0) * (144 * γ ^ 2 * n_0 * D_star ^ 2) =
          (72 * 144 * γ ^ 3 * δ_bad) * (n_0 * D_star) ^ 2 by ring,
        show (1 / 256 : ℝ) * (n_0 * D_star) ^ 2 =
          ((1 / 16 : ℝ) * (n_0 * D_star)) ^ 2 by ring]
    have hsq_le : (∑ x ∈ B_0, (deg_set P_0 x : ℝ)) ^ 2 ≤ ((1 / 16 : ℝ) * (n_0 * D_star)) ^ 2 :=
      le_trans hcs (le_trans hprod1 hprod2)
    have hrhs_pos : 0 < (1 / 16 : ℝ) * (n_0 * D_star) := by positivity
    nlinarith only [hsq_le, hrhs_pos]
  have hEX_low : (3 / 8 : ℝ) * (n_0 * D_star) ≤ ((E_set X).card : ℝ) := by
    linarith only [hZ_ω₀, hZ_del, hB0_deg_sum]
  have hDense : (D_star / γ) * (X.card : ℝ) ≤ 192 * ((E_set X).card : ℝ) := by
    have hDγ_nn : 0 ≤ D_star / γ := div_nonneg (le_of_lt hD) (le_of_lt hγ_pos)
    have h1 : (D_star / γ) * (X.card : ℝ) ≤ (D_star / γ) * (72 * γ * n_0) :=
      mul_le_mul_of_nonneg_left hX_up hDγ_nn
    have h2 : (D_star / γ) * (72 * γ * n_0) = 72 * (n_0 * D_star) := by
      field_simp [hγ_ne]
    linarith only [h1, h2, hEX_low]
  have hX_low : (1 / 1024 : ℝ) * γ⁻¹ ^ 2 * n_0 ≤ (X.card : ℝ) := by
    have hEX_deg_nat : (E_set X).card ≤ ∑ x ∈ X, deg_set P_0 x := by
      rw [h_fiber_left X X]
      refine Finset.sum_le_sum (fun x _ => ?_)
      exact Finset.card_le_card (Finset.filter_subset_filter (fun y => Rel x y) Finset.sdiff_subset)
    have hEX_deg : ((E_set X).card : ℝ) ≤ ∑ x ∈ X, (deg_set P_0 x : ℝ) := by
      have hcast : ((E_set X).card : ℝ) ≤ ((∑ x ∈ X, deg_set P_0 x : ℕ) : ℝ) := by
        exact_mod_cast hEX_deg_nat
      push_cast at hcast
      exact hcast
    have hsum_low : (3 / 8 : ℝ) * (n_0 * D_star) ≤ ∑ x ∈ X, (deg_set P_0 x : ℝ) :=
      le_trans hEX_low hEX_deg
    have hsq_low : (9 / 64 : ℝ) * n_0 ^ 2 * D_star ^ 2 ≤ (∑ x ∈ X, (deg_set P_0 x : ℝ)) ^ 2 := by
      have hpos : 0 < (3 / 8 : ℝ) * (n_0 * D_star) := by positivity
      have hsq : ((3 / 8 : ℝ) * (n_0 * D_star)) ^ 2 ≤ (∑ x ∈ X, (deg_set P_0 x : ℝ)) ^ 2 := by
        nlinarith only [hsum_low, hpos]
      linarith [hsq, show ((3 / 8 : ℝ) * (n_0 * D_star)) ^ 2 = (9 / 64 : ℝ) * n_0 ^ 2 * D_star ^ 2 by ring]
    have hcs_raw := Finset.sum_mul_sq_le_sq_mul_sq X (fun _ => (1 : ℝ)) (fun x => (deg_set P_0 x : ℝ))
    have hcs : (∑ x ∈ X, (deg_set P_0 x : ℝ)) ^ 2 ≤
        (X.card : ℝ) * ∑ x ∈ X, ((deg_set P_0 x : ℝ) ^ 2) := by
      have h1 : ∑ x ∈ X, (1 : ℝ) * (deg_set P_0 x : ℝ) = ∑ x ∈ X, (deg_set P_0 x : ℝ) := by
        simp only [one_mul]
      have h2 : ∑ _x ∈ X, (1 : ℝ) ^ 2 = (X.card : ℝ) := by
        simp only [one_pow, Finset.sum_const, nsmul_eq_mul, mul_one]
      rwa [h1, h2] at hcs_raw
    have hX_sq : ∑ x ∈ X, ((deg_set P_0 x : ℝ) ^ 2) ≤ 144 * γ ^ 2 * n_0 * D_star ^ 2 := by
      have hsub : ∑ x ∈ X, ((deg_set P_0 x : ℝ) ^ 2) ≤ W_2 ω₀ :=
        Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset (fun _ _ _ => sq_nonneg _)
      exact le_trans hsub hW2_ω₀
    have hprod : (9 / 64 : ℝ) * n_0 ^ 2 * D_star ^ 2 ≤
        (X.card : ℝ) * (144 * γ ^ 2 * n_0 * D_star ^ 2) :=
      le_trans hsq_low (le_trans hcs (mul_le_mul_of_nonneg_left hX_sq (Nat.cast_nonneg _)))
    have halg : ((1 / 1024 : ℝ) * γ⁻¹ ^ 2 * n_0) * (144 * γ ^ 2 * n_0 * D_star ^ 2) =
        (9 / 64 : ℝ) * n_0 ^ 2 * D_star ^ 2 := by
      field_simp [hγ_ne]
      ring
    have hfactor_pos : 0 < 144 * γ ^ 2 * n_0 * D_star ^ 2 := by positivity
    apply le_of_mul_le_mul_right _ hfactor_pos
    rw [halg]
    exact hprod
  exact ⟨ω₀, hX_low, hX_up, hDense⟩

private theorem csp_dyadic_calibration_and_first_moments (C₁ : ℕ) (hC₁ : 3 ≤ C₁) (r_star : ℕ) (hr : 1000 * C₁ < r_star) :
    0 < cspSigmaEdge C₁ r_star ∧
    0 < cspPEdge C₁ r_star ∧ cspPEdge C₁ r_star < 1 ∧
    (4 : ℝ) * (2 : ℝ) ^ cspL C₁ * ((cspQ C₁ - 1 : ℕ) : ℝ) *
      (cspPEdge C₁ r_star) ^ (2 ^ cspL C₁ * r_star - 1) = (2 : ℝ) ^ (- (cspGamma0 C₁ : ℝ)) ∧
    (cspBeta0 C₁ : ℝ) < cspSigmaEdge C₁ r_star * (r_star : ℝ) / 2 ∧
    cspSigmaEdge C₁ r_star * (r_star : ℝ) / 2 < (10001 / 10000 : ℝ) * (cspBeta0 C₁ : ℝ) ∧
    (∀ s : ℕ, ((2 ^ cspL C₁ * r_star).choose s : ℝ) * ((cspQ C₁ - 1 : ℕ) : ℝ) ^ s *
      (cspPEdge C₁ r_star) ^ (s * (2 ^ cspL C₁ * r_star - 1)) ≤
      (2 : ℝ) ^ (2 * (r_star : ℝ) - (cspGamma0 C₁ : ℝ) * (s : ℝ))) ∧
    (∀ s : ℕ, s ≤ 2 ^ cspL C₁ * r_star →
      cspDOmega C₁ r_star s ≤
        (2 : ℝ) ^ (2 * (r_star : ℝ) - (cspGamma0 C₁ : ℝ) * (s : ℝ) +
          cspSigmaEdge C₁ r_star * (s.choose 2 : ℝ))) ∧
    (2 : ℝ) ^ ((997 / 1000 : ℝ) * (cspLam0 C₁ : ℝ) * (r_star : ℝ)) ≤ cspDOmega C₁ r_star r_star ∧
    cspDOmega C₁ r_star r_star ≤
      (2 : ℝ) ^ ((1001 / 1000 : ℝ) * (cspLam0 C₁ : ℝ) * (r_star : ℝ)) ∧
    0 < cspPKeep C₁ r_star ∧ cspPKeep C₁ r_star < 1 ∧
    cspPKeep C₁ r_star ≤ (2 : ℝ) ^ (- (747 / 1000 : ℝ) * (cspLam0 C₁ : ℝ) * (r_star : ℝ)) ∧
    (2 : ℝ) ^ ((99 / 100 : ℝ) * (cspBeta0 C₁ : ℝ) * (2 : ℝ) ^ (2 * cspL C₁) * (r_star : ℝ)) ≤
      cspN0 C₁ r_star ∧
    cspN0 C₁ r_star ≤
      (2 : ℝ) ^ ((cspBeta0 C₁ : ℝ) * (2 : ℝ) ^ (2 * cspL C₁) * (r_star : ℝ)) ∧
    (∀ x : Fin (2 ^ cspL C₁ * r_star) → Fin (cspQ C₁),
      (homQueries x).card = (2 ^ cspL C₁ * r_star).choose 2) ∧
    (∀ x y : Fin (2 ^ cspL C₁ * r_star) → Fin (cspQ C₁),
      (homQueries x ∪ homQueries y).card =
        (2 ^ cspL C₁ * r_star).choose 2 +
          dHam x y * (2 ^ cspL C₁ * r_star - 1) - (dHam x y).choose 2) ∧
    (∀ (x : Fin (2 ^ cspL C₁ * r_star) → Fin (cspQ C₁)) (s : ℕ),
      (Finset.univ.filter (fun y => dHam x y = s)).card =
        (2 ^ cspL C₁ * r_star).choose s * (cspQ C₁ - 1) ^ s) ∧
    (∑ x : Fin (2 ^ cspL C₁ * r_star) → Fin (cspQ C₁),
      cspPKeep C₁ r_star * (cspPEdge C₁ r_star) ^ (homQueries x).card = cspN0 C₁ r_star) ∧
    (∑ xy ∈ Finset.univ.filter
        (fun xy : (Fin (2 ^ cspL C₁ * r_star) → Fin (cspQ C₁)) ×
                  (Fin (2 ^ cspL C₁ * r_star) → Fin (cspQ C₁)) => dHam xy.1 xy.2 = r_star),
      (cspPKeep C₁ r_star) ^ 2 * (cspPEdge C₁ r_star) ^ (homQueries xy.1 ∪ homQueries xy.2).card =
        cspN0 C₁ r_star * cspDStar C₁ r_star) ∧
    (∑ ab ∈ Finset.univ.filter
        (fun ab : (Fin (2 ^ cspL C₁ * r_star) → Fin (cspQ C₁)) ×
                  (Fin (2 ^ cspL C₁ * r_star) → Fin (cspQ C₁)) =>
          ab.1 ≠ ab.2 ∧ dHam ab.1 ab.2 ≤ C₁ * r_star),
      (cspPKeep C₁ r_star) ^ 2 * (cspPEdge C₁ r_star) ^ (homQueries ab.1 ∪ homQueries ab.2).card ≤
        cspN0 C₁ r_star *
          (2 : ℝ) ^ ((7 * (C₁ ^ 2 : ℕ) : ℝ) * (cspLam0 C₁ : ℝ) * (r_star : ℝ))) :=
by
  have h_core : ∀ (lam0 beta0 gamma0 L eq q : ℕ)
      (sigma_edge p_edge d_star p_keep n_0 : ℝ) (d_omega : ℕ → ℝ),
      3000 ≤ lam0 →
      beta0 = 6 * lam0 →
      gamma0 = 5 * lam0 →
      20 ≤ L →
      C₁ ≤ L →
      gamma0 ≤ L →
      eq = 2 * beta0 * 2 ^ L →
      q = 2 ^ eq + 1 →
      sigma_edge = ((eq + L + gamma0 + 2 : ℕ) : ℝ) / ((2 ^ L * r_star - 1 : ℕ) : ℝ) →
      p_edge = (2 : ℝ) ^ (- sigma_edge) →
      (∀ s : ℕ, d_omega s = ((2 ^ L * r_star).choose s : ℝ) * ((q - 1 : ℕ) : ℝ) ^ s *
        p_edge ^ (s * (2 ^ L * r_star - 1) - s.choose 2)) →
      d_star = (2 : ℝ) ^ ((1 / 4 : ℝ) * (lam0 : ℝ) * (r_star : ℝ)) →
      p_keep = d_star / d_omega r_star →
      n_0 = p_keep * ((q : ℝ) ^ (2 ^ L * r_star)) * p_edge ^ ((2 ^ L * r_star).choose 2) →
      0 < sigma_edge ∧
      0 < p_edge ∧ p_edge < 1 ∧
      (4 : ℝ) * (2 : ℝ) ^ L * ((q - 1 : ℕ) : ℝ) *
        p_edge ^ (2 ^ L * r_star - 1) = (2 : ℝ) ^ (- (gamma0 : ℝ)) ∧
      (beta0 : ℝ) < sigma_edge * (r_star : ℝ) / 2 ∧
      sigma_edge * (r_star : ℝ) / 2 < (10001 / 10000 : ℝ) * (beta0 : ℝ) ∧
      (∀ s : ℕ, ((2 ^ L * r_star).choose s : ℝ) * ((q - 1 : ℕ) : ℝ) ^ s *
        p_edge ^ (s * (2 ^ L * r_star - 1)) ≤
        (2 : ℝ) ^ (2 * (r_star : ℝ) - (gamma0 : ℝ) * (s : ℝ))) ∧
      (∀ s : ℕ, s ≤ 2 ^ L * r_star →
        d_omega s ≤
          (2 : ℝ) ^ (2 * (r_star : ℝ) - (gamma0 : ℝ) * (s : ℝ) + sigma_edge * (s.choose 2 : ℝ))) ∧
      (2 : ℝ) ^ ((997 / 1000 : ℝ) * (lam0 : ℝ) * (r_star : ℝ)) ≤ d_omega r_star ∧
      d_omega r_star ≤
        (2 : ℝ) ^ ((1001 / 1000 : ℝ) * (lam0 : ℝ) * (r_star : ℝ)) ∧
      0 < p_keep ∧ p_keep < 1 ∧
      p_keep ≤ (2 : ℝ) ^ (- (747 / 1000 : ℝ) * (lam0 : ℝ) * (r_star : ℝ)) ∧
      (2 : ℝ) ^ ((99 / 100 : ℝ) * (beta0 : ℝ) * (2 : ℝ) ^ (2 * L) * (r_star : ℝ)) ≤ n_0 ∧
      n_0 ≤ (2 : ℝ) ^ ((beta0 : ℝ) * (2 : ℝ) ^ (2 * L) * (r_star : ℝ)) ∧
      (∀ x : Fin (2 ^ L * r_star) → Fin q,
        (homQueries x).card = (2 ^ L * r_star).choose 2) ∧
      (∀ x y : Fin (2 ^ L * r_star) → Fin q,
        (homQueries x ∪ homQueries y).card =
          (2 ^ L * r_star).choose 2 +
            dHam x y * (2 ^ L * r_star - 1) - (dHam x y).choose 2) ∧
      (∀ (x : Fin (2 ^ L * r_star) → Fin q) (s : ℕ),
        (Finset.univ.filter (fun y => dHam x y = s)).card =
          (2 ^ L * r_star).choose s * (q - 1) ^ s) ∧
      (∑ x : Fin (2 ^ L * r_star) → Fin q,
        p_keep * p_edge ^ (homQueries x).card = n_0) ∧
      (∑ xy ∈ Finset.univ.filter
          (fun xy : (Fin (2 ^ L * r_star) → Fin q) ×
                    (Fin (2 ^ L * r_star) → Fin q) => dHam xy.1 xy.2 = r_star),
        p_keep ^ 2 * p_edge ^ (homQueries xy.1 ∪ homQueries xy.2).card =
          n_0 * d_star) ∧
      (∑ ab ∈ Finset.univ.filter
          (fun ab : (Fin (2 ^ L * r_star) → Fin q) ×
                    (Fin (2 ^ L * r_star) → Fin q) =>
            ab.1 ≠ ab.2 ∧ dHam ab.1 ab.2 ≤ C₁ * r_star),
        p_keep ^ 2 * p_edge ^ (homQueries ab.1 ∪ homQueries ab.2).card ≤
          n_0 * (2 : ℝ) ^ ((7 * (C₁ ^ 2 : ℕ) : ℝ) * (lam0 : ℝ) * (r_star : ℝ))) := by
    intro lam0 beta0 gamma0 L eq q sigma_edge p_edge d_star p_keep n_0 d_omega
      hlam0_ge hbeta0_def hgamma0_def hL_ge20 hC1_le_L hgamma0_le_L
      heq_def hq_def hsigma_def hpedge_def hdomega_def
      hdstar_def hpkeep_def hn0_def

    have hr_3001 : 3001 ≤ r_star := by omega
    have hr_pos : 0 < r_star := by omega
    have hr_real_pos : (0 : ℝ) < (r_star : ℝ) := by exact_mod_cast hr_pos
    have hr_real_nn : (0 : ℝ) ≤ (r_star : ℝ) := le_of_lt hr_real_pos
    have hr_real_3001 : (3001 : ℝ) ≤ (r_star : ℝ) := by exact_mod_cast hr_3001
    have hC2 : 9 ≤ C₁ ^ 2 := by nlinarith only [hC₁]
    have hC2_real : (9 : ℝ) ≤ ((C₁ ^ 2 : ℕ) : ℝ) := by exact_mod_cast hC2
    have hlam0_real_ge : (3000 : ℝ) ≤ (lam0 : ℝ) := by exact_mod_cast hlam0_ge
    have hlam0_real_pos : (0 : ℝ) < (lam0 : ℝ) := by linarith only [hlam0_real_ge]
    have hbeta0_ge : 18000 ≤ beta0 := by omega
    have hbeta0_real_ge : (18000 : ℝ) ≤ (beta0 : ℝ) := by exact_mod_cast hbeta0_ge
    have hbeta0_real : (beta0 : ℝ) = 6 * (lam0 : ℝ) := by rw [hbeta0_def]; push_cast; ring
    have hgamma0_real : (gamma0 : ℝ) = 5 * (lam0 : ℝ) := by rw [hgamma0_def]; push_cast; ring
    have h_exp_ind : ∀ m : ℕ, 20 ≤ m → 20000 * (m + 2) ≤ 2 ^ m := by
      intro m hm
      refine Nat.le_induction ?_ ?_ m hm
      · norm_num
      · intro k hk ih
        calc
          20000 * (k + 1 + 2) ≤ 2 * (20000 * (k + 2)) := by omega
          _ ≤ 2 * 2 ^ k := Nat.mul_le_mul_left 2 ih
          _ = 2 ^ (k + 1) := by ring
    have h2L_lin : 20000 * (L + 2) ≤ 2 ^ L := h_exp_ind L hL_ge20
    have h2L_lg : 10000 * (L + gamma0 + 2) ≤ 2 ^ L := by omega
    have h2L_mil : 1048576 ≤ 2 ^ L := by
      calc
        1048576 = 2 ^ 20 := by norm_num
        _ ≤ 2 ^ L := Nat.pow_le_pow_right (by norm_num) hL_ge20
    have hC1_le_2L : C₁ ≤ 2 ^ L := le_trans hC1_le_L (le_of_lt Nat.lt_two_pow_self)
    have hq_sub1 : q - 1 = 2 ^ eq := by
      rw [hq_def]
      exact Nat.add_sub_cancel _ _

    let N : ℕ := 2 ^ L * r_star
    have hN_def : N = 2 ^ L * r_star := rfl
    have hN_ge3001 : 3001 ≤ N := by
      rw [hN_def]
      nlinarith only [h2L_mil, hr_3001]
    have hN_ge1 : 1 ≤ N := by omega
    have hr_le_N : r_star ≤ N := by
      rw [hN_def]
      nlinarith only [h2L_mil, hr_3001]
    have hCr_le_N : C₁ * r_star ≤ N := Nat.mul_le_mul_right r_star hC1_le_2L
    have hN1_pos_nat : 0 < N - 1 := by omega
    have hN1_pos : (0 : ℝ) < ((N - 1 : ℕ) : ℝ) := by exact_mod_cast hN1_pos_nat
    have hN_pos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)

    have h_choose2_nat : ∀ m : ℕ, 2 * m.choose 2 = m * (m - 1) := by
      intro m
      induction m with
      | zero => rfl
      | succ m ih =>
        cases m with
        | zero => rfl
        | succ k =>
          have hc : (k + 2).choose 2 = (k + 1) + (k + 1).choose 2 := by
            rw [Nat.choose_succ_succ, Nat.choose_one_right]
          have ih' : 2 * (k + 1).choose 2 = (k + 1) * k := ih
          have hsub : k + 2 - 1 = k + 1 := rfl
          rw [hc, hsub]
          linarith only [ih']
    have h_choose2_int : ∀ m : ℕ, 2 * (m.choose 2 : ℤ) = (m : ℤ) * ((m : ℤ) - 1) := by
      intro m
      cases m with
      | zero => norm_num
      | succ k =>
        have hnat := h_choose2_nat (k + 1)
        have hcast : (2 : ℤ) * ((k + 1).choose 2 : ℤ) = ((k + 1 : ℕ) : ℤ) * (k : ℤ) := by
          exact_mod_cast hnat
        push_cast at hcast ⊢
        linarith only [hcast]
    have h_choose2_real : ∀ m : ℕ, 2 * (m.choose 2 : ℝ) = (m : ℝ) * ((m : ℝ) - 1) := by
      intro m
      exact_mod_cast h_choose2_int m
    have hs_choose_le_N : ∀ s : ℕ, s ≤ N → s.choose 2 ≤ s * (N - 1) := by
      intro s hs
      rcases Nat.eq_zero_or_pos s with rfl | hs_pos
      · simp
      · have h1 : s.choose 2 ≤ 2 * s.choose 2 := Nat.le_mul_of_pos_left _ (by omega)
        have h2 := h_choose2_nat s
        have h3 : s * (s - 1) ≤ s * (N - 1) := Nat.mul_le_mul_left s (by omega)
        omega

    
    
    
    have h_ord_pairs : ∀ A : Finset (Fin N),
        ((A ×ˢ A).filter (fun uv : Fin N × Fin N => uv.1 < uv.2)).card = A.card.choose 2 := by
      intro A
      rw [← Finset.card_powersetCard 2 A]
      refine Finset.card_bij (fun uv _ => ({uv.1, uv.2} : Finset (Fin N))) ?_ ?_ ?_
      · intro uv huv
        simp only [Finset.mem_filter, Finset.mem_product] at huv
        rw [Finset.mem_powersetCard]
        refine ⟨?_, Finset.card_pair (ne_of_lt huv.2)⟩
        intro z hz
        simp only [Finset.mem_insert, Finset.mem_singleton] at hz
        rcases hz with rfl | rfl
        · exact huv.1.1
        · exact huv.1.2
      · intro uv₁ h₁ uv₂ h₂ heq
        dsimp only at heq
        simp only [Finset.mem_filter, Finset.mem_product] at h₁ h₂
        have hm1 : uv₁.1 ∈ ({uv₂.1, uv₂.2} : Finset (Fin N)) := by
          rw [← heq]; simp
        have hm2 : uv₁.2 ∈ ({uv₂.1, uv₂.2} : Finset (Fin N)) := by
          rw [← heq]; simp
        simp only [Finset.mem_insert, Finset.mem_singleton] at hm1 hm2
        rcases hm1 with h11 | h12 <;> rcases hm2 with h21 | h22
        · exfalso; exact (ne_of_lt h₁.2) (h11.trans h21.symm)
        · exact Prod.ext h11 h22
        · exfalso
          have hlt1 : uv₁.1 < uv₁.2 := h₁.2
          have hlt2 : uv₂.1 < uv₂.2 := h₂.2
          rw [h12, h21] at hlt1
          exact lt_asymm hlt1 hlt2
        · exfalso; exact (ne_of_lt h₁.2) (h12.trans h22.symm)
      · intro T hT
        rw [Finset.mem_powersetCard] at hT
        rcases Finset.card_eq_two.mp hT.2 with ⟨a, b, hab, rfl⟩
        have ha : a ∈ A := hT.1 (by simp)
        have hb : b ∈ A := hT.1 (by simp)
        rcases lt_trichotomy a b with hlt | rfl | hgt
        · refine ⟨(a, b), ?_, rfl⟩
          simp [ha, hb, hlt]
        · exact absurd rfl hab
        · refine ⟨(b, a), ?_, Finset.pair_comm b a⟩
          simp [ha, hb, hgt]
    have h_psi_inj : ∀ z : Fin N → Fin q,
        Function.Injective (fun uv : Fin N × Fin N => (uv.1, uv.2, z uv.1, z uv.2)) := by
      intro z uv₁ uv₂ h
      simp only [Prod.mk.injEq] at h
      exact Prod.ext h.1 h.2.1
    have h_hom_card : ∀ x : Fin N → Fin q, (homQueries x).card = N.choose 2 := by
      intro x
      unfold homQueries
      rw [Finset.card_image_of_injective _ (h_psi_inj x)]
      have huniv_eq : (Finset.univ.filter (fun uv : Fin N × Fin N => uv.1 < uv.2)) =
          ((Finset.univ : Finset (Fin N)) ×ˢ (Finset.univ : Finset (Fin N))).filter
            (fun uv => uv.1 < uv.2) := by
        ext uv
        simp
      rw [huniv_eq, h_ord_pairs, Finset.card_univ, Fintype.card_fin]
    have h_union_card : ∀ x y : Fin N → Fin q,
        (homQueries x ∪ homQueries y).card =
          N.choose 2 + dHam x y * (N - 1) - (dHam x y).choose 2 := by
      intro x y
      let S := diffCoords x y
      let s := dHam x y
      let A : Finset (Fin N) := Finset.univ \ S
      have hs_eq : S.card = s := rfl
      have hs_le_N : s ≤ N := by
        simpa [hs_eq, Fintype.card_fin] using Finset.card_le_univ S
      have hA_card : A.card = N - s := by
        dsimp [A]
        rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_fin, hs_eq]
      have hinter_eq : homQueries x ∩ homQueries y =
          ((A ×ˢ A).filter (fun uv : Fin N × Fin N => uv.1 < uv.2)).image
            (fun uv => (uv.1, uv.2, x uv.1, x uv.2)) := by
        ext t
        simp only [Finset.mem_inter, homQueries, Finset.mem_image, Finset.mem_filter,
          Finset.mem_univ, true_and, Finset.mem_product, A, Finset.mem_sdiff, S, diffCoords,
          not_not]
        constructor
        · rintro ⟨⟨uv₁, h₁, rfl⟩, ⟨uv₂, h₂, heq⟩⟩
          simp only [Prod.mk.injEq] at heq
          rcases heq with ⟨heq1, heq2, heq3, heq4⟩
          refine ⟨uv₁, ⟨⟨?_, ?_⟩, h₁⟩, rfl⟩
          · rw [← heq3, heq1]
          · rw [← heq4, heq2]
        · rintro ⟨uv, ⟨⟨hx1, hx2⟩, huv⟩, rfl⟩
          refine ⟨⟨uv, huv, rfl⟩, ⟨uv, huv, ?_⟩⟩
          rw [hx1, hx2]
      have hinter_card : (homQueries x ∩ homQueries y).card = (N - s).choose 2 := by
        rw [hinter_eq, Finset.card_image_of_injective _ (h_psi_inj x), h_ord_pairs, hA_card]
      have hunion_ie := Finset.card_union_add_card_inter (homQueries x) (homQueries y)
      rw [hinter_card, h_hom_card x, h_hom_card y] at hunion_ie
      have hs_choose_le : s.choose 2 ≤ s * (N - 1) := hs_choose_le_N s hs_le_N
      have hs_choose_le_tot : s.choose 2 ≤ N.choose 2 + s * (N - 1) :=
        le_trans hs_choose_le (Nat.le_add_left _ _)
      suffices h_int : ((homQueries x ∪ homQueries y).card : ℤ) =
          ((N.choose 2 + s * (N - 1) - s.choose 2 : ℕ) : ℤ) from Int.ofNat.inj h_int
      have hie_int : ((homQueries x ∪ homQueries y).card : ℤ) + ((N - s).choose 2 : ℤ) =
          (N.choose 2 : ℤ) + (N.choose 2 : ℤ) := by exact_mod_cast hunion_ie
      have h2N := h_choose2_int N
      have h2s := h_choose2_int s
      have h2Ns := h_choose2_int (N - s)
      rw [Nat.cast_sub hs_le_N] at h2Ns
      rw [Nat.cast_sub hs_choose_le_tot, Nat.cast_add, Nat.cast_mul, Nat.cast_sub hN_ge1]
      push_cast
      have hpoly : ((N : ℤ) - (s : ℤ)) * ((N : ℤ) - (s : ℤ) - 1) +
          ((N : ℤ) * ((N : ℤ) - 1) + 2 * (s : ℤ) * ((N : ℤ) - 1) - (s : ℤ) * ((s : ℤ) - 1)) =
          2 * ((N : ℤ) * ((N : ℤ) - 1)) := by ring
      linarith only [hie_int, h2N, h2s, h2Ns, hpoly]
    have h_sphere : ∀ (x : Fin N → Fin q) (s : ℕ),
        (Finset.univ.filter (fun y => dHam x y = s)).card = N.choose s * (q - 1) ^ s := by
      intro x s
      let Fib : Finset (Fin N) → Finset (Fin N → Fin q) := fun S =>
        Fintype.piFinset (fun v : Fin N =>
          if v ∈ S then Finset.univ.erase (x v) else ({x v} : Finset (Fin q)))
      have hFib_mem : ∀ (S : Finset (Fin N)) (y : Fin N → Fin q),
          y ∈ Fib S ↔ diffCoords x y = S := by
        intro S y
        simp only [Fib, Fintype.mem_piFinset, Finset.ext_iff, diffCoords, Finset.mem_filter,
          Finset.mem_univ, true_and]
        constructor
        · intro hy v
          specialize hy v
          by_cases hv : v ∈ S
          · simp only [if_pos hv, Finset.mem_erase, Finset.mem_univ, and_true] at hy
            exact ⟨fun _ => hv, fun _ => Ne.symm hy⟩
          · simp only [if_neg hv, Finset.mem_singleton] at hy
            exact ⟨fun hne => absurd hy.symm hne, fun h => absurd h hv⟩
        · intro hS v
          by_cases hv : v ∈ S
          · simp only [if_pos hv, Finset.mem_erase, Finset.mem_univ, and_true]
            exact Ne.symm ((hS v).mpr hv)
          · simp only [if_neg hv, Finset.mem_singleton]
            by_contra hne
            exact hv ((hS v).mp (Ne.symm hne))
      have h_bi : Finset.univ.filter (fun y : Fin N → Fin q => dHam x y = s) =
          ((Finset.univ : Finset (Fin N)).powersetCard s).biUnion Fib := by
        ext y
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion,
          Finset.mem_powersetCard, hFib_mem, dHam]
        constructor
        · intro hs
          exact ⟨diffCoords x y, ⟨Finset.subset_univ _, hs⟩, rfl⟩
        · rintro ⟨S, ⟨_, hScard⟩, rfl⟩
          exact hScard
      have h_disj : (((Finset.univ : Finset (Fin N)).powersetCard s : Finset (Finset (Fin N))) :
          Set (Finset (Fin N))).PairwiseDisjoint Fib := by
        intro S₁ _ S₂ _ hne
        rw [Function.onFun, Finset.disjoint_left]
        intro y hy₁ hy₂
        rw [hFib_mem] at hy₁ hy₂
        exact hne (hy₁.symm.trans hy₂)
      rw [h_bi, Finset.card_biUnion h_disj]
      have hFib_card : ∀ S ∈ (Finset.univ : Finset (Fin N)).powersetCard s,
          (Fib S).card = (q - 1) ^ s := by
        intro S hS
        rw [Finset.mem_powersetCard] at hS
        dsimp [Fib]
        rw [Fintype.card_piFinset]
        have hterm : ∀ v : Fin N,
            (if v ∈ S then Finset.univ.erase (x v) else ({x v} : Finset (Fin q))).card =
              if v ∈ S then q - 1 else 1 := by
          intro v
          split_ifs
          · rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
          · exact Finset.card_singleton _
        simp_rw [hterm]
        rw [Finset.prod_ite_mem, Finset.univ_inter, Finset.prod_const, hS.2]
      rw [Finset.sum_congr rfl hFib_card, Finset.sum_const, smul_eq_mul,
        Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
    have h_pair_sphere : ∀ s : ℕ,
        (Finset.univ.filter
          (fun xy : (Fin N → Fin q) × (Fin N → Fin q) => dHam xy.1 xy.2 = s)).card =
          q ^ N * (N.choose s * (q - 1) ^ s) := by
      intro s
      let G : (Fin N → Fin q) → Finset ((Fin N → Fin q) × (Fin N → Fin q)) :=
        fun x => (Finset.univ.filter (fun y => dHam x y = s)).image (fun y => (x, y))
      have h_eq : Finset.univ.filter
          (fun xy : (Fin N → Fin q) × (Fin N → Fin q) => dHam xy.1 xy.2 = s) =
          (Finset.univ : Finset (Fin N → Fin q)).biUnion G := by
        ext xy
        simp only [G, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion,
          Finset.mem_image]
        constructor
        · intro h
          exact ⟨xy.1, xy.2, h, Prod.eta xy⟩
        · rintro ⟨x, y, h, rfl⟩
          exact h
      have h_disj : ((Finset.univ : Finset (Fin N → Fin q)) : Set (Fin N → Fin q)).PairwiseDisjoint G := by
        intro x₁ _ x₂ _ hne
        rw [Function.onFun, Finset.disjoint_left]
        intro p hp₁ hp₂
        rcases Finset.mem_image.mp hp₁ with ⟨_, _, rfl⟩
        rcases Finset.mem_image.mp hp₂ with ⟨_, _, hp⟩
        exact hne (Prod.mk.inj hp).1.symm
      rw [h_eq, Finset.card_biUnion h_disj]
      have hG_card : ∀ x ∈ (Finset.univ : Finset (Fin N → Fin q)),
          (G x).card = N.choose s * (q - 1) ^ s := by
        intro x _
        dsimp [G]
        rw [Finset.card_image_of_injective _ (fun _ _ h => (Prod.mk.inj h).2), h_sphere x s]
      rw [Finset.sum_congr rfl hG_card, Finset.sum_const, smul_eq_mul,
        Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]

    
    
    
    have h4_eq_rpow : (4 : ℝ) ^ r_star = (2 : ℝ) ^ (2 * (r_star : ℝ)) := by
      have h4 : (4 : ℝ) = (2 : ℝ) ^ (2 : ℕ) := by norm_num
      rw [h4, ← pow_mul, ← Real.rpow_natCast, Nat.cast_mul, Nat.cast_ofNat]
    have h_upper_s : ∀ s : ℕ,
        (N.choose s : ℝ) * ((r_star : ℝ) / (4 * (N : ℝ))) ^ s ≤ (4 : ℝ) ^ r_star / (4 : ℝ) ^ s := by
      intro s
      have h_exp_4 : Real.exp (r_star : ℝ) ≤ (4 : ℝ) ^ r_star := by
        have h1 : Real.exp (r_star : ℝ) = (Real.exp 1) ^ r_star := by
          simp
        have h2 : Real.exp 1 ≤ 4 := by
          have hlt := Real.exp_one_lt_d9
          linarith only [hlt]
        rw [h1]
        exact pow_le_pow_left₀ (le_of_lt (Real.exp_pos 1)) h2 r_star
      have hchoose : (N.choose s : ℝ) ≤ (N : ℝ) ^ s / (s.factorial : ℝ) :=
        Nat.choose_le_pow_div s N
      have hpow_div : ((r_star : ℝ) / (4 * (N : ℝ))) ^ s =
          (r_star : ℝ) ^ s / ((4 : ℝ) ^ s * (N : ℝ) ^ s) := by
        rw [div_pow, mul_pow]
      have hstep1 : (N.choose s : ℝ) * ((r_star : ℝ) / (4 * (N : ℝ))) ^ s ≤
          ((N : ℝ) ^ s / (s.factorial : ℝ)) *
            ((r_star : ℝ) ^ s / ((4 : ℝ) ^ s * (N : ℝ) ^ s)) := by
        rw [hpow_div]
        exact mul_le_mul_of_nonneg_right hchoose (by positivity)
      have hNs_ne : (N : ℝ) ^ s ≠ 0 := ne_of_gt (pow_pos hN_pos s)
      have hsimp : ((N : ℝ) ^ s / (s.factorial : ℝ)) *
          ((r_star : ℝ) ^ s / ((4 : ℝ) ^ s * (N : ℝ) ^ s)) =
          ((r_star : ℝ) ^ s / (s.factorial : ℝ)) / (4 : ℝ) ^ s := by
        field_simp [hNs_ne]
      have hexp_s : (r_star : ℝ) ^ s / (s.factorial : ℝ) ≤ (4 : ℝ) ^ r_star :=
        le_trans (Real.pow_div_factorial_le_exp (r_star : ℝ) hr_real_nn s) h_exp_4
      have hstep2 : ((r_star : ℝ) ^ s / (s.factorial : ℝ)) / (4 : ℝ) ^ s ≤
          (4 : ℝ) ^ r_star / (4 : ℝ) ^ s :=
        div_le_div_of_nonneg_right hexp_s (by positivity)
      linarith only [hstep1, hsimp, hstep2]
    have h_env_all : ∀ s : ℕ,
        (N.choose s : ℝ) * ((r_star : ℝ) / (4 * (N : ℝ))) ^ s ≤ (2 : ℝ) ^ (2 * (r_star : ℝ)) := by
      intro s
      rw [← h4_eq_rpow]
      have h4s_ge1 : (1 : ℝ) ≤ (4 : ℝ) ^ s := one_le_pow₀ (by norm_num)
      have hdiv : (4 : ℝ) ^ r_star / (4 : ℝ) ^ s ≤ (4 : ℝ) ^ r_star / 1 :=
        div_le_div_of_nonneg_left (by positivity) zero_lt_one h4s_ge1
      rw [div_one] at hdiv
      exact le_trans (h_upper_s s) hdiv
    have h_env_diag_up : (N.choose r_star : ℝ) * ((r_star : ℝ) / (4 * (N : ℝ))) ^ r_star ≤ 1 := by
      have hdiv1 : (4 : ℝ) ^ r_star / (4 : ℝ) ^ r_star = 1 :=
        div_self (ne_of_gt (by positivity : (0 : ℝ) < (4 : ℝ) ^ r_star))
      simpa [hdiv1] using h_upper_s r_star
    have h_env_diag_low :
        (2 : ℝ) ^ (- (2 * (r_star : ℝ))) ≤
          (N.choose r_star : ℝ) * ((r_star : ℝ) / (4 * (N : ℝ))) ^ r_star := by
      have h_fall : ∀ k M : ℕ, k ≤ M → M ^ k ≤ M.choose k * k ^ k := by
        intro k
        induction k with
        | zero =>
          intro M _
          simp
        | succ k ih =>
          intro M hM
          cases M with
          | zero => omega
          | succ M' =>
            have hM' : k ≤ M' := by omega
            cases k with
            | zero =>
              simp [Nat.choose_one_right]
            | succ k' =>
              let km := k' + 1
              have hkm_pos : 0 < km := by omega
              have hkm_le : km ≤ M' := hM'
              have hcross : (M' + 1) * km ≤ M' * (km + 1) := by nlinarith only [hkm_le]
              have hpow_cross : (M' + 1) ^ km * km ^ km ≤ M' ^ km * (km + 1) ^ km := by
                simpa [mul_pow] using Nat.pow_le_pow_left hcross km
              have h_ih := Nat.mul_le_mul_right ((km + 1) ^ km) (ih M' hkm_le)
              have hchain : (M' + 1) ^ km * km ^ km ≤ (M'.choose km * (km + 1) ^ km) * km ^ km := by
                calc
                  (M' + 1) ^ km * km ^ km ≤ M' ^ km * (km + 1) ^ km := hpow_cross
                  _ ≤ (M'.choose km * km ^ km) * (km + 1) ^ km := h_ih
                  _ = (M'.choose km * (km + 1) ^ km) * km ^ km := by ring
              have hstep : (M' + 1) ^ km ≤ M'.choose km * (km + 1) ^ km :=
                Nat.le_of_mul_le_mul_right hchain (Nat.pow_pos hkm_pos)
              have hmul := Nat.mul_le_mul_left (M' + 1) hstep
              have hid := Nat.add_one_mul_choose_eq M' km
              calc
                (M' + 1) ^ (km + 1) = (M' + 1) * (M' + 1) ^ km := by ring
                _ ≤ (M' + 1) * (M'.choose km * (km + 1) ^ km) := hmul
                _ = ((M' + 1) * M'.choose km) * (km + 1) ^ km := by ring
                _ = ((M' + 1).choose (km + 1) * (km + 1)) * (km + 1) ^ km := by rw [hid]
                _ = (M' + 1).choose (km + 1) * (km + 1) ^ (km + 1) := by ring
      have hNr_real : (N : ℝ) ^ r_star ≤ (N.choose r_star : ℝ) * (r_star : ℝ) ^ r_star := by
        exact_mod_cast h_fall r_star N hr_le_N
      have hdiv := div_le_div_of_nonneg_right hNr_real
        (by positivity : (0 : ℝ) ≤ (4 : ℝ) ^ r_star * (N : ℝ) ^ r_star)
      have hNr_ne : (N : ℝ) ^ r_star ≠ 0 := ne_of_gt (pow_pos hN_pos r_star)
      have hlhs : (N : ℝ) ^ r_star / ((4 : ℝ) ^ r_star * (N : ℝ) ^ r_star) =
          (2 : ℝ) ^ (- (2 * (r_star : ℝ))) := by
        have h1 : (N : ℝ) ^ r_star / ((4 : ℝ) ^ r_star * (N : ℝ) ^ r_star) =
            ((4 : ℝ) ^ r_star)⁻¹ := by
          field_simp [hNr_ne]
        rw [h1, h4_eq_rpow, ← Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
      have hrhs : (N.choose r_star : ℝ) * (r_star : ℝ) ^ r_star /
          ((4 : ℝ) ^ r_star * (N : ℝ) ^ r_star) =
          (N.choose r_star : ℝ) * ((r_star : ℝ) / (4 * (N : ℝ))) ^ r_star := by
        rw [div_pow, mul_pow, mul_div_assoc]
      rwa [hlhs, hrhs] at hdiv

    
    
    
    have hσ_pos : 0 < sigma_edge := by
      rw [hsigma_def, ← hN_def]
      have hnum : (0 : ℝ) < ((eq + L + gamma0 + 2 : ℕ) : ℝ) := by
        exact_mod_cast (show 0 < eq + L + gamma0 + 2 by omega)
      exact div_pos hnum hN1_pos
    have hp_edge_pos : 0 < p_edge := by
      rw [hpedge_def]
      exact Real.rpow_pos_of_pos (by norm_num) _
    have hp_edge_lt1 : p_edge < 1 := by
      rw [hpedge_def, show (1 : ℝ) = (2 : ℝ) ^ (0 : ℝ) by norm_num]
      exact Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (by linarith only [hσ_pos])
    have hp_edge_pow : ∀ k : ℕ, p_edge ^ k = (2 : ℝ) ^ (- sigma_edge * (k : ℝ)) := by
      intro k
      rw [hpedge_def, ← Real.rpow_natCast _ k, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    have h_cal : (4 : ℝ) * (2 : ℝ) ^ L * ((q - 1 : ℕ) : ℝ) * p_edge ^ (N - 1) =
        (2 : ℝ) ^ (- (gamma0 : ℝ)) := by
      have hq1_real : ((q - 1 : ℕ) : ℝ) = (2 : ℝ) ^ eq := by
        rw [hq_sub1, Nat.cast_pow, Nat.cast_ofNat]
      have hlhs1 : (4 : ℝ) * (2 : ℝ) ^ L * ((q - 1 : ℕ) : ℝ) =
          (2 : ℝ) ^ ((eq + L + 2 : ℕ) : ℝ) := by
        rw [hq1_real, show (4 : ℝ) = (2 : ℝ) ^ (2 : ℕ) by norm_num]
        have hp : (2 : ℝ) ^ (2 : ℕ) * (2 : ℝ) ^ L * (2 : ℝ) ^ eq = (2 : ℝ) ^ (eq + L + 2) := by
          rw [pow_add, pow_add]
          ring
        rw [hp, ← Real.rpow_natCast]
      have hlhs2 : p_edge ^ (N - 1) = (2 : ℝ) ^ (- ((eq + L + gamma0 + 2 : ℕ) : ℝ)) := by
        rw [hp_edge_pow (N - 1), hsigma_def, ← hN_def]
        congr 1
        field_simp [ne_of_gt hN1_pos]
      rw [hlhs1, hlhs2, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      congr 1
      push_cast
      ring

    have hσ_low : (beta0 : ℝ) < sigma_edge * (r_star : ℝ) / 2 := by
      have hnat : 2 * beta0 * (N - 1) < (eq + L + gamma0 + 2) * r_star := by
        have h1 : 2 * beta0 * (N - 1) ≤ 2 * beta0 * N :=
          Nat.mul_le_mul_left _ (Nat.sub_le N 1)
        have h2 : 2 * beta0 * N = eq * r_star := by
          rw [hN_def, heq_def]; ring
        have h3 : eq * r_star < (eq + L + gamma0 + 2) * r_star :=
          Nat.mul_lt_mul_of_pos_right (by omega) hr_pos
        omega
      have hreal : (2 : ℝ) * (beta0 : ℝ) * ((N - 1 : ℕ) : ℝ) <
          ((eq + L + gamma0 + 2 : ℕ) : ℝ) * (r_star : ℝ) := by exact_mod_cast hnat
      rw [hsigma_def, ← hN_def, lt_div_iff₀ (by norm_num : (0 : ℝ) < 2),
        div_mul_eq_mul_div, lt_div_iff₀ hN1_pos]
      linarith only [hreal]

    have hσ_up : sigma_edge * (r_star : ℝ) / 2 < (10001 / 10000 : ℝ) * (beta0 : ℝ) := by
      have hnat : 10000 * (eq + L + gamma0 + 2) * r_star < 20002 * beta0 * (N - 1) := by
        have hA : 10000 * (L + gamma0 + 2) * r_star ≤ beta0 * N := by
          have hA1 : 10000 * (L + gamma0 + 2) * r_star ≤ N := Nat.mul_le_mul_right r_star h2L_lg
          have hA2 : 1 * N ≤ beta0 * N := Nat.mul_le_mul_right N (by omega)
          omega
        have hB : 20002 * beta0 < beta0 * N := by
          have hB1 : 20002 < N := by
            rw [hN_def]
            nlinarith only [h2L_mil, hr_3001]
          nlinarith only [hbeta0_ge, hB1]
        have hN_split : N = (N - 1) + 1 := (Nat.sub_add_cancel hN_ge1).symm
        have heq_r : eq * r_star = 2 * beta0 * N := by
          rw [hN_def, heq_def]; ring
        have hexp : 10000 * (eq + L + gamma0 + 2) * r_star =
            10000 * (eq * r_star) + 10000 * (L + gamma0 + 2) * r_star := by ring
        rw [hexp, heq_r]
        nlinarith only [hA, hB, hN_split]
      have hreal : (10000 : ℝ) * ((eq + L + gamma0 + 2 : ℕ) : ℝ) * (r_star : ℝ) <
          (20002 : ℝ) * (beta0 : ℝ) * ((N - 1 : ℕ) : ℝ) := by exact_mod_cast hnat
      rw [hsigma_def, ← hN_def, div_lt_iff₀ (by norm_num : (0 : ℝ) < 2),
        div_mul_eq_mul_div, div_lt_iff₀ hN1_pos]
      linarith only [hreal]

    have h_qp_eq : ((q - 1 : ℕ) : ℝ) * p_edge ^ (N - 1) =
        ((r_star : ℝ) / (4 * (N : ℝ))) * (2 : ℝ) ^ (- (gamma0 : ℝ)) := by
      have h42L_pos : (0 : ℝ) < (4 : ℝ) * (2 : ℝ) ^ L := by positivity
      have hN_cast : (N : ℝ) = (2 : ℝ) ^ L * (r_star : ℝ) := by
        rw [hN_def]; push_cast; rfl
      have hrhs1 : ((4 : ℝ) * (2 : ℝ) ^ L) * ((r_star : ℝ) / (4 * (N : ℝ))) = 1 := by
        rw [hN_cast]
        field_simp [ne_of_gt hr_real_pos, ne_of_gt h42L_pos]
      have hrhs : ((4 : ℝ) * (2 : ℝ) ^ L) *
          (((r_star : ℝ) / (4 * (N : ℝ))) * (2 : ℝ) ^ (- (gamma0 : ℝ))) =
          (2 : ℝ) ^ (- (gamma0 : ℝ)) := by
        rw [← mul_assoc, hrhs1, one_mul]
      have hlhs : ((4 : ℝ) * (2 : ℝ) ^ L) * (((q - 1 : ℕ) : ℝ) * p_edge ^ (N - 1)) =
          (2 : ℝ) ^ (- (gamma0 : ℝ)) := by
        have hmul : ((4 : ℝ) * (2 : ℝ) ^ L) * (((q - 1 : ℕ) : ℝ) * p_edge ^ (N - 1)) =
            (4 : ℝ) * (2 : ℝ) ^ L * ((q - 1 : ℕ) : ℝ) * p_edge ^ (N - 1) := by ring
        rw [hmul, h_cal]
      exact mul_left_cancel₀ (ne_of_gt h42L_pos) (hlhs.trans hrhs.symm)

    have h_base_s : ∀ s : ℕ,
        (N.choose s : ℝ) * ((q - 1 : ℕ) : ℝ) ^ s * p_edge ^ (s * (N - 1)) =
          ((N.choose s : ℝ) * ((r_star : ℝ) / (4 * (N : ℝ))) ^ s) *
            (2 : ℝ) ^ (- (gamma0 : ℝ) * (s : ℝ)) := by
      intro s
      rw [mul_assoc, mul_comm s (N - 1), pow_mul, ← mul_pow, h_qp_eq, mul_pow, ← mul_assoc,
        ← Real.rpow_natCast ((2 : ℝ) ^ (- (gamma0 : ℝ))) s,
        ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]

    have h_binom_edge : ∀ s : ℕ,
        (N.choose s : ℝ) * ((q - 1 : ℕ) : ℝ) ^ s * p_edge ^ (s * (N - 1)) ≤
          (2 : ℝ) ^ (2 * (r_star : ℝ) - (gamma0 : ℝ) * (s : ℝ)) := by
      intro s
      rw [h_base_s s,
        show 2 * (r_star : ℝ) - (gamma0 : ℝ) * (s : ℝ) =
          2 * (r_star : ℝ) + (- (gamma0 : ℝ) * (s : ℝ)) by ring,
        Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      exact mul_le_mul_of_nonneg_right (h_env_all s) (by positivity)

    have h_DOm_eq : ∀ s : ℕ, s ≤ N →
        d_omega s =
          ((N.choose s : ℝ) * ((r_star : ℝ) / (4 * (N : ℝ))) ^ s) *
            (2 : ℝ) ^ (- (gamma0 : ℝ) * (s : ℝ) + sigma_edge * (s.choose 2 : ℝ)) := by
      intro s hs
      have hsub := hs_choose_le_N s hs
      have hp_split : p_edge ^ (s * (N - 1) - s.choose 2) =
          p_edge ^ (s * (N - 1)) * (2 : ℝ) ^ (sigma_edge * (s.choose 2 : ℝ)) := by
        have hp1 : p_edge ^ (s * (N - 1) - s.choose 2) * p_edge ^ (s.choose 2) =
            p_edge ^ (s * (N - 1)) := by
          rw [← pow_add, Nat.sub_add_cancel hsub]
        have hp2 : p_edge ^ (s.choose 2) * (2 : ℝ) ^ (sigma_edge * (s.choose 2 : ℝ)) = 1 := by
          rw [hp_edge_pow (s.choose 2), ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
          have hexp0 : - sigma_edge * (s.choose 2 : ℝ) + sigma_edge * (s.choose 2 : ℝ) = 0 := by
            ring
          rw [hexp0, Real.rpow_zero]
        calc
          p_edge ^ (s * (N - 1) - s.choose 2)
            = p_edge ^ (s * (N - 1) - s.choose 2) *
                (p_edge ^ (s.choose 2) * (2 : ℝ) ^ (sigma_edge * (s.choose 2 : ℝ))) := by
                  rw [hp2, mul_one]
          _ = (p_edge ^ (s * (N - 1) - s.choose 2) * p_edge ^ (s.choose 2)) *
                (2 : ℝ) ^ (sigma_edge * (s.choose 2 : ℝ)) := by ring
          _ = p_edge ^ (s * (N - 1)) * (2 : ℝ) ^ (sigma_edge * (s.choose 2 : ℝ)) := by rw [hp1]
      rw [hdomega_def s, ← hN_def, hp_split, ← mul_assoc, h_base_s s, mul_assoc,
        ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]

    have h_DOm_s : ∀ s : ℕ, s ≤ N →
        d_omega s ≤
          (2 : ℝ) ^ (2 * (r_star : ℝ) - (gamma0 : ℝ) * (s : ℝ) + sigma_edge * (s.choose 2 : ℝ)) := by
      intro s hs
      rw [h_DOm_eq s hs,
        show (2 : ℝ) ^ (2 * (r_star : ℝ) - (gamma0 : ℝ) * (s : ℝ) + sigma_edge * (s.choose 2 : ℝ)) =
          (2 : ℝ) ^ (2 * (r_star : ℝ)) *
            (2 : ℝ) ^ (- (gamma0 : ℝ) * (s : ℝ) + sigma_edge * (s.choose 2 : ℝ)) by
          rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]; congr 1; ring]
      exact mul_le_mul_of_nonneg_right (h_env_all s) (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _)

    have h_DOm_low :
        (2 : ℝ) ^ ((997 / 1000 : ℝ) * (lam0 : ℝ) * (r_star : ℝ)) ≤ d_omega r_star := by
      rw [h_DOm_eq r_star hr_le_N]
      have hstep1 : (2 : ℝ) ^ (- (2 * (r_star : ℝ)) +
          (- (gamma0 : ℝ) * (r_star : ℝ) + sigma_edge * (r_star.choose 2 : ℝ))) ≤
          ((N.choose r_star : ℝ) * ((r_star : ℝ) / (4 * (N : ℝ))) ^ r_star) *
            (2 : ℝ) ^ (- (gamma0 : ℝ) * (r_star : ℝ) + sigma_edge * (r_star.choose 2 : ℝ)) := by
        rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
        exact mul_le_mul_of_nonneg_right h_env_diag_low (by positivity)
      have hexp : (997 / 1000 : ℝ) * (lam0 : ℝ) * (r_star : ℝ) ≤
          - (2 * (r_star : ℝ)) +
            (- (gamma0 : ℝ) * (r_star : ℝ) + sigma_edge * (r_star.choose 2 : ℝ)) := by
        have hc2 := h_choose2_real r_star
        have hcr : (r_star.choose 2 : ℝ) = (r_star : ℝ) * ((r_star : ℝ) - 1) / 2 := by
          linarith only [hc2]
        rw [hcr, hgamma0_real]
        have hmul_eq : sigma_edge * ((r_star : ℝ) * ((r_star : ℝ) - 1) / 2) =
            (sigma_edge * (r_star : ℝ) / 2) * ((r_star : ℝ) - 1) := by ring
        rw [hmul_eq]
        have hlow_mul : (6 * (lam0 : ℝ)) * ((r_star : ℝ) - 1) ≤
            (sigma_edge * (r_star : ℝ) / 2) * ((r_star : ℝ) - 1) :=
          mul_le_mul_of_nonneg_right (by linarith only [hσ_low, hbeta0_real])
            (by linarith only [hr_real_3001])
        have hmargin : 6000 * (lam0 : ℝ) + 2000 * (r_star : ℝ) ≤
            3 * (lam0 : ℝ) * (r_star : ℝ) := by
          nlinarith only [hlam0_real_ge, hr_real_3001]
        linarith only [hlow_mul, hmargin]
      exact le_trans (Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp) hstep1

    have h_DOm_up :
        d_omega r_star ≤ (2 : ℝ) ^ ((1001 / 1000 : ℝ) * (lam0 : ℝ) * (r_star : ℝ)) := by
      rw [h_DOm_eq r_star hr_le_N]
      have hstep1 : ((N.choose r_star : ℝ) * ((r_star : ℝ) / (4 * (N : ℝ))) ^ r_star) *
          (2 : ℝ) ^ (- (gamma0 : ℝ) * (r_star : ℝ) + sigma_edge * (r_star.choose 2 : ℝ)) ≤
          (2 : ℝ) ^ (- (gamma0 : ℝ) * (r_star : ℝ) + sigma_edge * (r_star.choose 2 : ℝ)) := by
        simpa using mul_le_mul_of_nonneg_right h_env_diag_up
          (by positivity : (0 : ℝ) ≤
            (2 : ℝ) ^ (- (gamma0 : ℝ) * (r_star : ℝ) + sigma_edge * (r_star.choose 2 : ℝ)))
      have hexp : - (gamma0 : ℝ) * (r_star : ℝ) + sigma_edge * (r_star.choose 2 : ℝ) ≤
          (1001 / 1000 : ℝ) * (lam0 : ℝ) * (r_star : ℝ) := by
        have hc2 := h_choose2_real r_star
        have hcr_le : (r_star.choose 2 : ℝ) ≤ (r_star : ℝ) * (r_star : ℝ) / 2 := by
          linarith only [hr_real_pos, hc2]
        have hm1 : sigma_edge * (r_star.choose 2 : ℝ) ≤
            sigma_edge * ((r_star : ℝ) * (r_star : ℝ) / 2) :=
          mul_le_mul_of_nonneg_left hcr_le (le_of_lt hσ_pos)
        have hm2 : (sigma_edge * (r_star : ℝ) / 2) * (r_star : ℝ) ≤
            ((10001 / 10000 : ℝ) * (6 * (lam0 : ℝ))) * (r_star : ℝ) :=
          mul_le_mul_of_nonneg_right (by linarith only [hσ_up, hbeta0_real]) hr_real_nn
        have hring : sigma_edge * ((r_star : ℝ) * (r_star : ℝ) / 2) =
            (sigma_edge * (r_star : ℝ) / 2) * (r_star : ℝ) := by ring
        have hlr_nn : 0 ≤ (lam0 : ℝ) * (r_star : ℝ) := by positivity
        rw [hgamma0_real]
        linarith [hm1, hm2, hring, hlr_nn]
      exact le_trans hstep1 (Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp)

    have hDOm_r_pos : 0 < d_omega r_star := lt_of_lt_of_le (by positivity) h_DOm_low
    have hDStar_pos : 0 < d_star := by
      rw [hdstar_def]; positivity
    have hp_keep_pos : 0 < p_keep := by
      rw [hpkeep_def]; exact div_pos hDStar_pos hDOm_r_pos
    have hp_keep_up : p_keep ≤ (2 : ℝ) ^ (- (747 / 1000 : ℝ) * (lam0 : ℝ) * (r_star : ℝ)) := by
      rw [hpkeep_def, hdstar_def]
      have hdiv : (2 : ℝ) ^ ((1 / 4 : ℝ) * (lam0 : ℝ) * (r_star : ℝ)) / d_omega r_star ≤
          (2 : ℝ) ^ ((1 / 4 : ℝ) * (lam0 : ℝ) * (r_star : ℝ)) /
          (2 : ℝ) ^ ((997 / 1000 : ℝ) * (lam0 : ℝ) * (r_star : ℝ)) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) h_DOm_low
      rw [← Real.rpow_sub (by norm_num : (0 : ℝ) < 2)] at hdiv
      refine le_trans hdiv (le_of_eq ?_)
      congr 1
      ring
    have hp_keep_lt1 : p_keep < 1 := by
      have hlt1 : (2 : ℝ) ^ (- (747 / 1000 : ℝ) * (lam0 : ℝ) * (r_star : ℝ)) < 1 := by
        rw [show (1 : ℝ) = (2 : ℝ) ^ (0 : ℝ) by norm_num]
        apply Real.rpow_lt_rpow_of_exponent_lt (by norm_num)
        nlinarith only [hlam0_real_pos, hr_real_pos]
      exact lt_of_le_of_lt hp_keep_up hlt1
    have hp_keep_low :
        (2 : ℝ) ^ (- (751 / 1000 : ℝ) * (lam0 : ℝ) * (r_star : ℝ)) ≤ p_keep := by
      rw [hpkeep_def, hdstar_def]
      have hdiv : (2 : ℝ) ^ ((1 / 4 : ℝ) * (lam0 : ℝ) * (r_star : ℝ)) /
          (2 : ℝ) ^ ((1001 / 1000 : ℝ) * (lam0 : ℝ) * (r_star : ℝ)) ≤
          (2 : ℝ) ^ ((1 / 4 : ℝ) * (lam0 : ℝ) * (r_star : ℝ)) / d_omega r_star :=
        div_le_div_of_nonneg_left (by positivity) hDOm_r_pos h_DOm_up
      rw [← Real.rpow_sub (by norm_num : (0 : ℝ) < 2)] at hdiv
      refine le_trans (le_of_eq ?_) hdiv
      congr 1
      ring

    have hp_edge_Nchoose2 :
        p_edge ^ (N.choose 2) = (2 : ℝ) ^ (- ((N : ℝ) * ((eq + L + gamma0 + 2 : ℕ) : ℝ) / 2)) := by
      rw [hp_edge_pow (N.choose 2), hsigma_def, ← hN_def]
      congr 1
      have h2N : (2 : ℝ) * (N.choose 2 : ℝ) = (N : ℝ) * ((N - 1 : ℕ) : ℝ) := by
        exact_mod_cast h_choose2_nat N
      have hNc2 : (N.choose 2 : ℝ) = (N : ℝ) * ((N - 1 : ℕ) : ℝ) / 2 := by linarith only [h2N]
      rw [hNc2]
      field_simp [ne_of_gt hN1_pos]
    have hNeq_half :
        (N : ℝ) * (eq : ℝ) / 2 = (beta0 : ℝ) * (2 : ℝ) ^ (2 * L) * (r_star : ℝ) := by
      have hN_cast : (N : ℝ) = (2 : ℝ) ^ L * (r_star : ℝ) := by
        rw [hN_def]; push_cast; rfl
      have heq_cast : (eq : ℝ) = 2 * (beta0 : ℝ) * (2 : ℝ) ^ L := by
        rw [heq_def]; push_cast; ring
      have hpow2L : (2 : ℝ) ^ (2 * L) = (2 : ℝ) ^ L * (2 : ℝ) ^ L := by
        rw [two_mul, pow_add]
      rw [hN_cast, heq_cast, hpow2L]
      ring

    have hn0_low :
        (2 : ℝ) ^ ((99 / 100 : ℝ) * (beta0 : ℝ) * (2 : ℝ) ^ (2 * L) * (r_star : ℝ)) ≤ n_0 := by
      have hq_low : (2 : ℝ) ^ ((N : ℝ) * (eq : ℝ)) ≤ (q : ℝ) ^ N := by
        have hq1 : (2 : ℝ) ^ eq ≤ (q : ℝ) := by
          rw [hq_def]
          have hnat : 2 ^ eq ≤ 2 ^ eq + 1 := Nat.le_succ _
          exact_mod_cast hnat
        have hpow := pow_le_pow_left₀ (by positivity) hq1 N
        have hlhs : ((2 : ℝ) ^ eq) ^ N = (2 : ℝ) ^ ((N : ℝ) * (eq : ℝ)) := by
          rw [← pow_mul, ← Real.rpow_natCast]
          congr 1
          push_cast
          ring
        rwa [hlhs] at hpow
      have hprod_low :
          (2 : ℝ) ^ (- (751 / 1000 : ℝ) * (lam0 : ℝ) * (r_star : ℝ) +
            (N : ℝ) * (eq : ℝ) +
            (- ((N : ℝ) * ((eq + L + gamma0 + 2 : ℕ) : ℝ) / 2))) ≤ n_0 := by
        rw [hn0_def, ← hN_def, hp_edge_Nchoose2, Real.rpow_add (by norm_num : (0 : ℝ) < 2),
          Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
        have hm1 : (2 : ℝ) ^ (- (751 / 1000 : ℝ) * (lam0 : ℝ) * (r_star : ℝ)) *
            (2 : ℝ) ^ ((N : ℝ) * (eq : ℝ)) ≤ p_keep * (q : ℝ) ^ N :=
          mul_le_mul hp_keep_low hq_low (by positivity) (le_of_lt hp_keep_pos)
        exact mul_le_mul_of_nonneg_right hm1 (by positivity)
      have hexp :
          (99 / 100 : ℝ) * (beta0 : ℝ) * (2 : ℝ) ^ (2 * L) * (r_star : ℝ) ≤
            - (751 / 1000 : ℝ) * (lam0 : ℝ) * (r_star : ℝ) +
            (N : ℝ) * (eq : ℝ) +
            (- ((N : ℝ) * ((eq + L + gamma0 + 2 : ℕ) : ℝ) / 2)) := by
        have hN_cast : (N : ℝ) = (2 : ℝ) ^ L * (r_star : ℝ) := by
          rw [hN_def]; push_cast; rfl
        have hpow2L : (2 : ℝ) ^ (2 * L) = (2 : ℝ) ^ L * (2 : ℝ) ^ L := by
          rw [two_mul, pow_add]
        have hlin_real : (10000 : ℝ) * ((L : ℝ) + (gamma0 : ℝ) + 2) ≤ (2 : ℝ) ^ L := by
          exact_mod_cast h2L_lg
        have hmil_real : (1048576 : ℝ) ≤ (2 : ℝ) ^ L := by
          exact_mod_cast h2L_mil
        have h22L_ge : (1048576 : ℝ) ≤ (2 : ℝ) ^ (2 * L) := by
          rw [hpow2L]
          nlinarith only [hmil_real]
        have hterm1 : ((L : ℝ) + (gamma0 : ℝ) + 2) * (2 : ℝ) ^ L * (r_star : ℝ) / 2 ≤
            (1 / 20000 : ℝ) * (beta0 : ℝ) * (2 : ℝ) ^ (2 * L) * (r_star : ℝ) := by
          have h1 : ((L : ℝ) + (gamma0 : ℝ) + 2) * (2 : ℝ) ^ L / 2 ≤
              (1 / 20000 : ℝ) * (2 : ℝ) ^ (2 * L) := by
            rw [hpow2L]
            have h2L_nn : (0 : ℝ) ≤ (2 : ℝ) ^ L := by positivity
            nlinarith only [hlin_real, h2L_nn]
          have h2 : (1 / 20000 : ℝ) * (2 : ℝ) ^ (2 * L) ≤
              (1 / 20000 : ℝ) * (beta0 : ℝ) * (2 : ℝ) ^ (2 * L) := by
            have h22L_nn : (0 : ℝ) ≤ (2 : ℝ) ^ (2 * L) := by positivity
            nlinarith only [hbeta0_real_ge, h22L_nn]
          have hm := mul_le_mul_of_nonneg_right (le_trans h1 h2) hr_real_nn
          have hdiv_eq : ((L : ℝ) + (gamma0 : ℝ) + 2) * (2 : ℝ) ^ L * (r_star : ℝ) / 2 =
              ((L : ℝ) + (gamma0 : ℝ) + 2) * (2 : ℝ) ^ L / 2 * (r_star : ℝ) := by ring
          linarith only [hm, hdiv_eq]
        have hterm2 : (751 / 1000 : ℝ) * (lam0 : ℝ) * (r_star : ℝ) ≤
            (1 / 200 : ℝ) * (beta0 : ℝ) * (2 : ℝ) ^ (2 * L) * (r_star : ℝ) := by
          have hlr_nn : (0 : ℝ) ≤ (lam0 : ℝ) * (r_star : ℝ) := by positivity
          rw [hbeta0_real]
          nlinarith only [h22L_ge, hlr_nn]
        have hcast_sum : ((eq + L + gamma0 + 2 : ℕ) : ℝ) =
            (eq : ℝ) + (L : ℝ) + (gamma0 : ℝ) + 2 := by push_cast; ring
        rw [hcast_sum]
        have halg : (N : ℝ) * (eq : ℝ) +
            (- ((N : ℝ) * ((eq : ℝ) + (L : ℝ) + (gamma0 : ℝ) + 2) / 2)) =
            (N : ℝ) * (eq : ℝ) / 2 -
              ((L : ℝ) + (gamma0 : ℝ) + 2) * (2 : ℝ) ^ L * (r_star : ℝ) / 2 := by
          rw [hN_cast]
          ring
        have hX_nn : (0 : ℝ) ≤ (beta0 : ℝ) * (2 : ℝ) ^ (2 * L) * (r_star : ℝ) := by positivity
        linarith only [halg, hNeq_half, hterm1, hterm2, hX_nn]
      exact le_trans (Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp) hprod_low

    have hn0_up :
        n_0 ≤ (2 : ℝ) ^ ((beta0 : ℝ) * (2 : ℝ) ^ (2 * L) * (r_star : ℝ)) := by
      have hq_up : (q : ℝ) ^ N ≤ (2 : ℝ) ^ ((N : ℝ) * ((eq : ℝ) + 1)) := by
        have hq1 : (q : ℝ) ≤ (2 : ℝ) ^ (eq + 1) := by
          rw [hq_def]
          have h1 : 1 ≤ 2 ^ eq := Nat.one_le_two_pow
          have hnat : 2 ^ eq + 1 ≤ 2 ^ (eq + 1) := by
            rw [pow_succ]
            omega
          exact_mod_cast hnat
        have hpow := pow_le_pow_left₀ (Nat.cast_nonneg q) hq1 N
        have hrhs : ((2 : ℝ) ^ (eq + 1)) ^ N = (2 : ℝ) ^ ((N : ℝ) * ((eq : ℝ) + 1)) := by
          rw [← pow_mul, ← Real.rpow_natCast]
          congr 1
          push_cast
          ring
        rwa [hrhs] at hpow
      have hprod_up :
          n_0 ≤ (2 : ℝ) ^ ((N : ℝ) * ((eq : ℝ) + 1) +
            (- ((N : ℝ) * ((eq + L + gamma0 + 2 : ℕ) : ℝ) / 2))) := by
        rw [hn0_def, ← hN_def, hp_edge_Nchoose2, Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
        have hm1 : p_keep * (q : ℝ) ^ N ≤ 1 * (2 : ℝ) ^ ((N : ℝ) * ((eq : ℝ) + 1)) :=
          mul_le_mul (le_of_lt hp_keep_lt1) hq_up (by positivity) zero_le_one
        rw [one_mul] at hm1
        exact mul_le_mul_of_nonneg_right hm1 (by positivity)
      have hexp :
          (N : ℝ) * ((eq : ℝ) + 1) + (- ((N : ℝ) * ((eq + L + gamma0 + 2 : ℕ) : ℝ) / 2)) ≤
            (beta0 : ℝ) * (2 : ℝ) ^ (2 * L) * (r_star : ℝ) := by
        have hcast_sum : ((eq + L + gamma0 + 2 : ℕ) : ℝ) =
            (eq : ℝ) + (L : ℝ) + (gamma0 : ℝ) + 2 := by push_cast; ring
        rw [hcast_sum]
        have hNL_nn : (0 : ℝ) ≤ (N : ℝ) * ((L : ℝ) + (gamma0 : ℝ)) := by positivity
        linarith only [hNeq_half, hNL_nn]
      exact le_trans hprod_up (Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp)

    have hn0_pos : 0 < n_0 := lt_of_lt_of_le (by positivity) hn0_low

    have h_M1 : ∑ x : Fin N → Fin q, p_keep * p_edge ^ (homQueries x).card = n_0 := by
      have hcongr : ∀ x ∈ (Finset.univ : Finset (Fin N → Fin q)),
          p_keep * p_edge ^ (homQueries x).card = p_keep * p_edge ^ (N.choose 2) := by
        intro x _
        rw [h_hom_card x]
      rw [Finset.sum_congr rfl hcongr, Finset.sum_const, nsmul_eq_mul,
        Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin,
        hn0_def, ← hN_def]
      push_cast
      ring

    let PairSphere : ℕ → Finset ((Fin N → Fin q) × (Fin N → Fin q)) :=
      fun s => Finset.univ.filter (fun xy => dHam xy.1 xy.2 = s)

    have h_sphere_sum : ∀ s : ℕ, s ≤ N →
        ∑ xy ∈ PairSphere s,
          p_keep ^ 2 * p_edge ^ (homQueries xy.1 ∪ homQueries xy.2).card =
          n_0 * p_keep * d_omega s := by
      intro s hs
      have hsub := hs_choose_le_N s hs
      have hcongr : ∀ xy ∈ PairSphere s,
          p_keep ^ 2 * p_edge ^ (homQueries xy.1 ∪ homQueries xy.2).card =
            p_keep ^ 2 * (p_edge ^ (N.choose 2) * p_edge ^ (s * (N - 1) - s.choose 2)) := by
        intro xy hxy
        simp only [PairSphere, Finset.mem_filter, Finset.mem_univ, true_and] at hxy
        rw [h_union_card xy.1 xy.2, hxy, Nat.add_sub_assoc hsub, pow_add]
      rw [Finset.sum_congr rfl hcongr, Finset.sum_const, nsmul_eq_mul]
      have hcard : (PairSphere s).card = q ^ N * (N.choose s * (q - 1) ^ s) := h_pair_sphere s
      rw [hcard, hn0_def, hdomega_def s, ← hN_def]
      push_cast
      ring

    have h_M0 : ∑ xy ∈ PairSphere r_star,
        p_keep ^ 2 * p_edge ^ (homQueries xy.1 ∪ homQueries xy.2).card = n_0 * d_star := by
      rw [h_sphere_sum r_star hr_le_N, hpkeep_def]
      field_simp [ne_of_gt hDOm_r_pos]

    have h_ball_sum :
        ∑ ab ∈ Finset.univ.filter
            (fun ab : (Fin N → Fin q) × (Fin N → Fin q) =>
              ab.1 ≠ ab.2 ∧ dHam ab.1 ab.2 ≤ C₁ * r_star),
          p_keep ^ 2 * p_edge ^ (homQueries ab.1 ∪ homQueries ab.2).card ≤
        n_0 * (2 : ℝ) ^ ((7 * (C₁ ^ 2 : ℕ) : ℝ) * (lam0 : ℝ) * (r_star : ℝ)) := by
      have hne_iff : ∀ a b : Fin N → Fin q, a ≠ b ↔ 1 ≤ dHam a b := by
        intro a b
        constructor
        · intro hne
          have hex : ∃ v : Fin N, a v ≠ b v := by
            by_contra hall
            push_neg at hall
            exact hne (funext hall)
          rcases hex with ⟨v, hv⟩
          exact Finset.card_pos.mpr ⟨v, by simp [diffCoords, hv]⟩
        · intro h1 heq
          subst heq
          have h0 : dHam a a = 0 := by simp [dHam, diffCoords]
          omega
      have hball_eq : Finset.univ.filter
          (fun ab : (Fin N → Fin q) × (Fin N → Fin q) =>
            ab.1 ≠ ab.2 ∧ dHam ab.1 ab.2 ≤ C₁ * r_star) =
          (Finset.Icc 1 (C₁ * r_star)).biUnion PairSphere := by
        ext ab
        simp only [PairSphere, Finset.mem_filter, Finset.mem_univ, true_and,
          Finset.mem_biUnion, Finset.mem_Icc, hne_iff]
        constructor
        · rintro ⟨h1, h2⟩
          exact ⟨dHam ab.1 ab.2, ⟨h1, h2⟩, rfl⟩
        · rintro ⟨s, ⟨h1, h2⟩, rfl⟩
          exact ⟨h1, h2⟩
      have hdisj : ((Finset.Icc 1 (C₁ * r_star) : Finset ℕ) : Set ℕ).PairwiseDisjoint PairSphere := by
        intro s₁ _ s₂ _ hne
        rw [Function.onFun, Finset.disjoint_left]
        intro ab h₁ h₂
        simp only [PairSphere, Finset.mem_filter, Finset.mem_univ, true_and] at h₁ h₂
        exact hne (h₁.symm.trans h₂)
      rw [hball_eq, Finset.sum_biUnion hdisj]
      let B_term : ℝ := n_0 *
        (2 : ℝ) ^ (2 * (r_star : ℝ) +
          (60006 / 10000 : ℝ) * ((C₁ ^ 2 : ℕ) : ℝ) * (lam0 : ℝ) * (r_star : ℝ))
      have hterm_le : ∀ s ∈ Finset.Icc 1 (C₁ * r_star),
          ∑ xy ∈ PairSphere s,
            p_keep ^ 2 * p_edge ^ (homQueries xy.1 ∪ homQueries xy.2).card ≤ B_term := by
        intro s hs
        rw [Finset.mem_Icc] at hs
        have hsN : s ≤ N := le_trans hs.2 hCr_le_N
        rw [h_sphere_sum s hsN]
        have hDOm_nn : 0 ≤ d_omega s := by
          rw [hdomega_def s]
          positivity
        have hgs_nn : 0 ≤ (gamma0 : ℝ) * (s : ℝ) := by positivity
        have hpDOm : p_keep * d_omega s ≤
            (2 : ℝ) ^ (2 * (r_star : ℝ) + sigma_edge * (s.choose 2 : ℝ)) := by
          calc
            p_keep * d_omega s
              ≤ 1 * d_omega s := mul_le_mul_of_nonneg_right (le_of_lt hp_keep_lt1) hDOm_nn
            _ = d_omega s := one_mul _
            _ ≤ (2 : ℝ) ^ (2 * (r_star : ℝ) - (gamma0 : ℝ) * (s : ℝ) +
                  sigma_edge * (s.choose 2 : ℝ)) := h_DOm_s s hsN
            _ ≤ (2 : ℝ) ^ (2 * (r_star : ℝ) + sigma_edge * (s.choose 2 : ℝ)) :=
                  Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith only [hgs_nn])
        have hsc2_le : (s.choose 2 : ℝ) ≤ ((C₁ ^ 2 : ℕ) : ℝ) * (r_star : ℝ) ^ 2 / 2 := by
          have hnat : 2 * s.choose 2 ≤ C₁ ^ 2 * r_star ^ 2 := by
            calc
              2 * s.choose 2 = s * (s - 1) := h_choose2_nat s
              _ ≤ s * s := Nat.mul_le_mul_left s (Nat.sub_le s 1)
              _ ≤ (C₁ * r_star) * (C₁ * r_star) := Nat.mul_le_mul hs.2 hs.2
              _ = C₁ ^ 2 * r_star ^ 2 := by ring
          have hreal : (2 : ℝ) * (s.choose 2 : ℝ) ≤ ((C₁ ^ 2 : ℕ) : ℝ) * (r_star : ℝ) ^ 2 := by
            exact_mod_cast hnat
          linarith only [hreal]
        have hexp_s : 2 * (r_star : ℝ) + sigma_edge * (s.choose 2 : ℝ) ≤
            2 * (r_star : ℝ) +
              (60006 / 10000 : ℝ) * ((C₁ ^ 2 : ℕ) : ℝ) * (lam0 : ℝ) * (r_star : ℝ) := by
          have hm1 : sigma_edge * (s.choose 2 : ℝ) ≤
              sigma_edge * (((C₁ ^ 2 : ℕ) : ℝ) * (r_star : ℝ) ^ 2 / 2) :=
            mul_le_mul_of_nonneg_left hsc2_le (le_of_lt hσ_pos)
          have hm2 : (sigma_edge * (r_star : ℝ) / 2) * (((C₁ ^ 2 : ℕ) : ℝ) * (r_star : ℝ)) ≤
              ((10001 / 10000 : ℝ) * (6 * (lam0 : ℝ))) * (((C₁ ^ 2 : ℕ) : ℝ) * (r_star : ℝ)) :=
            mul_le_mul_of_nonneg_right (by linarith only [hσ_up, hbeta0_real]) (by positivity)
          have hr1 : sigma_edge * (((C₁ ^ 2 : ℕ) : ℝ) * (r_star : ℝ) ^ 2 / 2) =
              (sigma_edge * (r_star : ℝ) / 2) * (((C₁ ^ 2 : ℕ) : ℝ) * (r_star : ℝ)) := by ring
          have hr2 : ((10001 / 10000 : ℝ) * (6 * (lam0 : ℝ))) *
              (((C₁ ^ 2 : ℕ) : ℝ) * (r_star : ℝ)) =
              (60006 / 10000 : ℝ) * ((C₁ ^ 2 : ℕ) : ℝ) * (lam0 : ℝ) * (r_star : ℝ) := by ring
          linarith only [hm1, hm2, hr1, hr2]
        have hrpow_s := Real.rpow_le_rpow_of_exponent_le (x := (2 : ℝ)) (by norm_num) hexp_s
        dsimp [B_term]
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left (le_trans hpDOm hrpow_s) (le_of_lt hn0_pos)
      have hsum_le1 : ∑ s ∈ Finset.Icc 1 (C₁ * r_star),
          (∑ xy ∈ PairSphere s,
            p_keep ^ 2 * p_edge ^ (homQueries xy.1 ∪ homQueries xy.2).card) ≤
          ((Finset.Icc 1 (C₁ * r_star)).card : ℝ) * B_term := by
        calc
          ∑ s ∈ Finset.Icc 1 (C₁ * r_star), _
            ≤ ∑ _s ∈ Finset.Icc 1 (C₁ * r_star), B_term := Finset.sum_le_sum hterm_le
          _ = ((Finset.Icc 1 (C₁ * r_star)).card : ℝ) * B_term := by
              rw [Finset.sum_const, nsmul_eq_mul]
      have hcard_Icc : ((Finset.Icc 1 (C₁ * r_star)).card : ℝ) ≤ (2 : ℝ) ^ (2 * (r_star : ℝ)) := by
        have hc_eq : (Finset.Icc 1 (C₁ * r_star)).card = C₁ * r_star := by
          rw [Nat.card_Icc]
          omega
        have hr_pow : r_star ≤ 2 ^ r_star := le_of_lt Nat.lt_two_pow_self
        have hCr_le_pow : C₁ * r_star ≤ 2 ^ (2 * r_star) := by
          calc
            C₁ * r_star ≤ r_star * r_star := Nat.mul_le_mul_right r_star (by omega)
            _ ≤ 2 ^ r_star * 2 ^ r_star := Nat.mul_le_mul hr_pow hr_pow
            _ = 2 ^ (r_star + r_star) := (pow_add 2 r_star r_star).symm
            _ = 2 ^ (2 * r_star) := by rw [two_mul]
        rw [hc_eq]
        have hcast : ((C₁ * r_star : ℕ) : ℝ) ≤ ((2 ^ (2 * r_star) : ℕ) : ℝ) := by
          exact_mod_cast hCr_le_pow
        have hpow_eq : ((2 ^ (2 * r_star) : ℕ) : ℝ) = (2 : ℝ) ^ (2 * (r_star : ℝ)) := by
          rw [Nat.cast_pow, Nat.cast_ofNat, ← Real.rpow_natCast, Nat.cast_mul, Nat.cast_ofNat]
        linarith only [hcast, hpow_eq]
      have hB_nn : 0 ≤ B_term := by dsimp [B_term]; positivity
      have hsum_le2 : ((Finset.Icc 1 (C₁ * r_star)).card : ℝ) * B_term ≤
          n_0 * (2 : ℝ) ^ (4 * (r_star : ℝ) +
            (60006 / 10000 : ℝ) * ((C₁ ^ 2 : ℕ) : ℝ) * (lam0 : ℝ) * (r_star : ℝ)) := by
        have hm := mul_le_mul_of_nonneg_right hcard_Icc hB_nn
        have hrew : (2 : ℝ) ^ (2 * (r_star : ℝ)) * B_term =
            n_0 * (2 : ℝ) ^ (4 * (r_star : ℝ) +
              (60006 / 10000 : ℝ) * ((C₁ ^ 2 : ℕ) : ℝ) * (lam0 : ℝ) * (r_star : ℝ)) := by
          dsimp [B_term]
          have hcomm : (2 : ℝ) ^ (2 * (r_star : ℝ)) *
              (n_0 * (2 : ℝ) ^ (2 * (r_star : ℝ) +
                (60006 / 10000 : ℝ) * ((C₁ ^ 2 : ℕ) : ℝ) * (lam0 : ℝ) * (r_star : ℝ))) =
              n_0 * ((2 : ℝ) ^ (2 * (r_star : ℝ)) *
                (2 : ℝ) ^ (2 * (r_star : ℝ) +
                  (60006 / 10000 : ℝ) * ((C₁ ^ 2 : ℕ) : ℝ) * (lam0 : ℝ) * (r_star : ℝ))) := by ring
          rw [hcomm, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
          congr 2
          ring
        rwa [hrew] at hm
      have hexp_final :
          4 * (r_star : ℝ) +
            (60006 / 10000 : ℝ) * ((C₁ ^ 2 : ℕ) : ℝ) * (lam0 : ℝ) * (r_star : ℝ) ≤
            (7 * (C₁ ^ 2 : ℕ) : ℝ) * (lam0 : ℝ) * (r_star : ℝ) := by
        have hcast7 : (7 * (C₁ ^ 2 : ℕ) : ℝ) = 7 * ((C₁ ^ 2 : ℕ) : ℝ) := by push_cast; ring
        rw [hcast7]
        have hprod : (27000 : ℝ) ≤ ((C₁ ^ 2 : ℕ) : ℝ) * (lam0 : ℝ) := by
          nlinarith only [hC2_real, hlam0_real_ge]
        have h4_le : 4 * (r_star : ℝ) ≤
            (9994 / 10000 : ℝ) * ((C₁ ^ 2 : ℕ) : ℝ) * (lam0 : ℝ) * (r_star : ℝ) := by
          have hc : (4 : ℝ) ≤ (9994 / 10000 : ℝ) * (((C₁ ^ 2 : ℕ) : ℝ) * (lam0 : ℝ)) := by
            linarith only [hprod]
          have hm := mul_le_mul_of_nonneg_right hc hr_real_nn
          have hr1 : (9994 / 10000 : ℝ) * (((C₁ ^ 2 : ℕ) : ℝ) * (lam0 : ℝ)) * (r_star : ℝ) =
              (9994 / 10000 : ℝ) * ((C₁ ^ 2 : ℕ) : ℝ) * (lam0 : ℝ) * (r_star : ℝ) := by ring
          linarith only [hm, hr1]
        linarith only [h4_le]
      have hsum_le3 : n_0 *
          (2 : ℝ) ^ (4 * (r_star : ℝ) +
            (60006 / 10000 : ℝ) * ((C₁ ^ 2 : ℕ) : ℝ) * (lam0 : ℝ) * (r_star : ℝ)) ≤
          n_0 * (2 : ℝ) ^ ((7 * (C₁ ^ 2 : ℕ) : ℝ) * (lam0 : ℝ) * (r_star : ℝ)) :=
        mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp_final) (le_of_lt hn0_pos)
      exact le_trans hsum_le1 (le_trans hsum_le2 hsum_le3)

    exact ⟨hσ_pos, hp_edge_pos, hp_edge_lt1, h_cal, hσ_low, hσ_up,
      h_binom_edge, h_DOm_s, h_DOm_low, h_DOm_up,
      hp_keep_pos, hp_keep_lt1, hp_keep_up,
      hn0_low, hn0_up,
      h_hom_card, h_union_card, h_sphere,
      h_M1, h_M0, h_ball_sum⟩

  have hlam0_1000C1 : 1000 * C₁ ≤ cspLam0 C₁ := (lam0_ge_1000_C1 C₁ hC₁).2.1
  have hlam0_ge : 3000 ≤ cspLam0 C₁ := by omega
  have hL_ge20 : 20 ≤ cspL C₁ := Nat.le_add_right 20 _
  have hL_ge_lam : 1600 * cspLam0 C₁ ≤ cspL C₁ := by
    have hsq : 1 ≤ C₁ ^ 2 := Nat.one_le_pow 2 C₁ (by omega)
    unfold cspL cspInvEta0
    nlinarith only [hsq]
  have hC1_le_L : C₁ ≤ cspL C₁ := by omega
  have hgamma0_le_L : cspGamma0 C₁ ≤ cspL C₁ := by
    unfold cspGamma0
    omega

  exact h_core
    (cspLam0 C₁) (cspBeta0 C₁) (cspGamma0 C₁) (cspL C₁) (cspEq C₁) (cspQ C₁)
    (cspSigmaEdge C₁ r_star) (cspPEdge C₁ r_star) (cspDStar C₁ r_star)
    (cspPKeep C₁ r_star) (cspN0 C₁ r_star) (cspDOmega C₁ r_star)
    hlam0_ge rfl rfl hL_ge20 hC1_le_L hgamma0_le_L rfl rfl rfl rfl (fun _ => rfl) rfl rfl rfl

private theorem witness_list_step_query_sum_bound (C₁ : ℕ) (hC₁ : 3 ≤ C₁) (r_star : ℕ) (hr : 1000 * C₁ < r_star)
    (hσ_pos : 0 < cspSigmaEdge C₁ r_star)
    (_hp_edge_pos : 0 < cspPEdge C₁ r_star)
    (hσ_up : cspSigmaEdge C₁ r_star * (r_star : ℝ) / 2 ≤
      (10001 / 10000 : ℝ) * (cspBeta0 C₁ : ℝ))
    (h_binom_edge : ∀ s : ℕ,
      ((2 ^ cspL C₁ * r_star).choose s : ℝ) * ((cspQ C₁ - 1 : ℕ) : ℝ) ^ s *
        (cspPEdge C₁ r_star) ^ (s * (2 ^ cspL C₁ * r_star - 1)) ≤
        (2 : ℝ) ^ (2 * (r_star : ℝ) - (cspGamma0 C₁ : ℝ) * (s : ℝ)))
    (hp_keep_pos : 0 < cspPKeep C₁ r_star)
    (hp_keep_up : cspPKeep C₁ r_star ≤
      (2 : ℝ) ^ (- (747 / 1000 : ℝ) * (cspLam0 C₁ : ℝ) * (r_star : ℝ)))
    (a b : Fin (2 ^ cspL C₁ * r_star) → Fin (cspQ C₁))
    (_hab : a ≠ b) (hd_ab : dHam a b ≤ C₁ * r_star) :
    ∃ (M_wit : (m : ℕ) → (Fin m → (Fin (2 ^ cspL C₁ * r_star) → Fin (cspQ C₁))) →
        (Fin (2 ^ cspL C₁ * r_star) → Fin (cspQ C₁)) →
        Finset (candWitType (2 ^ cspL C₁ * r_star) C₁))
      (Q_cand : (m : ℕ) → (Fin m → (Fin (2 ^ cspL C₁ * r_star) → Fin (cspQ C₁))) →
        (Fin (2 ^ cspL C₁ * r_star) → Fin (cspQ C₁)) →
        candWitType (2 ^ cspL C₁ * r_star) C₁ →
        Finset (cspIota (2 ^ cspL C₁ * r_star) (cspQ C₁))),
      (∀ m < cspKMom C₁, ∀ z_prev : Fin m → (Fin (2 ^ cspL C₁ * r_star) → Fin (cspQ C₁)),
        Function.Injective z_prev →
        (∀ t : Fin m, z_prev t ∈ cspPoolCand C₁ r_star a b) →
        ∀ x ∈ cspPoolCand C₁ r_star a b \ Finset.univ.image z_prev,
        ∀ w ∈ M_wit m z_prev x,
          Q_cand m z_prev x w ⊆
            cspUCand a b (m + 1) (Fin.snoc z_prev x) \ cspUCand a b m z_prev) ∧
      (∀ (ω : cspIota (2 ^ cspL C₁ * r_star) (cspQ C₁) → Bool) (m : ℕ), m < cspKMom C₁ →
        ∀ z_prev : Fin m → (Fin (2 ^ cspL C₁ * r_star) → Fin (cspQ C₁)),
        Function.Injective z_prev →
        (∀ t : Fin m, z_prev t ∈ cspPoolCand C₁ r_star a b) →
        ∀ x ∈ cspPoolCand C₁ r_star a b \ Finset.univ.image z_prev,
          ω (Sum.inr x) = true →
          x ∈ bicliqueWitnessList (symROf ω) C₁ r_star a b →
          ∃ w ∈ M_wit m z_prev x, ∀ i ∈ Q_cand m z_prev x w, ω i = true) ∧
      (∀ m < cspKMom C₁, ∀ z_prev : Fin m → (Fin (2 ^ cspL C₁ * r_star) → Fin (cspQ C₁)),
        Function.Injective z_prev →
        (∀ t : Fin m, z_prev t ∈ cspPoolCand C₁ r_star a b) →
        ∑ x ∈ cspPoolCand C₁ r_star a b \ Finset.univ.image z_prev,
          ∑ w ∈ M_wit m z_prev x, (∏ i ∈ Q_cand m z_prev x w, cspPIota C₁ r_star i) ≤
            (2 : ℝ) ^ (- (72 / 100 : ℝ) * (cspLam0 C₁ : ℝ) * (r_star : ℝ))) :=
by
  have h_s1 : ∀ {N : ℕ} (S : Finset (Fin N)),
      2 * ((S.card : ℤ) * ((N - 1 : ℕ) : ℤ) - ((candA1 S).card : ℤ)) ≤ (S.card : ℤ) ^ 2 := by
    clear hσ_pos _hp_edge_pos hσ_up h_binom_edge hp_keep_pos hp_keep_up _hab hd_ab a b hr r_star hC₁ C₁
    intro N S
    let Ord : Finset (Fin N × Fin N) :=
      S.biUnion (fun u => ((Finset.univ : Finset (Fin N)).erase u).image (fun v => (u, v)))
    have hOrd_card : Ord.card = S.card * (N - 1) := by
      rw [Finset.card_biUnion]
      · have h_inner : ∀ u ∈ S,
            (((Finset.univ : Finset (Fin N)).erase u).image (fun v => (u, v))).card = N - 1 := by
          intro u _
          rw [Finset.card_image_of_injective _ (fun _ _ h => (Prod.mk.inj h).2),
            Finset.card_erase_of_mem (Finset.mem_univ u), Finset.card_fin]
        rw [Finset.sum_congr rfl h_inner, Finset.sum_const, smul_eq_mul]
      · intro u₁ _ u₂ _ hne
        simp only [Function.onFun, Finset.disjoint_left]
        intro p hp1 hp2
        rcases Finset.mem_image.mp hp1 with ⟨_, _, rfl⟩
        rcases Finset.mem_image.mp hp2 with ⟨_, _, hp⟩
        exact hne (Prod.mk.inj hp).1.symm
    let B_lt : Finset (Fin N × Fin N) := (S ×ˢ S).filter (fun uv => uv.1 < uv.2)
    let B_gt : Finset (Fin N × Fin N) := (S ×ˢ S).filter (fun uv => uv.2 < uv.1)
    let g : Fin N × Fin N → (Fin N × Fin N) ⊕ (Fin N × Fin N) :=
      fun ab =>
        if ab.1 < ab.2 then Sum.inl ab
        else if ab.2 ∈ S then Sum.inr (ab.2, ab.1)
        else Sum.inl (ab.2, ab.1)
    have hOrd_le : Ord.card ≤ (candA1 S).card + B_lt.card := by
      rw [← Finset.card_disjSum]
      apply Finset.card_le_card_of_injOn g
      · intro ab hab_mem
        simp only [Ord, Finset.mem_coe, Finset.mem_biUnion, Finset.mem_image,
          Finset.mem_erase, Finset.mem_univ, and_true] at hab_mem
        rcases hab_mem with ⟨a₀, ha₀, b₀, hba, rfl⟩
        dsimp [g]
        split_ifs with hlt hbS
        · simp only [Finset.mem_coe, Finset.mem_disjSum]
          refine Or.inl ⟨(a₀, b₀), ?_, rfl⟩
          simp only [candA1, Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨hlt, Or.inl ha₀⟩
        · simp only [Finset.mem_coe, Finset.mem_disjSum]
          refine Or.inr ⟨(b₀, a₀), ?_, rfl⟩
          simp only [B_lt, Finset.mem_filter, Finset.mem_product]
          exact ⟨⟨hbS, ha₀⟩, lt_of_le_of_ne (not_lt.mp hlt) hba⟩
        · simp only [Finset.mem_coe, Finset.mem_disjSum]
          refine Or.inl ⟨(b₀, a₀), ?_, rfl⟩
          simp only [candA1, Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨lt_of_le_of_ne (not_lt.mp hlt) hba, Or.inr ha₀⟩
      · intro ab₁ h₁ ab₂ h₂ heq
        simp only [Ord, Finset.mem_coe, Finset.mem_biUnion, Finset.mem_image,
          Finset.mem_erase, Finset.mem_univ, and_true] at h₁ h₂
        rcases h₁ with ⟨a₁, ha₁, b₁, _, rfl⟩
        rcases h₂ with ⟨a₂, ha₂, b₂, _, rfl⟩
        dsimp [g] at heq
        by_cases hlt₁ : a₁ < b₁ <;> by_cases hlt₂ : a₂ < b₂
        · rw [if_pos hlt₁, if_pos hlt₂] at heq
          exact Sum.inl.inj heq
        · rw [if_pos hlt₁, if_neg hlt₂] at heq
          by_cases hb₂ : b₂ ∈ S
          · rw [if_pos hb₂] at heq
            cases heq
          · rw [if_neg hb₂] at heq
            rcases Prod.mk.inj (Sum.inl.inj heq) with ⟨rfl, _⟩
            exact absurd ha₁ hb₂
        · rw [if_neg hlt₁, if_pos hlt₂] at heq
          by_cases hb₁ : b₁ ∈ S
          · rw [if_pos hb₁] at heq
            cases heq
          · rw [if_neg hb₁] at heq
            rcases Prod.mk.inj (Sum.inl.inj heq) with ⟨rfl, _⟩
            exact absurd ha₂ hb₁
        · rw [if_neg hlt₁, if_neg hlt₂] at heq
          by_cases hb₁ : b₁ ∈ S <;> by_cases hb₂ : b₂ ∈ S
          · rw [if_pos hb₁, if_pos hb₂] at heq
            rcases Prod.mk.inj (Sum.inr.inj heq) with ⟨rfl, rfl⟩
            rfl
          · rw [if_pos hb₁, if_neg hb₂] at heq
            cases heq
          · rw [if_neg hb₁, if_pos hb₂] at heq
            cases heq
          · rw [if_neg hb₁, if_neg hb₂] at heq
            rcases Prod.mk.inj (Sum.inl.inj heq) with ⟨rfl, rfl⟩
            rfl
    have hB_swap : B_lt.card ≤ B_gt.card := by
      apply Finset.card_le_card_of_injOn Prod.swap
      · intro uv huv
        simp only [B_lt, B_gt, Finset.mem_coe, Finset.mem_filter, Finset.mem_product, Prod.swap] at huv ⊢
        exact ⟨⟨huv.1.2, huv.1.1⟩, huv.2⟩
      · intro uv₁ _ uv₂ _ heq
        exact Prod.swap_injective heq
    have hB_disj : Disjoint B_lt B_gt := by
      rw [Finset.disjoint_left]
      intro uv h₁ h₂
      simp only [B_lt, B_gt, Finset.mem_filter] at h₁ h₂
      exact lt_asymm h₁.2 h₂.2
    have hB_sub : B_lt ∪ B_gt ⊆ S ×ˢ S :=
      Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _)
    have hB_two : 2 * B_lt.card ≤ S.card ^ 2 := by
      have hc := Finset.card_le_card hB_sub
      rw [Finset.card_union_of_disjoint hB_disj, Finset.card_product, ← sq] at hc
      omega
    have hnat : 2 * (S.card * (N - 1)) ≤ 2 * (candA1 S).card + S.card ^ 2 := by
      omega
    have hint : ((2 * (S.card * (N - 1)) : ℕ) : ℤ) ≤
        ((2 * (candA1 S).card + S.card ^ 2 : ℕ) : ℤ) := by
      exact_mod_cast hnat
    push_cast at hint
    linarith
  have h_s3 : ∀ {N q : ℕ} (C₁ r_star m : ℕ), 3 ≤ C₁ → 1000 * C₁ < r_star →
      ∀ (a b : Fin N → Fin q) (z_prev : Fin m → (Fin N → Fin q)) (x : Fin N → Fin q),
      x ∈ cspPoolCand C₁ r_star a b \ Finset.univ.image z_prev →
      candMFresh a b m z_prev x ⊆ diffCoords x a ∩ diffCoords x b ∧
      (∀ w ∈ candMWit C₁ r_star a b m z_prev x, candQCand C₁ a b m z_prev x w ⊆
        cspUCand a b (m + 1) (Fin.snoc z_prev x) \ cspUCand a b m z_prev) ∧
      (∀ ω : cspIota N q → Bool, ω (Sum.inr x) = true →
        x ∈ bicliqueWitnessList (symROf ω) C₁ r_star a b →
        ∃ w ∈ candMWit C₁ r_star a b m z_prev x, ∀ i ∈ candQCand C₁ a b m z_prev x w, ω i = true) ∧
      (∀ w, ∀ (p_edge p_keep : ℝ),
        ∏ i ∈ candQCand C₁ a b m z_prev x w, Sum.elim (fun _ => p_edge) (fun _ => p_keep) i =
          p_keep * p_edge ^ ((candA1 (candMFresh a b m z_prev x)).card +
            (candA2 C₁ a b x (candMFresh a b m z_prev x) w).card)) := by
    clear hσ_pos _hp_edge_pos hσ_up h_binom_edge hp_keep_pos hp_keep_up _hab hd_ab a b hr r_star hC₁ C₁
    intro N q C₁ r_star m hC₁_loc hr_loc a b z_prev x hx
    have hx_sdiff := Finset.mem_sdiff.mp hx
    have hx_pool := hx_sdiff.1
    simp only [cspPoolCand, Finset.mem_filter, Finset.mem_univ, true_and] at hx_pool
    rcases hx_pool with ⟨hx_ne_a, hx_ne_b, hd_xa, hd_xb⟩
    have hx_not_img : ∀ t : Fin m, z_prev t ≠ x :=
      fun t ht => hx_sdiff.2 (Finset.mem_image.mpr ⟨t, Finset.mem_univ t, ht⟩)
    let R_old := cspRvc a b m z_prev
    let R_new := cspRvc a b (m + 1) (Fin.snoc z_prev x)
    let S := candMFresh a b m z_prev x
    let W_ab := diffCoords x a ∪ diffCoords x b
    have ha_old : ∀ v : Fin N, (v, a v) ∈ R_old := by
      intro v
      simp only [R_old, cspRvc, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and]
      exact Or.inl (Or.inl ⟨v, rfl⟩)
    have hb_old : ∀ v : Fin N, (v, b v) ∈ R_old := by
      intro v
      simp only [R_old, cspRvc, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and]
      exact Or.inl (Or.inr ⟨v, rfl⟩)
    have hcstar_old : ∀ v : Fin N, (v, candCStar a b x v) ∈ R_old := by
      intro v
      unfold candCStar
      split_ifs
      · exact ha_old v
      · exact hb_old v
    have hcstar_ne : ∀ v ∈ W_ab, candCStar a b x v ≠ x v := by
      intro v hv
      simp only [W_ab, diffCoords, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and] at hv
      unfold candCStar
      split_ifs with hax
      · exact hax
      · push_neg at hax
        rcases hv with h1 | h2
        · exact absurd hax.symm h1
        · exact Ne.symm h2
    have hold_sub_new : R_old ⊆ R_new := by
      intro vc hvc
      simp only [R_old, R_new, cspRvc, Finset.mem_union, Finset.mem_image, Finset.mem_univ,
        true_and, Finset.mem_biUnion] at hvc ⊢
      rcases hvc with (h | h) | ⟨t, v, rfl⟩
      · exact Or.inl (Or.inl h)
      · exact Or.inl (Or.inr h)
      · exact Or.inr ⟨t.castSucc, v, by simp [Fin.snoc_castSucc]⟩
    have hx_new : ∀ v : Fin N, (v, x v) ∈ R_new := by
      intro v
      simp only [R_new, cspRvc, Finset.mem_union, Finset.mem_image, Finset.mem_univ,
        true_and, Finset.mem_biUnion]
      exact Or.inr ⟨Fin.last m, v, by simp [Fin.snoc_last]⟩
    have hPhi1_inj : Function.Injective (candPhi1 x) := by
      rintro ⟨u₁, v₁⟩ ⟨u₂, v₂⟩ heq
      simp only [candPhi1, Prod.mk.injEq] at heq
      exact Prod.ext heq.1 heq.2.1
    have hPhi2_injOn : ∀ w, Set.InjOn (candPhi2 a b x) (candA2 C₁ a b x S w) := by
      intro w ⟨u₁, v₁⟩ h₁ ⟨u₂, v₂⟩ h₂ heq
      simp only [candA2, Finset.mem_coe, Finset.mem_filter, Finset.mem_product] at h₁ h₂
      have hu₁_not : (u₁, x u₁) ∉ R_old := by
        have hS₁ := h₁.1.1
        simpa [S, candMFresh, R_old] using hS₁
      have hu₂_not : (u₂, x u₂) ∉ R_old := by
        have hS₂ := h₂.1.1
        simpa [S, candMFresh, R_old] using hS₂
      have hv₁_in : (v₁, candCStar a b x v₁) ∈ R_old := hcstar_old v₁
      have hv₂_in : (v₂, candCStar a b x v₂) ∈ R_old := hcstar_old v₂
      dsimp [candPhi2] at heq
      split_ifs at heq with hlt₁ hlt₂ hlt₂
      · simp only [Prod.mk.injEq] at heq
        exact Prod.ext heq.1 heq.2.1
      · simp only [Prod.mk.injEq] at heq
        rcases heq with ⟨rfl, _, hval, _⟩
        rw [hval] at hu₁_not
        exact absurd hv₂_in hu₁_not
      · simp only [Prod.mk.injEq] at heq
        rcases heq with ⟨rfl, _, hval, _⟩
        rw [← hval] at hu₂_not
        exact absurd hv₁_in hu₂_not
      · simp only [Prod.mk.injEq] at heq
        exact Prod.ext heq.2.1 heq.1
    have hPhi_disj : ∀ w,
        Disjoint ((candA1 S).image (candPhi1 x)) ((candA2 C₁ a b x S w).image (candPhi2 a b x)) := by
      intro w
      rw [Finset.disjoint_left]
      intro t ht₁ ht₂
      rcases Finset.mem_image.mp ht₁ with ⟨⟨u₁, v₁⟩, _, rfl⟩
      rcases Finset.mem_image.mp ht₂ with ⟨⟨u₂, v₂⟩, h₂, heq⟩
      simp only [candA2, Finset.mem_filter, Finset.mem_product] at h₂
      have hv₂_ne : candCStar a b x v₂ ≠ x v₂ := hcstar_ne v₂ h₂.1.2
      dsimp [candPhi1, candPhi2] at heq
      split_ifs at heq with hlt₂
      · simp only [Prod.mk.injEq] at heq
        rcases heq with ⟨_, rfl, _, hval⟩
        exact hv₂_ne hval
      · simp only [Prod.mk.injEq] at heq
        rcases heq with ⟨rfl, _, hval, _⟩
        exact hv₂_ne hval
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro v hv
      simp only [candMFresh, Finset.mem_filter, Finset.mem_univ, true_and] at hv
      simp only [diffCoords, Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨fun h => hv (h ▸ ha_old v), fun h => hv (h ▸ hb_old v)⟩
    · intro w hw i hi
      simp only [candQCand, Finset.mem_union, Finset.mem_image, Finset.mem_singleton] at hi
      rw [Finset.mem_sdiff]
      rcases hi with ⟨_, rfl, rfl⟩ | ⟨t, ht | ht, rfl⟩
      · refine ⟨?_, ?_⟩
        · simp only [cspUCand, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and]
          exact Or.inl (Or.inr ⟨Fin.last m, by simp [Fin.snoc_last]⟩)
        · intro hmem
          simp only [cspUCand, Finset.mem_union, Finset.mem_image, Finset.mem_insert,
            Finset.mem_singleton, Finset.mem_univ, true_and] at hmem
          rcases hmem with (⟨z, rfl | rfl, h⟩ | ⟨t₀, h⟩) | ⟨_, _, h⟩
          · exact hx_ne_a (Sum.inr.inj h).symm
          · exact hx_ne_b (Sum.inr.inj h).symm
          · exact hx_not_img t₀ (Sum.inr.inj h)
          · cases h
      · rcases ht with ⟨⟨u, v⟩, huv, rfl⟩
        simp only [candA1, Finset.mem_filter, Finset.mem_univ, true_and] at huv
        refine ⟨?_, ?_⟩
        · simp only [cspUCand, Finset.mem_union, Finset.mem_image, Finset.mem_filter,
            Finset.mem_univ, true_and]
          exact Or.inr ⟨(u, v, x u, x v), ⟨huv.1, hx_new u, hx_new v⟩, rfl⟩
        · intro hmem
          simp only [cspUCand, Finset.mem_union, Finset.mem_image, Finset.mem_filter,
            Finset.mem_univ, true_and] at hmem
          rcases hmem with (⟨_, _, h⟩ | ⟨_, h⟩) | ⟨t₀, ht₀, h⟩
          · cases h
          · cases h
          · have heq := Sum.inl.inj h
            subst heq
            rcases huv.2 with huS | hvS
            · have hu_not : (u, x u) ∉ R_old := by simpa [candMFresh, R_old] using huS
              exact hu_not ht₀.2.1
            · have hv_not : (v, x v) ∉ R_old := by simpa [candMFresh, R_old] using hvS
              exact hv_not ht₀.2.2
      · rcases ht with ⟨⟨u, v⟩, huv, rfl⟩
        have hne_uv : u ≠ v :=
          ((candMWit_card_and_quad C₁ r_star m hC₁_loc hr_loc a b z_prev x hd_xa hd_xb).2 w hw).1
            (u, v) huv
        have hu_not : (u, x u) ∉ R_old := by
          have huS := (Finset.mem_product.mp (Finset.mem_filter.mp huv).1).1
          simpa [candMFresh, R_old] using huS
        dsimp [candPhi2]
        split_ifs with hlt
        · refine ⟨?_, ?_⟩
          · simp only [cspUCand, Finset.mem_union, Finset.mem_image, Finset.mem_filter,
              Finset.mem_univ, true_and]
            exact Or.inr ⟨(u, v, x u, candCStar a b x v),
              ⟨hlt, hx_new u, hold_sub_new (hcstar_old v)⟩, rfl⟩
          · intro hmem
            simp only [cspUCand, Finset.mem_union, Finset.mem_image, Finset.mem_filter,
              Finset.mem_univ, true_and] at hmem
            rcases hmem with (⟨_, _, h⟩ | ⟨_, h⟩) | ⟨t₀, ht₀, h⟩
            · cases h
            · cases h
            · have heq := Sum.inl.inj h
              subst heq
              exact hu_not ht₀.2.1
        · have hgt : v < u := lt_of_le_of_ne (not_lt.mp hlt) (Ne.symm hne_uv)
          refine ⟨?_, ?_⟩
          · simp only [cspUCand, Finset.mem_union, Finset.mem_image, Finset.mem_filter,
              Finset.mem_univ, true_and]
            exact Or.inr ⟨(v, u, candCStar a b x v, x u),
              ⟨hgt, hold_sub_new (hcstar_old v), hx_new u⟩, rfl⟩
          · intro hmem
            simp only [cspUCand, Finset.mem_union, Finset.mem_image, Finset.mem_filter,
              Finset.mem_univ, true_and] at hmem
            rcases hmem with (⟨_, _, h⟩ | ⟨_, h⟩) | ⟨t₀, ht₀, h⟩
            · cases h
            · cases h
            · have heq := Sum.inl.inj h
              subst heq
              exact hu_not ht₀.2.2
    · intro ω hω_keep hx_wit
      exact candMWit_proj C₁ r_star m a b z_prev x ω hω_keep hx_wit
    · intro w p_edge p_keep
      have hdisj_sum : Disjoint
          (({x} : Finset (Fin N → Fin q)).image (Sum.inr : _ → cspIota N q))
          (((candA1 S).image (candPhi1 x) ∪
            (candA2 C₁ a b x S w).image (candPhi2 a b x)).image (Sum.inl : _ → cspIota N q)) := by
        rw [Finset.disjoint_left]
        intro i hi₁ hi₂
        rcases Finset.mem_image.mp hi₁ with ⟨_, _, rfl⟩
        rcases Finset.mem_image.mp hi₂ with ⟨_, _, h⟩
        cases h
      dsimp [candQCand]
      rw [Finset.prod_union hdisj_sum,
        Finset.prod_image (fun _ _ _ _ h => Sum.inr.inj h),
        Finset.prod_singleton,
        Finset.prod_image (fun _ _ _ _ h => Sum.inl.inj h),
        Finset.prod_union (hPhi_disj w),
        Finset.prod_image (fun _ _ _ _ h => hPhi1_inj h),
        Finset.prod_image (hPhi2_injOn w)]
      simp [S, pow_add]
  have h_s4 : ∀ {N q : ℕ} (C₁ r_star m : ℕ), 3 ≤ C₁ → m < cspKMom C₁ →
      ∀ (a b : Fin N → Fin q) (z_prev : Fin m → (Fin N → Fin q)),
      dHam a b ≤ C₁ * r_star →
      (∀ t : Fin m, dHam (z_prev t) a ≤ C₁ * r_star) →
      ∀ s : ℕ,
      ((Finset.univ.filter (fun x : Fin N → Fin q =>
        (candMFresh a b m z_prev x).card = s ∧ dHam x a ≤ C₁ * r_star)).card : ℝ) ≤
        ((C₁ * r_star + 1 : ℕ) : ℝ) *
          (2 : ℝ) ^ ((1 / 100 : ℝ) * (cspLam0 C₁ : ℝ) * (r_star : ℝ)) *
          ((N.choose s : ℝ) * ((q - 1 : ℕ) : ℝ) ^ s) := by
    clear hσ_pos _hp_edge_pos hσ_up h_binom_edge hp_keep_pos hp_keep_up _hab hd_ab a b hr r_star hC₁ C₁
    intro N q C₁ r_star m hC₁_loc hm_loc a b z_prev hd_ab_loc hz_prev s
    let R_old := cspRvc a b m z_prev
    let R_neq := R_old.filter (fun vc : Fin N × Fin q => vc.2 ≠ a vc.1)
    have hR_neq_card : R_neq.card ≤ (1 + m) * (C₁ * r_star) := by
      have hsub : R_neq ⊆ (diffCoords a b).image (fun v => (v, b v)) ∪
          Finset.univ.biUnion (fun t : Fin m =>
            (diffCoords (z_prev t) a).image (fun v => (v, z_prev t v))) := by
        intro vc hvc
        simp only [R_neq, R_old, cspRvc, Finset.mem_filter, Finset.mem_union,
          Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_biUnion] at hvc
        rcases hvc with ⟨(⟨v, rfl⟩ | ⟨v, rfl⟩) | ⟨t, v, rfl⟩, hne⟩
        · exact absurd rfl hne
        · simp only [Finset.mem_union, Finset.mem_image, Finset.mem_biUnion,
            Finset.mem_univ, true_and, diffCoords, Finset.mem_filter]
          exact Or.inl ⟨v, Ne.symm hne, rfl⟩
        · simp only [Finset.mem_union, Finset.mem_image, Finset.mem_biUnion,
            Finset.mem_univ, true_and, diffCoords, Finset.mem_filter]
          exact Or.inr ⟨t, v, hne, rfl⟩
      have hc1 := Finset.card_le_card hsub
      have hc2 := Finset.card_union_le
        ((diffCoords a b).image (fun v => (v, b v)))
        (Finset.univ.biUnion (fun t : Fin m =>
          (diffCoords (z_prev t) a).image (fun v => (v, z_prev t v))))
      have hc_ab : ((diffCoords a b).image (fun v => (v, b v))).card ≤ C₁ * r_star :=
        le_trans Finset.card_image_le hd_ab_loc
      have hc_z : (Finset.univ.biUnion (fun t : Fin m =>
          (diffCoords (z_prev t) a).image (fun v => (v, z_prev t v)))).card ≤
          m * (C₁ * r_star) := by
        calc
          (Finset.univ.biUnion (fun t : Fin m =>
              (diffCoords (z_prev t) a).image (fun v => (v, z_prev t v)))).card
            ≤ ∑ t : Fin m, ((diffCoords (z_prev t) a).image (fun v => (v, z_prev t v))).card :=
              Finset.card_biUnion_le
          _ ≤ ∑ _ : Fin m, (C₁ * r_star) :=
              Finset.sum_le_sum (fun t _ => le_trans Finset.card_image_le (hz_prev t))
          _ = m * (C₁ * r_star) := by rw [Finset.sum_const, Finset.card_fin, smul_eq_mul]
      have h_add : C₁ * r_star + m * (C₁ * r_star) = (1 + m) * (C₁ * r_star) := by ring
      omega
    have hR_neq_20 : R_neq.card ≤ 20 * C₁ ^ 2 * (C₁ * r_star) := by
      have h1m : 1 + m ≤ 20 * C₁ ^ 2 := by
        unfold cspKMom at hm_loc
        omega
      exact le_trans hR_neq_card (Nat.mul_le_mul_right (C₁ * r_star) h1m)
    let Sphere_a : Finset (Fin N → Fin q) :=
      ((Finset.univ : Finset (Fin N)).powersetCard s).biUnion (fun S =>
        Fintype.piFinset (fun v : Fin N =>
          if v ∈ S then (Finset.univ : Finset (Fin q)).erase (a v) else {a v}))
    have hSphere_card : Sphere_a.card ≤ N.choose s * (q - 1) ^ s := by
      calc
        Sphere_a.card
          ≤ ∑ S ∈ (Finset.univ : Finset (Fin N)).powersetCard s,
              (Fintype.piFinset (fun v : Fin N =>
                if v ∈ S then (Finset.univ : Finset (Fin q)).erase (a v) else {a v})).card :=
            Finset.card_biUnion_le
        _ = ∑ S ∈ (Finset.univ : Finset (Fin N)).powersetCard s, (q - 1) ^ s := by
            refine Finset.sum_congr rfl (fun S hS => ?_)
            have hS_card : S.card = s := (Finset.mem_powersetCard.mp hS).2
            rw [Fintype.card_piFinset]
            have hfac : ∀ v ∈ (Finset.univ : Finset (Fin N)),
                (if v ∈ S then (Finset.univ : Finset (Fin q)).erase (a v) else {a v}).card =
                  if v ∈ S then q - 1 else 1 := by
              intro v _
              split_ifs
              · rw [Finset.card_erase_of_mem (Finset.mem_univ (a v)), Finset.card_fin]
              · exact Finset.card_singleton _
            rw [Finset.prod_congr rfl hfac, Finset.prod_ite]
            have hfilt : (Finset.univ : Finset (Fin N)).filter (fun v => v ∈ S) = S := by
              ext v; simp
            rw [hfilt, Finset.prod_const, hS_card, Finset.prod_const_one, mul_one]
        _ = N.choose s * (q - 1) ^ s := by
            rw [Finset.sum_const, Finset.card_powersetCard, Finset.card_fin, smul_eq_mul]
    let G_of : (Fin N → Fin q) → Finset (Fin N × Fin q) :=
      fun x =>
        (Finset.univ.filter (fun v : Fin N => v ∉ candMFresh a b m z_prev x ∧ x v ≠ a v)).image
          (fun v => (v, x v))
    let y_of : (Fin N → Fin q) → (Fin N → Fin q) :=
      fun x v => if v ∈ candMFresh a b m z_prev x then x v else a v
    have hy_fresh : ∀ x : Fin N → Fin q,
        candMFresh a b m z_prev x = Finset.univ.filter (fun v : Fin N => y_of x v ≠ a v) := by
      intro x
      ext v
      simp only [candMFresh, y_of, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro hv
        rw [if_pos (by simpa [candMFresh] using hv)]
        intro heq
        apply hv
        rw [heq]
        simp only [cspRvc, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and]
        exact Or.inl (Or.inl ⟨v, rfl⟩)
      · intro hne
        by_contra hnot
        simp [hnot] at hne
    have hG_mem_iff : ∀ (x : Fin N → Fin q) (v : Fin N),
        v ∉ candMFresh a b m z_prev x →
        ∀ c : Fin q, (v, c) ∈ G_of x ↔ c = x v ∧ x v ≠ a v := by
      intro x v hv c
      simp only [G_of, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and, Prod.mk.injEq]
      constructor
      · rintro ⟨v', ⟨_, hne⟩, rfl, rfl⟩
        exact ⟨rfl, hne⟩
      · rintro ⟨rfl, hne⟩
        exact ⟨v, ⟨hv, hne⟩, rfl, rfl⟩
    let P_old := R_neq.powerset.filter (fun G => G.card ≤ C₁ * r_star)
    have hFib_le : (Finset.univ.filter (fun x : Fin N → Fin q =>
        (candMFresh a b m z_prev x).card = s ∧ dHam x a ≤ C₁ * r_star)).card ≤
        (P_old ×ˢ Sphere_a).card := by
      apply Finset.card_le_card_of_injOn (fun x => (G_of x, y_of x))
      · intro x hx
        simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hx
        simp only [P_old, Finset.mem_coe, Finset.mem_product, Finset.mem_filter,
          Finset.mem_powerset]
        refine ⟨⟨?_, ?_⟩, ?_⟩
        · intro vc hvc
          rcases Finset.mem_image.mp hvc with ⟨v, hv, rfl⟩
          simp only [candMFresh, Finset.mem_filter, Finset.mem_univ, true_and, not_not] at hv
          simp only [R_neq, R_old, Finset.mem_filter]
          exact ⟨hv.1, hv.2⟩
        · have hsub_da : Finset.univ.filter
              (fun v : Fin N => v ∉ candMFresh a b m z_prev x ∧ x v ≠ a v) ⊆ diffCoords x a := by
            intro v hv
            simp only [diffCoords, Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
            exact hv.2
          exact le_trans Finset.card_image_le (le_trans (Finset.card_le_card hsub_da) hx.2)
        · simp only [Sphere_a, Finset.mem_biUnion, Finset.mem_powersetCard,
            Fintype.mem_piFinset]
          refine ⟨candMFresh a b m z_prev x, ⟨Finset.subset_univ _, hx.1⟩, ?_⟩
          intro v
          dsimp [y_of]
          split_ifs with hv
          · rw [Finset.mem_erase]
            refine ⟨?_, Finset.mem_univ _⟩
            intro heq
            simp only [candMFresh, Finset.mem_filter, Finset.mem_univ, true_and] at hv
            apply hv
            rw [heq]
            simp only [cspRvc, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and]
            exact Or.inl (Or.inl ⟨v, rfl⟩)
          · exact Finset.mem_singleton_self _
      · intro x₁ _ x₂ _ heq
        rcases Prod.mk.inj heq with ⟨hG_eq, hy_eq⟩
        have hS_eq : candMFresh a b m z_prev x₁ = candMFresh a b m z_prev x₂ := by
          rw [hy_fresh x₁, hy_fresh x₂, hy_eq]
        funext v
        by_cases hv : v ∈ candMFresh a b m z_prev x₁
        · have hv₂ : v ∈ candMFresh a b m z_prev x₂ := hS_eq ▸ hv
          have hy_v := congr_fun hy_eq v
          simpa [y_of, if_pos hv, if_pos hv₂] using hy_v
        · have hv₂ : v ∉ candMFresh a b m z_prev x₂ := hS_eq ▸ hv
          by_cases hx₁_ne : x₁ v ≠ a v
          · have hmem₁ : (v, x₁ v) ∈ G_of x₁ := (hG_mem_iff x₁ v hv (x₁ v)).mpr ⟨rfl, hx₁_ne⟩
            rw [hG_eq] at hmem₁
            exact ((hG_mem_iff x₂ v hv₂ (x₁ v)).mp hmem₁).1
          · push_neg at hx₁_ne
            by_contra hx₂_ne
            have hx₂_ne_a : x₂ v ≠ a v := fun h => hx₂_ne (hx₁_ne.trans h.symm)
            have hmem₂ : (v, x₂ v) ∈ G_of x₂ := (hG_mem_iff x₂ v hv₂ (x₂ v)).mpr ⟨rfl, hx₂_ne_a⟩
            rw [← hG_eq] at hmem₂
            have heq₁₂ := ((hG_mem_iff x₁ v hv (x₂ v)).mp hmem₂).1
            exact hx₂_ne heq₁₂.symm
    rw [Finset.card_product] at hFib_le
    have hFib_nat := le_trans hFib_le (Nat.mul_le_mul_left P_old.card hSphere_card)
    have hFib_r : ((Finset.univ.filter (fun x : Fin N → Fin q =>
        (candMFresh a b m z_prev x).card = s ∧ dHam x a ≤ C₁ * r_star)).card : ℝ) ≤
        (P_old.card : ℝ) * ((N.choose s : ℝ) * ((q - 1 : ℕ) : ℝ) ^ s) := by
      exact_mod_cast hFib_nat
    have hP_old_r : (P_old.card : ℝ) ≤
        ((C₁ * r_star + 1 : ℕ) : ℝ) *
          (2 : ℝ) ^ (((2 * Nat.clog 2 C₁ + 6) * (C₁ * r_star) : ℕ) : ℝ) :=
      powerset_card_le_bound R_neq C₁ 20 (C₁ * r_star) hC₁_loc (by omega) hR_neq_20
    have hexp_eq : (((2 * Nat.clog 2 C₁ + 6) * (C₁ * r_star) : ℕ) : ℝ) =
        (1 / 100 : ℝ) * (cspLam0 C₁ : ℝ) * (r_star : ℝ) := by
      unfold cspLam0
      push_cast
      ring
    rw [hexp_eq] at hP_old_r
    exact le_trans hFib_r (mul_le_mul_of_nonneg_right hP_old_r (by positivity))
  have h_s5_poly : ∀ (N q : ℕ) (σ p_keep : ℝ),
      0 < σ →
      σ * (r_star : ℝ) / 2 ≤ (10001 / 10000 : ℝ) * (cspBeta0 C₁ : ℝ) →
      (∀ s : ℕ,
        (N.choose s : ℝ) * ((q - 1 : ℕ) : ℝ) ^ s * ((2 : ℝ) ^ (- σ)) ^ (s * (N - 1)) ≤
          (2 : ℝ) ^ (2 * (r_star : ℝ) - (cspGamma0 C₁ : ℝ) * (s : ℝ))) →
      0 < p_keep →
      p_keep ≤ (2 : ℝ) ^ (- (747 / 1000 : ℝ) * (cspLam0 C₁ : ℝ) * (r_star : ℝ)) →
      ∀ (a₀ b₀ : Fin N → Fin q), dHam a₀ b₀ ≤ C₁ * r_star →
      ∀ m < cspKMom C₁, ∀ z_prev : Fin m → (Fin N → Fin q),
        Function.Injective z_prev →
        (∀ t : Fin m, z_prev t ∈ cspPoolCand C₁ r_star a₀ b₀) →
        ∑ x ∈ cspPoolCand C₁ r_star a₀ b₀ \ Finset.univ.image z_prev,
          ∑ w ∈ candMWit C₁ r_star a₀ b₀ m z_prev x,
            (∏ i ∈ candQCand C₁ a₀ b₀ m z_prev x w,
              Sum.elim (fun _ => (2 : ℝ) ^ (- σ)) (fun _ => p_keep) i) ≤
          (2 : ℝ) ^ (- (72 / 100 : ℝ) * (cspLam0 C₁ : ℝ) * (r_star : ℝ)) := by
    clear hσ_pos _hp_edge_pos hσ_up h_binom_edge hp_keep_pos hp_keep_up _hab hd_ab a b
    intro N q σ p_keep hσ_pos_loc hσ_up_loc h_bin_loc hp_keep_pos_loc hp_keep_up_loc
      a₀ b₀ hd_ab_loc m hm z_prev _ hz_pool
    have hlam_ge : 3000 ≤ cspLam0 C₁ := by
      have h := (lam0_ge_1000_C1 C₁ hC₁).2.1
      omega
    have hbeta_eq : (cspBeta0 C₁ : ℝ) = 6 * (cspLam0 C₁ : ℝ) := by
      unfold cspBeta0; push_cast; ring
    have hgamma_eq : (cspGamma0 C₁ : ℝ) = 5 * (cspLam0 C₁ : ℝ) := by
      unfold cspGamma0; push_cast; ring
    let p_edge : ℝ := (2 : ℝ) ^ (- σ)
    let P_rem := cspPoolCand C₁ r_star a₀ b₀ \ Finset.univ.image z_prev
    have h_xw_bound : ∀ x ∈ P_rem, ∀ w ∈ candMWit C₁ r_star a₀ b₀ m z_prev x,
        ∏ i ∈ candQCand C₁ a₀ b₀ m z_prev x w,
          Sum.elim (fun _ => p_edge) (fun _ => p_keep) i ≤
          p_keep * p_edge ^ ((candMFresh a₀ b₀ m z_prev x).card * (N - 1)) *
            (2 : ℝ) ^ ((346 / 100 : ℝ) * (cspLam0 C₁ : ℝ) *
              ((candMFresh a₀ b₀ m z_prev x).card : ℝ)) := by
      intro x hx w hw
      have hx_pool := (Finset.mem_sdiff.mp hx).1
      simp only [cspPoolCand, Finset.mem_filter, Finset.mem_univ, true_and] at hx_pool
      rcases hx_pool with ⟨_, _, hd_xa, hd_xb⟩
      obtain ⟨_, _, _, h_prod_eq⟩ := h_s3 C₁ r_star m hC₁ hr a₀ b₀ z_prev x hx
      rw [h_prod_eq w p_edge p_keep]
      let S := candMFresh a₀ b₀ m z_prev x
      let s := S.card
      let a1 := (candA1 S).card
      let a2 := (candA2 C₁ a₀ b₀ x S w).card
      let N1 := N - 1
      have hs1_z : 2 * ((s : ℤ) * (N1 : ℤ) - (a1 : ℤ)) ≤ (s : ℤ) ^ 2 := h_s1 S
      have hs2_z : 40 * ((s : ℤ) ^ 2 - 2 * (a2 : ℤ)) ≤ 23 * (r_star : ℤ) * (s : ℤ) :=
        ((candMWit_card_and_quad C₁ r_star m hC₁ hr a₀ b₀ z_prev x hd_xa hd_xb).2 w hw).2
      have hdef_z : 80 * ((s : ℤ) * (N1 : ℤ) - ((a1 + a2 : ℕ) : ℤ)) ≤
          23 * (r_star : ℤ) * (s : ℤ) := by
        push_cast
        linarith only [hs1_z, hs2_z]
      have hdef_r : 80 * (((s * N1 : ℕ) : ℝ) - ((a1 + a2 : ℕ) : ℝ)) ≤
          23 * (r_star : ℝ) * (s : ℝ) := by
        have hcast : ((80 * ((s : ℤ) * (N1 : ℤ) - ((a1 + a2 : ℕ) : ℤ))) : ℝ) ≤
            ((23 * (r_star : ℤ) * (s : ℤ)) : ℝ) := by exact_mod_cast hdef_z
        push_cast at hcast ⊢
        linarith only [hcast]
      have hσ_def : σ * (((s * N1 : ℕ) : ℝ) - ((a1 + a2 : ℕ) : ℝ)) ≤
          (346 / 100 : ℝ) * (cspLam0 C₁ : ℝ) * (s : ℝ) := by
        have h1 : σ * (((s * N1 : ℕ) : ℝ) - ((a1 + a2 : ℕ) : ℝ)) ≤
            (σ * (r_star : ℝ) / 2) * ((23 / 40 : ℝ) * (s : ℝ)) := by
          have hm := mul_le_mul_of_nonneg_left hdef_r (le_of_lt hσ_pos_loc)
          linarith [hm,
            show σ * (23 * (r_star : ℝ) * (s : ℝ)) =
              80 * ((σ * (r_star : ℝ) / 2) * ((23 / 40 : ℝ) * (s : ℝ))) by ring,
            show σ * (80 * (((s * N1 : ℕ) : ℝ) - ((a1 + a2 : ℕ) : ℝ))) =
              80 * (σ * (((s * N1 : ℕ) : ℝ) - ((a1 + a2 : ℕ) : ℝ))) by ring]
        have h2 : (σ * (r_star : ℝ) / 2) * ((23 / 40 : ℝ) * (s : ℝ)) ≤
            ((10001 / 10000 : ℝ) * (6 * (cspLam0 C₁ : ℝ))) * ((23 / 40 : ℝ) * (s : ℝ)) :=
          mul_le_mul_of_nonneg_right (by linarith only [hσ_up_loc, hbeta_eq]) (by positivity)
        have hprod_nn : (0 : ℝ) ≤ (cspLam0 C₁ : ℝ) * (s : ℝ) := by positivity
        linarith [h1, h2, hprod_nn]
      have hp_pow : p_edge ^ (a1 + a2) ≤ p_edge ^ (s * N1) *
          (2 : ℝ) ^ ((346 / 100 : ℝ) * (cspLam0 C₁ : ℝ) * (s : ℝ)) := by
        have h_eq1 : p_edge ^ (a1 + a2) = (2 : ℝ) ^ (- σ * ((a1 + a2 : ℕ) : ℝ)) := by
          dsimp [p_edge]
          rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
        have h_eq2 : p_edge ^ (s * N1) *
            (2 : ℝ) ^ ((346 / 100 : ℝ) * (cspLam0 C₁ : ℝ) * (s : ℝ)) =
            (2 : ℝ) ^ (- σ * ((s * N1 : ℕ) : ℝ) +
              (346 / 100 : ℝ) * (cspLam0 C₁ : ℝ) * (s : ℝ)) := by
          dsimp [p_edge]
          rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),
            ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
        rw [h_eq1, h_eq2]
        apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
        linarith only [hσ_def]
      calc
        p_keep * p_edge ^ (a1 + a2)
          ≤ p_keep * (p_edge ^ (s * N1) *
              (2 : ℝ) ^ ((346 / 100 : ℝ) * (cspLam0 C₁ : ℝ) * (s : ℝ))) :=
            mul_le_mul_of_nonneg_left hp_pow (le_of_lt hp_keep_pos_loc)
        _ = p_keep * p_edge ^ (s * N1) *
              (2 : ℝ) ^ ((346 / 100 : ℝ) * (cspLam0 C₁ : ℝ) * (s : ℝ)) :=
            (mul_assoc _ _ _).symm
    let C_fixed : ℝ := (2 : ℝ) ^ (3 * (r_star : ℝ)) * p_keep
    have hC_nn : 0 ≤ C_fixed := by positivity
    have h_x_bound : ∀ x ∈ P_rem,
        ∑ w ∈ candMWit C₁ r_star a₀ b₀ m z_prev x,
          (∏ i ∈ candQCand C₁ a₀ b₀ m z_prev x w,
            Sum.elim (fun _ => p_edge) (fun _ => p_keep) i) ≤
        (p_edge ^ ((candMFresh a₀ b₀ m z_prev x).card * (N - 1)) *
          (2 : ℝ) ^ ((356 / 100 : ℝ) * (cspLam0 C₁ : ℝ) *
            ((candMFresh a₀ b₀ m z_prev x).card : ℝ))) * C_fixed := by
      intro x hx
      have hx_pool := (Finset.mem_sdiff.mp hx).1
      simp only [cspPoolCand, Finset.mem_filter, Finset.mem_univ, true_and] at hx_pool
      have h_wcard_r :=
        (candMWit_card_and_quad C₁ r_star m hC₁ hr a₀ b₀ z_prev x hx_pool.2.2.1 hx_pool.2.2.2).1
      let s := (candMFresh a₀ b₀ m z_prev x).card
      calc
        ∑ w ∈ candMWit C₁ r_star a₀ b₀ m z_prev x, _
          ≤ ∑ _w ∈ candMWit C₁ r_star a₀ b₀ m z_prev x,
              (p_keep * p_edge ^ (s * (N - 1)) *
                (2 : ℝ) ^ ((346 / 100 : ℝ) * (cspLam0 C₁ : ℝ) * (s : ℝ))) :=
            Finset.sum_le_sum (fun w hw => h_xw_bound x hx w hw)
        _ = ((candMWit C₁ r_star a₀ b₀ m z_prev x).card : ℝ) *
              (p_keep * p_edge ^ (s * (N - 1)) *
                (2 : ℝ) ^ ((346 / 100 : ℝ) * (cspLam0 C₁ : ℝ) * (s : ℝ))) := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ (2 : ℝ) ^ (3 * (r_star : ℝ) + (1 / 10 : ℝ) * (cspLam0 C₁ : ℝ) * (s : ℝ)) *
              (p_keep * p_edge ^ (s * (N - 1)) *
                (2 : ℝ) ^ ((346 / 100 : ℝ) * (cspLam0 C₁ : ℝ) * (s : ℝ))) :=
            mul_le_mul_of_nonneg_right h_wcard_r (by positivity)
        _ = (p_edge ^ (s * (N - 1)) *
              ((2 : ℝ) ^ ((1 / 10 : ℝ) * (cspLam0 C₁ : ℝ) * (s : ℝ)) *
                (2 : ℝ) ^ ((346 / 100 : ℝ) * (cspLam0 C₁ : ℝ) * (s : ℝ)))) * C_fixed := by
            rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
            dsimp [C_fixed]
            ring
        _ = (p_edge ^ (s * (N - 1)) *
              (2 : ℝ) ^ ((356 / 100 : ℝ) * (cspLam0 C₁ : ℝ) * (s : ℝ))) * C_fixed := by
            rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
            congr 3
            ring
    let R_s := Finset.range (C₁ * r_star + 1)
    have hP_bi : P_rem = R_s.biUnion
        (fun s => P_rem.filter (fun x => (candMFresh a₀ b₀ m z_prev x).card = s)) := by
      ext x
      simp only [R_s, Finset.mem_biUnion, Finset.mem_range, Finset.mem_filter]
      constructor
      · intro hx
        have hS_sub := (h_s3 C₁ r_star m hC₁ hr a₀ b₀ z_prev x hx).1
        have hx_pool := (Finset.mem_sdiff.mp hx).1
        simp only [cspPoolCand, Finset.mem_filter, Finset.mem_univ, true_and] at hx_pool
        have hs_le : (candMFresh a₀ b₀ m z_prev x).card ≤ C₁ * r_star :=
          le_trans (Finset.card_le_card (hS_sub.trans Finset.inter_subset_left)) hx_pool.2.2.1
        exact ⟨(candMFresh a₀ b₀ m z_prev x).card, Nat.lt_succ_of_le hs_le, hx, rfl⟩
      · rintro ⟨_, _, hx, _⟩
        exact hx
    have hP_disj : (R_s : Set ℕ).PairwiseDisjoint
        (fun s => P_rem.filter (fun x => (candMFresh a₀ b₀ m z_prev x).card = s)) := by
      intro s₁ _ s₂ _ hne
      simp only [Function.onFun, Finset.disjoint_left, Finset.mem_filter]
      intro x hx₁ hx₂
      exact hne (hx₁.2.symm.trans hx₂.2)
    have hz_da : ∀ t : Fin m, dHam (z_prev t) a₀ ≤ C₁ * r_star := by
      intro t
      have ht := hz_pool t
      simp only [cspPoolCand, Finset.mem_filter, Finset.mem_univ, true_and] at ht
      exact ht.2.2.1
    have h_range_r : ((C₁ * r_star + 1 : ℕ) : ℝ) ≤ (2 : ℝ) ^ (2 * (r_star : ℝ)) := by
      have hcr_le : C₁ * r_star + 1 ≤ r_star * r_star := by
        have hC1_le : C₁ + 1 ≤ r_star := by omega
        calc
          C₁ * r_star + 1 ≤ C₁ * r_star + r_star := by omega
          _ = (C₁ + 1) * r_star := (Nat.succ_mul C₁ r_star).symm
          _ ≤ r_star * r_star := Nat.mul_le_mul_right r_star hC1_le
      have hr_pow : r_star ≤ 2 ^ r_star := Nat.le_of_lt Nat.lt_two_pow_self
      have hsq_pow : r_star * r_star ≤ 2 ^ (2 * r_star) := by
        calc
          r_star * r_star ≤ 2 ^ r_star * 2 ^ r_star := Nat.mul_le_mul hr_pow hr_pow
          _ = 2 ^ (r_star + r_star) := (pow_add 2 r_star r_star).symm
          _ = 2 ^ (2 * r_star) := by rw [two_mul]
      have hnat := le_trans hcr_le hsq_pow
      have hcast : ((C₁ * r_star + 1 : ℕ) : ℝ) ≤ ((2 ^ (2 * r_star) : ℕ) : ℝ) := by
        exact_mod_cast hnat
      rwa [Nat.cast_pow, Nat.cast_ofNat, ← Real.rpow_natCast, Nat.cast_mul, Nat.cast_ofNat] at hcast
    have h_s_term : ∀ s ∈ R_s,
        ∑ x ∈ P_rem.filter (fun x => (candMFresh a₀ b₀ m z_prev x).card = s),
          ((p_edge ^ ((candMFresh a₀ b₀ m z_prev x).card * (N - 1)) *
            (2 : ℝ) ^ ((356 / 100 : ℝ) * (cspLam0 C₁ : ℝ) *
              ((candMFresh a₀ b₀ m z_prev x).card : ℝ))) * C_fixed) ≤
        (2 : ℝ) ^ (2 * (r_star : ℝ)) *
          (2 : ℝ) ^ ((1 / 100 : ℝ) * (cspLam0 C₁ : ℝ) * (r_star : ℝ)) *
          (2 : ℝ) ^ (2 * (r_star : ℝ)) * C_fixed := by
      intro s _
      have h_congr : ∑ x ∈ P_rem.filter (fun x => (candMFresh a₀ b₀ m z_prev x).card = s),
          ((p_edge ^ ((candMFresh a₀ b₀ m z_prev x).card * (N - 1)) *
            (2 : ℝ) ^ ((356 / 100 : ℝ) * (cspLam0 C₁ : ℝ) *
              ((candMFresh a₀ b₀ m z_prev x).card : ℝ))) * C_fixed) =
        ((P_rem.filter (fun x => (candMFresh a₀ b₀ m z_prev x).card = s)).card : ℝ) *
          ((p_edge ^ (s * (N - 1)) *
            (2 : ℝ) ^ ((356 / 100 : ℝ) * (cspLam0 C₁ : ℝ) * (s : ℝ))) * C_fixed) := by
        have h1 : ∀ x ∈ P_rem.filter (fun x => (candMFresh a₀ b₀ m z_prev x).card = s),
            (p_edge ^ ((candMFresh a₀ b₀ m z_prev x).card * (N - 1)) *
              (2 : ℝ) ^ ((356 / 100 : ℝ) * (cspLam0 C₁ : ℝ) *
                ((candMFresh a₀ b₀ m z_prev x).card : ℝ))) * C_fixed =
              (p_edge ^ (s * (N - 1)) *
                (2 : ℝ) ^ ((356 / 100 : ℝ) * (cspLam0 C₁ : ℝ) * (s : ℝ))) * C_fixed := by
          intro x hx
          rw [(Finset.mem_filter.mp hx).2]
        rw [Finset.sum_congr rfl h1, Finset.sum_const, nsmul_eq_mul]
      rw [h_congr]
      have hfib_sub : P_rem.filter (fun x => (candMFresh a₀ b₀ m z_prev x).card = s) ⊆
          Finset.univ.filter (fun x =>
            (candMFresh a₀ b₀ m z_prev x).card = s ∧ dHam x a₀ ≤ C₁ * r_star) := by
        intro x hx
        rcases Finset.mem_filter.mp hx with ⟨hxP, hxs⟩
        have hx_pool := (Finset.mem_sdiff.mp hxP).1
        simp only [cspPoolCand, Finset.mem_filter, Finset.mem_univ, true_and] at hx_pool
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ x, hxs, hx_pool.2.2.1⟩
      have hfib_le1 : ((P_rem.filter (fun x => (candMFresh a₀ b₀ m z_prev x).card = s)).card : ℝ) ≤
          ((Finset.univ.filter (fun x =>
            (candMFresh a₀ b₀ m z_prev x).card = s ∧ dHam x a₀ ≤ C₁ * r_star)).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hfib_sub
      have hfib_r : ((P_rem.filter (fun x => (candMFresh a₀ b₀ m z_prev x).card = s)).card : ℝ) ≤
          (2 : ℝ) ^ (2 * (r_star : ℝ)) *
            (2 : ℝ) ^ ((1 / 100 : ℝ) * (cspLam0 C₁ : ℝ) * (r_star : ℝ)) *
            ((N.choose s : ℝ) * ((q - 1 : ℕ) : ℝ) ^ s) := by
        have hs4 := le_trans hfib_le1 (h_s4 C₁ r_star m hC₁ hm a₀ b₀ z_prev hd_ab_loc hz_da s)
        exact le_trans hs4 (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right h_range_r (by positivity)) (by positivity))
      have hs_bin : ((N.choose s : ℝ) * ((q - 1 : ℕ) : ℝ) ^ s * p_edge ^ (s * (N - 1))) *
          (2 : ℝ) ^ ((356 / 100 : ℝ) * (cspLam0 C₁ : ℝ) * (s : ℝ)) ≤
          (2 : ℝ) ^ (2 * (r_star : ℝ)) := by
        calc
          ((N.choose s : ℝ) * ((q - 1 : ℕ) : ℝ) ^ s * p_edge ^ (s * (N - 1))) *
              (2 : ℝ) ^ ((356 / 100 : ℝ) * (cspLam0 C₁ : ℝ) * (s : ℝ))
            ≤ (2 : ℝ) ^ (2 * (r_star : ℝ) - (cspGamma0 C₁ : ℝ) * (s : ℝ)) *
                (2 : ℝ) ^ ((356 / 100 : ℝ) * (cspLam0 C₁ : ℝ) * (s : ℝ)) :=
              mul_le_mul_of_nonneg_right (h_bin_loc s) (by positivity)
          _ = (2 : ℝ) ^ (2 * (r_star : ℝ) - (cspGamma0 C₁ : ℝ) * (s : ℝ) +
                (356 / 100 : ℝ) * (cspLam0 C₁ : ℝ) * (s : ℝ)) := by
              rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
          _ ≤ (2 : ℝ) ^ (2 * (r_star : ℝ)) := by
              apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
              have hls_nn : 0 ≤ (cspLam0 C₁ : ℝ) * (s : ℝ) := by positivity
              rw [hgamma_eq]
              linarith only [hls_nn]
      calc
        ((P_rem.filter (fun x => (candMFresh a₀ b₀ m z_prev x).card = s)).card : ℝ) *
            ((p_edge ^ (s * (N - 1)) *
              (2 : ℝ) ^ ((356 / 100 : ℝ) * (cspLam0 C₁ : ℝ) * (s : ℝ))) * C_fixed)
          ≤ ((2 : ℝ) ^ (2 * (r_star : ℝ)) *
              (2 : ℝ) ^ ((1 / 100 : ℝ) * (cspLam0 C₁ : ℝ) * (r_star : ℝ)) *
              ((N.choose s : ℝ) * ((q - 1 : ℕ) : ℝ) ^ s)) *
              ((p_edge ^ (s * (N - 1)) *
                (2 : ℝ) ^ ((356 / 100 : ℝ) * (cspLam0 C₁ : ℝ) * (s : ℝ))) * C_fixed) :=
            mul_le_mul_of_nonneg_right hfib_r (by positivity)
        _ = (2 : ℝ) ^ (2 * (r_star : ℝ)) *
              (2 : ℝ) ^ ((1 / 100 : ℝ) * (cspLam0 C₁ : ℝ) * (r_star : ℝ)) *
              (((N.choose s : ℝ) * ((q - 1 : ℕ) : ℝ) ^ s * p_edge ^ (s * (N - 1))) *
                (2 : ℝ) ^ ((356 / 100 : ℝ) * (cspLam0 C₁ : ℝ) * (s : ℝ))) * C_fixed := by
            ring
        _ ≤ (2 : ℝ) ^ (2 * (r_star : ℝ)) *
              (2 : ℝ) ^ ((1 / 100 : ℝ) * (cspLam0 C₁ : ℝ) * (r_star : ℝ)) *
              (2 : ℝ) ^ (2 * (r_star : ℝ)) * C_fixed :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hs_bin (by positivity)) hC_nn
    have hRs_card : (R_s.card : ℝ) ≤ (2 : ℝ) ^ (2 * (r_star : ℝ)) := by
      simpa [R_s] using h_range_r
    have h_tot_1 : ∑ x ∈ P_rem, ∑ w ∈ candMWit C₁ r_star a₀ b₀ m z_prev x,
        (∏ i ∈ candQCand C₁ a₀ b₀ m z_prev x w,
          Sum.elim (fun _ => p_edge) (fun _ => p_keep) i) ≤
        (2 : ℝ) ^ (2 * (r_star : ℝ)) *
          ((2 : ℝ) ^ (2 * (r_star : ℝ)) *
            (2 : ℝ) ^ ((1 / 100 : ℝ) * (cspLam0 C₁ : ℝ) * (r_star : ℝ)) *
            (2 : ℝ) ^ (2 * (r_star : ℝ)) * C_fixed) := by
      calc
        ∑ x ∈ P_rem, ∑ w ∈ candMWit C₁ r_star a₀ b₀ m z_prev x, _
          ≤ ∑ x ∈ P_rem,
              ((p_edge ^ ((candMFresh a₀ b₀ m z_prev x).card * (N - 1)) *
                (2 : ℝ) ^ ((356 / 100 : ℝ) * (cspLam0 C₁ : ℝ) *
                  ((candMFresh a₀ b₀ m z_prev x).card : ℝ))) * C_fixed) :=
            Finset.sum_le_sum h_x_bound
        _ = ∑ s ∈ R_s, ∑ x ∈ P_rem.filter (fun x => (candMFresh a₀ b₀ m z_prev x).card = s),
              ((p_edge ^ ((candMFresh a₀ b₀ m z_prev x).card * (N - 1)) *
                (2 : ℝ) ^ ((356 / 100 : ℝ) * (cspLam0 C₁ : ℝ) *
                  ((candMFresh a₀ b₀ m z_prev x).card : ℝ))) * C_fixed) := by
            conv_lhs => rw [hP_bi]
            exact Finset.sum_biUnion hP_disj
        _ ≤ ∑ _s ∈ R_s,
              ((2 : ℝ) ^ (2 * (r_star : ℝ)) *
                (2 : ℝ) ^ ((1 / 100 : ℝ) * (cspLam0 C₁ : ℝ) * (r_star : ℝ)) *
                (2 : ℝ) ^ (2 * (r_star : ℝ)) * C_fixed) :=
            Finset.sum_le_sum h_s_term
        _ = (R_s.card : ℝ) *
              ((2 : ℝ) ^ (2 * (r_star : ℝ)) *
                (2 : ℝ) ^ ((1 / 100 : ℝ) * (cspLam0 C₁ : ℝ) * (r_star : ℝ)) *
                (2 : ℝ) ^ (2 * (r_star : ℝ)) * C_fixed) := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ (2 : ℝ) ^ (2 * (r_star : ℝ)) *
              ((2 : ℝ) ^ (2 * (r_star : ℝ)) *
                (2 : ℝ) ^ ((1 / 100 : ℝ) * (cspLam0 C₁ : ℝ) * (r_star : ℝ)) *
                (2 : ℝ) ^ (2 * (r_star : ℝ)) * C_fixed) :=
            mul_le_mul_of_nonneg_right hRs_card (by positivity)
    have hC_up : C_fixed ≤
        (2 : ℝ) ^ (3 * (r_star : ℝ)) *
          (2 : ℝ) ^ (- (747 / 1000 : ℝ) * (cspLam0 C₁ : ℝ) * (r_star : ℝ)) := by
      dsimp [C_fixed]
      exact mul_le_mul_of_nonneg_left hp_keep_up_loc (by positivity)
    have h_tot_2 : (2 : ℝ) ^ (2 * (r_star : ℝ)) *
          ((2 : ℝ) ^ (2 * (r_star : ℝ)) *
            (2 : ℝ) ^ ((1 / 100 : ℝ) * (cspLam0 C₁ : ℝ) * (r_star : ℝ)) *
            (2 : ℝ) ^ (2 * (r_star : ℝ)) * C_fixed) ≤
        (2 : ℝ) ^ (2 * (r_star : ℝ) + 2 * (r_star : ℝ) +
          (1 / 100 : ℝ) * (cspLam0 C₁ : ℝ) * (r_star : ℝ) + 2 * (r_star : ℝ) +
          3 * (r_star : ℝ) +
          (- (747 / 1000 : ℝ) * (cspLam0 C₁ : ℝ) * (r_star : ℝ))) := by
      calc
        (2 : ℝ) ^ (2 * (r_star : ℝ)) *
            ((2 : ℝ) ^ (2 * (r_star : ℝ)) *
              (2 : ℝ) ^ ((1 / 100 : ℝ) * (cspLam0 C₁ : ℝ) * (r_star : ℝ)) *
              (2 : ℝ) ^ (2 * (r_star : ℝ)) * C_fixed)
          ≤ (2 : ℝ) ^ (2 * (r_star : ℝ)) *
              ((2 : ℝ) ^ (2 * (r_star : ℝ)) *
                (2 : ℝ) ^ ((1 / 100 : ℝ) * (cspLam0 C₁ : ℝ) * (r_star : ℝ)) *
                (2 : ℝ) ^ (2 * (r_star : ℝ)) *
                ((2 : ℝ) ^ (3 * (r_star : ℝ)) *
                  (2 : ℝ) ^ (- (747 / 1000 : ℝ) * (cspLam0 C₁ : ℝ) * (r_star : ℝ)))) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left hC_up (by positivity)) (by positivity)
        _ = (2 : ℝ) ^ (2 * (r_star : ℝ)) *
              (2 : ℝ) ^ (2 * (r_star : ℝ)) *
              (2 : ℝ) ^ ((1 / 100 : ℝ) * (cspLam0 C₁ : ℝ) * (r_star : ℝ)) *
              (2 : ℝ) ^ (2 * (r_star : ℝ)) *
              (2 : ℝ) ^ (3 * (r_star : ℝ)) *
              (2 : ℝ) ^ (- (747 / 1000 : ℝ) * (cspLam0 C₁ : ℝ) * (r_star : ℝ)) := by ring
        _ = _ := by
            repeat rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    have h_exp_le : 2 * (r_star : ℝ) + 2 * (r_star : ℝ) +
        (1 / 100 : ℝ) * (cspLam0 C₁ : ℝ) * (r_star : ℝ) + 2 * (r_star : ℝ) +
        3 * (r_star : ℝ) +
        (- (747 / 1000 : ℝ) * (cspLam0 C₁ : ℝ) * (r_star : ℝ)) ≤
        - (72 / 100 : ℝ) * (cspLam0 C₁ : ℝ) * (r_star : ℝ) := by
      have hlam_r : (3000 : ℝ) ≤ (cspLam0 C₁ : ℝ) := by exact_mod_cast hlam_ge
      have hr_nn : (0 : ℝ) ≤ (r_star : ℝ) := Nat.cast_nonneg _
      nlinarith only [hlam_r, hr_nn]
    exact le_trans h_tot_1
      (le_trans h_tot_2 (Real.rpow_le_rpow_of_exponent_le (by norm_num) h_exp_le))
  refine ⟨fun m z_prev x => candMWit C₁ r_star a b m z_prev x,
    fun m z_prev x w => candQCand C₁ a b m z_prev x w, ?_, ?_, ?_⟩
  · intro m _ z_prev _ _ x hx w hw
    exact (h_s3 C₁ r_star m hC₁ hr a b z_prev x hx).2.1 w hw
  · intro ω m _ z_prev _ _ x hx hω hClean
    exact (h_s3 C₁ r_star m hC₁ hr a b z_prev x hx).2.2.1 ω hω hClean
  · unfold cspPEdge at h_binom_edge
    unfold cspPIota cspPEdge
    exact h_s5_poly (2 ^ cspL C₁ * r_star) (cspQ C₁)
      (cspSigmaEdge C₁ r_star) (cspPKeep C₁ r_star)
      hσ_pos hσ_up h_binom_edge hp_keep_pos hp_keep_up a b hd_ab

private theorem d3_and_cherry_query_sum_bounds (C₁ : ℕ) (hC₁ : 3 ≤ C₁) (r_star : ℕ) (hr : 1000 * C₁ < r_star)
    (hσ_pos : 0 < cspSigmaEdge C₁ r_star)
    (hp_edge_pos : 0 < cspPEdge C₁ r_star)
    (hp_edge_lt1 : cspPEdge C₁ r_star < 1)
    (h_cal : (4 : ℝ) * (2 : ℝ) ^ cspL C₁ * ((cspQ C₁ - 1 : ℕ) : ℝ) *
      (cspPEdge C₁ r_star) ^ (2 ^ cspL C₁ * r_star - 1) = (2 : ℝ) ^ (- (cspGamma0 C₁ : ℝ)))
    (hσ_up : cspSigmaEdge C₁ r_star * (r_star : ℝ) / 2 ≤
      (10001 / 10000 : ℝ) * (cspBeta0 C₁ : ℝ))
    (h_binom_edge : ∀ s : ℕ,
      ((2 ^ cspL C₁ * r_star).choose s : ℝ) * ((cspQ C₁ - 1 : ℕ) : ℝ) ^ s *
        (cspPEdge C₁ r_star) ^ (s * (2 ^ cspL C₁ * r_star - 1)) ≤
        (2 : ℝ) ^ (2 * (r_star : ℝ) - (cspGamma0 C₁ : ℝ) * (s : ℝ)))
    (hp_keep_pos : 0 < cspPKeep C₁ r_star)
    (hp_keep_up : cspPKeep C₁ r_star ≤
      (2 : ℝ) ^ (- (747 / 1000 : ℝ) * (cspLam0 C₁ : ℝ) * (r_star : ℝ))) :
    (∀ x u : Fin (2 ^ cspL C₁ * r_star) → Fin (cspQ C₁), x ≠ u → dHam x u ≤ C₁ * r_star →
      ∑ z ∈ Finset.univ.filter (fun z : Fin (2 ^ cspL C₁ * r_star) → Fin (cspQ C₁) =>
          dHam x z ≤ C₁ * r_star ∧
          r_star < cspInvEta0 C₁ * (d3Coords x u z).card),
        (cspPEdge C₁ r_star) ^ ((homQueries z \ (homQueries x ∪ homQueries u)).card) ≤
        (2 : ℝ) ^ (- (12 * (C₁ ^ 2 : ℕ) : ℝ) * (cspLam0 C₁ : ℝ) * (r_star : ℝ))) ∧
    (∀ x w₀ : Fin (2 ^ cspL C₁ * r_star) → Fin (cspQ C₁), x ≠ w₀ → dHam x w₀ ≤ C₁ * r_star →
      ∀ m < cspKCh C₁, ∀ y_prev : Fin m → (Fin (2 ^ cspL C₁ * r_star) → Fin (cspQ C₁)),
        Function.Injective y_prev →
        (∀ t : Fin m, y_prev t ∈ cspPoolCh C₁ r_star x w₀) →
        ∑ y ∈ cspPoolCh C₁ r_star x w₀ \ Finset.univ.image y_prev,
          (∏ i ∈ (({y} : Finset (Fin (2 ^ cspL C₁ * r_star) → Fin (cspQ C₁))).image Sum.inr ∪
              (homQueries y).image Sum.inl) \ cspUCh x w₀ m y_prev,
            cspPIota C₁ r_star i) ≤
          (2 : ℝ) ^ (- (72 / 100 : ℝ) * (cspLam0 C₁ : ℝ) * (r_star : ℝ))) :=
by
  classical
  have h_s1 : ∀ {N q : ℕ} (z : Fin N → Fin q) (S_old : Finset (Fin N → Fin q))
      (T : Finset (Fin N)), (∀ v ∈ T, ∀ y ∈ S_old, z v ≠ y v) →
      T.card * (N - 1) - T.card.choose 2 ≤ (homQueries z \ S_old.biUnion homQueries).card := by
    clear hC₁ hr hσ_pos hp_edge_pos hp_edge_lt1 h_cal hσ_up h_binom_edge hp_keep_pos hp_keep_up C₁ r_star
    intro N q z S_old T hT
    have hchoose2_int : ∀ m : ℕ, 2 * (m.choose 2 : ℤ) = (m : ℤ) * ((m : ℤ) - 1) := by
      intro m
      rcases m with _ | m
      · simp
      · have h2 : 2 * (m + 1).choose 2 = (m + 1) * m := by
          rw [Nat.choose_two_right, Nat.add_sub_cancel]
          exact Nat.mul_div_cancel' (Even.two_dvd (Nat.even_mul_pred_self (m + 1)))
        have hcast : ((2 * (m + 1).choose 2 : ℕ) : ℤ) = (((m + 1) * m : ℕ) : ℤ) := by
          exact_mod_cast h2
        push_cast at hcast ⊢
        linarith
    let P_sub : Finset (Fin N) → Finset (Fin N × Fin N) := fun S =>
      Finset.univ.filter (fun uv : Fin N × Fin N => uv.1 < uv.2 ∧ uv.1 ∈ S ∧ uv.2 ∈ S)
    have hP_sub_card : ∀ S : Finset (Fin N), (P_sub S).card = S.card.choose 2 := by
      intro S
      rw [← Finset.card_powersetCard 2 S]
      refine Finset.card_nbij (fun uv : Fin N × Fin N => ({uv.1, uv.2} : Finset (Fin N))) ?_ ?_ ?_
      · intro uv huv
        simp only [P_sub, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at huv
        rw [Finset.mem_coe, Finset.mem_powersetCard]
        refine ⟨?_, Finset.card_pair (ne_of_lt huv.1)⟩
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl
        · exact huv.2.1
        · exact huv.2.2
      · intro uv₁ h₁ uv₂ h₂ heq
        dsimp only at heq
        simp only [P_sub, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at h₁ h₂
        have hm1 : uv₁.1 ∈ ({uv₂.1, uv₂.2} : Finset (Fin N)) := by
          rw [← heq]; simp
        have hm2 : uv₁.2 ∈ ({uv₂.1, uv₂.2} : Finset (Fin N)) := by
          rw [← heq]; simp
        have hm3 : uv₂.1 ∈ ({uv₁.1, uv₁.2} : Finset (Fin N)) := by
          rw [heq]; simp
        have hm4 : uv₂.2 ∈ ({uv₁.1, uv₁.2} : Finset (Fin N)) := by
          rw [heq]; simp
        simp only [Finset.mem_insert, Finset.mem_singleton] at hm1 hm2 hm3 hm4
        have hlt1 : uv₁.1.1 < uv₁.2.1 := h₁.1
        have hlt2 : uv₂.1.1 < uv₂.2.1 := h₂.1
        have hv1 : uv₁.1.1 = uv₂.1.1 ∨ uv₁.1.1 = uv₂.2.1 := hm1.imp (congr_arg Fin.val) (congr_arg Fin.val)
        have hv2 : uv₁.2.1 = uv₂.1.1 ∨ uv₁.2.1 = uv₂.2.1 := hm2.imp (congr_arg Fin.val) (congr_arg Fin.val)
        have hv3 : uv₂.1.1 = uv₁.1.1 ∨ uv₂.1.1 = uv₁.2.1 := hm3.imp (congr_arg Fin.val) (congr_arg Fin.val)
        have hv4 : uv₂.2.1 = uv₁.1.1 ∨ uv₂.2.1 = uv₁.2.1 := hm4.imp (congr_arg Fin.val) (congr_arg Fin.val)
        ext <;> omega
      · intro e he
        rw [Finset.mem_coe, Finset.mem_powersetCard] at he
        obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp he.2
        have ha : a ∈ S := he.1 (by simp)
        have hb : b ∈ S := he.1 (by simp)
        rcases lt_trichotomy a b with hlt | rfl | hgt
        · refine ⟨(a, b), ?_, rfl⟩
          simp only [P_sub, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨hlt, ha, hb⟩
        · exact absurd rfl hab
        · refine ⟨(b, a), ?_, Finset.pair_comm b a⟩
          simp only [P_sub, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨hgt, hb, ha⟩
    let P_all : Finset (Fin N × Fin N) := Finset.univ.filter (fun uv : Fin N × Fin N => uv.1 < uv.2)
    let P_hit : Finset (Fin N × Fin N) := P_all.filter (fun uv => uv.1 ∈ T ∨ uv.2 ∈ T)
    have hP_all_card : P_all.card = N.choose 2 := by
      have heq : P_all = P_sub Finset.univ := by
        ext uv
        simp [P_all, P_sub]
      rw [heq, hP_sub_card, Finset.card_univ, Fintype.card_fin]
    have hP_miss_card : (P_all.filter (fun uv => ¬(uv.1 ∈ T ∨ uv.2 ∈ T))).card = (N - T.card).choose 2 := by
      have heq : P_all.filter (fun uv => ¬(uv.1 ∈ T ∨ uv.2 ∈ T)) = P_sub (Finset.univ \ T) := by
        ext uv
        simp only [P_all, P_sub, Finset.mem_filter, Finset.mem_univ, Finset.mem_sdiff, true_and, not_or]
      rw [heq, hP_sub_card, Finset.card_univ_diff, Fintype.card_fin]
    have hP_hit_card : P_hit.card = N.choose 2 - (N - T.card).choose 2 := by
      have hpart := Finset.card_filter_add_card_filter_not (s := P_all) (p := fun uv => uv.1 ∈ T ∨ uv.2 ∈ T)
      change P_hit.card + (P_all.filter (fun uv => ¬(uv.1 ∈ T ∨ uv.2 ∈ T))).card = P_all.card at hpart
      rw [hP_miss_card, hP_all_card] at hpart
      omega
    have hT_le : T.card ≤ N := by
      simpa [Fintype.card_fin] using (Finset.card_le_univ T)
    have hbinom_eq : T.card * (N - 1) - T.card.choose 2 = N.choose 2 - (N - T.card).choose 2 := by
      rcases Nat.eq_zero_or_pos N with rfl | hN_pos
      · have h0 : T.card = 0 := by omega
        simp [h0]
      · have hc1 : (N - T.card).choose 2 ≤ N.choose 2 := Nat.choose_le_choose 2 (Nat.sub_le N T.card)
        have hc2 : T.card.choose 2 ≤ T.card * (N - 1) := by
          have h2c : 2 * T.card.choose 2 = T.card * (T.card - 1) := by
            rw [Nat.choose_two_right]
            exact Nat.mul_div_cancel' (Even.two_dvd (Nat.even_mul_pred_self T.card))
          have hsub : T.card - 1 ≤ N - 1 := Nat.sub_le_sub_right hT_le 1
          have hmul : T.card * (T.card - 1) ≤ T.card * (N - 1) := Nat.mul_le_mul_left T.card hsub
          omega
        have hz : 2 * (((T.card * (N - 1) - T.card.choose 2 : ℕ) : ℤ)) =
            2 * (((N.choose 2 - (N - T.card).choose 2 : ℕ) : ℤ)) := by
          rw [Nat.cast_sub hc2, Nat.cast_sub hc1, mul_sub, mul_sub,
            hchoose2_int T.card, hchoose2_int N, hchoose2_int (N - T.card)]
          push_cast
          rw [Nat.cast_sub (show 1 ≤ N by omega), Nat.cast_sub hT_le]
          push_cast
          ring
        omega
    rw [hbinom_eq, ← hP_hit_card]
    apply Finset.card_le_card_of_injOn (fun uv : Fin N × Fin N => (uv.1, uv.2, z uv.1, z uv.2))
    · rintro ⟨u₀, v₀⟩ huv
      simp only [P_hit, P_all, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at huv
      rw [Finset.mem_coe, Finset.mem_sdiff]
      refine ⟨?_, ?_⟩
      · simp only [homQueries, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨(u₀, v₀), huv.1, rfl⟩
      · intro hmem
        rw [Finset.mem_biUnion] at hmem
        rcases hmem with ⟨y, hy, hqy⟩
        simp only [homQueries, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hqy
        rcases hqy with ⟨⟨u', v'⟩, _, heq⟩
        rcases Prod.mk.inj heq with ⟨rfl, heq2⟩
        rcases Prod.mk.inj heq2 with ⟨rfl, heq3⟩
        rcases Prod.mk.inj heq3 with ⟨hy1, hy2⟩
        rcases huv.2 with huT | hvT
        · exact hT u' huT y hy hy1.symm
        · exact hT v' hvT y hy hy2.symm
    · intro uv₁ _ uv₂ _ heq
      dsimp only at heq
      rcases Prod.mk.inj heq with ⟨h1, heq2⟩
      rcases Prod.mk.inj heq2 with ⟨h2, _⟩
      exact Prod.ext h1 h2
  have h_s2a : ∀ {N q : ℕ} (x : Fin N → Fin q) (U : Finset (Fin N)) (s : ℕ),
      (Finset.univ.filter (fun g : Fin N → Fin q => (∀ v ∉ U, g v = x v) ∧ dHam x g = s)).card =
        U.card.choose s * (q - 1) ^ s := by
    clear h_s1 hC₁ hr hσ_pos hp_edge_pos hp_edge_lt1 h_cal hσ_up h_binom_edge hp_keep_pos hp_keep_up C₁ r_star
    intro N q x U s
    let Sph := Finset.univ.filter (fun g : Fin N → Fin q => (∀ v ∉ U, g v = x v) ∧ dHam x g = s)
    have hmaps : Set.MapsTo (diffCoords x) (Sph : Set (Fin N → Fin q))
        (U.powersetCard s : Set (Finset (Fin N))) := by
      intro g hg
      simp only [Sph, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hg
      rw [Finset.mem_coe, Finset.mem_powersetCard]
      refine ⟨?_, hg.2⟩
      intro v hv
      simp only [diffCoords, Finset.mem_filter, Finset.mem_univ, true_and] at hv
      by_contra hvU
      exact hv (hg.1 v hvU).symm
    rw [Finset.card_eq_sum_card_fiberwise hmaps]
    have hfib : ∀ D ∈ U.powersetCard s,
        (Sph.filter (fun g => diffCoords x g = D)).card = (q - 1) ^ s := by
      intro D hD
      rw [Finset.mem_powersetCard] at hD
      have heq : Sph.filter (fun g => diffCoords x g = D) =
          Fintype.piFinset (fun v : Fin N => if v ∈ D then Finset.univ.erase (x v) else {x v}) := by
        ext g
        simp only [Sph, Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset]
        constructor
        · rintro ⟨_, rfl⟩ v
          by_cases hv : v ∈ diffCoords x g
          · rw [if_pos hv, Finset.mem_erase]
            simp only [diffCoords, Finset.mem_filter, Finset.mem_univ, true_and] at hv
            exact ⟨hv.symm, Finset.mem_univ _⟩
          · rw [if_neg hv, Finset.mem_singleton]
            simp only [diffCoords, Finset.mem_filter, Finset.mem_univ, true_and, not_not] at hv
            exact hv.symm
        · intro hg
          have hdiff : diffCoords x g = D := by
            ext v
            simp only [diffCoords, Finset.mem_filter, Finset.mem_univ, true_and]
            have hgv := hg v
            by_cases hv : v ∈ D
            · rw [if_pos hv, Finset.mem_erase] at hgv
              exact iff_of_true hgv.1.symm hv
            · rw [if_neg hv, Finset.mem_singleton] at hgv
              exact iff_of_false (not_not.mpr hgv.symm) hv
          refine ⟨⟨?_, ?_⟩, hdiff⟩
          · intro v hvU
            have hvD : v ∉ D := fun h => hvU (hD.1 h)
            have hgv := hg v
            rw [if_neg hvD, Finset.mem_singleton] at hgv
            exact hgv
          · rw [dHam, hdiff, hD.2]
      rw [heq, Fintype.card_piFinset]
      have hcard_v : ∀ v : Fin N,
          (if v ∈ D then Finset.univ.erase (x v) else {x v}).card = if v ∈ D then q - 1 else 1 := by
        intro v
        split_ifs
        · rw [Finset.card_erase_of_mem (Finset.mem_univ (x v)), Finset.card_univ, Fintype.card_fin]
        · exact Finset.card_singleton (x v)
      simp_rw [hcard_v]
      rw [Finset.prod_ite_mem, Finset.univ_inter, Finset.prod_const, hD.2]
    rw [Finset.sum_congr rfl hfib, Finset.sum_const, Finset.card_powersetCard, smul_eq_mul]
  have h_s2b : ∀ {N q : ℕ} (x u : Fin N → Fin q) (d₃ w : ℕ),
      (Finset.univ.filter (fun z : Fin N → Fin q =>
        (d3Coords x u z).card = d₃ ∧ (diffCoords x z \ diffCoords x u).card = w)).card ≤
        2 ^ (2 * dHam x u) * (q - 1) ^ d₃ * (N.choose w * (q - 1) ^ w) := by
    clear h_s1 hC₁ hr hσ_pos hp_edge_pos hp_edge_lt1 h_cal hσ_up h_binom_edge hp_keep_pos hp_keep_up C₁ r_star
    intro N q x u d₃ w
    let Sph := fun (U : Finset (Fin N)) (s : ℕ) =>
      Finset.univ.filter (fun g : Fin N → Fin q => (∀ v ∉ U, g v = x v) ∧ dHam x g = s)
    let B_copy := fun z : Fin N → Fin q => (diffCoords x u).filter (fun v => z v = u v)
    let z_d3 := fun (z : Fin N → Fin q) (v : Fin N) => if v ∈ d3Coords x u z then z v else x v
    let z_out := fun (z : Fin N → Fin q) (v : Fin N) =>
      if v ∈ diffCoords x z \ diffCoords x u then z v else x v
    let Φ := fun z : Fin N → Fin q => (B_copy z, (z_d3 z, z_out z))
    have hle : (Finset.univ.filter (fun z : Fin N → Fin q =>
        (d3Coords x u z).card = d₃ ∧ (diffCoords x z \ diffCoords x u).card = w)).card ≤
        ((diffCoords x u).powerset ×ˢ (Sph (diffCoords x u) d₃ ×ˢ Sph Finset.univ w)).card := by
      apply Finset.card_le_card_of_injOn Φ
      · intro z hz
        simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hz
        rw [Finset.mem_coe, Finset.mem_product, Finset.mem_product]
        refine ⟨Finset.mem_powerset.mpr (Finset.filter_subset _ _), ?_, ?_⟩
        · simp only [Sph, Finset.mem_filter, Finset.mem_univ, true_and]
          have hdiff : diffCoords x (z_d3 z) = d3Coords x u z := by
            ext v
            simp only [diffCoords, z_d3, d3Coords, Finset.mem_filter, Finset.mem_univ, true_and]
            split_ifs with hv
            · exact iff_of_true hv.2.1 hv
            · exact iff_of_false (not_not.mpr rfl) hv
          refine ⟨?_, ?_⟩
          · intro v hv
            have hvd3 : v ∉ d3Coords x u z := by
              intro hmem
              simp only [d3Coords, diffCoords, Finset.mem_filter, Finset.mem_univ, true_and] at hmem hv
              exact hv hmem.1
            exact if_neg hvd3
          · rw [dHam, hdiff, hz.1]
        · dsimp only [Sph]
          rw [Finset.mem_filter]
          have hdiff : diffCoords x (z_out z) = diffCoords x z \ diffCoords x u := by
            ext v
            simp only [diffCoords, z_out, Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ, true_and]
            split_ifs with hv
            · exact iff_of_true hv.1 hv
            · exact iff_of_false (not_not.mpr rfl) hv
          refine ⟨Finset.mem_univ _, fun v hv => absurd (Finset.mem_univ v) hv, ?_⟩
          rw [dHam, hdiff, hz.2]
      · intro z₁ _ z₂ _ heq
        rcases Prod.mk.inj heq with ⟨hB, hp⟩
        rcases Prod.mk.inj hp with ⟨hd3, hout⟩
        funext v
        by_cases hvu : v ∈ diffCoords x u
        · by_cases hzu : z₁ v = u v
          · have hvB1 : v ∈ B_copy z₁ := Finset.mem_filter.mpr ⟨hvu, hzu⟩
            rw [hB] at hvB1
            have hzu2 : z₂ v = u v := (Finset.mem_filter.mp hvB1).2
            rw [hzu, hzu2]
          · have hvB1 : v ∉ B_copy z₁ := fun hm => hzu (Finset.mem_filter.mp hm).2
            rw [hB] at hvB1
            have hzu2 : z₂ v ≠ u v := fun hm => hvB1 (Finset.mem_filter.mpr ⟨hvu, hm⟩)
            have hval : ∀ z : Fin N → Fin q, z v ≠ u v → z_d3 z v = z v := by
              intro z hzne
              dsimp only [z_d3]
              by_cases hzx : x v = z v
              · have hnot : v ∉ d3Coords x u z := by
                  simp [d3Coords, hzx]
                rw [if_neg hnot, hzx]
              · have hmem : v ∈ d3Coords x u z := by
                  simp only [diffCoords, Finset.mem_filter, Finset.mem_univ, true_and] at hvu
                  simp only [d3Coords, Finset.mem_filter, Finset.mem_univ, true_and]
                  exact ⟨hvu, hzx, Ne.symm hzne⟩
                exact if_pos hmem
            rw [← hval z₁ hzu, ← hval z₂ hzu2, congr_fun hd3 v]
        · have hval : ∀ z : Fin N → Fin q, z_out z v = z v := by
            intro z
            dsimp only [z_out]
            by_cases hzx : x v = z v
            · have hnot : v ∉ diffCoords x z \ diffCoords x u := by
                simp [diffCoords, hzx]
              rw [if_neg hnot, hzx]
            · have hmem : v ∈ diffCoords x z \ diffCoords x u := by
                rw [Finset.mem_sdiff]
                refine ⟨?_, hvu⟩
                simp [diffCoords, hzx]
              exact if_pos hmem
          rw [← hval z₁, ← hval z₂, congr_fun hout v]
    rw [Finset.card_product, Finset.card_product, Finset.card_powerset] at hle
    have hs1 : (Sph (diffCoords x u) d₃).card = (dHam x u).choose d₃ * (q - 1) ^ d₃ :=
      h_s2a x (diffCoords x u) d₃
    have hs2 : (Sph Finset.univ w).card = N.choose w * (q - 1) ^ w := by
      have h := h_s2a x Finset.univ w
      rwa [Finset.card_univ, Fintype.card_fin] at h
    rw [hs1, hs2] at hle
    have hch_le : (dHam x u).choose d₃ ≤ 2 ^ dHam x u := by
      rw [← Finset.card_powersetCard d₃ (diffCoords x u), ← Finset.card_powerset (diffCoords x u)]
      apply Finset.card_le_card
      intro A hA
      exact Finset.mem_powerset.mpr (Finset.mem_powersetCard.mp hA).1
    calc
      _ ≤ 2 ^ dHam x u * ((dHam x u).choose d₃ * (q - 1) ^ d₃ * (N.choose w * (q - 1) ^ w)) := hle
      _ ≤ 2 ^ dHam x u * (2 ^ dHam x u * (q - 1) ^ d₃ * (N.choose w * (q - 1) ^ w)) := by
        gcongr
      _ = 2 ^ (2 * dHam x u) * (q - 1) ^ d₃ * (N.choose w * (q - 1) ^ w) := by
        rw [two_mul, pow_add]
        ring
  have h_s2c : ∀ {N q : ℕ} (C₁ r_star : ℕ), 3 ≤ C₁ →
      ∀ (x : Fin N → Fin q) (R_old : Finset (Fin N × Fin q)),
      R_old.card ≤ 21 * C₁ ^ 2 * r_star →
      ∀ (s : ℕ),
      ((Finset.univ.filter (fun y : Fin N → Fin q =>
        ((diffCoords x y).filter (fun v => (v, y v) ∉ R_old)).card = s ∧
        dHam x y ≤ r_star)).card : ℝ) ≤
        ((r_star + 1 : ℕ) : ℝ) *
          (2 : ℝ) ^ ((1 / 100 : ℝ) * (cspLam0 C₁ : ℝ) * (r_star : ℝ)) *
          ((N.choose s : ℝ) * ((q - 1 : ℕ) : ℝ) ^ s) := by
    clear h_s1 h_s2b hC₁ hr hσ_pos hp_edge_pos hp_edge_lt1 h_cal hσ_up h_binom_edge hp_keep_pos hp_keep_up C₁ r_star
    intro N q C₁ r_star hC₁_loc x R_old hR_old s
    let Sph := Finset.univ.filter (fun g : Fin N → Fin q =>
      (∀ v ∉ (Finset.univ : Finset (Fin N)), g v = x v) ∧ dHam x g = s)
    let F_fresh := fun y : Fin N → Fin q => (diffCoords x y).filter (fun v => (v, y v) ∉ R_old)
    let A_rev := fun y : Fin N → Fin q =>
      ((diffCoords x y).filter (fun v => (v, y v) ∈ R_old)).image (fun v => (v, y v))
    let y_fresh := fun (y : Fin N → Fin q) (v : Fin N) => if v ∈ F_fresh y then y v else x v
    let Ψ := fun y : Fin N → Fin q => (A_rev y, y_fresh y)
    let P_old := R_old.powerset.filter (fun G => G.card ≤ r_star)
    have hle : (Finset.univ.filter (fun y : Fin N → Fin q =>
        (F_fresh y).card = s ∧ dHam x y ≤ r_star)).card ≤
        (P_old ×ˢ Sph).card := by
      apply Finset.card_le_card_of_injOn Ψ
      · intro y hy
        simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hy
        rw [Finset.mem_coe, Finset.mem_product]
        refine ⟨?_, ?_⟩
        · simp only [P_old, Finset.mem_filter, Finset.mem_powerset]
          refine ⟨?_, ?_⟩
          · intro vc hvc
            rcases Finset.mem_image.mp hvc with ⟨v, hv, rfl⟩
            exact (Finset.mem_filter.mp hv).2
          · exact le_trans Finset.card_image_le
              (le_trans (Finset.card_filter_le _ _) hy.2)
        · dsimp only [Sph]
          rw [Finset.mem_filter]
          have hdiff : diffCoords x (y_fresh y) = F_fresh y := by
            ext v
            simp only [diffCoords, y_fresh, F_fresh, Finset.mem_filter, Finset.mem_univ, true_and]
            split_ifs with hv
            · exact iff_of_true hv.1 hv
            · exact iff_of_false (not_not.mpr rfl) hv
          exact ⟨Finset.mem_univ _, fun v hv => absurd (Finset.mem_univ v) hv, by rw [dHam, hdiff, hy.1]⟩
      · intro y₁ _ y₂ _ heq
        rcases Prod.mk.inj heq with ⟨hA, hyf⟩
        have hnotA_eq : ∀ y : Fin N → Fin q, ∀ v : Fin N, (v, y v) ∉ A_rev y → y_fresh y v = y v := by
          intro y v hnotA
          dsimp only [y_fresh]
          by_cases hxy : x v = y v
          · have hnotF : v ∉ F_fresh y := by simp [F_fresh, diffCoords, hxy]
            rw [if_neg hnotF, hxy]
          · have hnotR : (v, y v) ∉ R_old := by
              intro hR
              apply hnotA
              exact Finset.mem_image.mpr ⟨v, Finset.mem_filter.mpr ⟨by simp [diffCoords, hxy], hR⟩, rfl⟩
            have hmemF : v ∈ F_fresh y := Finset.mem_filter.mpr ⟨by simp [diffCoords, hxy], hnotR⟩
            exact if_pos hmemF
        funext v
        by_cases h1 : (v, y₁ v) ∈ A_rev y₁
        · rw [hA] at h1
          rcases Finset.mem_image.mp h1 with ⟨v', _, hp⟩
          rcases Prod.mk.inj hp with ⟨rfl, hy21⟩
          exact hy21.symm
        · by_cases h2 : (v, y₂ v) ∈ A_rev y₂
          · rw [← hA] at h2
            rcases Finset.mem_image.mp h2 with ⟨v', _, hp⟩
            rcases Prod.mk.inj hp with ⟨rfl, hy12⟩
            exact hy12
          · rw [← hnotA_eq y₁ v h1, ← hnotA_eq y₂ v h2, congr_fun hyf v]
    rw [Finset.card_product] at hle
    have hSph : Sph.card = N.choose s * (q - 1) ^ s := by
      have h := h_s2a x Finset.univ s
      rwa [Finset.card_univ, Fintype.card_fin] at h
    rw [hSph] at hle
    have hle_r : ((Finset.univ.filter (fun y : Fin N → Fin q =>
        (F_fresh y).card = s ∧ dHam x y ≤ r_star)).card : ℝ) ≤
        (P_old.card : ℝ) * ((N.choose s : ℝ) * ((q - 1 : ℕ) : ℝ) ^ s) := by
      exact_mod_cast hle
    have hP_r : (P_old.card : ℝ) ≤
        ((r_star + 1 : ℕ) : ℝ) *
          (2 : ℝ) ^ (((2 * Nat.clog 2 C₁ + 6) * r_star : ℕ) : ℝ) :=
      powerset_card_le_bound R_old C₁ 21 r_star hC₁_loc (le_refl 21) hR_old
    have hexp_le : (2 : ℝ) ^ (((2 * Nat.clog 2 C₁ + 6) * r_star : ℕ) : ℝ) ≤
        (2 : ℝ) ^ ((1 / 100 : ℝ) * (cspLam0 C₁ : ℝ) * (r_star : ℝ)) := by
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      have h1 : 100 * ((2 * Nat.clog 2 C₁ + 6) * r_star) ≤ cspLam0 C₁ * r_star := by
        unfold cspLam0
        have hC1_ge1 : 1 ≤ C₁ := by omega
        have hm : 1 * (2 * Nat.clog 2 C₁ + 6) ≤ C₁ * (2 * Nat.clog 2 C₁ + 6) :=
          Nat.mul_le_mul_right _ hC1_ge1
        have h100 : 100 * (2 * Nat.clog 2 C₁ + 6) ≤ 100 * C₁ * (2 * Nat.clog 2 C₁ + 6) := by
          linarith only [hm]
        have hmr := Nat.mul_le_mul_right r_star h100
        rwa [Nat.mul_assoc 100 _ r_star] at hmr
      have h1r : ((100 * ((2 * Nat.clog 2 C₁ + 6) * r_star) : ℕ) : ℝ) ≤
          ((cspLam0 C₁ * r_star : ℕ) : ℝ) := by exact_mod_cast h1
      push_cast at h1r ⊢
      linarith only [h1r]
    have hP_r2 : (P_old.card : ℝ) ≤
        ((r_star + 1 : ℕ) : ℝ) *
          (2 : ℝ) ^ ((1 / 100 : ℝ) * (cspLam0 C₁ : ℝ) * (r_star : ℝ)) :=
      le_trans hP_r (mul_le_mul_of_nonneg_left hexp_le (Nat.cast_nonneg _))
    exact le_trans hle_r (mul_le_mul_of_nonneg_right hP_r2 (by positivity))
  clear h_s2a
  have h_s3 :
      (∀ d₃ w : ℕ, d₃ + w ≤ C₁ * r_star →
        r_star < cspInvEta0 C₁ * d₃ →
        (((C₁ * r_star + 1) ^ 2 : ℕ) : ℝ) *
          (((2 ^ (2 * (C₁ * r_star)) : ℕ) : ℝ) * ((cspQ C₁ - 1 : ℕ) : ℝ) ^ d₃ *
            (((2 ^ cspL C₁ * r_star).choose w : ℝ) * ((cspQ C₁ - 1 : ℕ) : ℝ) ^ w) *
            ((cspPEdge C₁ r_star) ^ ((d₃ + w) * (2 ^ cspL C₁ * r_star - 1) - (d₃ + w).choose 2))) ≤
          (2 : ℝ) ^ (- (12 * (C₁ ^ 2 : ℕ) : ℝ) * (cspLam0 C₁ : ℝ) * (r_star : ℝ))) ∧
      (∀ s : ℕ, 80 * s ≤ 61 * r_star →
        ((r_star + 1 : ℕ) : ℝ) *
          ((((r_star + 1 : ℕ) : ℝ) *
            (2 : ℝ) ^ ((1 / 100 : ℝ) * (cspLam0 C₁ : ℝ) * (r_star : ℝ)) *
            (((2 ^ cspL C₁ * r_star).choose s : ℝ) * ((cspQ C₁ - 1 : ℕ) : ℝ) ^ s)) *
            (cspPKeep C₁ r_star *
              (cspPEdge C₁ r_star) ^ (s * (2 ^ cspL C₁ * r_star - 1) - s.choose 2))) ≤
          (2 : ℝ) ^ (- (72 / 100 : ℝ) * (cspLam0 C₁ : ℝ) * (r_star : ℝ))) := by
    clear h_s1 h_s2b h_s2c
    have hlam_1000C1 : 1000 * C₁ ≤ cspLam0 C₁ := (lam0_ge_1000_C1 C₁ hC₁).2.1
    have hlam_ge : 3000 ≤ cspLam0 C₁ := by omega
    have hbeta_eq : (cspBeta0 C₁ : ℝ) = 6 * (cspLam0 C₁ : ℝ) := by
      unfold cspBeta0; push_cast; ring
    have hgamma_eq : (cspGamma0 C₁ : ℝ) = 5 * (cspLam0 C₁ : ℝ) := by
      unfold cspGamma0; push_cast; ring
    have hC₁_le_L : C₁ ≤ cspL C₁ := by
      have hc2 : 1 ≤ C₁ ^ 2 := Nat.one_le_pow 2 C₁ (by omega)
      unfold cspL cspInvEta0
      nlinarith only [hc2, hlam_1000C1]
    have hC₁_le_2L : C₁ ≤ 2 ^ cspL C₁ :=
      le_trans hC₁_le_L (Nat.le_of_lt Nat.lt_two_pow_self)
    have hCr_le_N : C₁ * r_star ≤ 2 ^ cspL C₁ * r_star :=
      Nat.mul_le_mul_right r_star hC₁_le_2L
    have hr_le_Cr : r_star ≤ C₁ * r_star := by
      simpa using Nat.mul_le_mul_right r_star (show 1 ≤ C₁ by omega)
    have hr_le_N : r_star ≤ 2 ^ cspL C₁ * r_star := le_trans hr_le_Cr hCr_le_N
    have h_edge_split : ∀ t : ℕ, t ≤ 2 ^ cspL C₁ * r_star →
        (cspPEdge C₁ r_star) ^ (t * (2 ^ cspL C₁ * r_star - 1) - t.choose 2) =
          (cspPEdge C₁ r_star) ^ (t * (2 ^ cspL C₁ * r_star - 1)) *
            (2 : ℝ) ^ (cspSigmaEdge C₁ r_star * (t.choose 2 : ℝ)) := by
      intro t ht
      have h2c : 2 * t.choose 2 = t * (t - 1) := by
        rw [Nat.choose_two_right]
        exact Nat.mul_div_cancel' (Even.two_dvd (Nat.even_mul_pred_self t))
      have hc_le : t.choose 2 ≤ t * (2 ^ cspL C₁ * r_star - 1) := by
        have hsub : t - 1 ≤ 2 ^ cspL C₁ * r_star - 1 := Nat.sub_le_sub_right ht 1
        have hm : t * (t - 1) ≤ t * (2 ^ cspL C₁ * r_star - 1) := Nat.mul_le_mul_left t hsub
        omega
      have hcancel : (cspPEdge C₁ r_star) ^ (t.choose 2) *
          (2 : ℝ) ^ (cspSigmaEdge C₁ r_star * (t.choose 2 : ℝ)) = 1 := by
        dsimp only [cspPEdge]
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),
          ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
        have hexp0 : - cspSigmaEdge C₁ r_star * (t.choose 2 : ℝ) +
            cspSigmaEdge C₁ r_star * (t.choose 2 : ℝ) = 0 := by ring
        rw [hexp0, Real.rpow_zero]
      calc
        (cspPEdge C₁ r_star) ^ (t * (2 ^ cspL C₁ * r_star - 1) - t.choose 2)
          = (cspPEdge C₁ r_star) ^ (t * (2 ^ cspL C₁ * r_star - 1) - t.choose 2) *
              ((cspPEdge C₁ r_star) ^ (t.choose 2) *
                (2 : ℝ) ^ (cspSigmaEdge C₁ r_star * (t.choose 2 : ℝ))) := by
            rw [hcancel, mul_one]
        _ = ((cspPEdge C₁ r_star) ^ (t * (2 ^ cspL C₁ * r_star - 1) - t.choose 2) *
              (cspPEdge C₁ r_star) ^ (t.choose 2)) *
              (2 : ℝ) ^ (cspSigmaEdge C₁ r_star * (t.choose 2 : ℝ)) := by ring
        _ = (cspPEdge C₁ r_star) ^ (t * (2 ^ cspL C₁ * r_star - 1)) *
              (2 : ℝ) ^ (cspSigmaEdge C₁ r_star * (t.choose 2 : ℝ)) := by
            rw [← pow_add, Nat.sub_add_cancel hc_le]
    constructor
    · intro d₃ w hdw hr_d3
      have ht_le_N : d₃ + w ≤ 2 ^ cspL C₁ * r_star := le_trans hdw hCr_le_N
      have hL_d3 : 20 * C₁ ^ 2 * cspLam0 C₁ * r_star ≤ cspL C₁ * d₃ := by
        have h1 : r_star ≤ cspInvEta0 C₁ * d₃ := le_of_lt hr_d3
        have h2 := Nat.mul_le_mul_left (20 * C₁ ^ 2 * cspLam0 C₁) h1
        have h3 : (20 * C₁ ^ 2 * cspLam0 C₁) * (cspInvEta0 C₁ * d₃) =
            (20 * C₁ ^ 2 * cspInvEta0 C₁ * cspLam0 C₁) * d₃ := by ring
        have h4 : 20 * C₁ ^ 2 * cspInvEta0 C₁ * cspLam0 C₁ ≤ cspL C₁ := by
          dsimp only [cspL]; omega
        have h5 := Nat.mul_le_mul_right d₃ h4
        have h6 : (20 * C₁ ^ 2 * cspLam0 C₁) * r_star = 20 * C₁ ^ 2 * cspLam0 C₁ * r_star := by ring
        rw [h6, h3] at h2
        exact le_trans h2 h5
      have hsplit := h_edge_split (d₃ + w) ht_le_N
      have hpow_dw : (cspPEdge C₁ r_star) ^ ((d₃ + w) * (2 ^ cspL C₁ * r_star - 1)) =
          (cspPEdge C₁ r_star) ^ (d₃ * (2 ^ cspL C₁ * r_star - 1)) *
            (cspPEdge C₁ r_star) ^ (w * (2 ^ cspL C₁ * r_star - 1)) := by
        rw [add_mul, pow_add]
      rw [hsplit, hpow_dw]
      let u_cal : ℝ := ((cspQ C₁ - 1 : ℕ) : ℝ) * (cspPEdge C₁ r_star) ^ (2 ^ cspL C₁ * r_star - 1)
      have hu_nn : 0 ≤ u_cal := mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (le_of_lt hp_edge_pos) _)
      have hF1 : (((C₁ * r_star + 1) ^ 2 : ℕ) : ℝ) ≤ (2 : ℝ) ^ (4 * (r_star : ℝ)) := by
        have hCr1 : C₁ * r_star + 1 ≤ r_star * r_star := by
          have hC1_lt : C₁ + 1 ≤ r_star := by omega
          calc
            C₁ * r_star + 1 ≤ C₁ * r_star + r_star := by omega
            _ = (C₁ + 1) * r_star := by ring
            _ ≤ r_star * r_star := Nat.mul_le_mul_right r_star hC1_lt
        have hr_pow : r_star ≤ 2 ^ r_star := Nat.le_of_lt Nat.lt_two_pow_self
        have hrr_pow : r_star * r_star ≤ 2 ^ (2 * r_star) := by
          calc
            r_star * r_star ≤ 2 ^ r_star * 2 ^ r_star := Nat.mul_le_mul hr_pow hr_pow
            _ = 2 ^ (r_star + r_star) := (pow_add 2 r_star r_star).symm
            _ = 2 ^ (2 * r_star) := by rw [two_mul]
        have hsq_nat : (C₁ * r_star + 1) ^ 2 ≤ 2 ^ (4 * r_star) := by
          have h1 : (C₁ * r_star + 1) ^ 2 ≤ (2 ^ (2 * r_star)) ^ 2 :=
            Nat.pow_le_pow_left (le_trans hCr1 hrr_pow) 2
          have h2 : (2 ^ (2 * r_star)) ^ 2 = 2 ^ (4 * r_star) := by
            rw [← pow_mul]
            congr 1
            omega
          rwa [h2] at h1
        have hcast : (((C₁ * r_star + 1) ^ 2 : ℕ) : ℝ) ≤ ((2 ^ (4 * r_star) : ℕ) : ℝ) := by
          exact_mod_cast hsq_nat
        have hrpow : ((2 ^ (4 * r_star) : ℕ) : ℝ) = (2 : ℝ) ^ (4 * (r_star : ℝ)) := by
          rw [Nat.cast_pow, Nat.cast_ofNat, ← Real.rpow_natCast]
          push_cast
          rfl
        linarith only [hcast, hrpow]
      have hF2 : ((2 ^ (2 * (C₁ * r_star)) : ℕ) : ℝ) = (2 : ℝ) ^ (2 * (C₁ : ℝ) * (r_star : ℝ)) := by
        rw [Nat.cast_pow, Nat.cast_ofNat, ← Real.rpow_natCast]
        congr 1
        push_cast
        ring
      have hF3 : u_cal ^ d₃ ≤ (2 : ℝ) ^ (- (cspL C₁ : ℝ) * (d₃ : ℝ)) := by
        have h2L_u : (2 : ℝ) ^ (cspL C₁ : ℝ) * u_cal ≤ 1 := by
          rw [Real.rpow_natCast]
          have hcal' : 4 * ((2 : ℝ) ^ cspL C₁ * u_cal) = (2 : ℝ) ^ (- (cspGamma0 C₁ : ℝ)) := by
            have heq : 4 * ((2 : ℝ) ^ cspL C₁ * u_cal) =
                (4 : ℝ) * (2 : ℝ) ^ cspL C₁ * ((cspQ C₁ - 1 : ℕ) : ℝ) *
                  (cspPEdge C₁ r_star) ^ (2 ^ cspL C₁ * r_star - 1) := by
              dsimp only [u_cal]
              ring
            rw [heq, h_cal]
          have hgam_le1 : (2 : ℝ) ^ (- (cspGamma0 C₁ : ℝ)) ≤ 1 := by
            rw [show (1 : ℝ) = (2 : ℝ) ^ (0 : ℝ) by norm_num]
            apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
            have hg_nn : 0 ≤ (cspGamma0 C₁ : ℝ) := Nat.cast_nonneg _
            linarith only [hg_nn]
          have hnn : 0 ≤ (2 : ℝ) ^ cspL C₁ * u_cal :=
            mul_nonneg (pow_nonneg (by norm_num) _) hu_nn
          linarith only [hcal', hgam_le1, hnn]
        have hu_le : u_cal ≤ (2 : ℝ) ^ (- (cspL C₁ : ℝ)) := by
          have hprod1 : (2 : ℝ) ^ (- (cspL C₁ : ℝ)) * (2 : ℝ) ^ (cspL C₁ : ℝ) = 1 := by
            rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2), neg_add_cancel, Real.rpow_zero]
          calc
            u_cal = ((2 : ℝ) ^ (- (cspL C₁ : ℝ)) * (2 : ℝ) ^ (cspL C₁ : ℝ)) * u_cal := by
              rw [hprod1, one_mul]
            _ = (2 : ℝ) ^ (- (cspL C₁ : ℝ)) * ((2 : ℝ) ^ (cspL C₁ : ℝ) * u_cal) := by ring
            _ ≤ (2 : ℝ) ^ (- (cspL C₁ : ℝ)) * 1 :=
              mul_le_mul_of_nonneg_left h2L_u (Real.rpow_nonneg (by norm_num) _)
            _ = (2 : ℝ) ^ (- (cspL C₁ : ℝ)) := mul_one _
        calc
          u_cal ^ d₃ ≤ ((2 : ℝ) ^ (- (cspL C₁ : ℝ))) ^ d₃ := pow_le_pow_left₀ hu_nn hu_le d₃
          _ = (2 : ℝ) ^ (- (cspL C₁ : ℝ) * (d₃ : ℝ)) := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
      have hF4 : ((2 ^ cspL C₁ * r_star).choose w : ℝ) * ((cspQ C₁ - 1 : ℕ) : ℝ) ^ w *
          (cspPEdge C₁ r_star) ^ (w * (2 ^ cspL C₁ * r_star - 1)) ≤
          (2 : ℝ) ^ (2 * (r_star : ℝ)) := by
        refine le_trans (h_binom_edge w) (Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_)
        have hgw_nn : 0 ≤ (cspGamma0 C₁ : ℝ) * (w : ℝ) :=
          mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
        linarith only [hgw_nn]
      have hF6 : (2 : ℝ) ^ (cspSigmaEdge C₁ r_star * ((d₃ + w).choose 2 : ℝ)) ≤
          (2 : ℝ) ^ ((60006 / 10000 : ℝ) * ((C₁ ^ 2 : ℕ) : ℝ) * (cspLam0 C₁ : ℝ) * (r_star : ℝ)) := by
        apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
        have h2c : 2 * (d₃ + w).choose 2 ≤ (C₁ ^ 2) * (r_star * r_star) := by
          have heq : 2 * (d₃ + w).choose 2 = (d₃ + w) * (d₃ + w - 1) := by
            rw [Nat.choose_two_right]
            exact Nat.mul_div_cancel' (Even.two_dvd (Nat.even_mul_pred_self (d₃ + w)))
          have hle1 : (d₃ + w) * (d₃ + w - 1) ≤ (d₃ + w) * (d₃ + w) :=
            Nat.mul_le_mul_left _ (Nat.sub_le _ 1)
          have hle2 : (d₃ + w) * (d₃ + w) ≤ (C₁ * r_star) * (C₁ * r_star) :=
            Nat.mul_le_mul hdw hdw
          have hle3 : (C₁ * r_star) * (C₁ * r_star) = (C₁ ^ 2) * (r_star * r_star) := by ring
          rw [heq]
          exact le_trans hle1 (hle3 ▸ hle2)
        have h2c_real : 2 * ((d₃ + w).choose 2 : ℝ) ≤
            ((C₁ ^ 2 : ℕ) : ℝ) * ((r_star : ℝ) * (r_star : ℝ)) := by
          have hc : ((2 * (d₃ + w).choose 2 : ℕ) : ℝ) ≤
              (((C₁ ^ 2) * (r_star * r_star) : ℕ) : ℝ) := by exact_mod_cast h2c
          push_cast at hc ⊢
          linarith only [hc]
        have h1 : cspSigmaEdge C₁ r_star * ((d₃ + w).choose 2 : ℝ) ≤
            (cspSigmaEdge C₁ r_star * (r_star : ℝ) / 2) * (((C₁ ^ 2 : ℕ) : ℝ) * (r_star : ℝ)) := by
          have hm := mul_le_mul_of_nonneg_left h2c_real (le_of_lt hσ_pos)
          have eq1 : cspSigmaEdge C₁ r_star * (((C₁ ^ 2 : ℕ) : ℝ) * ((r_star : ℝ) * (r_star : ℝ))) =
            2 * ((cspSigmaEdge C₁ r_star * (r_star : ℝ) / 2) * (((C₁ ^ 2 : ℕ) : ℝ) * (r_star : ℝ))) := by ring
          have eq2 : cspSigmaEdge C₁ r_star * (2 * ((d₃ + w).choose 2 : ℝ)) =
            2 * (cspSigmaEdge C₁ r_star * ((d₃ + w).choose 2 : ℝ)) := by ring
          linarith only [hm, eq1, eq2]
        have h2 : (cspSigmaEdge C₁ r_star * (r_star : ℝ) / 2) * (((C₁ ^ 2 : ℕ) : ℝ) * (r_star : ℝ)) ≤
            ((10001 / 10000 : ℝ) * (6 * (cspLam0 C₁ : ℝ))) * (((C₁ ^ 2 : ℕ) : ℝ) * (r_star : ℝ)) :=
          mul_le_mul_of_nonneg_right (by linarith only [hσ_up, hbeta_eq])
            (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
        have eq3 : ((10001 / 10000 : ℝ) * (6 * (cspLam0 C₁ : ℝ))) *
            (((C₁ ^ 2 : ℕ) : ℝ) * (r_star : ℝ)) =
            (60006 / 10000 : ℝ) * ((C₁ ^ 2 : ℕ) : ℝ) * (cspLam0 C₁ : ℝ) * (r_star : ℝ) := by ring
        linarith only [h1, h2, eq3]
      have hrearr :
          (((C₁ * r_star + 1) ^ 2 : ℕ) : ℝ) *
            (((2 ^ (2 * (C₁ * r_star)) : ℕ) : ℝ) * ((cspQ C₁ - 1 : ℕ) : ℝ) ^ d₃ *
              (((2 ^ cspL C₁ * r_star).choose w : ℝ) * ((cspQ C₁ - 1 : ℕ) : ℝ) ^ w) *
              ((cspPEdge C₁ r_star) ^ (d₃ * (2 ^ cspL C₁ * r_star - 1)) *
                (cspPEdge C₁ r_star) ^ (w * (2 ^ cspL C₁ * r_star - 1)) *
                (2 : ℝ) ^ (cspSigmaEdge C₁ r_star * ((d₃ + w).choose 2 : ℝ)))) =
          (((C₁ * r_star + 1) ^ 2 : ℕ) : ℝ) *
            ((2 ^ (2 * (C₁ * r_star)) : ℕ) : ℝ) *
            (u_cal ^ d₃) *
            (((2 ^ cspL C₁ * r_star).choose w : ℝ) * ((cspQ C₁ - 1 : ℕ) : ℝ) ^ w *
              (cspPEdge C₁ r_star) ^ (w * (2 ^ cspL C₁ * r_star - 1))) *
            (2 : ℝ) ^ (cspSigmaEdge C₁ r_star * ((d₃ + w).choose 2 : ℝ)) := by
        dsimp only [u_cal]
        rw [mul_pow, ← pow_mul]
        ring
      rw [hrearr, hF2]
      have hnn_2r : ∀ e : ℝ, (0 : ℝ) ≤ (2 : ℝ) ^ e := fun _ => Real.rpow_nonneg (by norm_num) _
      have hnn_F4 : 0 ≤ ((2 ^ cspL C₁ * r_star).choose w : ℝ) * ((cspQ C₁ - 1 : ℕ) : ℝ) ^ w *
          (cspPEdge C₁ r_star) ^ (w * (2 ^ cspL C₁ * r_star - 1)) :=
        mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (Nat.cast_nonneg _) _))
          (pow_nonneg (le_of_lt hp_edge_pos) _)
      have hm12 : (((C₁ * r_star + 1) ^ 2 : ℕ) : ℝ) * (2 : ℝ) ^ (2 * (C₁ : ℝ) * (r_star : ℝ)) ≤
          (2 : ℝ) ^ (4 * (r_star : ℝ)) * (2 : ℝ) ^ (2 * (C₁ : ℝ) * (r_star : ℝ)) :=
        mul_le_mul_of_nonneg_right hF1 (hnn_2r _)
      have hm123 := mul_le_mul hm12 hF3 (pow_nonneg hu_nn _) (mul_nonneg (hnn_2r _) (hnn_2r _))
      have hm1234 := mul_le_mul hm123 hF4 hnn_F4 (mul_nonneg (mul_nonneg (hnn_2r _) (hnn_2r _)) (hnn_2r _))
      have hm12346 := mul_le_mul hm1234 hF6 (hnn_2r _)
        (mul_nonneg (mul_nonneg (mul_nonneg (hnn_2r _) (hnn_2r _)) (hnn_2r _)) (hnn_2r _))
      refine le_trans hm12346 ?_
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2),
        ← Real.rpow_add (by norm_num : (0 : ℝ) < 2),
        ← Real.rpow_add (by norm_num : (0 : ℝ) < 2),
        ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      have hLd3_real : 20 * ((C₁ ^ 2 : ℕ) : ℝ) * (cspLam0 C₁ : ℝ) * (r_star : ℝ) ≤
          (cspL C₁ : ℝ) * (d₃ : ℝ) := by
        have hc : ((20 * C₁ ^ 2 * cspLam0 C₁ * r_star : ℕ) : ℝ) ≤ ((cspL C₁ * d₃ : ℕ) : ℝ) := by
          exact_mod_cast hL_d3
        push_cast at hc ⊢
        linarith only [hc]
      have hlam_2C : 100 * (2 * C₁ + 6) ≤ cspLam0 C₁ := by omega
      have hlam_2C_real : (6 + 2 * (C₁ : ℝ)) * (r_star : ℝ) ≤
          (1 / 100 : ℝ) * ((C₁ ^ 2 : ℕ) : ℝ) * (cspLam0 C₁ : ℝ) * (r_star : ℝ) := by
        have hc : (100 * (2 * (C₁ : ℝ) + 6)) ≤ (cspLam0 C₁ : ℝ) := by
          exact_mod_cast hlam_2C
        have hC2_ge1 : (1 : ℝ) ≤ ((C₁ ^ 2 : ℕ) : ℝ) := by
          exact_mod_cast (show 1 ≤ C₁ ^ 2 by nlinarith only [hC₁])
        have hlam_nn : (0 : ℝ) ≤ (cspLam0 C₁ : ℝ) := Nat.cast_nonneg _
        have hc2 : 100 * (2 * (C₁ : ℝ) + 6) ≤ ((C₁ ^ 2 : ℕ) : ℝ) * (cspLam0 C₁ : ℝ) := by
          nlinarith only [hc, hC2_ge1, hlam_nn]
        have hr_nn : (0 : ℝ) ≤ (r_star : ℝ) := Nat.cast_nonneg _
        nlinarith only [hc2, hr_nn]
      have hnn_C2 : 0 ≤ ((C₁ ^ 2 : ℕ) : ℝ) * (cspLam0 C₁ : ℝ) * (r_star : ℝ) :=
        mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (Nat.cast_nonneg _)
      have hcast12 : (12 * (C₁ ^ 2 : ℕ) : ℝ) = 12 * ((C₁ ^ 2 : ℕ) : ℝ) := by push_cast; ring
      rw [hcast12]
      linarith only [hLd3_real, hlam_2C_real, hnn_C2]
    · intro s hs
      have hs_le_r : s ≤ r_star := by omega
      have hs_le_N : s ≤ 2 ^ cspL C₁ * r_star := le_trans hs_le_r hr_le_N
      rw [h_edge_split s hs_le_N]
      have hG1 : ((r_star + 1 : ℕ) : ℝ) ≤ (2 : ℝ) ^ (r_star : ℝ) := by
        have hnat : r_star + 1 ≤ 2 ^ r_star := Nat.lt_two_pow_self
        have hc : ((r_star + 1 : ℕ) : ℝ) ≤ ((2 ^ r_star : ℕ) : ℝ) := by exact_mod_cast hnat
        have hrp : ((2 ^ r_star : ℕ) : ℝ) = (2 : ℝ) ^ (r_star : ℝ) := by
          rw [Nat.cast_pow, Nat.cast_ofNat, ← Real.rpow_natCast]
        linarith only [hc, hrp]
      have hG_s : (((2 ^ cspL C₁ * r_star).choose s : ℝ) * ((cspQ C₁ - 1 : ℕ) : ℝ) ^ s *
          (cspPEdge C₁ r_star) ^ (s * (2 ^ cspL C₁ * r_star - 1))) *
          (2 : ℝ) ^ (cspSigmaEdge C₁ r_star * (s.choose 2 : ℝ)) ≤
          (2 : ℝ) ^ (2 * (r_star : ℝ)) := by
        have hsc : cspSigmaEdge C₁ r_star * (s.choose 2 : ℝ) ≤
            (cspGamma0 C₁ : ℝ) * (s : ℝ) := by
          have h160 : 160 * s.choose 2 ≤ 61 * r_star * s := by
            have h2c : 2 * s.choose 2 = s * (s - 1) := by
              rw [Nat.choose_two_right]
              exact Nat.mul_div_cancel' (Even.two_dvd (Nat.even_mul_pred_self s))
            have h1 : 2 * s.choose 2 ≤ s * s := by
              rw [h2c]
              exact Nat.mul_le_mul_left s (Nat.sub_le s 1)
            have h2 : 80 * (2 * s.choose 2) ≤ (80 * s) * s := by
              have hm := Nat.mul_le_mul_left 80 h1
              rwa [← Nat.mul_assoc 80 s s] at hm
            have h3 : (80 * s) * s ≤ (61 * r_star) * s := Nat.mul_le_mul_right s hs
            omega
          have h160_r : 160 * (s.choose 2 : ℝ) ≤ 61 * (r_star : ℝ) * (s : ℝ) := by
            exact_mod_cast h160
          have h1 : cspSigmaEdge C₁ r_star * (s.choose 2 : ℝ) ≤
              (61 / 80 : ℝ) * ((cspSigmaEdge C₁ r_star * (r_star : ℝ) / 2) * (s : ℝ)) := by
            have hm := mul_le_mul_of_nonneg_left h160_r (le_of_lt hσ_pos)
            linarith [hm,
              show cspSigmaEdge C₁ r_star * (61 * (r_star : ℝ) * (s : ℝ)) =
                160 * ((61 / 80 : ℝ) *
                  ((cspSigmaEdge C₁ r_star * (r_star : ℝ) / 2) * (s : ℝ))) by ring,
              show cspSigmaEdge C₁ r_star * (160 * (s.choose 2 : ℝ)) =
                160 * (cspSigmaEdge C₁ r_star * (s.choose 2 : ℝ)) by ring]
          have h2 : (cspSigmaEdge C₁ r_star * (r_star : ℝ) / 2) * (s : ℝ) ≤
              ((10001 / 10000 : ℝ) * (6 * (cspLam0 C₁ : ℝ))) * (s : ℝ) :=
            mul_le_mul_of_nonneg_right (by linarith only [hσ_up, hbeta_eq]) (Nat.cast_nonneg _)
          have hls_nn : 0 ≤ (cspLam0 C₁ : ℝ) * (s : ℝ) := by positivity
          rw [hgamma_eq]
          linarith [h1, h2, hls_nn]
        calc
          (((2 ^ cspL C₁ * r_star).choose s : ℝ) * ((cspQ C₁ - 1 : ℕ) : ℝ) ^ s *
              (cspPEdge C₁ r_star) ^ (s * (2 ^ cspL C₁ * r_star - 1))) *
              (2 : ℝ) ^ (cspSigmaEdge C₁ r_star * (s.choose 2 : ℝ))
            ≤ (2 : ℝ) ^ (2 * (r_star : ℝ) - (cspGamma0 C₁ : ℝ) * (s : ℝ)) *
                (2 : ℝ) ^ (cspSigmaEdge C₁ r_star * (s.choose 2 : ℝ)) :=
              mul_le_mul_of_nonneg_right (h_binom_edge s) (by positivity)
          _ = (2 : ℝ) ^ (2 * (r_star : ℝ) - (cspGamma0 C₁ : ℝ) * (s : ℝ) +
                cspSigmaEdge C₁ r_star * (s.choose 2 : ℝ)) := by
              rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
          _ ≤ (2 : ℝ) ^ (2 * (r_star : ℝ)) :=
              Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith only [hsc])
      have hrearr :
          ((r_star + 1 : ℕ) : ℝ) *
            ((((r_star + 1 : ℕ) : ℝ) *
              (2 : ℝ) ^ ((1 / 100 : ℝ) * (cspLam0 C₁ : ℝ) * (r_star : ℝ)) *
              (((2 ^ cspL C₁ * r_star).choose s : ℝ) * ((cspQ C₁ - 1 : ℕ) : ℝ) ^ s)) *
              (cspPKeep C₁ r_star *
                ((cspPEdge C₁ r_star) ^ (s * (2 ^ cspL C₁ * r_star - 1)) *
                  (2 : ℝ) ^ (cspSigmaEdge C₁ r_star * (s.choose 2 : ℝ))))) =
          ((r_star + 1 : ℕ) : ℝ) *
            ((r_star + 1 : ℕ) : ℝ) *
            (2 : ℝ) ^ ((1 / 100 : ℝ) * (cspLam0 C₁ : ℝ) * (r_star : ℝ)) *
            ((((2 ^ cspL C₁ * r_star).choose s : ℝ) * ((cspQ C₁ - 1 : ℕ) : ℝ) ^ s *
              (cspPEdge C₁ r_star) ^ (s * (2 ^ cspL C₁ * r_star - 1))) *
              (2 : ℝ) ^ (cspSigmaEdge C₁ r_star * (s.choose 2 : ℝ))) *
            cspPKeep C₁ r_star := by ring
      rw [hrearr]
      have hnn_2r : ∀ e : ℝ, (0 : ℝ) ≤ (2 : ℝ) ^ e := fun _ => Real.rpow_nonneg (by norm_num) _
      have hnn_Gs : 0 ≤ (((2 ^ cspL C₁ * r_star).choose s : ℝ) * ((cspQ C₁ - 1 : ℕ) : ℝ) ^ s *
          (cspPEdge C₁ r_star) ^ (s * (2 ^ cspL C₁ * r_star - 1))) *
          (2 : ℝ) ^ (cspSigmaEdge C₁ r_star * (s.choose 2 : ℝ)) :=
        mul_nonneg
          (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (Nat.cast_nonneg _) _))
            (pow_nonneg (le_of_lt hp_edge_pos) _)) (hnn_2r _)
      have hm11 := mul_le_mul hG1 hG1 (Nat.cast_nonneg _) (hnn_2r _)
      have hm112 := mul_le_mul_of_nonneg_right hm11
        (hnn_2r ((1 / 100 : ℝ) * (cspLam0 C₁ : ℝ) * (r_star : ℝ)))
      have hm1123 := mul_le_mul hm112 hG_s hnn_Gs (by positivity)
      have hm11234 := mul_le_mul hm1123 hp_keep_up (le_of_lt hp_keep_pos) (by positivity)
      refine le_trans hm11234 ?_
      repeat rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      have hlam_r : (3000 : ℝ) ≤ (cspLam0 C₁ : ℝ) := by exact_mod_cast hlam_ge
      have hr_nn : (0 : ℝ) ≤ (r_star : ℝ) := Nat.cast_nonneg _
      nlinarith only [hlam_r, hr_nn]
  obtain ⟨h_s3a, h_s3b⟩ := h_s3
  clear hr hσ_pos h_cal hσ_up h_binom_edge hp_keep_up
  constructor
  · intro x u _hxu hd_xu
    let Z_bad := Finset.univ.filter (fun z : Fin (2 ^ cspL C₁ * r_star) → Fin (cspQ C₁) =>
      dHam x z ≤ C₁ * r_star ∧
      r_star < cspInvEta0 C₁ * (d3Coords x u z).card)
    let γ := fun z : Fin (2 ^ cspL C₁ * r_star) → Fin (cspQ C₁) =>
      ((d3Coords x u z).card, (diffCoords x z \ diffCoords x u).card)
    let B_idx := Finset.range (C₁ * r_star + 1) ×ˢ Finset.range (C₁ * r_star + 1)
    let f_z := fun z : Fin (2 ^ cspL C₁ * r_star) → Fin (cspQ C₁) =>
      (cspPEdge C₁ r_star) ^ ((homQueries z \ (homQueries x ∪ homQueries u)).card)
    let RHS_a : ℝ := (2 : ℝ) ^ (- (12 * (C₁ ^ 2 : ℕ) : ℝ) * (cspLam0 C₁ : ℝ) * (r_star : ℝ))
    have hd3w_le : ∀ z : Fin (2 ^ cspL C₁ * r_star) → Fin (cspQ C₁),
        (d3Coords x u z).card + (diffCoords x z \ diffCoords x u).card ≤ dHam x z := by
      intro z
      have hdisj : Disjoint (d3Coords x u z) (diffCoords x z \ diffCoords x u) := by
        rw [Finset.disjoint_left]
        intro v hv1 hv2
        simp only [d3Coords, diffCoords, Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ, true_and] at hv1 hv2
        exact hv2.2 hv1.1
      have hsub : d3Coords x u z ∪ (diffCoords x z \ diffCoords x u) ⊆ diffCoords x z := by
        intro v hv
        rcases Finset.mem_union.mp hv with hv1 | hv2
        · simp only [d3Coords, diffCoords, Finset.mem_filter, Finset.mem_univ, true_and] at hv1 ⊢
          exact hv1.2.1
        · exact (Finset.mem_sdiff.mp hv2).1
      rw [← Finset.card_union_of_disjoint hdisj]
      exact Finset.card_le_card hsub
    have hmaps : ∀ z ∈ Z_bad, γ z ∈ B_idx := by
      intro z hz
      simp only [Z_bad, Finset.mem_filter, Finset.mem_univ, true_and] at hz
      have hsum := le_trans (hd3w_le z) hz.1
      simp only [γ, B_idx, Finset.mem_product, Finset.mem_range]
      omega
    have hf_bound : ∀ z : Fin (2 ^ cspL C₁ * r_star) → Fin (cspQ C₁),
        f_z z ≤
          (cspPEdge C₁ r_star) ^
            (((d3Coords x u z).card + (diffCoords x z \ diffCoords x u).card) *
              (2 ^ cspL C₁ * r_star - 1) -
             ((d3Coords x u z).card + (diffCoords x z \ diffCoords x u).card).choose 2) := by
      intro z
      let T := d3Coords x u z ∪ (diffCoords x z \ diffCoords x u)
      have hdisj : Disjoint (d3Coords x u z) (diffCoords x z \ diffCoords x u) := by
        rw [Finset.disjoint_left]
        intro v hv1 hv2
        simp only [d3Coords, diffCoords, Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ, true_and] at hv1 hv2
        exact hv2.2 hv1.1
      have hT_card : T.card = (d3Coords x u z).card + (diffCoords x z \ diffCoords x u).card :=
        Finset.card_union_of_disjoint hdisj
      have hT_fresh : ∀ v ∈ T, ∀ y ∈ ({x, u} : Finset _), z v ≠ y v := by
        intro v hv y hy
        simp only [Finset.mem_insert, Finset.mem_singleton] at hy
        rcases Finset.mem_union.mp hv with hv1 | hv2
        · simp only [d3Coords, Finset.mem_filter, Finset.mem_univ, true_and] at hv1
          rcases hy with rfl | rfl
          · exact hv1.2.1.symm
          · exact hv1.2.2.symm
        · simp only [diffCoords, Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ, true_and, not_not] at hv2
          rcases hy with rfl | rfl
          · exact hv2.1.symm
          · rw [← hv2.2]; exact hv2.1.symm
      have hbi : ({x, u} : Finset _).biUnion homQueries = homQueries x ∪ homQueries u := by
        ext q_e
        simp
      have hq_le := h_s1 z ({x, u} : Finset _) T hT_fresh
      rw [hT_card, hbi] at hq_le
      exact pow_le_pow_of_le_one (le_of_lt hp_edge_pos) (le_of_lt hp_edge_lt1) hq_le
    rw [← Finset.sum_fiberwise_of_maps_to hmaps f_z]
    have hfib_le : ∀ dw ∈ B_idx,
        (((C₁ * r_star + 1) ^ 2 : ℕ) : ℝ) * (∑ z ∈ Z_bad with γ z = dw, f_z z) ≤ RHS_a := by
      rintro ⟨d₃, w⟩ _
      let Fib := Z_bad.filter (fun z => γ z = (d₃, w))
      change (((C₁ * r_star + 1) ^ 2 : ℕ) : ℝ) * (∑ z ∈ Fib, f_z z) ≤ RHS_a
      by_cases hne : Fib.Nonempty
      · obtain ⟨z₀, hz₀⟩ := hne
        simp only [Fib, Z_bad, γ, Finset.mem_filter, Finset.mem_univ, true_and, Prod.mk.injEq] at hz₀
        have hdw_le : d₃ + w ≤ C₁ * r_star := by
          have hs := le_trans (hd3w_le z₀) hz₀.1.1
          omega
        have hr_d3 : r_star < cspInvEta0 C₁ * d₃ := by
          rw [← hz₀.2.1]; exact hz₀.1.2
        let W_dw : ℝ :=
          (cspPEdge C₁ r_star) ^ ((d₃ + w) * (2 ^ cspL C₁ * r_star - 1) - (d₃ + w).choose 2)
        have hsum_W : ∑ z ∈ Fib, f_z z ≤ (Fib.card : ℝ) * W_dw := by
          calc
            ∑ z ∈ Fib, f_z z ≤ ∑ _z ∈ Fib, W_dw := by
              refine Finset.sum_le_sum (fun z hz => ?_)
              simp only [Fib, γ, Finset.mem_filter, Prod.mk.injEq] at hz
              simpa only [W_dw, hz.2.1, hz.2.2] using hf_bound z
            _ = (Fib.card : ℝ) * W_dw := by rw [Finset.sum_const, nsmul_eq_mul]
        have hcard_le : Fib.card ≤
            2 ^ (2 * (C₁ * r_star)) * (cspQ C₁ - 1) ^ d₃ *
              ((2 ^ cspL C₁ * r_star).choose w * (cspQ C₁ - 1) ^ w) := by
          have hsub : Fib ⊆ Finset.univ.filter (fun z =>
              (d3Coords x u z).card = d₃ ∧ (diffCoords x z \ diffCoords x u).card = w) := by
            intro z hz
            simp only [Fib, γ, Finset.mem_filter, Finset.mem_univ, true_and, Prod.mk.injEq] at hz ⊢
            exact hz.2
          have hc1 := le_trans (Finset.card_le_card hsub) (h_s2b x u d₃ w)
          have hpow : 2 ^ (2 * dHam x u) ≤ 2 ^ (2 * (C₁ * r_star)) :=
            Nat.pow_le_pow_right (by omega) (Nat.mul_le_mul_left 2 hd_xu)
          calc
            Fib.card ≤ 2 ^ (2 * dHam x u) * (cspQ C₁ - 1) ^ d₃ *
                ((2 ^ cspL C₁ * r_star).choose w * (cspQ C₁ - 1) ^ w) := hc1
            _ ≤ 2 ^ (2 * (C₁ * r_star)) * (cspQ C₁ - 1) ^ d₃ *
                ((2 ^ cspL C₁ * r_star).choose w * (cspQ C₁ - 1) ^ w) := by gcongr
        have hcard_real : (Fib.card : ℝ) ≤
            ((2 ^ (2 * (C₁ * r_star)) : ℕ) : ℝ) * ((cspQ C₁ - 1 : ℕ) : ℝ) ^ d₃ *
              (((2 ^ cspL C₁ * r_star).choose w : ℝ) * ((cspQ C₁ - 1 : ℕ) : ℝ) ^ w) := by
          exact_mod_cast hcard_le
        have hW_nn : 0 ≤ W_dw := pow_nonneg (le_of_lt hp_edge_pos) _
        calc
          (((C₁ * r_star + 1) ^ 2 : ℕ) : ℝ) * (∑ z ∈ Fib, f_z z)
            ≤ (((C₁ * r_star + 1) ^ 2 : ℕ) : ℝ) * ((Fib.card : ℝ) * W_dw) :=
              mul_le_mul_of_nonneg_left hsum_W (Nat.cast_nonneg _)
          _ ≤ (((C₁ * r_star + 1) ^ 2 : ℕ) : ℝ) *
                ((((2 ^ (2 * (C₁ * r_star)) : ℕ) : ℝ) * ((cspQ C₁ - 1 : ℕ) : ℝ) ^ d₃ *
                  (((2 ^ cspL C₁ * r_star).choose w : ℝ) * ((cspQ C₁ - 1 : ℕ) : ℝ) ^ w)) * W_dw) :=
              mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hcard_real hW_nn) (Nat.cast_nonneg _)
          _ ≤ RHS_a := h_s3a d₃ w hdw_le hr_d3
      · rw [Finset.not_nonempty_iff_eq_empty.mp hne, Finset.sum_empty, mul_zero]
        exact Real.rpow_nonneg (by norm_num) _
    have hB_card : B_idx.card = (C₁ * r_star + 1) ^ 2 := by
      simp [B_idx, Finset.card_product, sq]
    have hB_pos : (0 : ℝ) < (((C₁ * r_star + 1) ^ 2 : ℕ) : ℝ) := by positivity
    apply le_of_mul_le_mul_left _ hB_pos
    calc
      (((C₁ * r_star + 1) ^ 2 : ℕ) : ℝ) * ∑ dw ∈ B_idx, ∑ z ∈ Z_bad with γ z = dw, f_z z
        = ∑ dw ∈ B_idx, (((C₁ * r_star + 1) ^ 2 : ℕ) : ℝ) * (∑ z ∈ Z_bad with γ z = dw, f_z z) :=
          Finset.mul_sum _ _ _
      _ ≤ ∑ _dw ∈ B_idx, RHS_a := Finset.sum_le_sum hfib_le
      _ = (((C₁ * r_star + 1) ^ 2 : ℕ) : ℝ) * RHS_a := by
          rw [Finset.sum_const, hB_card, nsmul_eq_mul]
  · intro x w₀ _hxw₀ hd_xw₀ m hm y_prev _hinj hpool
    let P_rem := cspPoolCh C₁ r_star x w₀ \ Finset.univ.image y_prev
    let S_old : Finset (Fin (2 ^ cspL C₁ * r_star) → Fin (cspQ C₁)) :=
      ({x, w₀} : Finset _) ∪ Finset.univ.image y_prev
    let R_old : Finset (Fin (2 ^ cspL C₁ * r_star) × Fin (cspQ C₁)) :=
      (diffCoords x w₀).image (fun v => (v, w₀ v)) ∪
        Finset.univ.biUnion (fun t : Fin m =>
          (diffCoords x (y_prev t)).image (fun v => (v, y_prev t v)))
    let F_fresh := fun y : Fin (2 ^ cspL C₁ * r_star) → Fin (cspQ C₁) =>
      (diffCoords x y).filter (fun v => (v, y v) ∉ R_old)
    let g_y := fun y : Fin (2 ^ cspL C₁ * r_star) → Fin (cspQ C₁) =>
      ∏ i ∈ (({y} : Finset (Fin (2 ^ cspL C₁ * r_star) → Fin (cspQ C₁))).image Sum.inr ∪
          (homQueries y).image Sum.inl) \ cspUCh x w₀ m y_prev,
        cspPIota C₁ r_star i
    let RHS_b : ℝ := (2 : ℝ) ^ (- (72 / 100 : ℝ) * (cspLam0 C₁ : ℝ) * (r_star : ℝ))
    have hR_card : R_old.card ≤ (C₁ + cspKCh C₁) * r_star := by
      have hc1 : ((diffCoords x w₀).image (fun v => (v, w₀ v))).card ≤ C₁ * r_star :=
        le_trans Finset.card_image_le hd_xw₀
      have hc2 : (Finset.univ.biUnion (fun t : Fin m =>
          (diffCoords x (y_prev t)).image (fun v => (v, y_prev t v)))).card ≤ cspKCh C₁ * r_star := by
        calc
          (Finset.univ.biUnion (fun t : Fin m =>
              (diffCoords x (y_prev t)).image (fun v => (v, y_prev t v)))).card
            ≤ ∑ t : Fin m, ((diffCoords x (y_prev t)).image (fun v => (v, y_prev t v))).card :=
              Finset.card_biUnion_le
          _ ≤ ∑ _t : Fin m, r_star := by
              refine Finset.sum_le_sum (fun t _ => ?_)
              have ht := hpool t
              simp only [cspPoolCh, Finset.mem_filter, Finset.mem_univ, true_and] at ht
              exact le_trans Finset.card_image_le (le_of_eq ht.2.2.1)
          _ = m * r_star := by simp
          _ ≤ cspKCh C₁ * r_star := Nat.mul_le_mul_right r_star (le_of_lt hm)
      calc
        R_old.card ≤ ((diffCoords x w₀).image (fun v => (v, w₀ v))).card +
            (Finset.univ.biUnion (fun t : Fin m =>
              (diffCoords x (y_prev t)).image (fun v => (v, y_prev t v)))).card :=
          Finset.card_union_le _ _
        _ ≤ C₁ * r_star + cspKCh C₁ * r_star := Nat.add_le_add hc1 hc2
        _ = (C₁ + cspKCh C₁) * r_star := (add_mul C₁ (cspKCh C₁) r_star).symm
    have hR_card21 : R_old.card ≤ 21 * C₁ ^ 2 * r_star := by
      have hc21 : C₁ + cspKCh C₁ ≤ 21 * C₁ ^ 2 := by
        unfold cspKCh
        nlinarith only [hC₁]
      exact le_trans hR_card (Nat.mul_le_mul_right r_star hc21)
    have hy_eval : ∀ y ∈ P_rem,
        g_y y = cspPKeep C₁ r_star *
          (cspPEdge C₁ r_star) ^ ((homQueries y \ S_old.biUnion homQueries).card) ∧
        80 * (F_fresh y).card ≤ 61 * r_star ∧
        (F_fresh y).card < r_star + 1 := by
      intro y hy
      rcases Finset.mem_sdiff.mp hy with ⟨hy_pool, hy_not_img⟩
      simp only [cspPoolCh, Finset.mem_filter, Finset.mem_univ, true_and] at hy_pool
      rcases hy_pool with ⟨hy_ne_x, hy_ne_w0, hd_xy, hov_xy, hd3_xy⟩
      have hset_eq :
          (({y} : Finset (Fin (2 ^ cspL C₁ * r_star) → Fin (cspQ C₁))).image Sum.inr ∪
              (homQueries y).image Sum.inl) \ cspUCh x w₀ m y_prev =
          {Sum.inr y} ∪ (homQueries y \ S_old.biUnion homQueries).image Sum.inl := by
        ext i
        rcases i with q_e | z_v
        · simp only [cspUCh, S_old, Finset.mem_sdiff, Finset.mem_union, Finset.mem_image,
            Finset.mem_singleton, Finset.mem_insert, Finset.mem_univ, true_and,
            Finset.mem_biUnion, Sum.inl.injEq, reduceCtorEq]
          constructor
          · rintro ⟨(⟨_, _, h⟩ | ⟨t, ht, rfl⟩), hnot⟩
            · nomatch h
            · refine Or.inr ⟨t, ⟨ht, ?_⟩, rfl⟩
              rintro ⟨z, (rfl | rfl) | ⟨idx, rfl⟩, htz⟩
              · exact hnot (Or.inr ⟨t, Or.inl (Or.inl htz), rfl⟩)
              · exact hnot (Or.inr ⟨t, Or.inl (Or.inr htz), rfl⟩)
              · exact hnot (Or.inr ⟨t, Or.inr ⟨idx, htz⟩, rfl⟩)
          · rintro (h | ⟨t, ⟨ht, hnot⟩, rfl⟩)
            · nomatch h
            · refine ⟨Or.inr ⟨t, ht, rfl⟩, ?_⟩
              rintro ((⟨_, _, h⟩ | ⟨_, h⟩) | ⟨t', (htx | htw) | ⟨idx, hti⟩, rfl⟩)
              · nomatch h
              · nomatch h
              · exact hnot ⟨x, Or.inl (Or.inl rfl), htx⟩
              · exact hnot ⟨w₀, Or.inl (Or.inr rfl), htw⟩
              · exact hnot ⟨y_prev idx, Or.inr ⟨idx, rfl⟩, hti⟩
        · simp only [cspUCh, S_old, Finset.mem_sdiff, Finset.mem_union, Finset.mem_image,
            Finset.mem_singleton, Finset.mem_insert, Finset.mem_univ, true_and,
            Finset.mem_biUnion, Sum.inr.injEq, reduceCtorEq]
          constructor
          · rintro ⟨(⟨z, rfl, rfl⟩ | ⟨_, _, h⟩), _⟩
            · exact Or.inl rfl
            · nomatch h
          · rintro (rfl | ⟨_, _, h⟩)
            · refine ⟨Or.inl ⟨z_v, rfl, rfl⟩, ?_⟩
              rintro ((⟨z, rfl | rfl, rfl⟩ | ⟨idx, rfl⟩) | ⟨_, _, h⟩)
              · exact hy_ne_x rfl
              · exact hy_ne_w0 rfl
              · exact hy_not_img (Finset.mem_image.mpr ⟨idx, Finset.mem_univ idx, rfl⟩)
              · nomatch h
            · nomatch h
      have hg_eq : g_y y = cspPKeep C₁ r_star *
          (cspPEdge C₁ r_star) ^ ((homQueries y \ S_old.biUnion homQueries).card) := by
        dsimp only [g_y]
        rw [hset_eq, Finset.prod_union]
        · rw [Finset.prod_singleton, Finset.prod_image (fun _ _ _ _ h => Sum.inl.inj h)]
          simp [cspPIota]
        · rw [Finset.disjoint_left]
          intro i hi1 hi2
          rw [Finset.mem_singleton] at hi1
          subst hi1
          rcases Finset.mem_image.mp hi2 with ⟨_, _, h⟩
          cases h
      let B_w0 := (diffCoords x w₀ ∩ diffCoords x y) \ d3Coords x w₀ y
      have hdisj_FB : Disjoint (F_fresh y) B_w0 := by
        rw [Finset.disjoint_left]
        intro v hvF hvB
        simp only [F_fresh, Finset.mem_filter] at hvF
        simp only [B_w0, d3Coords, diffCoords, Finset.mem_sdiff, Finset.mem_inter,
          Finset.mem_filter, Finset.mem_univ, true_and] at hvB
        have hyw : w₀ v = y v := by
          by_contra hne
          exact hvB.2 ⟨hvB.1.1, hvB.1.2, hne⟩
        apply hvF.2
        rw [← hyw]
        exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨v,
          Finset.mem_filter.mpr ⟨Finset.mem_univ v, hvB.1.1⟩, rfl⟩)
      have hFB_sub : F_fresh y ∪ B_w0 ⊆ diffCoords x y := by
        intro v hv
        rcases Finset.mem_union.mp hv with hvF | hvB
        · exact (Finset.mem_filter.mp hvF).1
        · exact (Finset.mem_inter.mp (Finset.mem_sdiff.mp hvB).1).2
      have hFB_card : (F_fresh y).card + B_w0.card ≤ r_star := by
        rw [← Finset.card_union_of_disjoint hdisj_FB]
        exact le_trans (Finset.card_le_card hFB_sub) (le_of_eq hd_xy)
      have hinter_le : (diffCoords x w₀ ∩ diffCoords x y).card ≤ B_w0.card + (d3Coords x w₀ y).card := by
        have hcov : diffCoords x w₀ ∩ diffCoords x y ⊆ B_w0 ∪ d3Coords x w₀ y := by
          intro v hv
          by_cases hd3 : v ∈ d3Coords x w₀ y
          · exact Finset.mem_union_right _ hd3
          · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hv, hd3⟩)
        exact le_trans (Finset.card_le_card hcov) (Finset.card_union_le _ _)
      have hd3_80 : 80 * (d3Coords x w₀ y).card ≤ r_star := by
        simpa [cspInvEta0] using hd3_xy
      refine ⟨hg_eq, by omega, by omega⟩
    have hg_bound : ∀ y ∈ P_rem,
        g_y y ≤ cspPKeep C₁ r_star *
          (cspPEdge C₁ r_star) ^
            ((F_fresh y).card * (2 ^ cspL C₁ * r_star - 1) - (F_fresh y).card.choose 2) := by
      intro y hy
      rw [(hy_eval y hy).1]
      have hfresh : ∀ v ∈ F_fresh y, ∀ z ∈ S_old, y v ≠ z v := by
        intro v hv z hz
        simp only [F_fresh, diffCoords, Finset.mem_filter, Finset.mem_univ, true_and] at hv
        simp only [S_old, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton,
          Finset.mem_image, Finset.mem_univ, true_and] at hz
        rcases hz with (rfl | rfl) | ⟨t, rfl⟩
        · exact hv.1.symm
        · intro heq
          apply hv.2
          rw [heq]
          exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨v,
            Finset.mem_filter.mpr ⟨Finset.mem_univ v, by rw [← heq]; exact hv.1⟩, rfl⟩)
        · intro heq
          apply hv.2
          rw [heq]
          refine Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨t, Finset.mem_univ t, ?_⟩)
          exact Finset.mem_image.mpr ⟨v,
            Finset.mem_filter.mpr ⟨Finset.mem_univ v, by rw [← heq]; exact hv.1⟩, rfl⟩
      have hq_le := h_s1 y S_old (F_fresh y) hfresh
      exact mul_le_mul_of_nonneg_left
        (pow_le_pow_of_le_one (le_of_lt hp_edge_pos) (le_of_lt hp_edge_lt1) hq_le)
        (le_of_lt hp_keep_pos)
    have hmaps : ∀ y ∈ P_rem, (F_fresh y).card ∈ Finset.range (r_star + 1) := by
      intro y hy
      exact Finset.mem_range.mpr (hy_eval y hy).2.2
    rw [← Finset.sum_fiberwise_of_maps_to hmaps g_y]
    have hfib_le : ∀ s ∈ Finset.range (r_star + 1),
        ((r_star + 1 : ℕ) : ℝ) * (∑ y ∈ P_rem with (F_fresh y).card = s, g_y y) ≤ RHS_b := by
      intro s _
      let Fib := P_rem.filter (fun y => (F_fresh y).card = s)
      change ((r_star + 1 : ℕ) : ℝ) * (∑ y ∈ Fib, g_y y) ≤ RHS_b
      by_cases hne : Fib.Nonempty
      · obtain ⟨y₀, hy₀⟩ := hne
        rcases Finset.mem_filter.mp hy₀ with ⟨hy₀_rem, rfl⟩
        have hs_61 : 80 * (F_fresh y₀).card ≤ 61 * r_star := (hy_eval y₀ hy₀_rem).2.1
        let W_s : ℝ := cspPKeep C₁ r_star *
          (cspPEdge C₁ r_star) ^ ((F_fresh y₀).card * (2 ^ cspL C₁ * r_star - 1) -
            (F_fresh y₀).card.choose 2)
        have hsum_W : ∑ y ∈ Fib, g_y y ≤ (Fib.card : ℝ) * W_s := by
          calc
            ∑ y ∈ Fib, g_y y ≤ ∑ _y ∈ Fib, W_s := by
              refine Finset.sum_le_sum (fun y hy => ?_)
              rcases Finset.mem_filter.mp hy with ⟨hy_rem, hy_eq⟩
              simpa only [W_s, ← hy_eq] using hg_bound y hy_rem
            _ = (Fib.card : ℝ) * W_s := by rw [Finset.sum_const, nsmul_eq_mul]
        have hsub : Fib ⊆ Finset.univ.filter (fun y =>
            (F_fresh y).card = (F_fresh y₀).card ∧ dHam x y ≤ r_star) := by
          intro y hy
          rcases Finset.mem_filter.mp hy with ⟨hy_rem, hy_eq⟩
          have hy_pool := (Finset.mem_sdiff.mp hy_rem).1
          simp only [cspPoolCh, Finset.mem_filter, Finset.mem_univ, true_and] at hy_pool
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ y, hy_eq, le_of_eq hy_pool.2.2.1⟩
        have hcard_le1 : (Fib.card : ℝ) ≤
            ((Finset.univ.filter (fun y =>
              (F_fresh y).card = (F_fresh y₀).card ∧ dHam x y ≤ r_star)).card : ℝ) := by
          exact_mod_cast Finset.card_le_card hsub
        have hcard_real : (Fib.card : ℝ) ≤
            ((r_star + 1 : ℕ) : ℝ) *
              (2 : ℝ) ^ ((1 / 100 : ℝ) * (cspLam0 C₁ : ℝ) * (r_star : ℝ)) *
              (((2 ^ cspL C₁ * r_star).choose (F_fresh y₀).card : ℝ) *
                ((cspQ C₁ - 1 : ℕ) : ℝ) ^ (F_fresh y₀).card) :=
          le_trans hcard_le1 (h_s2c C₁ r_star hC₁ x R_old hR_card21 (F_fresh y₀).card)
        have hW_nn : 0 ≤ W_s :=
          mul_nonneg (le_of_lt hp_keep_pos) (pow_nonneg (le_of_lt hp_edge_pos) _)
        calc
          ((r_star + 1 : ℕ) : ℝ) * (∑ y ∈ Fib, g_y y)
            ≤ ((r_star + 1 : ℕ) : ℝ) * ((Fib.card : ℝ) * W_s) :=
              mul_le_mul_of_nonneg_left hsum_W (Nat.cast_nonneg _)
          _ ≤ ((r_star + 1 : ℕ) : ℝ) *
                ((((r_star + 1 : ℕ) : ℝ) *
                  (2 : ℝ) ^ ((1 / 100 : ℝ) * (cspLam0 C₁ : ℝ) * (r_star : ℝ)) *
                  (((2 ^ cspL C₁ * r_star).choose (F_fresh y₀).card : ℝ) *
                    ((cspQ C₁ - 1 : ℕ) : ℝ) ^ (F_fresh y₀).card)) * W_s) :=
              mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hcard_real hW_nn) (Nat.cast_nonneg _)
          _ ≤ RHS_b := h_s3b (F_fresh y₀).card hs_61
      · rw [Finset.not_nonempty_iff_eq_empty.mp hne, Finset.sum_empty, mul_zero]
        exact Real.rpow_nonneg (by norm_num) _
    have hr1_pos : (0 : ℝ) < ((r_star + 1 : ℕ) : ℝ) := by positivity
    apply le_of_mul_le_mul_left _ hr1_pos
    calc
      ((r_star + 1 : ℕ) : ℝ) * ∑ s ∈ Finset.range (r_star + 1), ∑ y ∈ P_rem with (F_fresh y).card = s, g_y y
        = ∑ s ∈ Finset.range (r_star + 1), ((r_star + 1 : ℕ) : ℝ) * (∑ y ∈ P_rem with (F_fresh y).card = s, g_y y) :=
          Finset.mul_sum _ _ _
      _ ≤ ∑ _s ∈ Finset.range (r_star + 1), RHS_b := Finset.sum_le_sum hfib_le
      _ = ((r_star + 1 : ℕ) : ℝ) * RHS_b := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

private theorem raw_degree_and_edge_second_moment_sums (C₁ : ℕ) (hC₁ : 3 ≤ C₁) (r_star : ℕ) (hr : 1000 * C₁ < r_star)
    (hσ_pos : 0 < cspSigmaEdge C₁ r_star)
    (hp_edge_pos : 0 < cspPEdge C₁ r_star)
    (hp_edge_lt1 : cspPEdge C₁ r_star < 1)
    (h_cal : (4 : ℝ) * (2 : ℝ) ^ cspL C₁ * ((cspQ C₁ - 1 : ℕ) : ℝ) *
      (cspPEdge C₁ r_star) ^ (2 ^ cspL C₁ * r_star - 1) = (2 : ℝ) ^ (- (cspGamma0 C₁ : ℝ)))
    (hσ_low : (cspBeta0 C₁ : ℝ) ≤ cspSigmaEdge C₁ r_star * (r_star : ℝ) / 2)
    (hp_keep_pos : 0 < cspPKeep C₁ r_star)
    (h_union_card : ∀ x y : Fin (2 ^ cspL C₁ * r_star) → Fin (cspQ C₁),
      (homQueries x ∪ homQueries y).card =
        (2 ^ cspL C₁ * r_star).choose 2 +
          dHam x y * (2 ^ cspL C₁ * r_star - 1) - (dHam x y).choose 2)
    (h_sphere : ∀ (x : Fin (2 ^ cspL C₁ * r_star) → Fin (cspQ C₁)) (s : ℕ),
      (Finset.univ.filter (fun y => dHam x y = s)).card =
        (2 ^ cspL C₁ * r_star).choose s * (cspQ C₁ - 1) ^ s)
    (h_M0 : ∑ xy ∈ Finset.univ.filter
        (fun xy : (Fin (2 ^ cspL C₁ * r_star) → Fin (cspQ C₁)) ×
                  (Fin (2 ^ cspL C₁ * r_star) → Fin (cspQ C₁)) =>
          dHam xy.1 xy.2 = r_star),
      (cspPKeep C₁ r_star) ^ 2 *
        (cspPEdge C₁ r_star) ^ (homQueries xy.1 ∪ homQueries xy.2).card =
      cspN0 C₁ r_star * cspDStar C₁ r_star) :
    (∑ xyz ∈ Finset.univ.filter
        (fun xyz : (Fin (2 ^ cspL C₁ * r_star) → Fin (cspQ C₁)) ×
                   (Fin (2 ^ cspL C₁ * r_star) → Fin (cspQ C₁)) ×
                   (Fin (2 ^ cspL C₁ * r_star) → Fin (cspQ C₁)) =>
          dHam xyz.1 xyz.2.1 = r_star ∧ dHam xyz.1 xyz.2.2 = r_star ∧ xyz.2.1 ≠ xyz.2.2),
      (cspPKeep C₁ r_star) ^ 3 *
        (cspPEdge C₁ r_star) ^ (homQueries xyz.1 ∪ homQueries xyz.2.1 ∪ homQueries xyz.2.2).card ≤
        (3 / 2 : ℝ) * cspGamma r_star *
          cspN0 C₁ r_star * (cspDStar C₁ r_star) ^ 2) ∧
    (∑ e₁₂ ∈ Finset.univ.filter
        (fun e₁₂ : ((Fin (2 ^ cspL C₁ * r_star) → Fin (cspQ C₁)) ×
                    (Fin (2 ^ cspL C₁ * r_star) → Fin (cspQ C₁))) ×
                   ((Fin (2 ^ cspL C₁ * r_star) → Fin (cspQ C₁)) ×
                    (Fin (2 ^ cspL C₁ * r_star) → Fin (cspQ C₁))) =>
          dHam e₁₂.1.1 e₁₂.1.2 = r_star ∧ dHam e₁₂.2.1 e₁₂.2.2 = r_star ∧
          e₁₂.2.1 ≠ e₁₂.1.1 ∧ e₁₂.2.1 ≠ e₁₂.1.2 ∧
          e₁₂.2.2 ≠ e₁₂.1.1 ∧ e₁₂.2.2 ≠ e₁₂.1.2),
      (cspPKeep C₁ r_star) ^ 4 *
        (cspPEdge C₁ r_star) ^ (homQueries e₁₂.1.1 ∪ homQueries e₁₂.1.2 ∪
                                homQueries e₁₂.2.1 ∪ homQueries e₁₂.2.2).card ≤
        2 * cspGamma r_star *
          (cspN0 C₁ r_star * cspDStar C₁ r_star) ^ 2) :=
by
  have h_mem_hq : ∀ {N0 q0 : ℕ} (z : Fin N0 → Fin q0)
      (t : Fin N0 × Fin N0 × Fin q0 × Fin q0),
      t ∈ homQueries z ↔ t.1 < t.2.1 ∧ t.2.2.1 = z t.1 ∧ t.2.2.2 = z t.2.1 := by
    intro N0 q0 z ⟨u, v, c₁, c₂⟩
    simp only [homQueries, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and,
      Prod.mk.injEq]
    constructor
    · rintro ⟨⟨u', v'⟩, huv, rfl, rfl, h1, h2⟩
      exact ⟨huv, h1.symm, h2.symm⟩
    · rintro ⟨huv, rfl, rfl⟩
      exact ⟨(u, v), huv, rfl, rfl, rfl, rfl⟩
  have h_two_ch2 : ∀ s : ℕ, 2 * s.choose 2 = s * (s - 1) := by
    intro s
    rw [Nat.choose_two_right]
    exact Nat.mul_div_cancel' (Even.two_dvd (Nat.even_mul_pred_self s))
  have h_ch2_le : ∀ {s N0 : ℕ}, s ≤ N0 → s.choose 2 ≤ s * (N0 - 1) := by
    intro s N0 hs
    have h2 := h_two_ch2 s
    have hsub : s - 1 ≤ N0 - 1 := Nat.sub_le_sub_right hs 1
    have hmul : s * (s - 1) ≤ s * (N0 - 1) := Nat.mul_le_mul_left s hsub
    omega
  have h_s1 : ∀ (N0 q0 r0 : ℕ), 2 ≤ q0 → r0 ≤ N0 →
      (∀ a b : Fin N0 → Fin q0,
        (homQueries a ∪ homQueries b).card =
          N0.choose 2 + dHam a b * (N0 - 1) - (dHam a b).choose 2) →
      ∀ (x y : Fin N0 → Fin q0), dHam x y = r0 →
        (∀ z : Fin N0 → Fin q0, dHam x z = r0 →
          ((diffCoords x y).filter (fun v => z v = y v)).card ≤ r0 ∧
          (homQueries x ∪ homQueries y).card +
            ((r0 - ((diffCoords x y).filter (fun v => z v = y v)).card) * (N0 - 1) -
             (r0 - ((diffCoords x y).filter (fun v => z v = y v)).card).choose 2) ≤
            (homQueries x ∪ homQueries y ∪ homQueries z).card) ∧
        (∀ b : ℕ, b ≤ r0 →
          (Finset.univ.filter (fun z : Fin N0 → Fin q0 =>
            dHam x z = r0 ∧
            ((diffCoords x y).filter (fun v => z v = y v)).card = b)).card ≤
            r0.choose b * (N0 - b).choose (r0 - b) * (q0 - 1) ^ (r0 - b)) := by
    intro N0 q0 r0 hq hrN h_union x y hdxy
    have hB_sub_xz : ∀ z : Fin N0 → Fin q0,
        (diffCoords x y).filter (fun v => z v = y v) ⊆ diffCoords x z := by
      intro z v hv
      simp only [diffCoords, Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
      rw [hv.2]
      exact hv.1
    constructor
    · intro z hdxz
      let B := (diffCoords x y).filter (fun v => z v = y v)
      let b := B.card
      have hb_le : b ≤ r0 := by
        rw [← hdxy]
        exact Finset.card_le_card (Finset.filter_subset _ _)
      refine ⟨hb_le, ?_⟩
      let T := diffCoords x z \ B
      have hT_card : T.card = r0 - b := by
        have hadd := Finset.card_sdiff_add_card_eq_card (hB_sub_xz z)
        change T.card + b = dHam x z at hadd
        omega
      have hT_ne : ∀ w ∈ T, z w ≠ x w ∧ z w ≠ y w := by
        intro w hw
        simp only [T, B, diffCoords, Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ,
          true_and, not_and] at hw
        refine ⟨hw.1.symm, fun hzy => ?_⟩
        apply hw.2
        · rw [← hzy]
          exact hw.1
        · exact hzy
      let U_all := Finset.univ.filter (fun uv : Fin N0 × Fin N0 => uv.1 < uv.2)
      let P_T := U_all.filter (fun uv => uv.1 ∈ T ∨ uv.2 ∈ T)
      let c₀ : Fin q0 := ⟨0, by omega⟩
      let c₁ : Fin q0 := ⟨1, by omega⟩
      have hc_ne : c₀ ≠ c₁ := by
        intro h
        have := congr_arg Fin.val h
        simp [c₀, c₁] at this
      let x₀ : Fin N0 → Fin q0 := fun _ => c₀
      let y₀ : Fin N0 → Fin q0 := fun v => if v ∈ T then c₁ else c₀
      have hd_x0 : dHam x₀ x₀ = 0 := by simp [dHam, diffCoords]
      have hcard_x0 : (homQueries x₀).card = N0.choose 2 := by
        have hu := h_union x₀ x₀
        rw [Finset.union_idempotent, hd_x0] at hu
        simpa using hu
      have hdiff_x0y0 : diffCoords x₀ y₀ = T := by
        ext v
        simp only [diffCoords, x₀, y₀, Finset.mem_filter, Finset.mem_univ, true_and]
        split_ifs with hv
        · simp [hv, hc_ne]
        · simp [hv]
      have hd_x0y0 : dHam x₀ y₀ = r0 - b := by
        unfold dHam
        rw [hdiff_x0y0, hT_card]
      have hsdiff_y0 : homQueries y₀ \ homQueries x₀ =
          P_T.image (fun uv => (uv.1, uv.2, y₀ uv.1, y₀ uv.2)) := by
        ext ⟨u, v, d₁, d₂⟩
        simp only [Finset.mem_sdiff, h_mem_hq, P_T, U_all, Finset.mem_image,
          Finset.mem_filter, Finset.mem_univ, true_and, Prod.mk.injEq]
        constructor
        · rintro ⟨⟨huv, rfl, rfl⟩, hnot⟩
          refine ⟨(u, v), ⟨huv, ?_⟩, rfl, rfl, rfl, rfl⟩
          by_contra hnor
          push_neg at hnor
          apply hnot
          exact ⟨huv, by simp [x₀, y₀, hnor.1], by simp [x₀, y₀, hnor.2]⟩
        · rintro ⟨⟨u', v'⟩, ⟨huv, hor⟩, rfl, rfl, rfl, rfl⟩
          refine ⟨⟨huv, rfl, rfl⟩, ?_⟩
          rintro ⟨_, h1, h2⟩
          rcases hor with hu | hv
          · simp [x₀, y₀, hu] at h1
            exact hc_ne h1.symm
          · simp [x₀, y₀, hv] at h2
            exact hc_ne h2.symm
      have hPT_card : P_T.card = (r0 - b) * (N0 - 1) - (r0 - b).choose 2 := by
        have hg0_inj : Function.Injective
            (fun uv : Fin N0 × Fin N0 => (uv.1, uv.2, y₀ uv.1, y₀ uv.2)) := by
          intro a₁ a₂ h
          simp only [Prod.mk.injEq] at h
          exact Prod.ext h.1 h.2.1
        have hsdiff_card : (homQueries y₀ \ homQueries x₀).card = P_T.card := by
          rw [hsdiff_y0, Finset.card_image_of_injective _ hg0_inj]
        have hunion_eq : (homQueries x₀ ∪ homQueries y₀).card =
            (homQueries x₀).card + (homQueries y₀ \ homQueries x₀).card := by
          rw [← Finset.union_sdiff_self_eq_union,
            Finset.card_union_of_disjoint disjoint_sdiff_self_right]
        have hu := h_union x₀ y₀
        rw [hunion_eq, hcard_x0, hsdiff_card, hd_x0y0] at hu
        have hle_ch : (r0 - b).choose 2 ≤ (r0 - b) * (N0 - 1) := h_ch2_le (by omega)
        omega
      have hPT_le_fresh : P_T.card ≤ (homQueries z \ (homQueries x ∪ homQueries y)).card := by
        apply Finset.card_le_card_of_injOn (fun uv : Fin N0 × Fin N0 => (uv.1, uv.2, z uv.1, z uv.2))
        · intro uv huv
          simp only [P_T, U_all, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at huv
          simp only [Finset.mem_coe, Finset.mem_sdiff, Finset.mem_union, h_mem_hq, and_true]
          refine ⟨huv.1, ?_⟩
          rintro (⟨_, hx1, hx2⟩ | ⟨_, hy1, hy2⟩)
          · rcases huv.2 with hu | hv
            · exact (hT_ne uv.1 hu).1 hx1
            · exact (hT_ne uv.2 hv).1 hx2
          · rcases huv.2 with hu | hv
            · exact (hT_ne uv.1 hu).2 hy1
            · exact (hT_ne uv.2 hv).2 hy2
        · intro a₁ _ a₂ _ h
          simp only [Prod.mk.injEq] at h
          exact Prod.ext h.1 h.2.1
      have hunion3 : (homQueries x ∪ homQueries y ∪ homQueries z).card =
          (homQueries x ∪ homQueries y).card +
          (homQueries z \ (homQueries x ∪ homQueries y)).card := by
        rw [← Finset.union_sdiff_self_eq_union (s := homQueries x ∪ homQueries y) (t := homQueries z),
          Finset.card_union_of_disjoint disjoint_sdiff_self_right]
      change (homQueries x ∪ homQueries y).card +
        ((r0 - b) * (N0 - 1) - (r0 - b).choose 2) ≤ _
      rw [hunion3, ← hPT_card]
      exact Nat.add_le_add_left hPT_le_fresh _
    · intro b hb
      let B_of : (Fin N0 → Fin q0) → Finset (Fin N0) :=
        fun z => (diffCoords x y).filter (fun v => z v = y v)
      let T_of : (Fin N0 → Fin q0) → Finset (Fin N0) :=
        fun z => diffCoords x z \ B_of z
      let F_b := Finset.univ.filter (fun z : Fin N0 → Fin q0 => dHam x z = r0 ∧ (B_of z).card = b)
      let S₁ := (diffCoords x y).powersetCard b
      have hS₁_card : S₁.card = r0.choose b := by
        rw [Finset.card_powersetCard, ← hdxy]
      have hmaps1 : ∀ z ∈ F_b, B_of z ∈ S₁ := by
        intro z hz
        simp only [F_b, Finset.mem_filter, Finset.mem_univ, true_and] at hz
        rw [Finset.mem_powersetCard]
        exact ⟨Finset.filter_subset _ _, hz.2⟩
      have hfib1 : F_b.card = ∑ B ∈ S₁, (F_b.filter (fun z => B_of z = B)).card := by
        simp_rw [Finset.card_eq_sum_ones]
        exact (Finset.sum_fiberwise_of_maps_to hmaps1 _).symm
      have hbound1 : ∀ B ∈ S₁, (F_b.filter (fun z => B_of z = B)).card ≤
          (N0 - b).choose (r0 - b) * (q0 - 1) ^ (r0 - b) := by
        intro B hB
        have hB_card : B.card = b := (Finset.mem_powersetCard.mp hB).2
        let S₂ := (Finset.univ \ B).powersetCard (r0 - b)
        have hS₂_card : S₂.card = (N0 - b).choose (r0 - b) := by
          rw [Finset.card_powersetCard]
          have hadd := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ B)
          rw [Finset.card_univ, Fintype.card_fin, hB_card] at hadd
          have hcard_u : (Finset.univ \ B).card = N0 - b := by omega
          rw [hcard_u]
        have hmaps2 : ∀ z ∈ F_b.filter (fun z => B_of z = B), T_of z ∈ S₂ := by
          intro z hz
          simp only [F_b, Finset.mem_filter, Finset.mem_univ, true_and] at hz
          rw [Finset.mem_powersetCard]
          refine ⟨?_, ?_⟩
          · intro v hv
            simp only [T_of, Finset.mem_sdiff, Finset.mem_univ, true_and] at hv ⊢
            rw [← hz.2]
            exact hv.2
          · have hsub : B_of z ⊆ diffCoords x z := hB_sub_xz z
            have hadd := Finset.card_sdiff_add_card_eq_card hsub
            change (T_of z).card + (B_of z).card = dHam x z at hadd
            omega
        have hfib2 : (F_b.filter (fun z => B_of z = B)).card =
            ∑ T ∈ S₂, ((F_b.filter (fun z => B_of z = B)).filter (fun z => T_of z = T)).card := by
          simp_rw [Finset.card_eq_sum_ones]
          exact (Finset.sum_fiberwise_of_maps_to hmaps2 _).symm
        have hbound2 : ∀ T ∈ S₂,
            ((F_b.filter (fun z => B_of z = B)).filter (fun z => T_of z = T)).card ≤
              (q0 - 1) ^ (r0 - b) := by
          intro T hT
          have hT_card : T.card = r0 - b := (Finset.mem_powersetCard.mp hT).2
          let P_target := Fintype.piFinset (fun v : ↥T => Finset.univ.erase (x v.1))
          have hP_card : P_target.card = (q0 - 1) ^ (r0 - b) := by
            rw [Fintype.card_piFinset]
            have h1 : ∀ v : ↥T, (Finset.univ.erase (x v.1)).card = q0 - 1 := by
              intro v
              rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
            simp_rw [h1]
            simp [Finset.prod_const, hT_card]
          rw [← hP_card]
          apply Finset.card_le_card_of_injOn (fun z (v : ↥T) => z v.1)
          · intro z hz
            simp only [Finset.mem_coe, Finset.mem_filter] at hz
            rw [Finset.mem_coe, Fintype.mem_piFinset]
            intro v
            have hvT : v.1 ∈ T_of z := by rw [hz.2]; exact v.2
            simp only [T_of, diffCoords, Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ,
              true_and] at hvT
            exact Finset.mem_erase.mpr ⟨hvT.1.symm, Finset.mem_univ _⟩
          · intro z₁ hz₁ z₂ hz₂ heq
            simp only [Finset.mem_coe, Finset.mem_filter] at hz₁ hz₂
            funext w
            by_cases hwB : w ∈ B
            · have h1 : w ∈ B_of z₁ := by rwa [hz₁.1.2]
              have h2 : w ∈ B_of z₂ := by rwa [hz₂.1.2]
              simp only [B_of, Finset.mem_filter] at h1 h2
              rw [h1.2, h2.2]
            · by_cases hwT : w ∈ T
              · exact congr_fun heq ⟨w, hwT⟩
              · have hn1 : w ∉ diffCoords x z₁ := by
                  intro hd
                  have hTw : w ∈ T_of z₁ := Finset.mem_sdiff.mpr ⟨hd, by rwa [hz₁.1.2]⟩
                  rw [hz₁.2] at hTw
                  exact hwT hTw
                have hn2 : w ∉ diffCoords x z₂ := by
                  intro hd
                  have hTw : w ∈ T_of z₂ := Finset.mem_sdiff.mpr ⟨hd, by rwa [hz₂.1.2]⟩
                  rw [hz₂.2] at hTw
                  exact hwT hTw
                simp only [diffCoords, Finset.mem_filter, Finset.mem_univ, true_and, not_not] at hn1 hn2
                rw [← hn1, ← hn2]
        rw [hfib2]
        calc
          ∑ T ∈ S₂, ((F_b.filter (fun z => B_of z = B)).filter (fun z => T_of z = T)).card
            ≤ S₂.card • ((q0 - 1) ^ (r0 - b)) := Finset.sum_le_card_nsmul _ _ _ hbound2
          _ = (N0 - b).choose (r0 - b) * (q0 - 1) ^ (r0 - b) := by rw [hS₂_card, smul_eq_mul]
      change F_b.card ≤ _
      rw [hfib1, mul_assoc]
      calc
        ∑ B ∈ S₁, (F_b.filter (fun z => B_of z = B)).card
          ≤ S₁.card • ((N0 - b).choose (r0 - b) * (q0 - 1) ^ (r0 - b)) :=
            Finset.sum_le_card_nsmul _ _ _ hbound1
        _ = r0.choose b * ((N0 - b).choose (r0 - b) * (q0 - 1) ^ (r0 - b)) := by
            rw [hS₁_card, smul_eq_mul]

  have h_s2 : ∀ (N0 q0 r0 : ℕ), 2 ≤ q0 → r0 ≤ N0 →
      ∀ (x y : Fin N0 → Fin q0),
        (∀ x' y' : Fin N0 → Fin q0,
          ((homQueries x ∪ homQueries y) ∩ (homQueries x' ∪ homQueries y')).card ≤
            ((Finset.univ.filter (fun v : Fin N0 => x' v = x v ∨ x' v = y v)).card +
             ((diffCoords x' y').filter (fun v : Fin N0 => y' v = x v ∨ y' v = y v)).card).choose 2) ∧
        (∀ k₁ k₂ : ℕ, k₁ ≤ N0 → k₂ ≤ r0 →
          (Finset.univ.filter (fun xy' : (Fin N0 → Fin q0) × (Fin N0 → Fin q0) =>
            dHam xy'.1 xy'.2 = r0 ∧
            (Finset.univ.filter (fun v : Fin N0 => xy'.1 v = x v ∨ xy'.1 v = y v)).card = k₁ ∧
            ((diffCoords xy'.1 xy'.2).filter (fun v : Fin N0 => xy'.2 v = x v ∨ xy'.2 v = y v)).card = k₂)).card ≤
            N0.choose k₁ * 2 ^ k₁ * q0 ^ (N0 - k₁) *
              (N0.choose r0 * r0.choose k₂ * 2 ^ k₂ * (q0 - 1) ^ (r0 - k₂))) := by
    intro N0 q0 r0 _hq _hrN x y
    constructor
    · intro x' y'
      let K₁ := Finset.univ.filter (fun v : Fin N0 => x' v = x v ∨ x' v = y v)
      let K₂ := (diffCoords x' y').filter (fun v : Fin N0 => y' v = x v ∨ y' v = y v)
      let S : Finset (Fin N0 ⊕ Fin N0) := K₁.disjSum K₂
      let I := (homQueries x ∪ homQueries y) ∩ (homQueries x' ∪ homQueries y')
      have hS_pow_card : (S.powersetCard 2).card = (K₁.card + K₂.card).choose 2 := by
        rw [Finset.card_powersetCard, Finset.card_disjSum]
      change I.card ≤ _
      rw [← hS_pow_card]
      let τ : Fin N0 → Fin N0 ⊕ Fin N0 := fun w => if x' w = y' w then Sum.inl w else Sum.inr w
      let π : Fin N0 ⊕ Fin N0 → Fin N0 := Sum.elim id id
      let γ_col : Fin N0 ⊕ Fin N0 → Fin q0 := Sum.elim x' y'
      have hπ_τ : ∀ w : Fin N0, π (τ w) = w := by
        intro w
        dsimp [π, τ]
        split_ifs <;> rfl
      have hγ_τ : ∀ w : Fin N0, γ_col (τ w) = y' w := by
        intro w
        dsimp [γ_col, τ]
        split_ifs with h
        · exact h
        · rfl
      have hτ_mem : ∀ w : Fin N0, (y' w = x w ∨ y' w = y w) → τ w ∈ S := by
        intro w hw
        dsimp [τ, S]
        split_ifs with heq_xy
        · rw [Finset.inl_mem_disjSum]
          simp only [K₁, Finset.mem_filter, Finset.mem_univ, true_and]
          rwa [heq_xy]
        · rw [Finset.inr_mem_disjSum]
          simp only [K₂, diffCoords, Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨heq_xy, hw⟩
      let α_map : Fin N0 × Fin N0 × Fin q0 × Fin q0 → Fin N0 ⊕ Fin N0 :=
        fun t => if t.2.2.1 = x' t.1 ∧ t.2.2.2 = x' t.2.1 then Sum.inl t.1 else τ t.1
      let β_map : Fin N0 × Fin N0 × Fin q0 × Fin q0 → Fin N0 ⊕ Fin N0 :=
        fun t => if t.2.2.1 = x' t.1 ∧ t.2.2.2 = x' t.2.1 then Sum.inl t.2.1 else τ t.2.1
      let Ψ : Fin N0 × Fin N0 × Fin q0 × Fin q0 → Finset (Fin N0 ⊕ Fin N0) :=
        fun t => {α_map t, β_map t}
      have hπ_α : ∀ t, π (α_map t) = t.1 := by
        intro t
        dsimp [α_map]
        split_ifs
        · rfl
        · exact hπ_τ t.1
      have hπ_β : ∀ t, π (β_map t) = t.2.1 := by
        intro t
        dsimp [β_map]
        split_ifs
        · rfl
        · exact hπ_τ t.2.1
      have h_props : ∀ t ∈ I,
          t.1 < t.2.1 ∧ α_map t ≠ β_map t ∧ α_map t ∈ S ∧ β_map t ∈ S ∧
          γ_col (α_map t) = t.2.2.1 ∧ γ_col (β_map t) = t.2.2.2 := by
        intro t ht
        simp only [I, Finset.mem_inter, Finset.mem_union, h_mem_hq] at ht
        have hlt : t.1 < t.2.1 := by
          rcases ht.1 with h | h <;> exact h.1
        have hc1_xy : t.2.2.1 = x t.1 ∨ t.2.2.1 = y t.1 := by
          rcases ht.1 with h | h
          · exact Or.inl h.2.1
          · exact Or.inr h.2.1
        have hc2_xy : t.2.2.2 = x t.2.1 ∨ t.2.2.2 = y t.2.1 := by
          rcases ht.1 with h | h
          · exact Or.inl h.2.2
          · exact Or.inr h.2.2
        have hne_αβ : α_map t ≠ β_map t := by
          intro heq
          have hp := congr_arg π heq
          rw [hπ_α, hπ_β] at hp
          exact (ne_of_lt hlt) hp
        refine ⟨hlt, hne_αβ, ?_⟩
        by_cases hx' : t.2.2.1 = x' t.1 ∧ t.2.2.2 = x' t.2.1
        · have hα_eq : α_map t = Sum.inl t.1 := if_pos hx'
          have hβ_eq : β_map t = Sum.inl t.2.1 := if_pos hx'
          rw [hα_eq, hβ_eq]
          refine ⟨?_, ?_, hx'.1.symm, hx'.2.symm⟩
          · rw [Finset.inl_mem_disjSum]
            simp only [K₁, Finset.mem_filter, Finset.mem_univ, true_and]
            rwa [← hx'.1]
          · rw [Finset.inl_mem_disjSum]
            simp only [K₁, Finset.mem_filter, Finset.mem_univ, true_and]
            rwa [← hx'.2]
        · have hy' : t.2.2.1 = y' t.1 ∧ t.2.2.2 = y' t.2.1 := by
            rcases ht.2 with h | h
            · exact absurd ⟨h.2.1, h.2.2⟩ hx'
            · exact ⟨h.2.1, h.2.2⟩
          have hα_eq : α_map t = τ t.1 := if_neg hx'
          have hβ_eq : β_map t = τ t.2.1 := if_neg hx'
          rw [hα_eq, hβ_eq]
          refine ⟨hτ_mem t.1 (by rwa [← hy'.1]), hτ_mem t.2.1 (by rwa [← hy'.2]), ?_, ?_⟩
          · rw [hγ_τ, hy'.1]
          · rw [hγ_τ, hy'.2]
      apply Finset.card_le_card_of_injOn Ψ
      · intro t ht
        rw [Finset.mem_coe] at ht ⊢
        obtain ⟨_, hne, hαS, hβS, _, _⟩ := h_props t ht
        rw [Finset.mem_powersetCard]
        refine ⟨?_, Finset.card_pair hne⟩
        intro z hz
        simp only [Ψ, Finset.mem_insert, Finset.mem_singleton] at hz
        rcases hz with rfl | rfl
        · exact hαS
        · exact hβS
      · intro t₁ ht₁ t₂ ht₂ heq
        rw [Finset.mem_coe] at ht₁ ht₂
        obtain ⟨hlt₁, hne₁, _, _, hγα₁, hγβ₁⟩ := h_props t₁ ht₁
        obtain ⟨hlt₂, _, _, _, hγα₂, hγβ₂⟩ := h_props t₂ ht₂
        have hα_mem : α_map t₁ ∈ ({α_map t₂, β_map t₂} : Finset _) := by
          change α_map t₁ ∈ Ψ t₂
          rw [← heq]
          exact Finset.mem_insert_self _ _
        have hβ_mem : β_map t₁ ∈ ({α_map t₂, β_map t₂} : Finset _) := by
          change β_map t₁ ∈ Ψ t₂
          rw [← heq]
          exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
        simp only [Finset.mem_insert, Finset.mem_singleton] at hα_mem hβ_mem
        have hα_eq : α_map t₁ = α_map t₂ := by
          rcases hα_mem with h1 | h1
          · exact h1
          · exfalso
            have hβ_eq : β_map t₁ = α_map t₂ := by
              rcases hβ_mem with h2 | h2
              · exact h2
              · exfalso; apply hne₁; rw [h1, h2]
            have hp1 := congr_arg π h1
            have hp2 := congr_arg π hβ_eq
            rw [hπ_α, hπ_β] at hp1
            rw [hπ_β, hπ_α] at hp2
            have : t₂.2.1 < t₂.2.1 := by
              calc
                t₂.2.1 = t₁.1 := hp1.symm
                _ < t₁.2.1 := hlt₁
                _ = t₂.1 := hp2
                _ < t₂.2.1 := hlt₂
            exact lt_irrefl _ this
        have hβ_eq : β_map t₁ = β_map t₂ := by
          rcases hβ_mem with h2 | h2
          · exfalso; apply hne₁; rw [hα_eq, h2]
          · exact h2
        have hu_eq : t₁.1 = t₂.1 := by
          have hp := congr_arg π hα_eq
          rwa [hπ_α, hπ_α] at hp
        have hv_eq : t₁.2.1 = t₂.2.1 := by
          have hp := congr_arg π hβ_eq
          rwa [hπ_β, hπ_β] at hp
        have hc1_eq : t₁.2.2.1 = t₂.2.2.1 := by
          rw [← hγα₁, ← hγα₂, hα_eq]
        have hc2_eq : t₁.2.2.2 = t₂.2.2.2 := by
          rw [← hγβ₁, ← hγβ₂, hβ_eq]
        rcases t₁ with ⟨u₁, v₁, c₁₁, c₁₂⟩
        rcases t₂ with ⟨u₂, v₂, c₂₁, c₂₂⟩
        simp only [Prod.mk.injEq] at hu_eq hv_eq hc1_eq hc2_eq ⊢
        exact ⟨hu_eq, hv_eq, hc1_eq, hc2_eq⟩
    · intro k₁ k₂ hk₁ _hk₂
      let K₁_of : (Fin N0 → Fin q0) → Finset (Fin N0) :=
        fun x' => Finset.univ.filter (fun v : Fin N0 => x' v = x v ∨ x' v = y v)
      let K₂_of : (Fin N0 → Fin q0) → (Fin N0 → Fin q0) → Finset (Fin N0) :=
        fun x' y' => (diffCoords x' y').filter (fun v : Fin N0 => y' v = x v ∨ y' v = y v)
      let F_pair := Finset.univ.filter (fun xy' : (Fin N0 → Fin q0) × (Fin N0 → Fin q0) =>
        dHam xy'.1 xy'.2 = r0 ∧ (K₁_of xy'.1).card = k₁ ∧ (K₂_of xy'.1 xy'.2).card = k₂)
      let X_fib := Finset.univ.filter (fun x' : Fin N0 → Fin q0 => (K₁_of x').card = k₁)
      let Y_fib : (Fin N0 → Fin q0) → Finset (Fin N0 → Fin q0) :=
        fun x' => Finset.univ.filter (fun y' : Fin N0 → Fin q0 =>
          dHam x' y' = r0 ∧ (K₂_of x' y').card = k₂)
      have hX_bound : X_fib.card ≤ N0.choose k₁ * 2 ^ k₁ * q0 ^ (N0 - k₁) := by
        let S_K₁ := (Finset.univ : Finset (Fin N0)).powersetCard k₁
        have hSK₁_card : S_K₁.card = N0.choose k₁ := by
          rw [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
        have hmaps_x : ∀ x' ∈ X_fib, K₁_of x' ∈ S_K₁ := by
          intro x' hx'
          simp only [X_fib, Finset.mem_filter, Finset.mem_univ, true_and] at hx'
          rw [Finset.mem_powersetCard]
          exact ⟨Finset.subset_univ _, hx'⟩
        have hfib_x : X_fib.card = ∑ K₁ ∈ S_K₁, (X_fib.filter (fun x' => K₁_of x' = K₁)).card := by
          simp_rw [Finset.card_eq_sum_ones]
          exact (Finset.sum_fiberwise_of_maps_to hmaps_x _).symm
        have hbx : ∀ K₁ ∈ S_K₁,
            (X_fib.filter (fun x' => K₁_of x' = K₁)).card ≤ 2 ^ k₁ * q0 ^ (N0 - k₁) := by
          intro K₁ hK₁
          have hK₁_card : K₁.card = k₁ := (Finset.mem_powersetCard.mp hK₁).2
          let _ := hk₁
          let U_target : Finset ((↥K₁ → Bool) × (↥(Finset.univ \ K₁) → Fin q0)) := Finset.univ
          have hU_card : U_target.card = 2 ^ k₁ * q0 ^ (N0 - k₁) := by
            simp [U_target, Fintype.card_bool, hK₁_card]
          rw [← hU_card]
          apply Finset.card_le_card_of_injOn
            (fun x' => ((fun v : ↥K₁ => decide (x' v.1 = x v.1)),
                        (fun w : ↥(Finset.univ \ K₁) => x' w.1)))
          · intro x' _; exact Finset.mem_coe.mpr (Finset.mem_univ _)
          · intro x'₁ hx₁ x'₂ hx₂ heq
            simp only [Finset.mem_coe, Finset.mem_filter] at hx₁ hx₂
            simp only [Prod.mk.injEq] at heq
            funext u
            by_cases hu : u ∈ K₁
            · have hdec := congr_fun heq.1 ⟨u, hu⟩
              have hu1 : u ∈ K₁_of x'₁ := by rwa [hx₁.2]
              have hu2 : u ∈ K₁_of x'₂ := by rwa [hx₂.2]
              simp only [K₁_of, Finset.mem_filter, Finset.mem_univ, true_and] at hu1 hu2
              by_cases hxu1 : x'₁ u = x u
              · simp [hxu1] at hdec
                rw [hxu1, hdec]
              · simp [hxu1] at hdec
                have hy1 : x'₁ u = y u := hu1.resolve_left hxu1
                have hy2 : x'₂ u = y u := hu2.resolve_left hdec
                rw [hy1, hy2]
            · exact congr_fun heq.2 ⟨u, Finset.mem_sdiff.mpr ⟨Finset.mem_univ u, hu⟩⟩
        rw [hfib_x, mul_assoc]
        calc
          ∑ K₁ ∈ S_K₁, (X_fib.filter (fun x' => K₁_of x' = K₁)).card
            ≤ S_K₁.card • (2 ^ k₁ * q0 ^ (N0 - k₁)) := Finset.sum_le_card_nsmul _ _ _ hbx
          _ = N0.choose k₁ * (2 ^ k₁ * q0 ^ (N0 - k₁)) := by rw [hSK₁_card, smul_eq_mul]
      have hY_bound : ∀ x' : Fin N0 → Fin q0,
          (Y_fib x').card ≤ N0.choose r0 * r0.choose k₂ * 2 ^ k₂ * (q0 - 1) ^ (r0 - k₂) := by
        intro x'
        let S_D := (Finset.univ : Finset (Fin N0)).powersetCard r0
        have hSD_card : S_D.card = N0.choose r0 := by
          rw [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
        have hmaps_D : ∀ y' ∈ Y_fib x', diffCoords x' y' ∈ S_D := by
          intro y' hy'
          simp only [Y_fib, Finset.mem_filter, Finset.mem_univ, true_and] at hy'
          rw [Finset.mem_powersetCard]
          exact ⟨Finset.subset_univ _, hy'.1⟩
        have hfib_D : (Y_fib x').card =
            ∑ D ∈ S_D, ((Y_fib x').filter (fun y' => diffCoords x' y' = D)).card := by
          simp_rw [Finset.card_eq_sum_ones]
          exact (Finset.sum_fiberwise_of_maps_to hmaps_D _).symm
        have hbD : ∀ D ∈ S_D,
            ((Y_fib x').filter (fun y' => diffCoords x' y' = D)).card ≤
              r0.choose k₂ * (2 ^ k₂ * (q0 - 1) ^ (r0 - k₂)) := by
          intro D hD
          have hD_card : D.card = r0 := (Finset.mem_powersetCard.mp hD).2
          let S_K₂ := D.powersetCard k₂
          have hSK₂_card : S_K₂.card = r0.choose k₂ := by
            rw [Finset.card_powersetCard, hD_card]
          have hmaps_K₂ : ∀ y' ∈ (Y_fib x').filter (fun y' => diffCoords x' y' = D),
              K₂_of x' y' ∈ S_K₂ := by
            intro y' hy'
            simp only [Y_fib, Finset.mem_filter, Finset.mem_univ, true_and] at hy'
            rw [Finset.mem_powersetCard]
            refine ⟨?_, hy'.1.2⟩
            rw [← hy'.2]
            exact Finset.filter_subset _ _
          have hfib_K₂ : ((Y_fib x').filter (fun y' => diffCoords x' y' = D)).card =
              ∑ K₂ ∈ S_K₂, (((Y_fib x').filter (fun y' => diffCoords x' y' = D)).filter
                (fun y' => K₂_of x' y' = K₂)).card := by
            simp_rw [Finset.card_eq_sum_ones]
            exact (Finset.sum_fiberwise_of_maps_to hmaps_K₂ _).symm
          have hbK₂ : ∀ K₂ ∈ S_K₂,
              (((Y_fib x').filter (fun y' => diffCoords x' y' = D)).filter
                (fun y' => K₂_of x' y' = K₂)).card ≤ 2 ^ k₂ * (q0 - 1) ^ (r0 - k₂) := by
            intro K₂ hK₂
            obtain ⟨hK₂_sub, hK₂_card⟩ := Finset.mem_powersetCard.mp hK₂
            have hsdiff_card : (D \ K₂).card = r0 - k₂ := by
              have hadd := Finset.card_sdiff_add_card_eq_card hK₂_sub
              rw [hD_card, hK₂_card] at hadd
              omega
            let B_univ : Finset (↥K₂ → Bool) := Finset.univ
            let P_rem := Fintype.piFinset (fun w : ↥(D \ K₂) => Finset.univ.erase (x' w.1))
            have hBP_card : (B_univ ×ˢ P_rem).card = 2 ^ k₂ * (q0 - 1) ^ (r0 - k₂) := by
              rw [Finset.card_product]
              have hB : B_univ.card = 2 ^ k₂ := by simp [B_univ, Fintype.card_bool, hK₂_card]
              have hP : P_rem.card = (q0 - 1) ^ (r0 - k₂) := by
                rw [Fintype.card_piFinset]
                have h1 : ∀ w : ↥(D \ K₂), (Finset.univ.erase (x' w.1)).card = q0 - 1 := by
                  intro w
                  rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
                simp_rw [h1]
                simp [Finset.prod_const, hsdiff_card]
              rw [hB, hP]
            rw [← hBP_card]
            apply Finset.card_le_card_of_injOn
              (fun y' => ((fun v : ↥K₂ => decide (y' v.1 = x v.1)),
                          (fun w : ↥(D \ K₂) => y' w.1)))
            · intro y' hy'
              simp only [Finset.mem_coe, Finset.mem_filter] at hy'
              rw [Finset.mem_coe, Finset.mem_product]
              refine ⟨Finset.mem_univ _, Fintype.mem_piFinset.mpr (fun w => ?_)⟩
              have hwD : w.1 ∈ diffCoords x' y' := by
                rw [hy'.1.2]
                exact (Finset.mem_sdiff.mp w.2).1
              simp only [diffCoords, Finset.mem_filter, Finset.mem_univ, true_and] at hwD
              exact Finset.mem_erase.mpr ⟨hwD.symm, Finset.mem_univ _⟩
            · intro y'₁ hy₁ y'₂ hy₂ heq
              simp only [Finset.mem_coe, Finset.mem_filter] at hy₁ hy₂
              simp only [Prod.mk.injEq] at heq
              funext u
              by_cases huK₂ : u ∈ K₂
              · have hdec := congr_fun heq.1 ⟨u, huK₂⟩
                have hu1 : u ∈ K₂_of x' y'₁ := by rwa [hy₁.2]
                have hu2 : u ∈ K₂_of x' y'₂ := by rwa [hy₂.2]
                simp only [K₂_of, Finset.mem_filter] at hu1 hu2
                by_cases hxu1 : y'₁ u = x u
                · simp [hxu1] at hdec
                  rw [hxu1, hdec]
                · simp [hxu1] at hdec
                  have hyu1 : y'₁ u = y u := hu1.2.resolve_left hxu1
                  have hyu2 : y'₂ u = y u := hu2.2.resolve_left hdec
                  rw [hyu1, hyu2]
              · by_cases huD : u ∈ D
                · exact congr_fun heq.2 ⟨u, Finset.mem_sdiff.mpr ⟨huD, huK₂⟩⟩
                · have hn1 : u ∉ diffCoords x' y'₁ := by rwa [hy₁.1.2]
                  have hn2 : u ∉ diffCoords x' y'₂ := by rwa [hy₂.1.2]
                  simp only [diffCoords, Finset.mem_filter, Finset.mem_univ, true_and, not_not] at hn1 hn2
                  rw [← hn1, ← hn2]
          rw [hfib_K₂]
          calc
            ∑ K₂ ∈ S_K₂, (((Y_fib x').filter (fun y' => diffCoords x' y' = D)).filter
                (fun y' => K₂_of x' y' = K₂)).card
              ≤ S_K₂.card • (2 ^ k₂ * (q0 - 1) ^ (r0 - k₂)) := Finset.sum_le_card_nsmul _ _ _ hbK₂
            _ = r0.choose k₂ * (2 ^ k₂ * (q0 - 1) ^ (r0 - k₂)) := by
                rw [hSK₂_card, smul_eq_mul]
        calc
          (Y_fib x').card
            = ∑ D ∈ S_D, ((Y_fib x').filter (fun y' => diffCoords x' y' = D)).card := hfib_D
          _ ≤ S_D.card • (r0.choose k₂ * (2 ^ k₂ * (q0 - 1) ^ (r0 - k₂))) :=
              Finset.sum_le_card_nsmul _ _ _ hbD
          _ = N0.choose r0 * r0.choose k₂ * 2 ^ k₂ * (q0 - 1) ^ (r0 - k₂) := by
              rw [hSD_card, smul_eq_mul]
              ring
      have hmaps_pair : ∀ xy' ∈ F_pair, xy'.1 ∈ X_fib := by
        intro xy' hxy'
        simp only [F_pair, X_fib, Finset.mem_filter, Finset.mem_univ, true_and] at hxy' ⊢
        exact hxy'.2.1
      have hfib_pair : F_pair.card = ∑ x' ∈ X_fib, (F_pair.filter (fun xy' => xy'.1 = x')).card := by
        simp_rw [Finset.card_eq_sum_ones]
        exact (Finset.sum_fiberwise_of_maps_to hmaps_pair _).symm
      have hpair_snd : ∀ x' ∈ X_fib, (F_pair.filter (fun xy' => xy'.1 = x')).card ≤ (Y_fib x').card := by
        intro x' _
        apply Finset.card_le_card_of_injOn Prod.snd
        · intro xy' hxy'
          simp only [F_pair, Y_fib, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hxy' ⊢
          rw [← hxy'.2]
          exact ⟨hxy'.1.1, hxy'.1.2.2⟩
        · intro a ha b hb heq
          simp only [Finset.mem_coe, Finset.mem_filter] at ha hb
          exact Prod.ext (ha.2.trans hb.2.symm) heq
      change F_pair.card ≤ _
      rw [hfib_pair]
      calc
        ∑ x' ∈ X_fib, (F_pair.filter (fun xy' => xy'.1 = x')).card
          ≤ X_fib.card • (N0.choose r0 * r0.choose k₂ * 2 ^ k₂ * (q0 - 1) ^ (r0 - k₂)) := by
            refine Finset.sum_le_card_nsmul _ _ _ (fun x' hx' => ?_)
            exact le_trans (hpair_snd x' hx') (hY_bound x')
        _ = X_fib.card * (N0.choose r0 * r0.choose k₂ * 2 ^ k₂ * (q0 - 1) ^ (r0 - k₂)) :=
            smul_eq_mul _ _
        _ ≤ (N0.choose k₁ * 2 ^ k₁ * q0 ^ (N0 - k₁)) *
              (N0.choose r0 * r0.choose k₂ * 2 ^ k₂ * (q0 - 1) ^ (r0 - k₂)) :=
            Nat.mul_le_mul_right _ hX_bound

  have h_exp_gamma : ∀ r0 : ℕ,
      Real.exp ((r0 : ℝ) * ((2 : ℝ) ^ (- (999 : ℝ)))) ≤ cspGamma r0 := by
    intro r0
    unfold cspGamma
    conv_rhs => rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
    apply Real.exp_le_exp.mpr
    have h999 : (2 : ℝ) ^ (- (999 : ℝ)) = (1 / 2 : ℝ) / ((2 : ℝ) ^ (998 : ℕ)) := by
      have h1 : (- (999 : ℝ)) = (- (1 : ℝ)) - ((998 : ℕ) : ℝ) := by push_cast; norm_num
      rw [h1, Real.rpow_sub (by norm_num : (0 : ℝ) < 2),
        show (2 : ℝ) ^ (- (1 : ℝ)) = 1 / 2 by norm_num, Real.rpow_natCast]
    rw [h999]
    have hrew : (r0 : ℝ) * ((1 / 2 : ℝ) / ((2 : ℝ) ^ (998 : ℕ))) =
        (1 / 2 : ℝ) * ((r0 : ℝ) / ((2 : ℝ) ^ (998 : ℕ))) := by
      generalize ((2 : ℝ) ^ (998 : ℕ)) = d998
      ring
    rw [hrew]
    have hlog : (1 / 2 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
    have hden_pos : (0 : ℝ) < (2 : ℝ) ^ (998 : ℕ) := pow_pos (by norm_num) 998
    have hfrac_nn : (0 : ℝ) ≤ (r0 : ℝ) / ((2 : ℝ) ^ (998 : ℕ)) :=
      div_nonneg (Nat.cast_nonneg r0) (le_of_lt hden_pos)
    exact mul_le_mul_of_nonneg_right hlog hfrac_nn

  have h_hypergeom_abs : ∀ (L r0 q1 lam0 gamma0 : ℕ) (σ D_star : ℝ),
      3001 ≤ r0 → 1 ≤ q1 → 3000 ≤ lam0 → gamma0 = 5 * lam0 → 0 < σ → 0 ≤ D_star →
      (4 : ℝ) * (2 : ℝ) ^ L * (q1 : ℝ) * ((2 : ℝ) ^ (- σ)) ^ (2 ^ L * r0 - 1) =
        (2 : ℝ) ^ (- (gamma0 : ℝ)) →
      6 * (lam0 : ℝ) ≤ σ * (r0 : ℝ) / 2 →
      let N0 := 2 ^ L * r0
      let p_e := (2 : ℝ) ^ (- σ)
      let D_om := (N0.choose r0 : ℝ) * (q1 : ℝ) ^ r0 * p_e ^ (r0 * (N0 - 1) - r0.choose 2)
      ∑ b ∈ Finset.range (r0 + 1),
        (D_star / D_om) *
          (((r0.choose b : ℝ) * (((N0 - b).choose (r0 - b) : ℕ) : ℝ) * (q1 : ℝ) ^ (r0 - b)) *
           p_e ^ ((r0 - b) * (N0 - 1) - (r0 - b).choose 2)) ≤
        (3 / 2 : ℝ) * cspGamma r0 * D_star := by
    intro L r0 q1 lam0 gamma0 σ D_star hr_ge hq1_pos_nat hlam0_ge hgam_eq hσ_pos0 hD_nn h_cal0 hσ_low0 N0 p_e D_om
    have h1_le_2L : 1 ≤ 2 ^ L := Nat.one_le_two_pow
    have hrN : r0 ≤ N0 := Nat.le_mul_of_pos_left r0 h1_le_2L
    have hq1_pos : (0 : ℝ) < (q1 : ℝ) := by exact_mod_cast (show 0 < q1 by omega)
    have hpe_pos : 0 < p_e := Real.rpow_pos_of_pos (by norm_num) (- σ)
    let G : ℝ := (2 : ℝ) ^ (gamma0 : ℝ)
    have hG_pos : 0 < G := Real.rpow_pos_of_pos (by norm_num) (gamma0 : ℝ)
    have h_cal1 : (4 : ℝ) * G * (2 : ℝ) ^ L * (q1 : ℝ) * p_e ^ (N0 - 1) = 1 := by
      have hmul : G * ((4 : ℝ) * (2 : ℝ) ^ L * (q1 : ℝ) * p_e ^ (N0 - 1)) = 1 := by
        change G * ((4 : ℝ) * (2 : ℝ) ^ L * (q1 : ℝ) * ((2 : ℝ) ^ (- σ)) ^ (2 ^ L * r0 - 1)) = 1
        rw [h_cal0]
        dsimp [G]
        rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2), add_neg_cancel, Real.rpow_zero]
      linarith
    have h_binom_ratio : ∀ b : ℕ, b ≤ r0 →
        (N0 - b).choose (r0 - b) * (2 ^ L) ^ b ≤ N0.choose r0 := by
      intro b
      induction b with
      | zero =>
        intro _
        simp
      | succ b ih =>
        intro hb1
        have hr'_pos : 1 ≤ r0 - b := by omega
        have hb_le_2Lb : b ≤ 2 ^ L * b := Nat.le_mul_of_pos_left b h1_le_2L
        have h2Lr_sum : 2 ^ L * (r0 - b) + 2 ^ L * b = N0 := by
          dsimp [N0]
          rw [← mul_add, show r0 - b + b = r0 by omega]
        have h2Lr_le : 2 ^ L * (r0 - b) ≤ N0 - b := by omega
        have habs : (N0 - b) * (N0 - b - 1).choose (r0 - b - 1) =
            (N0 - b).choose (r0 - b) * (r0 - b) := by
          have h := Nat.add_one_mul_choose_eq (N0 - b - 1) (r0 - b - 1)
          rwa [show N0 - b - 1 + 1 = N0 - b by omega, show r0 - b - 1 + 1 = r0 - b by omega] at h
        have hmul_step : ((N0 - b - 1).choose (r0 - b - 1) * 2 ^ L) * (r0 - b) ≤
            (N0 - b).choose (r0 - b) * (r0 - b) := by
          calc
            ((N0 - b - 1).choose (r0 - b - 1) * 2 ^ L) * (r0 - b)
              = (N0 - b - 1).choose (r0 - b - 1) * (2 ^ L * (r0 - b)) := mul_assoc _ _ _
            _ ≤ (N0 - b - 1).choose (r0 - b - 1) * (N0 - b) := Nat.mul_le_mul_left _ h2Lr_le
            _ = (N0 - b) * (N0 - b - 1).choose (r0 - b - 1) := mul_comm _ _
            _ = (N0 - b).choose (r0 - b) * (r0 - b) := habs
        have hstep : (N0 - b - 1).choose (r0 - b - 1) * 2 ^ L ≤ (N0 - b).choose (r0 - b) :=
          Nat.le_of_mul_le_mul_right hmul_step (by omega)
        rw [show N0 - (b + 1) = N0 - b - 1 by omega, show r0 - (b + 1) = r0 - b - 1 by omega,
          pow_succ']
        calc
          (N0 - b - 1).choose (r0 - b - 1) * (2 ^ L * (2 ^ L) ^ b)
            = ((N0 - b - 1).choose (r0 - b - 1) * 2 ^ L) * (2 ^ L) ^ b := (mul_assoc _ _ _).symm
          _ ≤ (N0 - b).choose (r0 - b) * (2 ^ L) ^ b := Nat.mul_le_mul_right _ hstep
          _ ≤ N0.choose r0 := ih (by omega)
    have hDOm_pos : 0 < D_om := by
      dsimp [D_om]
      have hch_pos : (0 : ℝ) < (N0.choose r0 : ℝ) := by exact_mod_cast (Nat.choose_pos hrN)
      exact mul_pos (mul_pos hch_pos (pow_pos hq1_pos r0)) (pow_pos hpe_pos _)
    let ε : ℝ := (2 : ℝ) ^ (- (999 : ℝ))
    have h_term : ∀ b ∈ Finset.range (r0 + 1),
        (D_star / D_om) *
          (((r0.choose b : ℝ) * (((N0 - b).choose (r0 - b) : ℕ) : ℝ) * (q1 : ℝ) ^ (r0 - b)) *
           p_e ^ ((r0 - b) * (N0 - 1) - (r0 - b).choose 2)) ≤
        D_star * ((r0.choose b : ℝ) * ε ^ b) := by
      intro b hb_mem
      have hb : b ≤ r0 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hb_mem)
      let E_r := r0 * (N0 - 1) - r0.choose 2
      let E_s := (r0 - b) * (N0 - 1) - (r0 - b).choose 2
      let Δ_b := r0.choose 2 - (r0 - b).choose 2
      have hch_mono : (r0 - b).choose 2 ≤ r0.choose 2 :=
        Nat.choose_le_choose 2 (Nat.sub_le r0 b)
      have hch_r : r0.choose 2 ≤ r0 * (N0 - 1) := h_ch2_le hrN
      have hch_s : (r0 - b).choose 2 ≤ (r0 - b) * (N0 - 1) :=
        h_ch2_le (le_trans (Nat.sub_le _ _) hrN)
      have hmul_split : (r0 - b) * (N0 - 1) + b * (N0 - 1) = r0 * (N0 - 1) := by
        rw [← add_mul, Nat.sub_add_cancel hb]
      have hexp_id : E_s + b * (N0 - 1) = E_r + Δ_b := by omega
      have hcal_b : (4 : ℝ) ^ b * G ^ b * ((2 : ℝ) ^ L) ^ b * (q1 : ℝ) ^ b * p_e ^ (b * (N0 - 1)) = 1 := by
        have hp := congr_arg (· ^ b) h_cal1
        change ((4 : ℝ) * G * (2 : ℝ) ^ L * (q1 : ℝ) * p_e ^ (N0 - 1)) ^ b = 1 ^ b at hp
        rw [one_pow, mul_pow, mul_pow, mul_pow, mul_pow, ← pow_mul p_e (N0 - 1) b, mul_comm (N0 - 1) b] at hp
        exact hp
      have hq_pow : (q1 : ℝ) ^ (r0 - b) * (q1 : ℝ) ^ b = (q1 : ℝ) ^ r0 := by
        rw [← pow_add, Nat.sub_add_cancel hb]
      have hpe_pow : p_e ^ E_s * p_e ^ (b * (N0 - 1)) = p_e ^ E_r * p_e ^ Δ_b := by
        rw [← pow_add, hexp_id, pow_add]
      have hbin_real : (((N0 - b).choose (r0 - b) : ℕ) : ℝ) * ((2 : ℝ) ^ L) ^ b ≤
          (N0.choose r0 : ℝ) := by
        have hcast : (((N0 - b).choose (r0 - b) * (2 ^ L) ^ b : ℕ) : ℝ) ≤ (N0.choose r0 : ℝ) := by
          exact_mod_cast h_binom_ratio b hb
        push_cast at hcast
        exact hcast
      have hT_le : (((r0.choose b : ℝ) * (((N0 - b).choose (r0 - b) : ℕ) : ℝ) * (q1 : ℝ) ^ (r0 - b)) *
          p_e ^ E_s) ≤
          D_om * ((r0.choose b : ℝ) * ((4 : ℝ) ^ b * G ^ b * p_e ^ Δ_b)) := by
        have h1 : (((r0.choose b : ℝ) * (((N0 - b).choose (r0 - b) : ℕ) : ℝ) * (q1 : ℝ) ^ (r0 - b)) *
            p_e ^ E_s) =
            ((((N0 - b).choose (r0 - b) : ℕ) : ℝ) * ((2 : ℝ) ^ L) ^ b) *
            ((r0.choose b : ℝ) * (4 : ℝ) ^ b * G ^ b * (q1 : ℝ) ^ r0 * p_e ^ E_r * p_e ^ Δ_b) := by
          calc
            (((r0.choose b : ℝ) * (((N0 - b).choose (r0 - b) : ℕ) : ℝ) * (q1 : ℝ) ^ (r0 - b)) * p_e ^ E_s)
              = (((r0.choose b : ℝ) * (((N0 - b).choose (r0 - b) : ℕ) : ℝ) * (q1 : ℝ) ^ (r0 - b)) * p_e ^ E_s) *
                ((4 : ℝ) ^ b * G ^ b * ((2 : ℝ) ^ L) ^ b * (q1 : ℝ) ^ b * p_e ^ (b * (N0 - 1))) := by
                  rw [hcal_b, mul_one]
            _ = ((((N0 - b).choose (r0 - b) : ℕ) : ℝ) * ((2 : ℝ) ^ L) ^ b) *
                ((r0.choose b : ℝ) * (4 : ℝ) ^ b * G ^ b * ((q1 : ℝ) ^ (r0 - b) * (q1 : ℝ) ^ b) *
                 (p_e ^ E_s * p_e ^ (b * (N0 - 1)))) := by ring
            _ = ((((N0 - b).choose (r0 - b) : ℕ) : ℝ) * ((2 : ℝ) ^ L) ^ b) *
                ((r0.choose b : ℝ) * (4 : ℝ) ^ b * G ^ b * (q1 : ℝ) ^ r0 * p_e ^ E_r * p_e ^ Δ_b) := by
                  rw [hq_pow, hpe_pow]
                  ring
        rw [h1]
        have hnn : 0 ≤ (r0.choose b : ℝ) * (4 : ℝ) ^ b * G ^ b * (q1 : ℝ) ^ r0 * p_e ^ E_r * p_e ^ Δ_b :=
          mul_nonneg
            (mul_nonneg
              (mul_nonneg
                (mul_nonneg
                  (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (by norm_num) b))
                  (pow_nonneg (le_of_lt hG_pos) b))
                (pow_nonneg (le_of_lt hq1_pos) r0))
              (pow_nonneg (le_of_lt hpe_pos) E_r))
            (pow_nonneg (le_of_lt hpe_pos) Δ_b)
        calc
          ((((N0 - b).choose (r0 - b) : ℕ) : ℝ) * ((2 : ℝ) ^ L) ^ b) *
              ((r0.choose b : ℝ) * (4 : ℝ) ^ b * G ^ b * (q1 : ℝ) ^ r0 * p_e ^ E_r * p_e ^ Δ_b)
            ≤ (N0.choose r0 : ℝ) *
              ((r0.choose b : ℝ) * (4 : ℝ) ^ b * G ^ b * (q1 : ℝ) ^ r0 * p_e ^ E_r * p_e ^ Δ_b) :=
                mul_le_mul_of_nonneg_right hbin_real hnn
          _ = D_om * ((r0.choose b : ℝ) * ((4 : ℝ) ^ b * G ^ b * p_e ^ Δ_b)) := by
                dsimp [D_om]
                ring
      have hΔ_quad_nat : b * (r0 - 1) ≤ 2 * Δ_b := by
        have hc1 := h_two_ch2 (r0 - b)
        have hc2 := h_two_ch2 r0
        have hle1 : (r0 - b) * (r0 - b - 1) ≤ (r0 - b) * (r0 - 1) :=
          Nat.mul_le_mul_left _ (by omega)
        have hadd1 : (r0 - b) * (r0 - 1) + b * (r0 - 1) = r0 * (r0 - 1) := by
          rw [← add_mul, Nat.sub_add_cancel hb]
        omega
      have hΔ_quad_real : (b : ℝ) * ((r0 : ℝ) - 1) ≤ 2 * (Δ_b : ℝ) := by
        have hcast : ((b * (r0 - 1) : ℕ) : ℝ) ≤ ((2 * Δ_b : ℕ) : ℝ) := by exact_mod_cast hΔ_quad_nat
        rw [Nat.cast_mul, Nat.cast_sub (by omega : 1 ≤ r0), Nat.cast_one, Nat.cast_mul,
          Nat.cast_ofNat] at hcast
        exact hcast
      have hdecay : (4 : ℝ) ^ b * G ^ b * p_e ^ Δ_b ≤ ε ^ b := by
        have h4_eq : (4 : ℝ) ^ b = (2 : ℝ) ^ (2 * (b : ℝ)) := by
          have h4 : (4 : ℝ) = (2 : ℝ) ^ (2 : ℝ) := by norm_num
          rw [h4, ← Real.rpow_natCast ((2 : ℝ) ^ (2 : ℝ)) b,
            ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
        have hG_eq : G ^ b = (2 : ℝ) ^ ((gamma0 : ℝ) * (b : ℝ)) := by
          dsimp [G]
          rw [← Real.rpow_natCast _ b, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
        have hpe_eq : p_e ^ Δ_b = (2 : ℝ) ^ (- σ * (Δ_b : ℝ)) := by
          dsimp [p_e]
          rw [← Real.rpow_natCast _ Δ_b, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
        have hε_eq : ε ^ b = (2 : ℝ) ^ (- (999 : ℝ) * (b : ℝ)) := by
          dsimp [ε]
          rw [← Real.rpow_natCast _ b, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
        rw [h4_eq, hG_eq, hpe_eq, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2),
          ← Real.rpow_add (by norm_num : (0 : ℝ) < 2), hε_eq]
        apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
        have hr_real : (3001 : ℝ) ≤ (r0 : ℝ) := by exact_mod_cast hr_ge
        have hlam0_real : (3000 : ℝ) ≤ (lam0 : ℝ) := by exact_mod_cast hlam0_ge
        have hgam_real : (gamma0 : ℝ) = 5 * (lam0 : ℝ) := by
          rw [hgam_eq]
          push_cast
          ring
        have hb_nn : (0 : ℝ) ≤ (b : ℝ) := Nat.cast_nonneg b
        have hlam0_nn : (0 : ℝ) ≤ (lam0 : ℝ) := Nat.cast_nonneg lam0
        have hr0_pos : (0 : ℝ) < 2 * (r0 : ℝ) := by linarith only [hr_real]
        have hbr1_nn : (0 : ℝ) ≤ (b : ℝ) * ((r0 : ℝ) - 1) :=
          mul_nonneg hb_nn (by linarith only [hr_real])
        have hm1 : (12 * (lam0 : ℝ)) * ((b : ℝ) * ((r0 : ℝ) - 1)) ≤
            (σ * (r0 : ℝ)) * ((b : ℝ) * ((r0 : ℝ) - 1)) :=
          mul_le_mul_of_nonneg_right (by linarith only [hσ_low0]) hbr1_nn
        have hm2 : (σ * (r0 : ℝ)) * ((b : ℝ) * ((r0 : ℝ) - 1)) ≤
            (σ * (r0 : ℝ)) * (2 * (Δ_b : ℝ)) :=
          mul_le_mul_of_nonneg_left hΔ_quad_real
            (mul_nonneg (le_of_lt hσ_pos0) (by linarith only [hr_real]))
        have hm3 : 12 * ((lam0 : ℝ) * (b : ℝ)) ≤ (r0 : ℝ) * ((lam0 : ℝ) * (b : ℝ)) :=
          mul_le_mul_of_nonneg_right (by linarith only [hr_real]) (mul_nonneg hlam0_nn hb_nn)
        have hm4 : 3000 * ((b : ℝ) * (r0 : ℝ)) ≤ (lam0 : ℝ) * ((b : ℝ) * (r0 : ℝ)) :=
          mul_le_mul_of_nonneg_right hlam0_real (mul_nonneg hb_nn (by linarith only [hr_real]))
        have hscaled : (2 * (r0 : ℝ)) * (2 * (b : ℝ) + (gamma0 : ℝ) * (b : ℝ) + - σ * (Δ_b : ℝ)) ≤
            (2 * (r0 : ℝ)) * (- (999 : ℝ) * (b : ℝ)) := by
          rw [hgam_real]
          linarith [hm1, hm2, hm3, hm4,
            show (12 * (lam0 : ℝ)) * ((b : ℝ) * ((r0 : ℝ) - 1)) =
              12 * ((lam0 : ℝ) * ((b : ℝ) * (r0 : ℝ))) - 12 * ((lam0 : ℝ) * (b : ℝ)) by ring,
            show (σ * (r0 : ℝ)) * (2 * (Δ_b : ℝ)) = 2 * (r0 : ℝ) * (σ * (Δ_b : ℝ)) by ring,
            show (r0 : ℝ) * ((lam0 : ℝ) * (b : ℝ)) = (lam0 : ℝ) * ((b : ℝ) * (r0 : ℝ)) by ring,
            show (2 * (r0 : ℝ)) * (2 * (b : ℝ) + 5 * (lam0 : ℝ) * (b : ℝ) + - σ * (Δ_b : ℝ)) =
              4 * ((b : ℝ) * (r0 : ℝ)) + 10 * ((lam0 : ℝ) * ((b : ℝ) * (r0 : ℝ))) -
                2 * (r0 : ℝ) * (σ * (Δ_b : ℝ)) by ring,
            show (2 * (r0 : ℝ)) * (- (999 : ℝ) * (b : ℝ)) = - 1998 * ((b : ℝ) * (r0 : ℝ)) by ring]
        exact le_of_mul_le_mul_left hscaled hr0_pos
      calc
        (D_star / D_om) *
            (((r0.choose b : ℝ) * (((N0 - b).choose (r0 - b) : ℕ) : ℝ) * (q1 : ℝ) ^ (r0 - b)) *
             p_e ^ E_s)
          ≤ (D_star / D_om) * (D_om * ((r0.choose b : ℝ) * ((4 : ℝ) ^ b * G ^ b * p_e ^ Δ_b))) :=
            mul_le_mul_of_nonneg_left hT_le (div_nonneg hD_nn (le_of_lt hDOm_pos))
        _ = D_star * ((r0.choose b : ℝ) * ((4 : ℝ) ^ b * G ^ b * p_e ^ Δ_b)) := by
            have hne : D_om ≠ 0 := ne_of_gt hDOm_pos
            field_simp [hne]
        _ ≤ D_star * ((r0.choose b : ℝ) * ε ^ b) := by
            refine mul_le_mul_of_nonneg_left ?_ hD_nn
            exact mul_le_mul_of_nonneg_left hdecay (Nat.cast_nonneg _)
    have hsum_bin : ∑ b ∈ Finset.range (r0 + 1), (r0.choose b : ℝ) * ε ^ b = (ε + 1) ^ r0 := by
      rw [add_pow]
      refine Finset.sum_congr rfl (fun b _ => ?_)
      simp [mul_comm]
    have hε_pos : 0 < ε := Real.rpow_pos_of_pos (by norm_num) _
    have hexp_bound : (ε + 1) ^ r0 ≤ (3 / 2 : ℝ) * cspGamma r0 := by
      have h1 : (ε + 1) ^ r0 ≤ Real.exp ((r0 : ℝ) * ε) := by
        calc
          (ε + 1) ^ r0 ≤ (Real.exp ε) ^ r0 :=
            pow_le_pow_left₀ (by linarith) (Real.add_one_le_exp ε) r0
          _ = Real.exp ((r0 : ℝ) * ε) := (Real.exp_nat_mul ε r0).symm
      have h2 : Real.exp ((r0 : ℝ) * ε) ≤ cspGamma r0 := h_exp_gamma r0
      have hγ_nn : 0 ≤ cspGamma r0 := by
        unfold cspGamma
        exact Real.rpow_nonneg (by norm_num) _
      linarith only [h1, h2, hγ_nn]
    calc
      ∑ b ∈ Finset.range (r0 + 1),
          (D_star / D_om) *
            (((r0.choose b : ℝ) * (((N0 - b).choose (r0 - b) : ℕ) : ℝ) * (q1 : ℝ) ^ (r0 - b)) *
             p_e ^ ((r0 - b) * (N0 - 1) - (r0 - b).choose 2))
        ≤ ∑ b ∈ Finset.range (r0 + 1), D_star * ((r0.choose b : ℝ) * ε ^ b) :=
          Finset.sum_le_sum h_term
      _ = D_star * (∑ b ∈ Finset.range (r0 + 1), (r0.choose b : ℝ) * ε ^ b) :=
          (Finset.mul_sum _ _ _).symm
      _ = D_star * (ε + 1) ^ r0 := by rw [hsum_bin]
      _ ≤ D_star * ((3 / 2 : ℝ) * cspGamma r0) :=
          mul_le_mul_of_nonneg_left hexp_bound hD_nn
      _ = (3 / 2 : ℝ) * cspGamma r0 * D_star := by ring

  have h_vand_abs : ∀ (L beta0 gamma0 r0 : ℕ),
      20 ≤ L → 1000 ≤ beta0 → gamma0 ≤ L → 3001 ≤ r0 →
      let N0 := 2 ^ L * r0
      let E_q := 2 * beta0 * 2 ^ L
      let σ := ((E_q + L + gamma0 + 2 : ℕ) : ℝ) / ((N0 - 1 : ℕ) : ℝ)
      let p_e := (2 : ℝ) ^ (- σ)
      ∑ k₁ ∈ Finset.range (N0 + 1),
        ∑ k₂ ∈ Finset.range (r0 + 1),
          ((N0.choose k₁ : ℕ) : ℝ) *
          ((r0.choose k₂ : ℕ) : ℝ) *
          ((2 : ℝ) / ((2 ^ E_q : ℕ) : ℝ)) ^ (k₁ + k₂) *
          (p_e⁻¹) ^ ((k₁ + k₂).choose 2) ≤
        2 * cspGamma r0 := by
    intro L beta0 gamma0 r0 hL_ge20 hbeta0_ge hgam_le_L hr_ge N0 E_q σ p_e
    let M := N0 + r0
    let w : ℕ → ℝ := fun k => ((2 : ℝ) / ((2 ^ E_q : ℕ) : ℝ)) ^ k * (p_e⁻¹) ^ (k.choose 2)
    have h2L_gt_L : L + 1 ≤ 2 ^ L := Nat.lt_two_pow_self
    have h2L_ge21 : 21 ≤ 2 ^ L := by omega
    have hN_ge2 : 2 ≤ N0 := by
      dsimp [N0]
      have : 21 * 3001 ≤ 2 ^ L * r0 := Nat.mul_le_mul h2L_ge21 hr_ge
      omega
    have hpe_pos : 0 < p_e := Real.rpow_pos_of_pos (by norm_num) (- σ)
    have hw_nn : ∀ k : ℕ, 0 ≤ w k := by
      intro k
      dsimp [w]
      exact mul_nonneg
        (pow_nonneg (div_nonneg (by norm_num) (Nat.cast_nonneg _)) k)
        (pow_nonneg (inv_nonneg.mpr (le_of_lt hpe_pos)) _)
    have h_vand :
        ∑ k₁ ∈ Finset.range (N0 + 1),
          ∑ k₂ ∈ Finset.range (r0 + 1),
            ((N0.choose k₁ : ℕ) : ℝ) * ((r0.choose k₂ : ℕ) : ℝ) * w (k₁ + k₂) ≤
        ∑ k ∈ Finset.range (M + 1), (M.choose k : ℝ) * w k := by
      let S_prod := Finset.range (N0 + 1) ×ˢ Finset.range (r0 + 1)
      rw [← Finset.sum_product']
      have hmaps : ∀ p ∈ S_prod, p.1 + p.2 ∈ Finset.range (M + 1) := by
        intro p hp
        simp only [S_prod, M, Finset.mem_product, Finset.mem_range] at hp ⊢
        omega
      rw [← Finset.sum_fiberwise_of_maps_to hmaps]
      refine Finset.sum_le_sum (fun k _ => ?_)
      have hcongr : ∑ p ∈ S_prod.filter (fun p => p.1 + p.2 = k),
          ((N0.choose p.1 : ℕ) : ℝ) * ((r0.choose p.2 : ℕ) : ℝ) * w (p.1 + p.2) =
        (∑ p ∈ S_prod.filter (fun p => p.1 + p.2 = k),
          ((N0.choose p.1 : ℕ) : ℝ) * ((r0.choose p.2 : ℕ) : ℝ)) * w k := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl (fun p hp => ?_)
        rw [(Finset.mem_filter.mp hp).2]
      rw [hcongr]
      refine mul_le_mul_of_nonneg_right ?_ (hw_nn k)
      have hsub : S_prod.filter (fun p => p.1 + p.2 = k) ⊆ Finset.antidiagonal k := by
        intro p hp
        exact Finset.mem_antidiagonal.mpr (Finset.mem_filter.mp hp).2
      calc
        ∑ p ∈ S_prod.filter (fun p => p.1 + p.2 = k),
            ((N0.choose p.1 : ℕ) : ℝ) * ((r0.choose p.2 : ℕ) : ℝ)
          ≤ ∑ p ∈ Finset.antidiagonal k,
              ((N0.choose p.1 : ℕ) : ℝ) * ((r0.choose p.2 : ℕ) : ℝ) :=
            Finset.sum_le_sum_of_subset_of_nonneg hsub
              (fun _ _ _ => mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
        _ = ((∑ p ∈ Finset.antidiagonal k, N0.choose p.1 * r0.choose p.2 : ℕ) : ℝ) := by
            push_cast
            rfl
        _ = (M.choose k : ℝ) := by
            dsimp [M]
            rw [Nat.add_choose_eq]
    let μ : ℝ := (1 / 2 : ℝ) * (beta0 : ℝ) * (2 : ℝ) ^ L
    let η : ℝ := (2 : ℝ) ^ (- μ)
    have hbeta0_real : (1000 : ℝ) ≤ (beta0 : ℝ) := by exact_mod_cast hbeta0_ge
    have hL_real : (20 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL_ge20
    have hgam_real : (gamma0 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hgam_le_L
    have h2L_real : (L : ℝ) + 1 ≤ (2 : ℝ) ^ L := by
      have hcast : ((L + 1 : ℕ) : ℝ) ≤ ((2 ^ L : ℕ) : ℝ) := by exact_mod_cast h2L_gt_L
      simpa using hcast
    have hprod_ge : 1000 * ((L : ℝ) + 1) ≤ (beta0 : ℝ) * (2 : ℝ) ^ L := by
      calc
        1000 * ((L : ℝ) + 1) ≤ (beta0 : ℝ) * ((L : ℝ) + 1) :=
          mul_le_mul_of_nonneg_right hbeta0_real (by linarith only [hL_real])
        _ ≤ (beta0 : ℝ) * (2 : ℝ) ^ L :=
          mul_le_mul_of_nonneg_left h2L_real (Nat.cast_nonneg beta0)
    have hw_le_η : ∀ k ∈ Finset.range (M + 1), w k ≤ η ^ k := by
      intro k hk_mem
      have hk_le : k ≤ M := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk_mem)
      have hdiv_eq : (2 : ℝ) / ((2 ^ E_q : ℕ) : ℝ) = (2 : ℝ) ^ ((1 : ℝ) - (E_q : ℝ)) := by
        rw [Real.rpow_sub (by norm_num : (0 : ℝ) < 2), Real.rpow_one, Real.rpow_natCast]
        push_cast
        rfl
      have hinv_eq : p_e⁻¹ = (2 : ℝ) ^ σ := by
        dsimp [p_e]
        rw [← Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), neg_neg]
      have hwk_eq : w k = (2 : ℝ) ^ (((1 : ℝ) - (E_q : ℝ)) * (k : ℝ) + σ * (k.choose 2 : ℝ)) := by
        dsimp [w]
        rw [hdiv_eq, hinv_eq, ← Real.rpow_natCast _ k, ← Real.rpow_natCast _ (k.choose 2),
          ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),
          ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),
          ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      have hηk_eq : η ^ k = (2 : ℝ) ^ (- μ * (k : ℝ)) := by
        dsimp [η]
        rw [← Real.rpow_natCast _ k, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
      rw [hwk_eq, hηk_eq]
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      by_cases hk0 : k = 0
      · subst hk0
        simp
      · have hk_pos : 1 ≤ k := by omega
        have hch_real : (k.choose 2 : ℝ) = (k : ℝ) * (((k : ℝ) - 1) / 2) := by
          have hc := h_two_ch2 k
          have hcast : ((2 * k.choose 2 : ℕ) : ℝ) = ((k * (k - 1) : ℕ) : ℝ) := by exact_mod_cast hc
          rw [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_mul, Nat.cast_sub hk_pos, Nat.cast_one] at hcast
          linarith only [hcast]
        have h4k_nat : 4 * (k - 1) ≤ 5 * (N0 - 1) := by
          have h4r : 4 * r0 + 1 ≤ N0 := by
            dsimp [N0]
            have : 21 * r0 ≤ 2 ^ L * r0 := Nat.mul_le_mul_right r0 h2L_ge21
            omega
          dsimp [M] at hk_le
          omega
        have h4k_real : 4 * ((k : ℝ) - 1) ≤ 5 * ((N0 - 1 : ℕ) : ℝ) := by
          have hcast : ((4 * (k - 1) : ℕ) : ℝ) ≤ ((5 * (N0 - 1) : ℕ) : ℝ) := by exact_mod_cast h4k_nat
          rw [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_sub hk_pos, Nat.cast_one,
            Nat.cast_mul, Nat.cast_ofNat] at hcast
          exact hcast
        have hN1_pos : (0 : ℝ) < ((N0 - 1 : ℕ) : ℝ) := by
          exact_mod_cast (show 0 < N0 - 1 by omega)
        have hrat_le : ((k : ℝ) - 1) / ((N0 - 1 : ℕ) : ℝ) ≤ 5 / 4 := by
          rw [div_le_iff₀ hN1_pos]
          linarith only [h4k_real]
        have hσ_term : σ * (((k : ℝ) - 1) / 2) ≤
            (5 / 8 : ℝ) * ((E_q : ℝ) + (L : ℝ) + (gamma0 : ℝ) + 2) := by
          dsimp [σ]
          have hrew : (((E_q + L + gamma0 + 2 : ℕ) : ℝ) / ((N0 - 1 : ℕ) : ℝ)) * (((k : ℝ) - 1) / 2) =
              (((E_q + L + gamma0 + 2 : ℕ) : ℝ) / 2) * (((k : ℝ) - 1) / ((N0 - 1 : ℕ) : ℝ)) := by ring
          rw [hrew]
          have hnum_nn : (0 : ℝ) ≤ ((E_q + L + gamma0 + 2 : ℕ) : ℝ) / 2 :=
            div_nonneg (Nat.cast_nonneg _) (by norm_num)
          have hm := mul_le_mul_of_nonneg_left hrat_le hnum_nn
          push_cast at hm ⊢
          linarith only [hm]
        have hEq_real : (E_q : ℝ) = 2 * (beta0 : ℝ) * (2 : ℝ) ^ L := by
          dsimp [E_q]
          push_cast
          ring
        have hdrift_1 : (1 : ℝ) - (E_q : ℝ) + σ * (((k : ℝ) - 1) / 2) ≤ - μ := by
          dsimp [μ]
          linarith only [hσ_term, hEq_real, hprod_ge, hL_real, hgam_real]
        have hk_nn : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
        have hm := mul_le_mul_of_nonneg_right hdrift_1 hk_nn
        rw [hch_real]
        linarith [hm,
          show ((1 : ℝ) - (E_q : ℝ) + σ * (((k : ℝ) - 1) / 2)) * (k : ℝ) =
            ((1 : ℝ) - (E_q : ℝ)) * (k : ℝ) + σ * ((k : ℝ) * (((k : ℝ) - 1) / 2)) by ring]
    have hsum_bin : ∑ k ∈ Finset.range (M + 1), (M.choose k : ℝ) * η ^ k = (η + 1) ^ M := by
      rw [add_pow]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      simp [mul_comm]
    have hexp_bound : (η + 1) ^ M ≤ 2 * cspGamma r0 := by
      have hη_pos : 0 < η := Real.rpow_pos_of_pos (by norm_num) (- μ)
      have h1 : (η + 1) ^ M ≤ Real.exp ((M : ℝ) * η) := by
        calc
          (η + 1) ^ M ≤ (Real.exp η) ^ M :=
            pow_le_pow_left₀ (by linarith) (Real.add_one_le_exp η) M
          _ = Real.exp ((M : ℝ) * η) := (Real.exp_nat_mul η M).symm
      have hM_le : (M : ℝ) ≤ (r0 : ℝ) * (2 : ℝ) ^ ((L : ℝ) + 1) := by
        have hM_nat : M ≤ r0 * 2 ^ (L + 1) := by
          dsimp [M, N0]
          have h1_2L : 1 ≤ 2 ^ L := Nat.one_le_two_pow
          have hr_le_N : r0 ≤ 2 ^ L * r0 := Nat.le_mul_of_pos_left r0 h1_2L
          rw [pow_succ, show r0 * (2 ^ L * 2) = 2 ^ L * r0 + 2 ^ L * r0 by ring]
          omega
        have hcast : (M : ℝ) ≤ ((r0 * 2 ^ (L + 1) : ℕ) : ℝ) := by exact_mod_cast hM_nat
        rw [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat,
          ← Real.rpow_natCast (2 : ℝ) (L + 1), Nat.cast_add L 1, Nat.cast_one] at hcast
        exact hcast
      have hexp_le : (2 : ℝ) ^ ((L : ℝ) + 1) * η ≤ (2 : ℝ) ^ (- (999 : ℝ)) := by
        dsimp [η, μ]
        rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
        apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
        linarith only [hprod_ge, hL_real]
      have hMη_le : (M : ℝ) * η ≤ (r0 : ℝ) * (2 : ℝ) ^ (- (999 : ℝ)) := by
        have hm1 := mul_le_mul_of_nonneg_right hM_le (le_of_lt hη_pos)
        have hm2 := mul_le_mul_of_nonneg_left hexp_le (Nat.cast_nonneg r0)
        linarith [hm1, hm2, mul_assoc (r0 : ℝ) ((2 : ℝ) ^ ((L : ℝ) + 1)) η]
      have h2 : Real.exp ((M : ℝ) * η) ≤ cspGamma r0 :=
        le_trans (Real.exp_le_exp.mpr hMη_le) (h_exp_gamma r0)
      have hγ_nn : 0 ≤ cspGamma r0 := by
        unfold cspGamma
        exact Real.rpow_nonneg (by norm_num) _
      linarith only [h1, h2, hγ_nn]
    calc
      ∑ k₁ ∈ Finset.range (N0 + 1),
        ∑ k₂ ∈ Finset.range (r0 + 1),
          ((N0.choose k₁ : ℕ) : ℝ) * ((r0.choose k₂ : ℕ) : ℝ) *
          ((2 : ℝ) / ((2 ^ E_q : ℕ) : ℝ)) ^ (k₁ + k₂) *
          (p_e⁻¹) ^ ((k₁ + k₂).choose 2)
        = ∑ k₁ ∈ Finset.range (N0 + 1),
            ∑ k₂ ∈ Finset.range (r0 + 1),
              ((N0.choose k₁ : ℕ) : ℝ) * ((r0.choose k₂ : ℕ) : ℝ) * w (k₁ + k₂) := by
            refine Finset.sum_congr rfl (fun k₁ _ => Finset.sum_congr rfl (fun k₂ _ => ?_))
            dsimp [w]
            ring
      _ ≤ ∑ k ∈ Finset.range (M + 1), (M.choose k : ℝ) * w k := h_vand
      _ ≤ ∑ k ∈ Finset.range (M + 1), (M.choose k : ℝ) * η ^ k :=
          Finset.sum_le_sum (fun k hk => mul_le_mul_of_nonneg_left (hw_le_η k hk) (Nat.cast_nonneg _))
      _ = (η + 1) ^ M := hsum_bin
      _ ≤ 2 * cspGamma r0 := hexp_bound

  have h_assembly : ∀ (N0 q0 r0 : ℕ) (p_k p_e n_0 D_star γ : ℝ),
      2 ≤ q0 → r0 ≤ N0 →
      0 < p_k → 0 < p_e → p_e < 1 →
      (∀ a b : Fin N0 → Fin q0,
        (homQueries a ∪ homQueries b).card =
          N0.choose 2 + dHam a b * (N0 - 1) - (dHam a b).choose 2) →
      (∀ (x : Fin N0 → Fin q0) (s : ℕ),
        (Finset.univ.filter (fun y => dHam x y = s)).card = N0.choose s * (q0 - 1) ^ s) →
      (∑ xy ∈ Finset.univ.filter
          (fun xy : (Fin N0 → Fin q0) × (Fin N0 → Fin q0) => dHam xy.1 xy.2 = r0),
        p_k ^ 2 * p_e ^ (homQueries xy.1 ∪ homQueries xy.2).card = n_0 * D_star) →
      (∑ b ∈ Finset.range (r0 + 1),
        p_k *
          (((r0.choose b : ℝ) * (((N0 - b).choose (r0 - b) : ℕ) : ℝ) *
            ((q0 - 1 : ℕ) : ℝ) ^ (r0 - b)) *
           p_e ^ ((r0 - b) * (N0 - 1) - (r0 - b).choose 2)) ≤
        (3 / 2 : ℝ) * γ * D_star) →
      (∑ k₁ ∈ Finset.range (N0 + 1),
        ∑ k₂ ∈ Finset.range (r0 + 1),
          ((N0.choose k₁ : ℕ) : ℝ) * ((r0.choose k₂ : ℕ) : ℝ) *
          ((2 : ℝ) / ((q0 - 1 : ℕ) : ℝ)) ^ (k₁ + k₂) *
          (p_e⁻¹) ^ ((k₁ + k₂).choose 2) ≤ 2 * γ) →
      (∑ xyz ∈ Finset.univ.filter
          (fun xyz : (Fin N0 → Fin q0) × (Fin N0 → Fin q0) × (Fin N0 → Fin q0) =>
            dHam xyz.1 xyz.2.1 = r0 ∧ dHam xyz.1 xyz.2.2 = r0 ∧ xyz.2.1 ≠ xyz.2.2),
        p_k ^ 3 * p_e ^ (homQueries xyz.1 ∪ homQueries xyz.2.1 ∪ homQueries xyz.2.2).card ≤
          (3 / 2 : ℝ) * γ * n_0 * D_star ^ 2) ∧
      (∑ e₁₂ ∈ Finset.univ.filter
          (fun e₁₂ : ((Fin N0 → Fin q0) × (Fin N0 → Fin q0)) ×
                     ((Fin N0 → Fin q0) × (Fin N0 → Fin q0)) =>
            dHam e₁₂.1.1 e₁₂.1.2 = r0 ∧ dHam e₁₂.2.1 e₁₂.2.2 = r0 ∧
            e₁₂.2.1 ≠ e₁₂.1.1 ∧ e₁₂.2.1 ≠ e₁₂.1.2 ∧
            e₁₂.2.2 ≠ e₁₂.1.1 ∧ e₁₂.2.2 ≠ e₁₂.1.2),
        p_k ^ 4 * p_e ^ (homQueries e₁₂.1.1 ∪ homQueries e₁₂.1.2 ∪
                         homQueries e₁₂.2.1 ∪ homQueries e₁₂.2.2).card ≤
          2 * γ * (n_0 * D_star) ^ 2) := by
    intro N0 q0 r0 p_k p_e n_0 D_star γ hq hrN hpk_pos hpe_pos hpe_lt1
      h_union h_sph h_M0_gen h_s3_gen h_s4_gen
    let U_r := N0.choose 2 + r0 * (N0 - 1) - r0.choose 2
    let E_all := Finset.univ.filter
      (fun xy : (Fin N0 → Fin q0) × (Fin N0 → Fin q0) => dHam xy.1 xy.2 = r0)
    have hM0_const : (E_all.card : ℝ) * (p_k ^ 2 * p_e ^ U_r) = n_0 * D_star := by
      rw [← h_M0_gen]
      have hcongr : ∑ xy ∈ E_all, p_k ^ 2 * p_e ^ (homQueries xy.1 ∪ homQueries xy.2).card =
          ∑ _xy ∈ E_all, (p_k ^ 2 * p_e ^ U_r) := by
        refine Finset.sum_congr rfl (fun xy hxy => ?_)
        have hd : dHam xy.1 xy.2 = r0 := (Finset.mem_filter.mp hxy).2
        rw [h_union xy.1 xy.2, hd]
      rw [hcongr, Finset.sum_const, nsmul_eq_mul]
    have hE_card : E_all.card = q0 ^ N0 * (N0.choose r0 * (q0 - 1) ^ r0) := by
      have hmaps : ∀ xy ∈ E_all, xy.1 ∈ (Finset.univ : Finset (Fin N0 → Fin q0)) :=
        fun _ _ => Finset.mem_univ _
      have hfib : E_all.card = ∑ x : (Fin N0 → Fin q0), (E_all.filter (fun xy => xy.1 = x)).card := by
        simp_rw [Finset.card_eq_sum_ones]
        exact (Finset.sum_fiberwise_of_maps_to hmaps _).symm
      have hfib_eq : ∀ x : Fin N0 → Fin q0,
          (E_all.filter (fun xy => xy.1 = x)).card = N0.choose r0 * (q0 - 1) ^ r0 := by
        intro x
        rw [← h_sph x r0]
        have himg : E_all.filter (fun xy => xy.1 = x) =
            (Finset.univ.filter (fun y => dHam x y = r0)).image (fun y => (x, y)) := by
          ext ⟨a, b⟩
          simp only [E_all, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image,
            Prod.mk.injEq]
          constructor
          · rintro ⟨hd, rfl⟩
            exact ⟨b, hd, rfl, rfl⟩
          · rintro ⟨y, hd, rfl, rfl⟩
            exact ⟨hd, rfl⟩
        rw [himg, Finset.card_image_of_injective _ (fun _ _ h => (Prod.mk.inj h).2)]
      rw [hfib]
      simp_rw [hfib_eq]
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin,
        smul_eq_mul]
    constructor
    · let T3_off := Finset.univ.filter
        (fun xyz : (Fin N0 → Fin q0) × (Fin N0 → Fin q0) × (Fin N0 → Fin q0) =>
          dHam xyz.1 xyz.2.1 = r0 ∧ dHam xyz.1 xyz.2.2 = r0 ∧ xyz.2.1 ≠ xyz.2.2)
      let T3_all := Finset.univ.filter
        (fun xyz : (Fin N0 → Fin q0) × (Fin N0 → Fin q0) × (Fin N0 → Fin q0) =>
          dHam xyz.1 xyz.2.1 = r0 ∧ dHam xyz.1 xyz.2.2 = r0)
      have hT3_sub : T3_off ⊆ T3_all := by
        intro xyz hxyz
        simp only [T3_off, T3_all, Finset.mem_filter, Finset.mem_univ, true_and] at hxyz ⊢
        exact ⟨hxyz.1, hxyz.2.1⟩
      have hmaps3 : ∀ xyz ∈ T3_all, (xyz.1, xyz.2.1) ∈ E_all := by
        intro xyz hxyz
        simp only [T3_all, E_all, Finset.mem_filter, Finset.mem_univ, true_and] at hxyz ⊢
        exact hxyz.1
      have hxy_bound : ∀ xy ∈ E_all,
          ∑ xyz ∈ T3_all.filter (fun xyz => (xyz.1, xyz.2.1) = xy),
            p_k ^ 3 * p_e ^ (homQueries xyz.1 ∪ homQueries xyz.2.1 ∪ homQueries xyz.2.2).card ≤
          (p_k ^ 2 * p_e ^ U_r) * ((3 / 2 : ℝ) * γ * D_star) := by
        intro ⟨x, y⟩ hxy
        have hdxy : dHam x y = r0 := (Finset.mem_filter.mp hxy).2
        let S_x := Finset.univ.filter (fun z : Fin N0 → Fin q0 => dHam x z = r0)
        have hfib_img : T3_all.filter (fun xyz => (xyz.1, xyz.2.1) = (x, y)) =
            S_x.image (fun z => (x, (y, z))) := by
          ext ⟨x', y', z'⟩
          simp only [T3_all, S_x, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image,
            Prod.mk.injEq]
          constructor
          · rintro ⟨⟨_, hdz⟩, rfl, rfl⟩
            exact ⟨z', hdz, rfl, rfl, rfl⟩
          · rintro ⟨z, hdz, rfl, rfl, rfl⟩
            exact ⟨⟨hdxy, hdz⟩, rfl, rfl⟩
        rw [hfib_img, Finset.sum_image (fun _ _ _ _ h => (Prod.mk.inj (Prod.mk.inj h).2).2)]
        obtain ⟨hs1_a, hs1_b⟩ := h_s1 N0 q0 r0 hq hrN h_union x y hdxy
        let b_fn : (Fin N0 → Fin q0) → ℕ :=
          fun z => ((diffCoords x y).filter (fun v => z v = y v)).card
        have hmaps_b : ∀ z ∈ S_x, b_fn z ∈ Finset.range (r0 + 1) := by
          intro z hz
          have hdz : dHam x z = r0 := (Finset.mem_filter.mp hz).2
          exact Finset.mem_range.mpr (Nat.lt_succ_of_le (hs1_a z hdz).1)
        rw [← Finset.sum_fiberwise_of_maps_to hmaps_b]
        have hb_bound : ∀ b ∈ Finset.range (r0 + 1),
            ∑ z ∈ S_x.filter (fun z => b_fn z = b),
              p_k ^ 3 * p_e ^ (homQueries x ∪ homQueries y ∪ homQueries z).card ≤
            (p_k ^ 2 * p_e ^ U_r) *
              (p_k *
                (((r0.choose b : ℝ) * (((N0 - b).choose (r0 - b) : ℕ) : ℝ) *
                  ((q0 - 1 : ℕ) : ℝ) ^ (r0 - b)) *
                 p_e ^ ((r0 - b) * (N0 - 1) - (r0 - b).choose 2))) := by
          intro b hb_mem
          have hb : b ≤ r0 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hb_mem)
          have hpt : ∀ z ∈ S_x.filter (fun z => b_fn z = b),
              p_k ^ 3 * p_e ^ (homQueries x ∪ homQueries y ∪ homQueries z).card ≤
              (p_k ^ 2 * p_e ^ U_r) *
                (p_k * p_e ^ ((r0 - b) * (N0 - 1) - (r0 - b).choose 2)) := by
            intro z hz
            obtain ⟨hzS, hbz⟩ := Finset.mem_filter.mp hz
            have hdz : dHam x z = r0 := (Finset.mem_filter.mp hzS).2
            have hcard_le := (hs1_a z hdz).2
            change (homQueries x ∪ homQueries y).card +
              ((r0 - b_fn z) * (N0 - 1) - (r0 - b_fn z).choose 2) ≤ _ at hcard_le
            rw [h_union x y, hdxy, hbz] at hcard_le
            have hpe_le := pow_le_pow_of_le_one (le_of_lt hpe_pos) (le_of_lt hpe_lt1) hcard_le
            rw [pow_add] at hpe_le
            have hpk_nn : 0 ≤ p_k ^ 3 := by positivity
            calc
              p_k ^ 3 * p_e ^ (homQueries x ∪ homQueries y ∪ homQueries z).card
                ≤ p_k ^ 3 * (p_e ^ U_r * p_e ^ ((r0 - b) * (N0 - 1) - (r0 - b).choose 2)) :=
                  mul_le_mul_of_nonneg_left hpe_le hpk_nn
              _ = (p_k ^ 2 * p_e ^ U_r) *
                    (p_k * p_e ^ ((r0 - b) * (N0 - 1) - (r0 - b).choose 2)) := by ring
          have hcard_fib : ((S_x.filter (fun z => b_fn z = b)).card : ℝ) ≤
              (r0.choose b : ℝ) * (((N0 - b).choose (r0 - b) : ℕ) : ℝ) *
                ((q0 - 1 : ℕ) : ℝ) ^ (r0 - b) := by
            have hfeq : S_x.filter (fun z => b_fn z = b) =
                Finset.univ.filter (fun z => dHam x z = r0 ∧ b_fn z = b) := by
              ext z
              simp [S_x]
            rw [hfeq]
            have hnat := hs1_b b hb
            have hcast : (((Finset.univ.filter (fun z => dHam x z = r0 ∧ b_fn z = b)).card : ℕ) : ℝ) ≤
                ((r0.choose b * (N0 - b).choose (r0 - b) * (q0 - 1) ^ (r0 - b) : ℕ) : ℝ) := by
              exact_mod_cast hnat
            push_cast at hcast
            exact hcast
          calc
            ∑ z ∈ S_x.filter (fun z => b_fn z = b),
                p_k ^ 3 * p_e ^ (homQueries x ∪ homQueries y ∪ homQueries z).card
              ≤ ((S_x.filter (fun z => b_fn z = b)).card : ℝ) *
                  ((p_k ^ 2 * p_e ^ U_r) *
                    (p_k * p_e ^ ((r0 - b) * (N0 - 1) - (r0 - b).choose 2))) := by
                simpa [nsmul_eq_mul] using Finset.sum_le_card_nsmul _ _ _ hpt
            _ ≤ ((r0.choose b : ℝ) * (((N0 - b).choose (r0 - b) : ℕ) : ℝ) *
                  ((q0 - 1 : ℕ) : ℝ) ^ (r0 - b)) *
                  ((p_k ^ 2 * p_e ^ U_r) *
                    (p_k * p_e ^ ((r0 - b) * (N0 - 1) - (r0 - b).choose 2))) :=
                mul_le_mul_of_nonneg_right hcard_fib (by positivity)
            _ = (p_k ^ 2 * p_e ^ U_r) *
                  (p_k *
                    (((r0.choose b : ℝ) * (((N0 - b).choose (r0 - b) : ℕ) : ℝ) *
                      ((q0 - 1 : ℕ) : ℝ) ^ (r0 - b)) *
                     p_e ^ ((r0 - b) * (N0 - 1) - (r0 - b).choose 2))) := by ring
        calc
          ∑ b ∈ Finset.range (r0 + 1),
              ∑ z ∈ S_x.filter (fun z => b_fn z = b),
                p_k ^ 3 * p_e ^ (homQueries x ∪ homQueries y ∪ homQueries z).card
            ≤ ∑ b ∈ Finset.range (r0 + 1),
                (p_k ^ 2 * p_e ^ U_r) *
                  (p_k *
                    (((r0.choose b : ℝ) * (((N0 - b).choose (r0 - b) : ℕ) : ℝ) *
                      ((q0 - 1 : ℕ) : ℝ) ^ (r0 - b)) *
                     p_e ^ ((r0 - b) * (N0 - 1) - (r0 - b).choose 2))) :=
              Finset.sum_le_sum hb_bound
          _ = (p_k ^ 2 * p_e ^ U_r) *
                ∑ b ∈ Finset.range (r0 + 1),
                  p_k *
                    (((r0.choose b : ℝ) * (((N0 - b).choose (r0 - b) : ℕ) : ℝ) *
                      ((q0 - 1 : ℕ) : ℝ) ^ (r0 - b)) *
                     p_e ^ ((r0 - b) * (N0 - 1) - (r0 - b).choose 2)) :=
              (Finset.mul_sum _ _ _).symm
          _ ≤ (p_k ^ 2 * p_e ^ U_r) * ((3 / 2 : ℝ) * γ * D_star) :=
              mul_le_mul_of_nonneg_left h_s3_gen (by positivity)
      calc
        ∑ xyz ∈ T3_off,
            p_k ^ 3 * p_e ^ (homQueries xyz.1 ∪ homQueries xyz.2.1 ∪ homQueries xyz.2.2).card
          ≤ ∑ xyz ∈ T3_all,
              p_k ^ 3 * p_e ^ (homQueries xyz.1 ∪ homQueries xyz.2.1 ∪ homQueries xyz.2.2).card :=
            Finset.sum_le_sum_of_subset_of_nonneg hT3_sub (fun _ _ _ => by positivity)
        _ = ∑ xy ∈ E_all,
              ∑ xyz ∈ T3_all.filter (fun xyz => (xyz.1, xyz.2.1) = xy),
                p_k ^ 3 * p_e ^ (homQueries xyz.1 ∪ homQueries xyz.2.1 ∪ homQueries xyz.2.2).card :=
            (Finset.sum_fiberwise_of_maps_to hmaps3 _).symm
        _ ≤ (E_all.card : ℝ) * ((p_k ^ 2 * p_e ^ U_r) * ((3 / 2 : ℝ) * γ * D_star)) := by
            simpa [nsmul_eq_mul] using Finset.sum_le_card_nsmul _ _ _ hxy_bound
        _ = ((E_all.card : ℝ) * (p_k ^ 2 * p_e ^ U_r)) * ((3 / 2 : ℝ) * γ * D_star) := by ring
        _ = (3 / 2 : ℝ) * γ * n_0 * D_star ^ 2 := by
            rw [hM0_const]
            ring
    · let E4_disj := Finset.univ.filter
        (fun e₁₂ : ((Fin N0 → Fin q0) × (Fin N0 → Fin q0)) ×
                   ((Fin N0 → Fin q0) × (Fin N0 → Fin q0)) =>
          dHam e₁₂.1.1 e₁₂.1.2 = r0 ∧ dHam e₁₂.2.1 e₁₂.2.2 = r0 ∧
          e₁₂.2.1 ≠ e₁₂.1.1 ∧ e₁₂.2.1 ≠ e₁₂.1.2 ∧
          e₁₂.2.2 ≠ e₁₂.1.1 ∧ e₁₂.2.2 ≠ e₁₂.1.2)
      have hE4_sub : E4_disj ⊆ E_all ×ˢ E_all := by
        intro e₁₂ he
        simp only [E4_disj, E_all, Finset.mem_product, Finset.mem_filter, Finset.mem_univ,
          true_and] at he ⊢
        exact ⟨he.1, he.2.1⟩
      have hq1_pos : (0 : ℝ) < ((q0 - 1 : ℕ) : ℝ) := by
        exact_mod_cast (show 0 < q0 - 1 by omega)
      have hq1_le_qr : ((q0 - 1 : ℕ) : ℝ) ≤ (q0 : ℝ) := by
        exact_mod_cast (Nat.sub_le q0 1)
      have h1_le_inv_pe : 1 ≤ p_e⁻¹ := (one_le_inv₀ hpe_pos).mpr (le_of_lt hpe_lt1)
      have hinner_bound : ∀ xy ∈ E_all,
          ∑ xy' ∈ E_all,
            p_k ^ 4 * p_e ^ (homQueries xy.1 ∪ homQueries xy.2 ∪
                             homQueries xy'.1 ∪ homQueries xy'.2).card ≤
          (E_all.card : ℝ) * (p_k ^ 2 * p_e ^ U_r) ^ 2 * (2 * γ) := by
        intro ⟨x, y⟩ hxy
        have hdxy : dHam x y = r0 := (Finset.mem_filter.mp hxy).2
        obtain ⟨hs2_a, hs2_b⟩ := h_s2 N0 q0 r0 hq hrN x y
        let k1_fn : (Fin N0 → Fin q0) → ℕ :=
          fun x' => (Finset.univ.filter (fun v : Fin N0 => x' v = x v ∨ x' v = y v)).card
        let k2_fn : (Fin N0 → Fin q0) → (Fin N0 → Fin q0) → ℕ :=
          fun x' y' => ((diffCoords x' y').filter (fun v : Fin N0 => y' v = x v ∨ y' v = y v)).card
        let S_kr := Finset.range (N0 + 1) ×ˢ Finset.range (r0 + 1)
        have hmaps_kr : ∀ xy' ∈ E_all, (k1_fn xy'.1, k2_fn xy'.1 xy'.2) ∈ S_kr := by
          intro xy' hxy'
          have hdxy' : dHam xy'.1 xy'.2 = r0 := (Finset.mem_filter.mp hxy').2
          have hk1 : k1_fn xy'.1 ≤ N0 := by
            simpa using Finset.card_le_univ
              (Finset.univ.filter (fun v : Fin N0 => xy'.1 v = x v ∨ xy'.1 v = y v))
          have hk2 : k2_fn xy'.1 xy'.2 ≤ r0 := by
            rw [← hdxy']
            exact Finset.card_le_card (Finset.filter_subset _ _)
          simp only [S_kr, Finset.mem_product, Finset.mem_range]
          omega
        rw [← Finset.sum_fiberwise_of_maps_to hmaps_kr]
        have hkk_bound : ∀ kk ∈ S_kr,
            ∑ xy' ∈ E_all.filter (fun xy' => (k1_fn xy'.1, k2_fn xy'.1 xy'.2) = kk),
              p_k ^ 4 * p_e ^ (homQueries x ∪ homQueries y ∪
                               homQueries xy'.1 ∪ homQueries xy'.2).card ≤
            ((E_all.card : ℝ) * (p_k ^ 2 * p_e ^ U_r) ^ 2) *
              (((N0.choose kk.1 : ℕ) : ℝ) * ((r0.choose kk.2 : ℕ) : ℝ) *
               ((2 : ℝ) / ((q0 - 1 : ℕ) : ℝ)) ^ (kk.1 + kk.2) *
               (p_e⁻¹) ^ ((kk.1 + kk.2).choose 2)) := by
          rintro ⟨k₁, k₂⟩ hkk
          simp only [S_kr, Finset.mem_product, Finset.mem_range] at hkk
          have hk₁ : k₁ ≤ N0 := Nat.lt_succ_iff.mp hkk.1
          have hk₂ : k₂ ≤ r0 := Nat.lt_succ_iff.mp hkk.2
          have hpt : ∀ xy' ∈ E_all.filter (fun xy' => (k1_fn xy'.1, k2_fn xy'.1 xy'.2) = (k₁, k₂)),
              p_k ^ 4 * p_e ^ (homQueries x ∪ homQueries y ∪
                               homQueries xy'.1 ∪ homQueries xy'.2).card ≤
              (p_k ^ 2 * p_e ^ U_r) ^ 2 * (p_e⁻¹) ^ ((k₁ + k₂).choose 2) := by
            intro xy' hxy'_f
            obtain ⟨hxy'E, hpair_eq⟩ := Finset.mem_filter.mp hxy'_f
            have hdxy' : dHam xy'.1 xy'.2 = r0 := (Finset.mem_filter.mp hxy'E).2
            obtain ⟨hk1_eq, hk2_eq⟩ := Prod.mk.inj hpair_eq
            let Q₁ := homQueries x ∪ homQueries y
            let Q₂ := homQueries xy'.1 ∪ homQueries xy'.2
            have hu_assoc : homQueries x ∪ homQueries y ∪ homQueries xy'.1 ∪ homQueries xy'.2 =
                Q₁ ∪ Q₂ := Finset.union_assoc _ _ _
            have hQ₁_card : Q₁.card = U_r := by dsimp [Q₁]; rw [h_union x y, hdxy]
            have hQ₂_card : Q₂.card = U_r := by dsimp [Q₂]; rw [h_union xy'.1 xy'.2, hdxy']
            have hcard_ui : (Q₁ ∪ Q₂).card + (Q₁ ∩ Q₂).card = U_r + U_r := by
              rw [Finset.card_union_add_card_inter, hQ₁_card, hQ₂_card]
            have hpe_split : p_e ^ (Q₁ ∪ Q₂).card =
                p_e ^ U_r * p_e ^ U_r * (p_e⁻¹) ^ (Q₁ ∩ Q₂).card := by
              have hne : p_e ≠ 0 := ne_of_gt hpe_pos
              have h1 : p_e ^ (Q₁ ∪ Q₂).card * p_e ^ (Q₁ ∩ Q₂).card = p_e ^ U_r * p_e ^ U_r := by
                rw [← pow_add, hcard_ui, pow_add]
              calc
                p_e ^ (Q₁ ∪ Q₂).card
                  = p_e ^ (Q₁ ∪ Q₂).card * (p_e ^ (Q₁ ∩ Q₂).card * (p_e⁻¹) ^ (Q₁ ∩ Q₂).card) := by
                      rw [← mul_pow, mul_inv_cancel₀ hne, one_pow, mul_one]
                _ = (p_e ^ (Q₁ ∪ Q₂).card * p_e ^ (Q₁ ∩ Q₂).card) * (p_e⁻¹) ^ (Q₁ ∩ Q₂).card := by
                      ring
                _ = p_e ^ U_r * p_e ^ U_r * (p_e⁻¹) ^ (Q₁ ∩ Q₂).card := by rw [h1]
            have hinter_le : (Q₁ ∩ Q₂).card ≤ (k₁ + k₂).choose 2 := by
              rw [← hk1_eq, ← hk2_eq]
              exact hs2_a xy'.1 xy'.2
            have hinv_pow := pow_le_pow_right₀ h1_le_inv_pe hinter_le
            rw [hu_assoc, hpe_split]
            calc
              p_k ^ 4 * (p_e ^ U_r * p_e ^ U_r * (p_e⁻¹) ^ (Q₁ ∩ Q₂).card)
                = (p_k ^ 2 * p_e ^ U_r) ^ 2 * (p_e⁻¹) ^ (Q₁ ∩ Q₂).card := by ring
              _ ≤ (p_k ^ 2 * p_e ^ U_r) ^ 2 * (p_e⁻¹) ^ ((k₁ + k₂).choose 2) :=
                  mul_le_mul_of_nonneg_left hinv_pow (by positivity)
          have hcard_fib :
              ((E_all.filter (fun xy' => (k1_fn xy'.1, k2_fn xy'.1 xy'.2) = (k₁, k₂))).card : ℝ) ≤
              (E_all.card : ℝ) * ((N0.choose k₁ : ℕ) : ℝ) * ((r0.choose k₂ : ℕ) : ℝ) *
                ((2 : ℝ) / ((q0 - 1 : ℕ) : ℝ)) ^ (k₁ + k₂) := by
            have hfeq : E_all.filter (fun xy' => (k1_fn xy'.1, k2_fn xy'.1 xy'.2) = (k₁, k₂)) =
                Finset.univ.filter (fun xy' =>
                  dHam xy'.1 xy'.2 = r0 ∧ k1_fn xy'.1 = k₁ ∧ k2_fn xy'.1 xy'.2 = k₂) := by
              ext xy'
              simp [E_all, Prod.mk.injEq]
            rw [hfeq]
            have hnat := hs2_b k₁ k₂ hk₁ hk₂
            let q_r : ℝ := (q0 : ℝ)
            let q_1 : ℝ := ((q0 - 1 : ℕ) : ℝ)
            have hcast : ((Finset.univ.filter
                (fun (xy' : (Fin N0 → Fin q0) × (Fin N0 → Fin q0)) =>
                  dHam xy'.1 xy'.2 = r0 ∧ k1_fn xy'.1 = k₁ ∧ k2_fn xy'.1 xy'.2 = k₂)).card : ℝ) ≤
                ((N0.choose k₁ : ℕ) : ℝ) * (2 : ℝ) ^ k₁ * q_r ^ (N0 - k₁) *
                  ((N0.choose r0 : ℝ) * ((r0.choose k₂ : ℕ) : ℝ) * (2 : ℝ) ^ k₂ * q_1 ^ (r0 - k₂)) := by
              dsimp [q_r, q_1]
              exact_mod_cast hnat
            have hpow1 : (2 : ℝ) ^ k₁ * q_r ^ (N0 - k₁) ≤ ((2 : ℝ) / q_1) ^ k₁ * q_r ^ N0 := by
              have hdiv_ge1 : (1 : ℝ) ≤ q_r / q_1 := (one_le_div hq1_pos).mpr hq1_le_qr
              have h2_le : (2 : ℝ) ≤ ((2 : ℝ) / q_1) * q_r := by
                have hm := mul_le_mul_of_nonneg_left hdiv_ge1 (by norm_num : (0 : ℝ) ≤ 2)
                linarith [hm, show (2 : ℝ) * (q_r / q_1) = ((2 : ℝ) / q_1) * q_r by ring]
              have hp1 : (2 : ℝ) ^ k₁ ≤ ((2 : ℝ) / q_1) ^ k₁ * q_r ^ k₁ := by
                rw [← mul_pow]
                exact pow_le_pow_left₀ (by norm_num) h2_le k₁
              calc
                (2 : ℝ) ^ k₁ * q_r ^ (N0 - k₁)
                  ≤ (((2 : ℝ) / q_1) ^ k₁ * q_r ^ k₁) * q_r ^ (N0 - k₁) :=
                    mul_le_mul_of_nonneg_right hp1 (pow_nonneg (Nat.cast_nonneg q0) _)
                _ = ((2 : ℝ) / q_1) ^ k₁ * (q_r ^ k₁ * q_r ^ (N0 - k₁)) := by ring
                _ = ((2 : ℝ) / q_1) ^ k₁ * q_r ^ N0 := by
                    rw [← pow_add, Nat.add_sub_of_le hk₁]
            have hpow2 : (2 : ℝ) ^ k₂ * q_1 ^ (r0 - k₂) = ((2 : ℝ) / q_1) ^ k₂ * q_1 ^ r0 := by
              have hq1_ne : q_1 ^ k₂ ≠ 0 := pow_ne_zero k₂ (ne_of_gt hq1_pos)
              have hr_split : q_1 ^ r0 = q_1 ^ k₂ * q_1 ^ (r0 - k₂) := by
                rw [← pow_add, Nat.add_sub_of_le hk₂]
              rw [div_pow, hr_split]
              field_simp [hq1_ne]
            have hE_real : (E_all.card : ℝ) = q_r ^ N0 * ((N0.choose r0 : ℝ) * q_1 ^ r0) := by
              have hc : (E_all.card : ℝ) = ((q0 ^ N0 * (N0.choose r0 * (q0 - 1) ^ r0) : ℕ) : ℝ) := by
                exact_mod_cast hE_card
              push_cast at hc
              exact hc
            have hprod_le :
                ((N0.choose k₁ : ℕ) : ℝ) * (2 : ℝ) ^ k₁ * q_r ^ (N0 - k₁) *
                  ((N0.choose r0 : ℝ) * ((r0.choose k₂ : ℕ) : ℝ) * (2 : ℝ) ^ k₂ * q_1 ^ (r0 - k₂)) ≤
                (E_all.card : ℝ) * ((N0.choose k₁ : ℕ) : ℝ) * ((r0.choose k₂ : ℕ) : ℝ) *
                  ((2 : ℝ) / q_1) ^ (k₁ + k₂) := by
              have hnn2 : 0 ≤ ((N0.choose k₁ : ℕ) : ℝ) * ((N0.choose r0 : ℝ) *
                  ((r0.choose k₂ : ℕ) : ℝ) * (((2 : ℝ) / q_1) ^ k₂ * q_1 ^ r0)) := by
                dsimp [q_1]
                positivity
              calc
                ((N0.choose k₁ : ℕ) : ℝ) * (2 : ℝ) ^ k₁ * q_r ^ (N0 - k₁) *
                    ((N0.choose r0 : ℝ) * ((r0.choose k₂ : ℕ) : ℝ) * (2 : ℝ) ^ k₂ * q_1 ^ (r0 - k₂))
                  = ((2 : ℝ) ^ k₁ * q_r ^ (N0 - k₁)) *
                      (((N0.choose k₁ : ℕ) : ℝ) * ((N0.choose r0 : ℝ) *
                        ((r0.choose k₂ : ℕ) : ℝ) * ((2 : ℝ) ^ k₂ * q_1 ^ (r0 - k₂)))) := by ring
                _ = ((2 : ℝ) ^ k₁ * q_r ^ (N0 - k₁)) *
                      (((N0.choose k₁ : ℕ) : ℝ) * ((N0.choose r0 : ℝ) *
                        ((r0.choose k₂ : ℕ) : ℝ) * (((2 : ℝ) / q_1) ^ k₂ * q_1 ^ r0))) := by
                      rw [hpow2]
                _ ≤ (((2 : ℝ) / q_1) ^ k₁ * q_r ^ N0) *
                      (((N0.choose k₁ : ℕ) : ℝ) * ((N0.choose r0 : ℝ) *
                        ((r0.choose k₂ : ℕ) : ℝ) * (((2 : ℝ) / q_1) ^ k₂ * q_1 ^ r0))) :=
                      mul_le_mul_of_nonneg_right hpow1 hnn2
                _ = (q_r ^ N0 * ((N0.choose r0 : ℝ) * q_1 ^ r0)) *
                      ((N0.choose k₁ : ℕ) : ℝ) * ((r0.choose k₂ : ℕ) : ℝ) *
                      (((2 : ℝ) / q_1) ^ k₁ * ((2 : ℝ) / q_1) ^ k₂) := by ring
                _ = (E_all.card : ℝ) * ((N0.choose k₁ : ℕ) : ℝ) * ((r0.choose k₂ : ℕ) : ℝ) *
                      ((2 : ℝ) / q_1) ^ (k₁ + k₂) := by
                      rw [← hE_real, ← pow_add]
            exact le_trans hcast hprod_le
          calc
            ∑ xy' ∈ E_all.filter (fun xy' => (k1_fn xy'.1, k2_fn xy'.1 xy'.2) = (k₁, k₂)),
                p_k ^ 4 * p_e ^ (homQueries x ∪ homQueries y ∪
                                 homQueries xy'.1 ∪ homQueries xy'.2).card
              ≤ ((E_all.filter (fun xy' => (k1_fn xy'.1, k2_fn xy'.1 xy'.2) = (k₁, k₂))).card : ℝ) *
                  ((p_k ^ 2 * p_e ^ U_r) ^ 2 * (p_e⁻¹) ^ ((k₁ + k₂).choose 2)) := by
                simpa [nsmul_eq_mul] using Finset.sum_le_card_nsmul _ _ _ hpt
            _ ≤ ((E_all.card : ℝ) * ((N0.choose k₁ : ℕ) : ℝ) * ((r0.choose k₂ : ℕ) : ℝ) *
                  ((2 : ℝ) / ((q0 - 1 : ℕ) : ℝ)) ^ (k₁ + k₂)) *
                  ((p_k ^ 2 * p_e ^ U_r) ^ 2 * (p_e⁻¹) ^ ((k₁ + k₂).choose 2)) :=
                mul_le_mul_of_nonneg_right hcard_fib (by positivity)
            _ = ((E_all.card : ℝ) * (p_k ^ 2 * p_e ^ U_r) ^ 2) *
                  (((N0.choose k₁ : ℕ) : ℝ) * ((r0.choose k₂ : ℕ) : ℝ) *
                   ((2 : ℝ) / ((q0 - 1 : ℕ) : ℝ)) ^ (k₁ + k₂) *
                   (p_e⁻¹) ^ ((k₁ + k₂).choose 2)) := by ring
        calc
          ∑ kk ∈ S_kr,
              ∑ xy' ∈ E_all.filter (fun xy' => (k1_fn xy'.1, k2_fn xy'.1 xy'.2) = kk),
                p_k ^ 4 * p_e ^ (homQueries x ∪ homQueries y ∪
                                 homQueries xy'.1 ∪ homQueries xy'.2).card
            ≤ ∑ kk ∈ S_kr,
                ((E_all.card : ℝ) * (p_k ^ 2 * p_e ^ U_r) ^ 2) *
                  (((N0.choose kk.1 : ℕ) : ℝ) * ((r0.choose kk.2 : ℕ) : ℝ) *
                   ((2 : ℝ) / ((q0 - 1 : ℕ) : ℝ)) ^ (kk.1 + kk.2) *
                   (p_e⁻¹) ^ ((kk.1 + kk.2).choose 2)) :=
              Finset.sum_le_sum hkk_bound
          _ = ((E_all.card : ℝ) * (p_k ^ 2 * p_e ^ U_r) ^ 2) *
                ∑ kk ∈ S_kr,
                  (((N0.choose kk.1 : ℕ) : ℝ) * ((r0.choose kk.2 : ℕ) : ℝ) *
                   ((2 : ℝ) / ((q0 - 1 : ℕ) : ℝ)) ^ (kk.1 + kk.2) *
                   (p_e⁻¹) ^ ((kk.1 + kk.2).choose 2)) :=
              (Finset.mul_sum _ _ _).symm
          _ = ((E_all.card : ℝ) * (p_k ^ 2 * p_e ^ U_r) ^ 2) *
                ∑ k₁ ∈ Finset.range (N0 + 1),
                  ∑ k₂ ∈ Finset.range (r0 + 1),
                    (((N0.choose k₁ : ℕ) : ℝ) * ((r0.choose k₂ : ℕ) : ℝ) *
                     ((2 : ℝ) / ((q0 - 1 : ℕ) : ℝ)) ^ (k₁ + k₂) *
                     (p_e⁻¹) ^ ((k₁ + k₂).choose 2)) :=
              congrArg (((E_all.card : ℝ) * (p_k ^ 2 * p_e ^ U_r) ^ 2) * ·)
                (Finset.sum_product' (Finset.range (N0 + 1)) (Finset.range (r0 + 1))
                  (fun k₁ k₂ => ((N0.choose k₁ : ℕ) : ℝ) * ((r0.choose k₂ : ℕ) : ℝ) *
                    ((2 : ℝ) / ((q0 - 1 : ℕ) : ℝ)) ^ (k₁ + k₂) *
                    (p_e⁻¹) ^ ((k₁ + k₂).choose 2)))
          _ ≤ ((E_all.card : ℝ) * (p_k ^ 2 * p_e ^ U_r) ^ 2) * (2 * γ) :=
              mul_le_mul_of_nonneg_left h_s4_gen (by positivity)
          _ = (E_all.card : ℝ) * (p_k ^ 2 * p_e ^ U_r) ^ 2 * (2 * γ) := by ring
      calc
        ∑ e₁₂ ∈ E4_disj,
            p_k ^ 4 * p_e ^ (homQueries e₁₂.1.1 ∪ homQueries e₁₂.1.2 ∪
                             homQueries e₁₂.2.1 ∪ homQueries e₁₂.2.2).card
          ≤ ∑ e₁₂ ∈ E_all ×ˢ E_all,
              p_k ^ 4 * p_e ^ (homQueries e₁₂.1.1 ∪ homQueries e₁₂.1.2 ∪
                               homQueries e₁₂.2.1 ∪ homQueries e₁₂.2.2).card :=
            Finset.sum_le_sum_of_subset_of_nonneg hE4_sub (fun _ _ _ => by positivity)
        _ = ∑ xy ∈ E_all,
              ∑ xy' ∈ E_all,
                p_k ^ 4 * p_e ^ (homQueries xy.1 ∪ homQueries xy.2 ∪
                                 homQueries xy'.1 ∪ homQueries xy'.2).card :=
            Finset.sum_product' E_all E_all (fun xy xy' =>
              p_k ^ 4 * p_e ^ (homQueries xy.1 ∪ homQueries xy.2 ∪
                               homQueries xy'.1 ∪ homQueries xy'.2).card)
        _ ≤ (E_all.card : ℝ) * ((E_all.card : ℝ) * (p_k ^ 2 * p_e ^ U_r) ^ 2 * (2 * γ)) := by
            simpa [nsmul_eq_mul] using Finset.sum_le_card_nsmul _ _ _ hinner_bound
        _ = 2 * γ * ((E_all.card : ℝ) * (p_k ^ 2 * p_e ^ U_r)) ^ 2 := by ring
        _ = 2 * γ * (n_0 * D_star) ^ 2 := by rw [hM0_const]

  have hr_ge : 3001 ≤ r_star := by omega
  have h1_le_2L : 1 ≤ 2 ^ cspL C₁ := Nat.one_le_two_pow
  have hrN : r_star ≤ 2 ^ cspL C₁ * r_star := Nat.le_mul_of_pos_left r_star h1_le_2L
  have hq_ge2 : 2 ≤ cspQ C₁ := by
    unfold cspQ
    have := @Nat.one_le_two_pow (cspEq C₁)
    omega
  have hq1_pos_nat : 1 ≤ cspQ C₁ - 1 := by omega
  have hL_ge20 : 20 ≤ cspL C₁ := by unfold cspL; omega
  have hlam0_1000 := (lam0_ge_1000_C1 C₁ hC₁).2.1
  have hlam0_ge3000 : 3000 ≤ cspLam0 C₁ := by omega
  have hbeta0_ge1000 : 1000 ≤ cspBeta0 C₁ := by unfold cspBeta0; omega
  have hgam_le_L : cspGamma0 C₁ ≤ cspL C₁ := by
    unfold cspGamma0 cspL cspInvEta0
    have hsq : 9 ≤ C₁ ^ 2 := Nat.pow_le_pow_left hC₁ 2
    have hmul : 5 * cspLam0 C₁ ≤ 20 * C₁ ^ 2 * 80 * cspLam0 C₁ :=
      Nat.mul_le_mul_right _ (by omega)
    omega
  have hσ_low6 : 6 * (cspLam0 C₁ : ℝ) ≤ cspSigmaEdge C₁ r_star * (r_star : ℝ) / 2 := by
    have hbeq : (cspBeta0 C₁ : ℝ) = 6 * (cspLam0 C₁ : ℝ) := by unfold cspBeta0; push_cast; ring
    linarith only [hbeq, hσ_low]
  have hD_nn : 0 ≤ cspDStar C₁ r_star := by
    unfold cspDStar
    exact Real.rpow_nonneg (by norm_num) _
  have h_s3 := h_hypergeom_abs (cspL C₁) r_star (cspQ C₁ - 1) (cspLam0 C₁) (cspGamma0 C₁)
    (cspSigmaEdge C₁ r_star) (cspDStar C₁ r_star)
    hr_ge hq1_pos_nat hlam0_ge3000 rfl hσ_pos hD_nn h_cal hσ_low6
  have h_s4 : ∑ k₁ ∈ Finset.range (2 ^ cspL C₁ * r_star + 1),
      ∑ k₂ ∈ Finset.range (r_star + 1),
        (((2 ^ cspL C₁ * r_star).choose k₁ : ℕ) : ℝ) *
        ((r_star.choose k₂ : ℕ) : ℝ) *
        ((2 : ℝ) / ((cspQ C₁ - 1 : ℕ) : ℝ)) ^ (k₁ + k₂) *
        ((cspPEdge C₁ r_star)⁻¹) ^ ((k₁ + k₂).choose 2) ≤
      2 * cspGamma r_star := by
    have hq1_eq : cspQ C₁ - 1 = 2 ^ (2 * cspBeta0 C₁ * 2 ^ cspL C₁) := Nat.add_sub_cancel _ 1
    rw [hq1_eq]
    exact h_vand_abs (cspL C₁) (cspBeta0 C₁) (cspGamma0 C₁) r_star
      hL_ge20 hbeta0_ge1000 hgam_le_L hr_ge
  exact h_assembly (2 ^ cspL C₁ * r_star) (cspQ C₁) r_star
    (cspPKeep C₁ r_star) (cspPEdge C₁ r_star)
    (cspN0 C₁ r_star) (cspDStar C₁ r_star) (cspGamma r_star)
    hq_ge2 hrN hp_keep_pos hp_edge_pos hp_edge_lt1
    h_union_card h_sphere h_M0 h_s3 h_s4

private theorem close_pair_query_sum_bound (C₁ : ℕ) (hC₁ : 3 ≤ C₁) (r_star : ℕ) (hr : 1000 * C₁ < r_star)
    (hσ_pos : 0 < cspSigmaEdge C₁ r_star)
    (hp_edge_pos : 0 < cspPEdge C₁ r_star)
    (hσ_up : cspSigmaEdge C₁ r_star * (r_star : ℝ) / 2 ≤ (10001 / 10000 : ℝ) * (cspBeta0 C₁ : ℝ))
    (hDOm_s : ∀ s : ℕ, s ≤ 2 ^ cspL C₁ * r_star →
      cspDOmega C₁ r_star s ≤
        (2 : ℝ) ^ (2 * (r_star : ℝ) - (cspGamma0 C₁ : ℝ) * (s : ℝ) +
          cspSigmaEdge C₁ r_star * (s.choose 2 : ℝ)))
    (hp_keep_pos : 0 < cspPKeep C₁ r_star)
    (hp_keep_up : cspPKeep C₁ r_star ≤
      (2 : ℝ) ^ (- (747 / 1000 : ℝ) * (cspLam0 C₁ : ℝ) * (r_star : ℝ)))
    (hn0_pos : 0 < cspN0 C₁ r_star)
    (h_union_card : ∀ x y : Fin (2 ^ cspL C₁ * r_star) → Fin (cspQ C₁),
      (homQueries x ∪ homQueries y).card =
        (2 ^ cspL C₁ * r_star).choose 2 +
          dHam x y * (2 ^ cspL C₁ * r_star - 1) - (dHam x y).choose 2)
    (h_sphere : ∀ (x : Fin (2 ^ cspL C₁ * r_star) → Fin (cspQ C₁)) (s : ℕ),
      (Finset.univ.filter (fun y => dHam x y = s)).card =
        (2 ^ cspL C₁ * r_star).choose s * (cspQ C₁ - 1) ^ s) :
    ∑ ab ∈ Finset.univ.filter
        (fun ab : (Fin (2 ^ cspL C₁ * r_star) → Fin (cspQ C₁)) ×
                  (Fin (2 ^ cspL C₁ * r_star) → Fin (cspQ C₁)) =>
          ab.1 ≠ ab.2 ∧ 2 * dHam ab.1 ab.2 < r_star),
      (cspPKeep C₁ r_star) ^ 2 *
        (cspPEdge C₁ r_star) ^ (homQueries ab.1 ∪ homQueries ab.2).card ≤
      (1 / 4 : ℝ) * cspDeltaBad C₁ r_star * cspN0 C₁ r_star := by
  have h_core : ∀ (N q lam0 beta0 gamma0 : ℕ)
      (sigma_edge p_edge p_keep n_0 delta_bad : ℝ) (d_omega : ℕ → ℝ),
      1000 ≤ lam0 →
      beta0 = 6 * lam0 →
      gamma0 = 5 * lam0 →
      r_star < N →
      0 < sigma_edge →
      0 < p_edge →
      sigma_edge * (r_star : ℝ) / 2 ≤ (10001 / 10000 : ℝ) * (beta0 : ℝ) →
      (∀ s : ℕ, d_omega s = (N.choose s : ℝ) * ((q - 1 : ℕ) : ℝ) ^ s *
        p_edge ^ (s * (N - 1) - s.choose 2)) →
      (∀ s : ℕ, s ≤ N →
        d_omega s ≤ (2 : ℝ) ^ (2 * (r_star : ℝ) - (gamma0 : ℝ) * (s : ℝ) +
          sigma_edge * (s.choose 2 : ℝ))) →
      0 < p_keep →
      p_keep ≤ (2 : ℝ) ^ (- (747 / 1000 : ℝ) * (lam0 : ℝ) * (r_star : ℝ)) →
      n_0 = p_keep * ((q : ℝ) ^ N) * p_edge ^ (N.choose 2) →
      0 < n_0 →
      delta_bad = (2 : ℝ) ^ (- (6 / 10 : ℝ) * (lam0 : ℝ) * (r_star : ℝ)) →
      (∀ x y : Fin N → Fin q,
        (homQueries x ∪ homQueries y).card =
          N.choose 2 + dHam x y * (N - 1) - (dHam x y).choose 2) →
      (∀ (x : Fin N → Fin q) (s : ℕ),
        (Finset.univ.filter (fun y => dHam x y = s)).card = N.choose s * (q - 1) ^ s) →
      ∑ ab ∈ Finset.univ.filter
          (fun ab : (Fin N → Fin q) × (Fin N → Fin q) =>
            ab.1 ≠ ab.2 ∧ 2 * dHam ab.1 ab.2 < r_star),
        p_keep ^ 2 * p_edge ^ (homQueries ab.1 ∪ homQueries ab.2).card ≤
        (1 / 4 : ℝ) * delta_bad * n_0 := by
    intro N q lam0 beta0 gamma0 sigma_edge p_edge p_keep n_0 delta_bad d_omega
      hlam0_ge hbeta_eq hgam_eq hN_gt_r hσ0 hp_edge0 hσ_up0 hdomega_def hDOm_s0
      hp_keep0 hp_keep_up0 hn0_def hn0_pos0 hdelta_def h_uc h_sph
    have hr_ge : 3001 ≤ r_star := by omega
    have hr_real : (3001 : ℝ) ≤ (r_star : ℝ) := by exact_mod_cast hr_ge
    have hr_pos : (0 : ℝ) < (r_star : ℝ) := by linarith
    have hlam0_real : (1000 : ℝ) ≤ (lam0 : ℝ) := by exact_mod_cast hlam0_ge
    have hbeta_real : (beta0 : ℝ) = 6 * (lam0 : ℝ) := by rw [hbeta_eq]; push_cast; ring
    have hgam_real : (gamma0 : ℝ) = 5 * (lam0 : ℝ) := by rw [hgam_eq]; push_cast; ring
    have h_choose2_nat : ∀ s : ℕ, 2 * s.choose 2 = s * (s - 1) := by
      intro s
      rw [Nat.choose_two_right, Nat.mul_div_cancel' (Nat.even_mul_pred_self s).two_dvd]
    have hs_choose_le : ∀ s : ℕ, s ≤ r_star / 2 → s.choose 2 ≤ s * (N - 1) := by
      intro s hs
      have hs1 : s - 1 ≤ 2 * (N - 1) := by omega
      have h2 : 2 * s.choose 2 ≤ 2 * (s * (N - 1)) := by
        rw [h_choose2_nat s]
        calc s * (s - 1) ≤ s * (2 * (N - 1)) := Nat.mul_le_mul_left s hs1
          _ = 2 * (s * (N - 1)) := by ring
      omega
    let PairSphere : ℕ → Finset ((Fin N → Fin q) × (Fin N → Fin q)) :=
      fun s => Finset.univ.filter (fun xy => dHam xy.1 xy.2 = s)
    have h_sphere_sum : ∀ s : ℕ, s ≤ r_star / 2 →
        ∑ xy ∈ PairSphere s,
          p_keep ^ 2 * p_edge ^ (homQueries xy.1 ∪ homQueries xy.2).card =
          n_0 * p_keep * d_omega s := by
      intro s hs
      have hsub := hs_choose_le s hs
      have hbi : PairSphere s = Finset.univ.biUnion
          (fun x : Fin N → Fin q =>
            (Finset.univ.filter (fun y => dHam x y = s)).image (fun y => (x, y))) := by
        ext xy
        simp only [PairSphere, Finset.mem_filter, Finset.mem_univ, true_and,
          Finset.mem_biUnion, Finset.mem_image]
        constructor
        · intro h
          exact ⟨xy.1, xy.2, h, Prod.eta xy⟩
        · rintro ⟨x, y, h, rfl⟩
          exact h
      have hdisj_x : ((Finset.univ : Finset (Fin N → Fin q)) : Set (Fin N → Fin q)).PairwiseDisjoint
          (fun x => (Finset.univ.filter (fun y => dHam x y = s)).image (fun y => (x, y))) := by
        intro x₁ _ x₂ _ hne
        rw [Function.onFun, Finset.disjoint_left]
        intro p hp1 hp2
        rcases Finset.mem_image.mp hp1 with ⟨_, _, rfl⟩
        rcases Finset.mem_image.mp hp2 with ⟨_, _, hp⟩
        exact hne (Prod.mk.inj hp).1.symm
      have hcard_ps : (PairSphere s).card = q ^ N * (N.choose s * (q - 1) ^ s) := by
        rw [hbi, Finset.card_biUnion hdisj_x]
        have h_inner : ∀ x ∈ (Finset.univ : Finset (Fin N → Fin q)),
            ((Finset.univ.filter (fun y => dHam x y = s)).image (fun y => (x, y))).card =
              N.choose s * (q - 1) ^ s := by
          intro x _
          rw [Finset.card_image_of_injective _ (fun _ _ h => (Prod.mk.inj h).2)]
          exact h_sph x s
        rw [Finset.sum_congr rfl h_inner, Finset.sum_const, smul_eq_mul,
          Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]
      have hcongr : ∀ xy ∈ PairSphere s,
          p_keep ^ 2 * p_edge ^ (homQueries xy.1 ∪ homQueries xy.2).card =
          p_keep ^ 2 * (p_edge ^ (N.choose 2) * p_edge ^ (s * (N - 1) - s.choose 2)) := by
        intro xy hxy
        simp only [PairSphere, Finset.mem_filter, Finset.mem_univ, true_and] at hxy
        rw [h_uc xy.1 xy.2, hxy, Nat.add_sub_assoc hsub, pow_add]
      rw [Finset.sum_congr rfl hcongr, Finset.sum_const, nsmul_eq_mul, hcard_ps,
        hn0_def, hdomega_def s]
      push_cast
      ring
    have hne_iff : ∀ a b : Fin N → Fin q, a ≠ b ↔ 1 ≤ dHam a b := by
      intro a b
      constructor
      · intro hne
        obtain ⟨v, hv⟩ := Function.ne_iff.mp hne
        exact Finset.card_pos.mpr ⟨v, Finset.mem_filter.mpr ⟨Finset.mem_univ v, hv⟩⟩
      · intro h1 heq
        subst heq
        have h0 : dHam a a = 0 := by simp [dHam, diffCoords]
        omega
    have hsub_close : Finset.univ.filter
        (fun ab : (Fin N → Fin q) × (Fin N → Fin q) =>
          ab.1 ≠ ab.2 ∧ 2 * dHam ab.1 ab.2 < r_star) ⊆
        (Finset.Icc 1 (r_star / 2)).biUnion PairSphere := by
      intro ab hab
      simp only [PairSphere, Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_biUnion, Finset.mem_Icc, hne_iff] at hab ⊢
      exact ⟨dHam ab.1 ab.2, ⟨hab.1, by omega⟩, rfl⟩
    have hdisj : ((Finset.Icc 1 (r_star / 2) : Finset ℕ) : Set ℕ).PairwiseDisjoint PairSphere := by
      intro s₁ _ s₂ _ hne
      rw [Function.onFun, Finset.disjoint_left]
      intro ab h₁ h₂
      simp only [PairSphere, Finset.mem_filter, Finset.mem_univ, true_and] at h₁ h₂
      exact hne (h₁.symm.trans h₂)
    have hle_bi : ∑ ab ∈ Finset.univ.filter
        (fun ab : (Fin N → Fin q) × (Fin N → Fin q) =>
          ab.1 ≠ ab.2 ∧ 2 * dHam ab.1 ab.2 < r_star),
        p_keep ^ 2 * p_edge ^ (homQueries ab.1 ∪ homQueries ab.2).card ≤
      ∑ s ∈ Finset.Icc 1 (r_star / 2), ∑ xy ∈ PairSphere s,
        p_keep ^ 2 * p_edge ^ (homQueries xy.1 ∪ homQueries xy.2).card := by
      rw [← Finset.sum_biUnion hdisj]
      exact Finset.sum_le_sum_of_subset_of_nonneg hsub_close (fun _ _ _ => by positivity)
    let B_close : ℝ := n_0 * (2 : ℝ) ^ (- (74 / 100 : ℝ) * (lam0 : ℝ) * (r_star : ℝ))
    have hterm_le : ∀ s ∈ Finset.Icc 1 (r_star / 2),
        ∑ xy ∈ PairSphere s,
          p_keep ^ 2 * p_edge ^ (homQueries xy.1 ∪ homQueries xy.2).card ≤ B_close := by
      intro s hs
      rw [Finset.mem_Icc] at hs
      rw [h_sphere_sum s hs.2]
      have hsN : s ≤ N := by omega
      have hDOm_nn : 0 ≤ d_omega s := by
        rw [hdomega_def s]
        positivity
      have hsc2_le : (s.choose 2 : ℝ) ≤ (r_star : ℝ) * (s : ℝ) / 4 := by
        have hnat : 4 * s.choose 2 ≤ r_star * s := by
          have h2s : 2 * s ≤ r_star := by omega
          calc 4 * s.choose 2 = 2 * (2 * s.choose 2) := by ring
            _ = 2 * (s * (s - 1)) := by rw [h_choose2_nat s]
            _ ≤ 2 * (s * s) := Nat.mul_le_mul_left 2 (Nat.mul_le_mul_left s (Nat.sub_le s 1))
            _ = (2 * s) * s := by ring
            _ ≤ r_star * s := Nat.mul_le_mul_right s h2s
        have hreal : (4 : ℝ) * (s.choose 2 : ℝ) ≤ (r_star : ℝ) * (s : ℝ) := by exact_mod_cast hnat
        linarith
      have hsig_sc2 : sigma_edge * (s.choose 2 : ℝ) ≤ (gamma0 : ℝ) * (s : ℝ) := by
        have hm1 : sigma_edge * (s.choose 2 : ℝ) ≤ sigma_edge * ((r_star : ℝ) * (s : ℝ) / 4) :=
          mul_le_mul_of_nonneg_left hsc2_le (le_of_lt hσ0)
        have hm2 : (sigma_edge * (r_star : ℝ) / 2) * ((s : ℝ) / 2) ≤
            ((10001 / 10000 : ℝ) * (beta0 : ℝ)) * ((s : ℝ) / 2) :=
          mul_le_mul_of_nonneg_right hσ_up0 (by positivity)
        have hprod_nn : (0 : ℝ) ≤ (lam0 : ℝ) * (s : ℝ) := by positivity
        rw [hbeta_real] at hm2
        rw [hgam_real]
        linarith
      have hpDOm : p_keep * d_omega s ≤
          (2 : ℝ) ^ (- (74 / 100 : ℝ) * (lam0 : ℝ) * (r_star : ℝ)) := by
        have hm := mul_le_mul hp_keep_up0 (hDOm_s0 s hsN) hDOm_nn (by positivity)
        rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)] at hm
        have hexp : - (747 / 1000 : ℝ) * (lam0 : ℝ) * (r_star : ℝ) +
            (2 * (r_star : ℝ) - (gamma0 : ℝ) * (s : ℝ) + sigma_edge * (s.choose 2 : ℝ)) ≤
            - (74 / 100 : ℝ) * (lam0 : ℝ) * (r_star : ℝ) := by
          have h2r_le : 2 * (r_star : ℝ) ≤ (2 / 1000 : ℝ) * (lam0 : ℝ) * (r_star : ℝ) := by
            nlinarith only [hlam0_real, hr_pos]
          have hprod_nn : (0 : ℝ) ≤ (lam0 : ℝ) * (r_star : ℝ) := by positivity
          linarith only [hsig_sc2, h2r_le, hprod_nn]
        exact le_trans hm (Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp)
      dsimp [B_close]
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left hpDOm (le_of_lt hn0_pos0)
    have hsum_le1 : ∑ s ∈ Finset.Icc 1 (r_star / 2), ∑ xy ∈ PairSphere s,
        p_keep ^ 2 * p_edge ^ (homQueries xy.1 ∪ homQueries xy.2).card ≤
        ((Finset.Icc 1 (r_star / 2)).card : ℝ) * B_close := by
      calc
        ∑ s ∈ Finset.Icc 1 (r_star / 2), _
          ≤ ∑ _s ∈ Finset.Icc 1 (r_star / 2), B_close := Finset.sum_le_sum hterm_le
        _ = ((Finset.Icc 1 (r_star / 2)).card : ℝ) * B_close := by
            rw [Finset.sum_const, nsmul_eq_mul]
    have hcard_le : ((Finset.Icc 1 (r_star / 2)).card : ℝ) ≤ (2 : ℝ) ^ (r_star : ℝ) := by
      have hc_nat : (Finset.Icc 1 (r_star / 2)).card ≤ 2 ^ r_star := by
        have hc1 : (Finset.Icc 1 (r_star / 2)).card ≤ r_star := by
          rw [Nat.card_Icc]; omega
        exact le_trans hc1 (le_of_lt Nat.lt_two_pow_self)
      have hcast : ((Finset.Icc 1 (r_star / 2)).card : ℝ) ≤ ((2 ^ r_star : ℕ) : ℝ) := by
        exact_mod_cast hc_nat
      rwa [Nat.cast_pow, Nat.cast_ofNat, ← Real.rpow_natCast] at hcast
    have hB_nn : 0 ≤ B_close := by dsimp [B_close]; positivity
    have hsum_le2 : ((Finset.Icc 1 (r_star / 2)).card : ℝ) * B_close ≤
        (1 / 4 : ℝ) * delta_bad * n_0 := by
      have hm := mul_le_mul_of_nonneg_right hcard_le hB_nn
      dsimp [B_close] at hm
      have hrew : (2 : ℝ) ^ (r_star : ℝ) *
          (n_0 * (2 : ℝ) ^ (- (74 / 100 : ℝ) * (lam0 : ℝ) * (r_star : ℝ))) =
          n_0 * (2 : ℝ) ^ ((r_star : ℝ) + (- (74 / 100 : ℝ) * (lam0 : ℝ) * (r_star : ℝ))) := by
        rw [mul_left_comm, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      rw [hrew] at hm
      have htarget : (2 : ℝ) ^ ((r_star : ℝ) + (- (74 / 100 : ℝ) * (lam0 : ℝ) * (r_star : ℝ))) ≤
          (1 / 4 : ℝ) * delta_bad := by
        rw [hdelta_def]
        have hquarter : (1 / 4 : ℝ) = (2 : ℝ) ^ (- (2 : ℝ)) := by norm_num
        rw [hquarter, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
        apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
        have h1r : (r_star : ℝ) ≤ (1 / 1000 : ℝ) * (lam0 : ℝ) * (r_star : ℝ) := by
          nlinarith only [hlam0_real, hr_pos]
        have hlam_r : (1000 : ℝ) ≤ (lam0 : ℝ) * (r_star : ℝ) := by
          nlinarith only [hlam0_real, hr_real]
        linarith only [h1r, hlam_r]
      have hm2 := mul_le_mul_of_nonneg_left htarget (le_of_lt hn0_pos0)
      have hrhs_eq : n_0 * ((1 / 4 : ℝ) * delta_bad) = (1 / 4 : ℝ) * delta_bad * n_0 := by ring
      rw [hrhs_eq] at hm2
      dsimp [B_close]
      exact le_trans hm hm2
    exact le_trans hle_bi (le_trans hsum_le1 hsum_le2)
  have hlam0_1000 := (lam0_ge_1000_C1 C₁ hC₁).2.1
  have hlam0_ge : 1000 ≤ cspLam0 C₁ := by omega
  have hN_gt_r : r_star < 2 ^ cspL C₁ * r_star := by
    have hr_pos : 0 < r_star := by omega
    have hL_ge1 : 1 ≤ cspL C₁ := Nat.le_trans (by decide : 1 ≤ 20) (Nat.le_add_right 20 _)
    have h2L : 2 ≤ 2 ^ cspL C₁ := by
      simpa using Nat.pow_le_pow_right (by decide : 1 ≤ 2) hL_ge1
    calc
      r_star = 1 * r_star := (one_mul r_star).symm
      _ < 2 * r_star := Nat.mul_lt_mul_of_pos_right (by decide : 1 < 2) hr_pos
      _ ≤ 2 ^ cspL C₁ * r_star := Nat.mul_le_mul_right r_star h2L
  exact h_core
    (2 ^ cspL C₁ * r_star) (cspQ C₁) (cspLam0 C₁) (cspBeta0 C₁) (cspGamma0 C₁)
    (cspSigmaEdge C₁ r_star) (cspPEdge C₁ r_star) (cspPKeep C₁ r_star)
    (cspN0 C₁ r_star) (cspDeltaBad C₁ r_star) (cspDOmega C₁ r_star)
    hlam0_ge rfl rfl hN_gt_r hσ_pos hp_edge_pos hσ_up (fun _ => rfl) hDOm_s
    hp_keep_pos hp_keep_up rfl hn0_pos rfl h_union_card h_sphere

private theorem complete_graph_2csp_expurgated_existence (C₁ : ℕ) (hC₁ : 3 ≤ C₁)
    (r_star : ℕ) (hr : 1000 * C₁ < r_star) :
    ∃ (R : Fin (2 ^ cspL C₁ * r_star) → Fin (2 ^ cspL C₁ * r_star) →
          Fin (cspQ C₁) → Fin (cspQ C₁) → Prop)
      (X_set : Finset (Fin (2 ^ cspL C₁ * r_star) → Fin (cspQ C₁))),
      Symmetric2CSP R ∧
      X_set ⊆ satisfyingSet R ∧
      ((2 : ℝ) ^ ((98 / 100 : ℝ) * (cspBeta0 C₁ : ℝ) * (2 : ℝ) ^ (2 * cspL C₁) * (r_star : ℝ)) ≤
        (X_set.card : ℝ) ∧
       (X_set.card : ℝ) ≤
        (2 : ℝ) ^ ((102 / 100 : ℝ) * (cspBeta0 C₁ : ℝ) * (2 : ℝ) ^ (2 * cspL C₁) * (r_star : ℝ))) ∧
      ((2 : ℝ) ^ ((1 / 5 : ℝ) * (cspLam0 C₁ : ℝ) * (r_star : ℝ)) * (X_set.card : ℝ) ≤
        192 * (((X_set ×ˢ X_set).filter (fun xy => dHam xy.1 xy.2 = r_star)).card : ℝ)) ∧
      (∀ x ∈ X_set, ∀ u ∈ X_set, ∀ z ∈ satisfyingSet R,
        dHam x u ≤ C₁ * r_star → dHam x z ≤ C₁ * r_star →
        cspInvEta0 C₁ * (d3Coords x u z).card ≤ r_star) ∧
      (∀ x ∈ X_set, ∀ w₀ ∈ X_set, x ≠ w₀ → dHam x w₀ ≤ C₁ * r_star →
        (X_set.filter (fun y =>
          y ≠ x ∧ y ≠ w₀ ∧ dHam x y = r_star ∧
          r_star < 4 * (diffCoords x w₀ ∩ diffCoords x y).card)).card < cspKCh C₁) ∧
      (∀ a ∈ X_set, ∀ b ∈ X_set, a ≠ b → dHam a b ≤ C₁ * r_star →
        (X_set.filter (fun x => x ∈ bicliqueWitnessList R C₁ r_star a b)).card < cspKMom C₁) ∧
      (∀ x ∈ X_set, ∀ y ∈ X_set, x ≠ y → r_star ≤ 2 * dHam x y) :=
by
  have hr_ge : 3001 ≤ r_star := by omega
  have hr_pos_real : (0 : ℝ) < (r_star : ℝ) := by exact_mod_cast (show 0 < r_star by omega)
  have hr_ge3001_real : (3001 : ℝ) ≤ (r_star : ℝ) := by exact_mod_cast hr_ge
  have hC₁_sq_ge9 : 9 ≤ C₁ ^ 2 := by nlinarith only [hC₁]
  have hC₁_sq_real : (9 : ℝ) ≤ ((C₁ ^ 2 : ℕ) : ℝ) := by exact_mod_cast hC₁_sq_ge9
  have hlam0_1000 := (lam0_ge_1000_C1 C₁ hC₁).2.1
  have hlam0_ge : 1000 ≤ cspLam0 C₁ := by omega
  have hlam0_real : (1000 : ℝ) ≤ (cspLam0 C₁ : ℝ) := by exact_mod_cast hlam0_ge
  have hbeta0_ge : 6000 ≤ cspBeta0 C₁ := by unfold cspBeta0; omega
  have hbeta0_real : (6000 : ℝ) ≤ (cspBeta0 C₁ : ℝ) := by exact_mod_cast hbeta0_ge
  have h22L_real : (1 : ℝ) ≤ (2 : ℝ) ^ (2 * cspL C₁) := by
    exact_mod_cast (Nat.one_le_two_pow (n := 2 * cspL C₁))
  have hpow998 : (4 : ℝ) ≤ (2 : ℝ) ^ (998 : ℕ) := by
    calc
      (4 : ℝ) = (2 : ℝ) ^ (2 : ℕ) := by norm_num
      _ ≤ (2 : ℝ) ^ (998 : ℕ) := pow_le_pow_right₀ (by norm_num) (by omega)
  have hdiv998 : ∀ c : ℝ, c ≤ 4 →
      c * (r_star : ℝ) / ((2 : ℝ) ^ (998 : ℕ)) ≤ (r_star : ℝ) := by
    intro c hc
    rw [div_le_iff₀ (by positivity)]
    have hc_le : c ≤ (2 : ℝ) ^ (998 : ℕ) := le_trans hc hpow998
    calc
      c * (r_star : ℝ) = (r_star : ℝ) * c := mul_comm _ _
      _ ≤ (r_star : ℝ) * ((2 : ℝ) ^ (998 : ℕ)) :=
        mul_le_mul_of_nonneg_left hc_le (Nat.cast_nonneg _)
  obtain ⟨hσ_pos, hp_edge_pos, hp_edge_lt1, h_cal, hσ_low_strict, hσ_up_strict,
    h_binom_edge, hDOm_s, _hDOm_low, _hDOm_up,
    hp_keep_pos, hp_keep_lt1, hp_keep_up,
    hn0_low, hn0_up,
    _h_hom_card, h_union_card, h_sphere,
    h_M1_eq, h_M0_eq, h_ball_sum⟩ :=
    csp_dyadic_calibration_and_first_moments C₁ hC₁ r_star hr
  have hσ_low : (cspBeta0 C₁ : ℝ) ≤ cspSigmaEdge C₁ r_star * (r_star : ℝ) / 2 :=
    le_of_lt hσ_low_strict
  have hσ_up : cspSigmaEdge C₁ r_star * (r_star : ℝ) / 2 ≤
      (10001 / 10000 : ℝ) * (cspBeta0 C₁ : ℝ) :=
    le_of_lt hσ_up_strict
  have hn0_pos : 0 < cspN0 C₁ r_star := by
    have hpos : (0 : ℝ) <
        (2 : ℝ) ^ ((99 / 100 : ℝ) * (cspBeta0 C₁ : ℝ) * (2 : ℝ) ^ (2 * cspL C₁) * (r_star : ℝ)) :=
      Real.rpow_pos_of_pos (by norm_num) _
    linarith only [hpos, hn0_low]
  have hD_pos : 0 < cspDStar C₁ r_star := by
    unfold cspDStar
    positivity
  have hγ_ge1 : 1 ≤ cspGamma r_star := by
    unfold cspGamma
    have hexp_nn : (0 : ℝ) ≤ (r_star : ℝ) / ((2 : ℝ) ^ (998 : ℕ)) := by positivity
    calc
      (1 : ℝ) = (2 : ℝ) ^ (0 : ℝ) := by norm_num
      _ ≤ (2 : ℝ) ^ ((r_star : ℝ) / ((2 : ℝ) ^ (998 : ℕ))) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp_nn
  have hδ_pos : 0 < cspDeltaBad C₁ r_star := by
    unfold cspDeltaBad
    positivity
  have hp_iota : ∀ i : cspIota (2 ^ cspL C₁ * r_star) (cspQ C₁),
      0 ≤ cspPIota C₁ r_star i ∧ cspPIota C₁ r_star i ≤ 1 := by
    rintro (i | i)
    · exact ⟨le_of_lt hp_edge_pos, le_of_lt hp_edge_lt1⟩
    · exact ⟨le_of_lt hp_keep_pos, le_of_lt hp_keep_lt1⟩
  obtain ⟨hW_nn, hW_sum, h_cyl, h_seq⟩ :=
    finite_bernoulli_cylinder_and_sequential_moment (cspPIota C₁ r_star) hp_iota
  have hdHam_symm : ∀ {N q : ℕ} (x y : Fin N → Fin q), dHam x y = dHam y x := by
    intro N q x y
    unfold dHam diffCoords
    congr 1
    ext v
    simp [ne_comm]
  have hRel_symm : Symmetric
      (fun x y : Fin (2 ^ cspL C₁ * r_star) → Fin (cspQ C₁) => dHam x y = r_star) := by
    intro x y hxy
    rwa [hdHam_symm y x]
  have hdHam_ne_of_r : ∀ {N q : ℕ} {x y : Fin N → Fin q}, dHam x y = r_star → x ≠ y := by
    intro N q x y hd hxy
    subst hxy
    have h0 : dHam x x = 0 := by simp [dHam, diffCoords]
    omega
  have h_sym_R : ∀ {N q : ℕ} (ω : cspIota N q → Bool), Symmetric2CSP (symROf ω) := by
    intro N q ω u v c₁ c₂
    unfold symROf
    rcases lt_trichotomy u v with hlt | rfl | hgt
    · have hnot : ¬ v < u := lt_asymm hlt
      simp [hlt, hnot]
    · simp
    · have hnot : ¬ u < v := lt_asymm hgt
      simp [hgt, hnot]
  have h_hom_iff : ∀ {N q : ℕ} (ω : cspIota N q → Bool) (x : Fin N → Fin q),
      (∀ t ∈ homQueries x, ω (Sum.inl t) = true) ↔ x ∈ satisfyingSet (symROf ω) := by
    intro N q ω x
    simp only [satisfyingSet, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro ht u v huv
      have h := ht (u, v, x u, x v) (by
        simp only [homQueries, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨(u, v), huv, rfl⟩)
      simpa [symROf, if_pos huv] using h
    · intro hhom t ht
      simp only [homQueries, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at ht
      rcases ht with ⟨⟨u, v⟩, huv, rfl⟩
      have h := hhom u v huv
      simpa [symROf, if_pos huv] using h
  have h_sum_card_filter : ∀ {Ω α : Type} [Fintype Ω] [DecidableEq α] (W : Ω → ℝ) (S : Finset α)
      (P : Ω → α → Prop) [∀ ω, DecidablePred (P ω)],
      ∑ ω : Ω, W ω * ((S.filter (P ω)).card : ℝ) =
        ∑ a ∈ S, ∑ ω : Ω, (if P ω a then W ω else 0) := by
    intro Ω α _ _ W S P _
    have h1 : ∀ ω : Ω,
        W ω * ((S.filter (P ω)).card : ℝ) = ∑ a ∈ S, (if P ω a then W ω else 0) := by
      intro ω
      rw [Finset.card_filter, Nat.cast_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun a _ => ?_)
      split_ifs <;> simp
    simp_rw [h1]
    exact Finset.sum_comm
  have h_prod_iota : ∀ (V_keep : Finset (Fin (2 ^ cspL C₁ * r_star) → Fin (cspQ C₁)))
      (Q_edges : Finset (Fin (2 ^ cspL C₁ * r_star) × Fin (2 ^ cspL C₁ * r_star) ×
        Fin (cspQ C₁) × Fin (cspQ C₁))),
      ∏ i ∈ V_keep.image Sum.inr ∪ Q_edges.image Sum.inl, cspPIota C₁ r_star i =
        (cspPKeep C₁ r_star) ^ V_keep.card * (cspPEdge C₁ r_star) ^ Q_edges.card := by
    intro V_keep Q_edges
    have hdisj : Disjoint
        (V_keep.image (Sum.inr : _ → cspIota (2 ^ cspL C₁ * r_star) (cspQ C₁)))
        (Q_edges.image (Sum.inl : _ → cspIota (2 ^ cspL C₁ * r_star) (cspQ C₁))) := by
      rw [Finset.disjoint_left]
      intro i hi1 hi2
      rcases Finset.mem_image.mp hi1 with ⟨_, _, rfl⟩
      rcases Finset.mem_image.mp hi2 with ⟨_, _, h⟩
      cases h
    rw [Finset.prod_union hdisj,
      Finset.prod_image (fun _ _ _ _ h => Sum.inr.inj h),
      Finset.prod_image (fun _ _ _ _ h => Sum.inl.inj h)]
    simp [cspPIota]
  have h_exp_ind : ∀ (V_keep : Finset (Fin (2 ^ cspL C₁ * r_star) → Fin (cspQ C₁)))
      (Q_edges : Finset (Fin (2 ^ cspL C₁ * r_star) × Fin (2 ^ cspL C₁ * r_star) ×
        Fin (cspQ C₁) × Fin (cspQ C₁))),
      ∑ ω : cspIota (2 ^ cspL C₁ * r_star) (cspQ C₁) → Bool,
        (if (∀ x ∈ V_keep, ω (Sum.inr x) = true) ∧ (∀ t ∈ Q_edges, ω (Sum.inl t) = true)
         then bernWeight (cspPIota C₁ r_star) ω else 0) =
        (cspPKeep C₁ r_star) ^ V_keep.card * (cspPEdge C₁ r_star) ^ Q_edges.card := by
    intro V_keep Q_edges
    have hcond : ∀ ω : cspIota (2 ^ cspL C₁ * r_star) (cspQ C₁) → Bool,
        ((∀ x ∈ V_keep, ω (Sum.inr x) = true) ∧ (∀ t ∈ Q_edges, ω (Sum.inl t) = true)) ↔
        (∀ i ∈ V_keep.image Sum.inr ∪ Q_edges.image Sum.inl, ω i = true) := by
      intro ω
      simp only [Finset.mem_union, Finset.mem_image]
      constructor
      · rintro ⟨h1, h2⟩ _ (⟨x, hx, rfl⟩ | ⟨t, ht, rfl⟩)
        · exact h1 x hx
        · exact h2 t ht
      · intro h
        exact ⟨fun x hx => h _ (Or.inl ⟨x, hx, rfl⟩),
               fun t ht => h _ (Or.inr ⟨t, ht, rfl⟩)⟩
    simp_rw [hcond]
    rw [h_cyl, h_prod_iota]
  
  have hM1 : ∑ ω : cspIota (2 ^ cspL C₁ * r_star) (cspQ C₁) → Bool,
      bernWeight (cspPIota C₁ r_star) ω * ((cspPRaw ω).card : ℝ) ≤ cspN0 C₁ r_star := by
    have hM1_exact : ∑ ω : cspIota (2 ^ cspL C₁ * r_star) (cspQ C₁) → Bool,
        bernWeight (cspPIota C₁ r_star) ω * ((cspPRaw ω).card : ℝ) = cspN0 C₁ r_star := by
      unfold cspPRaw
      rw [h_sum_card_filter]
      have h1 : ∀ x : Fin (2 ^ cspL C₁ * r_star) → Fin (cspQ C₁),
          ∑ ω : cspIota (2 ^ cspL C₁ * r_star) (cspQ C₁) → Bool,
            (if ω (Sum.inr x) = true ∧ ∀ t ∈ homQueries x, ω (Sum.inl t) = true
             then bernWeight (cspPIota C₁ r_star) ω else 0) =
          cspPKeep C₁ r_star * (cspPEdge C₁ r_star) ^ (homQueries x).card := by
        intro x
        have hiff : ∀ ω : cspIota (2 ^ cspL C₁ * r_star) (cspQ C₁) → Bool,
            (ω (Sum.inr x) = true ∧ ∀ t ∈ homQueries x, ω (Sum.inl t) = true) ↔
            ((∀ z ∈ ({x} : Finset _), ω (Sum.inr z) = true) ∧
             (∀ t ∈ homQueries x, ω (Sum.inl t) = true)) := by
          intro ω
          simp
        simp_rw [hiff]
        simpa using h_exp_ind {x} (homQueries x)
      simp_rw [h1]
      exact h_M1_eq
    exact le_of_eq hM1_exact
  
  have h_pair_exp : ∀ {x y : Fin (2 ^ cspL C₁ * r_star) → Fin (cspQ C₁)}, x ≠ y →
      ∑ ω : cspIota (2 ^ cspL C₁ * r_star) (cspQ C₁) → Bool,
        (if x ∈ cspPRaw ω ∧ y ∈ cspPRaw ω then bernWeight (cspPIota C₁ r_star) ω else 0) =
        (cspPKeep C₁ r_star) ^ 2 * (cspPEdge C₁ r_star) ^ (homQueries x ∪ homQueries y).card := by
    intro x y hne
    have hiff : ∀ ω : cspIota (2 ^ cspL C₁ * r_star) (cspQ C₁) → Bool,
        (x ∈ cspPRaw ω ∧ y ∈ cspPRaw ω) ↔
        ((∀ z ∈ ({x, y} : Finset _), ω (Sum.inr z) = true) ∧
         (∀ t ∈ homQueries x ∪ homQueries y, ω (Sum.inl t) = true)) := by
      intro ω
      simp only [cspPRaw, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
        Finset.mem_singleton, Finset.mem_union, forall_eq_or_imp, forall_eq]
      constructor
      · rintro ⟨⟨hx1, hx2⟩, ⟨hy1, hy2⟩⟩
        exact ⟨⟨hx1, hy1⟩, fun t ht => ht.elim (hx2 t) (hy2 t)⟩
      · rintro ⟨⟨hx1, hy1⟩, hq⟩
        exact ⟨⟨hx1, fun t ht => hq t (Or.inl ht)⟩, ⟨hy1, fun t ht => hq t (Or.inr ht)⟩⟩
    simp_rw [hiff]
    rw [h_exp_ind, Finset.card_pair hne]
  have h_triple_exp : ∀ {x y z : Fin (2 ^ cspL C₁ * r_star) → Fin (cspQ C₁)},
      x ≠ y → x ≠ z → y ≠ z →
      ∑ ω : cspIota (2 ^ cspL C₁ * r_star) (cspQ C₁) → Bool,
        (if x ∈ cspPRaw ω ∧ y ∈ cspPRaw ω ∧ z ∈ cspPRaw ω
         then bernWeight (cspPIota C₁ r_star) ω else 0) =
        (cspPKeep C₁ r_star) ^ 3 *
          (cspPEdge C₁ r_star) ^ (homQueries x ∪ homQueries y ∪ homQueries z).card := by
    intro x y z hxy hxz hyz
    have hiff : ∀ ω : cspIota (2 ^ cspL C₁ * r_star) (cspQ C₁) → Bool,
        (x ∈ cspPRaw ω ∧ y ∈ cspPRaw ω ∧ z ∈ cspPRaw ω) ↔
        ((∀ v ∈ ({x, y, z} : Finset _), ω (Sum.inr v) = true) ∧
         (∀ t ∈ homQueries x ∪ homQueries y ∪ homQueries z, ω (Sum.inl t) = true)) := by
      intro ω
      simp only [cspPRaw, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
        Finset.mem_singleton, Finset.mem_union, forall_eq_or_imp, forall_eq]
      constructor
      · rintro ⟨⟨hx1, hx2⟩, ⟨hy1, hy2⟩, ⟨hz1, hz2⟩⟩
        refine ⟨⟨hx1, hy1, hz1⟩, fun t ht => ?_⟩
        rcases ht with (ht | ht) | ht
        · exact hx2 t ht
        · exact hy2 t ht
        · exact hz2 t ht
      · rintro ⟨⟨hx1, hy1, hz1⟩, hq⟩
        exact ⟨⟨hx1, fun t ht => hq t (Or.inl (Or.inl ht))⟩,
               ⟨hy1, fun t ht => hq t (Or.inl (Or.inr ht))⟩,
               ⟨hz1, fun t ht => hq t (Or.inr ht)⟩⟩
    have hcard3 : ({x, y, z} : Finset _).card = 3 := by
      have hx_not : x ∉ ({y, z} : Finset _) := by simp [hxy, hxz]
      rw [Finset.card_insert_of_notMem hx_not, Finset.card_pair hyz]
    simp_rw [hiff]
    rw [h_exp_ind, hcard3]
  have h_quad_exp : ∀ {x₁ y₁ x₂ y₂ : Fin (2 ^ cspL C₁ * r_star) → Fin (cspQ C₁)},
      x₁ ≠ y₁ → x₂ ≠ y₂ → x₂ ≠ x₁ → x₂ ≠ y₁ → y₂ ≠ x₁ → y₂ ≠ y₁ →
      ∑ ω : cspIota (2 ^ cspL C₁ * r_star) (cspQ C₁) → Bool,
        (if x₁ ∈ cspPRaw ω ∧ y₁ ∈ cspPRaw ω ∧ x₂ ∈ cspPRaw ω ∧ y₂ ∈ cspPRaw ω
         then bernWeight (cspPIota C₁ r_star) ω else 0) =
        (cspPKeep C₁ r_star) ^ 4 *
          (cspPEdge C₁ r_star) ^
            (homQueries x₁ ∪ homQueries y₁ ∪ homQueries x₂ ∪ homQueries y₂).card := by
    intro x₁ y₁ x₂ y₂ h12 h34 h31 h32 h41 h42
    have hiff : ∀ ω : cspIota (2 ^ cspL C₁ * r_star) (cspQ C₁) → Bool,
        (x₁ ∈ cspPRaw ω ∧ y₁ ∈ cspPRaw ω ∧ x₂ ∈ cspPRaw ω ∧ y₂ ∈ cspPRaw ω) ↔
        ((∀ v ∈ ({x₁, y₁, x₂, y₂} : Finset _), ω (Sum.inr v) = true) ∧
         (∀ t ∈ homQueries x₁ ∪ homQueries y₁ ∪ homQueries x₂ ∪ homQueries y₂,
           ω (Sum.inl t) = true)) := by
      intro ω
      simp only [cspPRaw, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
        Finset.mem_singleton, Finset.mem_union, forall_eq_or_imp, forall_eq]
      constructor
      · rintro ⟨⟨hx1, hx2⟩, ⟨hy1, hy2⟩, ⟨hz1, hz2⟩, ⟨hw1, hw2⟩⟩
        refine ⟨⟨hx1, hy1, hz1, hw1⟩, fun t ht => ?_⟩
        rcases ht with ((ht | ht) | ht) | ht
        · exact hx2 t ht
        · exact hy2 t ht
        · exact hz2 t ht
        · exact hw2 t ht
      · rintro ⟨⟨hx1, hy1, hz1, hw1⟩, hq⟩
        exact ⟨⟨hx1, fun t ht => hq t (Or.inl (Or.inl (Or.inl ht)))⟩,
               ⟨hy1, fun t ht => hq t (Or.inl (Or.inl (Or.inr ht)))⟩,
               ⟨hz1, fun t ht => hq t (Or.inl (Or.inr ht))⟩,
               ⟨hw1, fun t ht => hq t (Or.inr ht)⟩⟩
    have hcard4 : ({x₁, y₁, x₂, y₂} : Finset _).card = 4 := by
      have hn1 : x₁ ∉ ({y₁, x₂, y₂} : Finset _) := by
        simp [h12, Ne.symm h31, Ne.symm h41]
      have hn2 : y₁ ∉ ({x₂, y₂} : Finset _) := by
        simp [Ne.symm h32, Ne.symm h42]
      rw [Finset.card_insert_of_notMem hn1, Finset.card_insert_of_notMem hn2,
        Finset.card_pair h34]
    simp_rw [hiff]
    rw [h_exp_ind, hcard4]
  
  have hE1_exact : ∑ ω : cspIota (2 ^ cspL C₁ * r_star) (cspQ C₁) → Bool,
      bernWeight (cspPIota C₁ r_star) ω *
        (((cspPRaw ω ×ˢ cspPRaw ω).filter (fun xy => dHam xy.1 xy.2 = r_star)).card : ℝ) =
      cspN0 C₁ r_star * cspDStar C₁ r_star := by
    let E_all : Finset ((Fin (2 ^ cspL C₁ * r_star) → Fin (cspQ C₁)) ×
                        (Fin (2 ^ cspL C₁ * r_star) → Fin (cspQ C₁))) :=
      Finset.univ.filter (fun xy => dHam xy.1 xy.2 = r_star)
    have hE_eq_filter : ∀ ω : cspIota (2 ^ cspL C₁ * r_star) (cspQ C₁) → Bool,
        (cspPRaw ω ×ˢ cspPRaw ω).filter (fun xy => dHam xy.1 xy.2 = r_star) =
          E_all.filter (fun xy => xy.1 ∈ cspPRaw ω ∧ xy.2 ∈ cspPRaw ω) := by
      intro ω
      ext xy
      simp only [E_all, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, true_and]
      exact ⟨fun ⟨⟨h1, h2⟩, h3⟩ => ⟨h3, h1, h2⟩, fun ⟨h3, h1, h2⟩ => ⟨⟨h1, h2⟩, h3⟩⟩
    simp_rw [hE_eq_filter]
    rw [h_sum_card_filter]
    have hcongr : ∑ xy ∈ E_all, ∑ ω : cspIota (2 ^ cspL C₁ * r_star) (cspQ C₁) → Bool,
        (if xy.1 ∈ cspPRaw ω ∧ xy.2 ∈ cspPRaw ω
         then bernWeight (cspPIota C₁ r_star) ω else 0) =
      ∑ xy ∈ E_all,
        (cspPKeep C₁ r_star) ^ 2 * (cspPEdge C₁ r_star) ^ (homQueries xy.1 ∪ homQueries xy.2).card := by
      refine Finset.sum_congr rfl (fun xy hxy => ?_)
      simp only [E_all, Finset.mem_filter, Finset.mem_univ, true_and] at hxy
      exact h_pair_exp (hdHam_ne_of_r hxy)
    rw [hcongr]
    exact h_M0_eq
  have hE1 : cspN0 C₁ r_star * cspDStar C₁ r_star ≤
      ∑ ω : cspIota (2 ^ cspL C₁ * r_star) (cspQ C₁) → Bool,
        bernWeight (cspPIota C₁ r_star) ω *
          (((cspPRaw ω ×ˢ cspPRaw ω).filter (fun xy => dHam xy.1 xy.2 = r_star)).card : ℝ) :=
    le_of_eq hE1_exact.symm
  
  obtain ⟨h_s6_deg, h_s6_edge⟩ :=
    raw_degree_and_edge_second_moment_sums C₁ hC₁ r_star hr hσ_pos hp_edge_pos hp_edge_lt1
      h_cal hσ_low hp_keep_pos h_union_card h_sphere h_M0_eq
  
  have hW2 : ∑ ω : cspIota (2 ^ cspL C₁ * r_star) (cspQ C₁) → Bool,
      bernWeight (cspPIota C₁ r_star) ω *
        (∑ x ∈ cspPRaw ω, (((cspPRaw ω).filter (fun y => dHam x y = r_star)).card : ℝ) ^ 2) ≤
      2 * cspGamma r_star * cspN0 C₁ r_star * (cspDStar C₁ r_star) ^ 2 := by
    have hW2_pt_gen : ∀ {V : Type} [Fintype V] [DecidableEq V]
        (Rel : V → V → Prop) [DecidableRel Rel] (S : Finset V),
        (∑ x ∈ S, ((S.filter (fun y => Rel x y)).card : ℝ) ^ 2) ≤
          (((S ×ˢ S).filter (fun xy => Rel xy.1 xy.2)).card : ℝ) +
          (((Finset.univ.filter (fun xyz : V × V × V =>
              Rel xyz.1 xyz.2.1 ∧ Rel xyz.1 xyz.2.2 ∧ xyz.2.1 ≠ xyz.2.2)).filter
            (fun xyz => xyz.1 ∈ S ∧ xyz.2.1 ∈ S ∧ xyz.2.2 ∈ S)).card : ℝ) := by
      intro V _ _ Rel _ S
      let Nx := fun x : V => S.filter (fun y => Rel x y)
      let T3_off := Finset.univ.filter (fun xyz : V × V × V =>
        Rel xyz.1 xyz.2.1 ∧ Rel xyz.1 xyz.2.2 ∧ xyz.2.1 ≠ xyz.2.2)
      have hsq_nat : ∀ x ∈ S,
          (Nx x).card ^ 2 ≤ (Nx x).card + ((Nx x ×ˢ Nx x).filter (fun yz => yz.1 ≠ yz.2)).card := by
        intro x _
        have hcard_prod : (Nx x).card ^ 2 = (Nx x ×ˢ Nx x).card := by
          rw [sq, Finset.card_product]
        have hcov_nx : Nx x ×ˢ Nx x ⊆
            (Nx x ×ˢ Nx x).filter (fun yz => yz.1 = yz.2) ∪
            (Nx x ×ˢ Nx x).filter (fun yz => yz.1 ≠ yz.2) := by
          intro yz hyz
          simp only [Finset.mem_union, Finset.mem_filter]
          by_cases h : yz.1 = yz.2
          · exact Or.inl ⟨hyz, h⟩
          · exact Or.inr ⟨hyz, h⟩
        have hc1 := Finset.card_le_card hcov_nx
        have hc2 := Finset.card_union_le
          ((Nx x ×ˢ Nx x).filter (fun yz => yz.1 = yz.2))
          ((Nx x ×ˢ Nx x).filter (fun yz => yz.1 ≠ yz.2))
        have hdiag : ((Nx x ×ˢ Nx x).filter (fun yz => yz.1 = yz.2)).card ≤ (Nx x).card := by
          apply Finset.card_le_card_of_injOn Prod.fst
          · intro yz hyz
            simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_product] at hyz
            exact hyz.1.1
          · intro yz₁ h₁ yz₂ h₂ heq
            simp only [Finset.mem_coe, Finset.mem_filter] at h₁ h₂
            ext
            · exact heq
            · rw [← h₁.2, ← h₂.2, heq]
        omega
      have hsum1 : ∑ x ∈ S, (Nx x).card =
          ((S ×ˢ S).filter (fun xy => Rel xy.1 xy.2)).card := by
        have hbi : (S ×ˢ S).filter (fun xy => Rel xy.1 xy.2) =
            S.biUnion (fun x => (Nx x).image (fun y => (x, y))) := by
          ext xy
          simp only [Nx, Finset.mem_filter, Finset.mem_product, Finset.mem_biUnion, Finset.mem_image]
          constructor
          · rintro ⟨⟨hx, hy⟩, hr_xy⟩
            exact ⟨xy.1, hx, xy.2, ⟨hy, hr_xy⟩, Prod.eta xy⟩
          · rintro ⟨x, hx, y, ⟨hy, hr_xy⟩, rfl⟩
            exact ⟨⟨hx, hy⟩, hr_xy⟩
        rw [hbi, Finset.card_biUnion]
        · refine Finset.sum_congr rfl
            (fun x _ => (Finset.card_image_of_injective _ (fun _ _ h => (Prod.mk.inj h).2)).symm)
        · intro x₁ _ x₂ _ hne
          simp only [Function.onFun, Finset.disjoint_left]
          intro p hp1 hp2
          rcases Finset.mem_image.mp hp1 with ⟨_, _, rfl⟩
          rcases Finset.mem_image.mp hp2 with ⟨_, _, hp⟩
          exact hne (Prod.mk.inj hp).1.symm
      have hsum2 : ∑ x ∈ S, ((Nx x ×ˢ Nx x).filter (fun yz => yz.1 ≠ yz.2)).card ≤
          (T3_off.filter (fun xyz => xyz.1 ∈ S ∧ xyz.2.1 ∈ S ∧ xyz.2.2 ∈ S)).card := by
        have hdisj : (S : Set V).PairwiseDisjoint
            (fun x => (((Nx x ×ˢ Nx x).filter (fun yz => yz.1 ≠ yz.2)).image (fun yz => (x, yz)))) := by
          intro x₁ _ x₂ _ hne
          simp only [Function.onFun, Finset.disjoint_left]
          intro p hp1 hp2
          rcases Finset.mem_image.mp hp1 with ⟨_, _, rfl⟩
          rcases Finset.mem_image.mp hp2 with ⟨_, _, hp⟩
          exact hne (Prod.mk.inj hp).1.symm
        have hsub : S.biUnion
            (fun x => (((Nx x ×ˢ Nx x).filter (fun yz => yz.1 ≠ yz.2)).image (fun yz => (x, yz)))) ⊆
            T3_off.filter (fun xyz => xyz.1 ∈ S ∧ xyz.2.1 ∈ S ∧ xyz.2.2 ∈ S) := by
          intro xyz hxyz
          rcases Finset.mem_biUnion.mp hxyz with ⟨x, hx, himg⟩
          rcases Finset.mem_image.mp himg with ⟨⟨y, z⟩, hyz, rfl⟩
          simp only [Nx, Finset.mem_filter, Finset.mem_product] at hyz
          simp only [T3_off, Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨⟨hyz.1.1.2, hyz.1.2.2, hyz.2⟩, hx, hyz.1.1.1, hyz.1.2.1⟩
        calc
          ∑ x ∈ S, ((Nx x ×ˢ Nx x).filter (fun yz => yz.1 ≠ yz.2)).card
            = ∑ x ∈ S, (((Nx x ×ˢ Nx x).filter (fun yz => yz.1 ≠ yz.2)).image
                (fun yz => (x, yz))).card := by
                refine Finset.sum_congr rfl (fun x _ =>
                  (Finset.card_image_of_injective _ (fun _ _ h => (Prod.mk.inj h).2)).symm)
          _ = (S.biUnion (fun x => (((Nx x ×ˢ Nx x).filter (fun yz => yz.1 ≠ yz.2)).image
                (fun yz => (x, yz))))).card := (Finset.card_biUnion hdisj).symm
          _ ≤ (T3_off.filter (fun xyz => xyz.1 ∈ S ∧ xyz.2.1 ∈ S ∧ xyz.2.2 ∈ S)).card :=
                Finset.card_le_card hsub
      have hnat_tot : ∑ x ∈ S, (Nx x).card ^ 2 ≤
          ((S ×ˢ S).filter (fun xy => Rel xy.1 xy.2)).card +
          (T3_off.filter (fun xyz => xyz.1 ∈ S ∧ xyz.2.1 ∈ S ∧ xyz.2.2 ∈ S)).card := by
        calc
          ∑ x ∈ S, (Nx x).card ^ 2
            ≤ ∑ x ∈ S, ((Nx x).card + ((Nx x ×ˢ Nx x).filter (fun yz => yz.1 ≠ yz.2)).card) :=
              Finset.sum_le_sum hsq_nat
          _ = (∑ x ∈ S, (Nx x).card) +
                ∑ x ∈ S, ((Nx x ×ˢ Nx x).filter (fun yz => yz.1 ≠ yz.2)).card :=
              Finset.sum_add_distrib
          _ ≤ ((S ×ˢ S).filter (fun xy => Rel xy.1 xy.2)).card +
                (T3_off.filter (fun xyz => xyz.1 ∈ S ∧ xyz.2.1 ∈ S ∧ xyz.2.2 ∈ S)).card := by
              rw [hsum1]
              exact Nat.add_le_add_left hsum2 _
      exact_mod_cast hnat_tot
    let T3_off := Finset.univ.filter
      (fun xyz : (Fin (2 ^ cspL C₁ * r_star) → Fin (cspQ C₁)) ×
                 (Fin (2 ^ cspL C₁ * r_star) → Fin (cspQ C₁)) ×
                 (Fin (2 ^ cspL C₁ * r_star) → Fin (cspQ C₁)) =>
        dHam xyz.1 xyz.2.1 = r_star ∧ dHam xyz.1 xyz.2.2 = r_star ∧ xyz.2.1 ≠ xyz.2.2)
    have hW2_off_exp : ∑ ω : cspIota (2 ^ cspL C₁ * r_star) (cspQ C₁) → Bool,
        bernWeight (cspPIota C₁ r_star) ω *
          ((T3_off.filter (fun xyz =>
            xyz.1 ∈ cspPRaw ω ∧ xyz.2.1 ∈ cspPRaw ω ∧ xyz.2.2 ∈ cspPRaw ω)).card : ℝ) ≤
        (3 / 2 : ℝ) * cspGamma r_star * cspN0 C₁ r_star * (cspDStar C₁ r_star) ^ 2 := by
      rw [h_sum_card_filter]
      have hcongr : ∑ xyz ∈ T3_off, ∑ ω : cspIota (2 ^ cspL C₁ * r_star) (cspQ C₁) → Bool,
          (if xyz.1 ∈ cspPRaw ω ∧ xyz.2.1 ∈ cspPRaw ω ∧ xyz.2.2 ∈ cspPRaw ω
           then bernWeight (cspPIota C₁ r_star) ω else 0) =
        ∑ xyz ∈ T3_off,
          (cspPKeep C₁ r_star) ^ 3 *
            (cspPEdge C₁ r_star) ^ (homQueries xyz.1 ∪ homQueries xyz.2.1 ∪ homQueries xyz.2.2).card := by
        refine Finset.sum_congr rfl (fun xyz hxyz => ?_)
        simp only [T3_off, Finset.mem_filter, Finset.mem_univ, true_and] at hxyz
        exact h_triple_exp (hdHam_ne_of_r hxyz.1) (hdHam_ne_of_r hxyz.2.1) hxyz.2.2
      rw [hcongr]
      exact h_s6_deg
    have hD_ge2 : (2 : ℝ) ≤ cspDStar C₁ r_star := by
      unfold cspDStar
      have hexp : (1 : ℝ) ≤ (1 / 4 : ℝ) * (cspLam0 C₁ : ℝ) * (r_star : ℝ) := by
        nlinarith only [hlam0_real, hr_ge3001_real]
      calc
        (2 : ℝ) = (2 : ℝ) ^ (1 : ℝ) := (Real.rpow_one 2).symm
        _ ≤ (2 : ℝ) ^ ((1 / 4 : ℝ) * (cspLam0 C₁ : ℝ) * (r_star : ℝ)) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
    have hstep1 : ∑ ω : cspIota (2 ^ cspL C₁ * r_star) (cspQ C₁) → Bool,
        bernWeight (cspPIota C₁ r_star) ω *
          (∑ x ∈ cspPRaw ω, (((cspPRaw ω).filter (fun y => dHam x y = r_star)).card : ℝ) ^ 2) ≤
      (∑ ω : cspIota (2 ^ cspL C₁ * r_star) (cspQ C₁) → Bool,
        bernWeight (cspPIota C₁ r_star) ω *
          (((cspPRaw ω ×ˢ cspPRaw ω).filter (fun xy => dHam xy.1 xy.2 = r_star)).card : ℝ)) +
      (∑ ω : cspIota (2 ^ cspL C₁ * r_star) (cspQ C₁) → Bool,
        bernWeight (cspPIota C₁ r_star) ω *
          ((T3_off.filter (fun xyz =>
            xyz.1 ∈ cspPRaw ω ∧ xyz.2.1 ∈ cspPRaw ω ∧ xyz.2.2 ∈ cspPRaw ω)).card : ℝ)) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_le_sum (fun ω _ => ?_)
      rw [← mul_add]
      exact mul_le_mul_of_nonneg_left
        (hW2_pt_gen (fun x y => dHam x y = r_star) (cspPRaw ω)) (hW_nn ω)
    have hdiag_le : cspN0 C₁ r_star * cspDStar C₁ r_star ≤
        (1 / 2 : ℝ) * cspGamma r_star * cspN0 C₁ r_star * (cspDStar C₁ r_star) ^ 2 := by
      have h1 : (1 : ℝ) ≤ (1 / 2 : ℝ) * cspGamma r_star * cspDStar C₁ r_star := by
        nlinarith only [hγ_ge1, hD_ge2]
      have h2 : 0 ≤ cspN0 C₁ r_star * cspDStar C₁ r_star := by positivity
      have hmul := mul_le_mul_of_nonneg_right h1 h2
      linarith [show ((1 / 2 : ℝ) * cspGamma r_star * cspDStar C₁ r_star) *
        (cspN0 C₁ r_star * cspDStar C₁ r_star) =
        (1 / 2 : ℝ) * cspGamma r_star * cspN0 C₁ r_star * (cspDStar C₁ r_star) ^ 2 by ring]
    linarith only [hstep1, hE1_exact, hW2_off_exp, hdiag_le]
  
  have hE2 : ∑ ω : cspIota (2 ^ cspL C₁ * r_star) (cspQ C₁) → Bool,
      bernWeight (cspPIota C₁ r_star) ω *
        ((((cspPRaw ω ×ˢ cspPRaw ω).filter (fun xy => dHam xy.1 xy.2 = r_star)).card : ℝ) ^ 2) ≤
      3 * cspGamma r_star * (cspN0 C₁ r_star * cspDStar C₁ r_star) ^ 2 := by
    have hE2_pt_gen : ∀ {V : Type} [Fintype V] [DecidableEq V]
        (Rel : V → V → Prop) [DecidableRel Rel] (hSymm : Symmetric Rel) (S : Finset V),
        ((((S ×ˢ S).filter (fun xy => Rel xy.1 xy.2)).card : ℝ) ^ 2) ≤
        4 * (∑ x ∈ S, ((S.filter (fun y => Rel x y)).card : ℝ) ^ 2) +
        (((Finset.univ.filter (fun e₁₂ : (V × V) × (V × V) =>
            Rel e₁₂.1.1 e₁₂.1.2 ∧ Rel e₁₂.2.1 e₁₂.2.2 ∧
            e₁₂.2.1 ≠ e₁₂.1.1 ∧ e₁₂.2.1 ≠ e₁₂.1.2 ∧
            e₁₂.2.2 ≠ e₁₂.1.1 ∧ e₁₂.2.2 ≠ e₁₂.1.2)).filter
          (fun e₁₂ => e₁₂.1.1 ∈ S ∧ e₁₂.1.2 ∈ S ∧ e₁₂.2.1 ∈ S ∧ e₁₂.2.2 ∈ S)).card : ℝ) := by
      intro V _ _ Rel _ hSymm S
      let Eω := (S ×ˢ S).filter (fun xy => Rel xy.1 xy.2)
      let Nx := fun x : V => S.filter (fun y => Rel x y)
      let T3ω := S.biUnion (fun x => ((Nx x ×ˢ Nx x).image (fun yz => (x, yz))))
      let E4_d := Finset.univ.filter (fun e₁₂ : (V × V) × (V × V) =>
        Rel e₁₂.1.1 e₁₂.1.2 ∧ Rel e₁₂.2.1 e₁₂.2.2 ∧
        e₁₂.2.1 ≠ e₁₂.1.1 ∧ e₁₂.2.1 ≠ e₁₂.1.2 ∧
        e₁₂.2.2 ≠ e₁₂.1.1 ∧ e₁₂.2.2 ≠ e₁₂.1.2)
      have hT3_card : T3ω.card = ∑ x ∈ S, (Nx x).card ^ 2 := by
        rw [Finset.card_biUnion]
        · refine Finset.sum_congr rfl (fun x _ => ?_)
          rw [Finset.card_image_of_injective _ (fun _ _ h => (Prod.mk.inj h).2),
            Finset.card_product, sq]
        · intro x₁ _ x₂ _ hne
          simp only [Function.onFun, Finset.disjoint_left]
          intro p hp1 hp2
          rcases Finset.mem_image.mp hp1 with ⟨_, _, rfl⟩
          rcases Finset.mem_image.mp hp2 with ⟨_, _, hp⟩
          exact hne (Prod.mk.inj hp).1.symm
      have hdisj_sub : ((Eω ×ˢ Eω).filter (fun e₁₂ =>
          e₁₂.2.1 ≠ e₁₂.1.1 ∧ e₁₂.2.1 ≠ e₁₂.1.2 ∧
          e₁₂.2.2 ≠ e₁₂.1.1 ∧ e₁₂.2.2 ≠ e₁₂.1.2)).card ≤
        (E4_d.filter (fun e₁₂ =>
          e₁₂.1.1 ∈ S ∧ e₁₂.1.2 ∈ S ∧ e₁₂.2.1 ∈ S ∧ e₁₂.2.2 ∈ S)).card := by
        apply Finset.card_le_card
        intro e₁₂ he
        simp only [Eω, E4_d, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, true_and] at he ⊢
        exact ⟨⟨he.1.1.2, he.1.2.2, he.2⟩, he.1.1.1.1, he.1.1.1.2, he.1.2.1.1, he.1.2.1.2⟩
      let O₁ := (Eω ×ˢ Eω).filter (fun e₁₂ => e₁₂.2.1 = e₁₂.1.1)
      let O₂ := (Eω ×ˢ Eω).filter (fun e₁₂ => e₁₂.2.1 = e₁₂.1.2)
      let O₃ := (Eω ×ˢ Eω).filter (fun e₁₂ => e₁₂.2.2 = e₁₂.1.1)
      let O₄ := (Eω ×ˢ Eω).filter (fun e₁₂ => e₁₂.2.2 = e₁₂.1.2)
      have hcov : Eω ×ˢ Eω ⊆ ((O₁ ∪ O₂) ∪ (O₃ ∪ O₄)) ∪
          (Eω ×ˢ Eω).filter (fun e₁₂ =>
            e₁₂.2.1 ≠ e₁₂.1.1 ∧ e₁₂.2.1 ≠ e₁₂.1.2 ∧
            e₁₂.2.2 ≠ e₁₂.1.1 ∧ e₁₂.2.2 ≠ e₁₂.1.2) := by
        intro e₁₂ he
        simp only [O₁, O₂, O₃, O₄, Finset.mem_union, Finset.mem_filter]
        by_cases h1 : e₁₂.2.1 = e₁₂.1.1
        · exact Or.inl (Or.inl (Or.inl ⟨he, h1⟩))
        · by_cases h2 : e₁₂.2.1 = e₁₂.1.2
          · exact Or.inl (Or.inl (Or.inr ⟨he, h2⟩))
          · by_cases h3 : e₁₂.2.2 = e₁₂.1.1
            · exact Or.inl (Or.inr (Or.inl ⟨he, h3⟩))
            · by_cases h4 : e₁₂.2.2 = e₁₂.1.2
              · exact Or.inl (Or.inr (Or.inr ⟨he, h4⟩))
              · exact Or.inr ⟨he, h1, h2, h3, h4⟩
      have hO₁ : O₁.card ≤ T3ω.card := by
        apply Finset.card_le_card_of_injOn (fun e₁₂ => (e₁₂.1.1, (e₁₂.1.2, e₁₂.2.2)))
        · intro e₁₂ he
          simp only [O₁, Eω, T3ω, Nx, Finset.mem_coe, Finset.mem_filter, Finset.mem_product,
            Finset.mem_biUnion, Finset.mem_image] at he ⊢
          refine ⟨e₁₂.1.1, he.1.1.1.1, (e₁₂.1.2, e₁₂.2.2), ?_, rfl⟩
          refine ⟨⟨he.1.1.1.2, he.1.1.2⟩, ⟨he.1.2.1.2, ?_⟩⟩
          rw [← he.2]
          exact he.1.2.2
        · rintro ⟨⟨a₁, b₁⟩, ⟨c₁, d₁⟩⟩ h₁ ⟨⟨a₂, b₂⟩, ⟨c₂, d₂⟩⟩ h₂ heq
          simp only [O₁, Finset.mem_coe, Finset.mem_filter, Prod.mk.injEq] at h₁ h₂ heq
          rcases heq with ⟨rfl, rfl, rfl⟩
          rw [h₁.2, h₂.2]
      have hO₂ : O₂.card ≤ T3ω.card := by
        apply Finset.card_le_card_of_injOn (fun e₁₂ => (e₁₂.1.2, (e₁₂.1.1, e₁₂.2.2)))
        · intro e₁₂ he
          simp only [O₂, Eω, T3ω, Nx, Finset.mem_coe, Finset.mem_filter, Finset.mem_product,
            Finset.mem_biUnion, Finset.mem_image] at he ⊢
          refine ⟨e₁₂.1.2, he.1.1.1.2, (e₁₂.1.1, e₁₂.2.2), ?_, rfl⟩
          refine ⟨⟨he.1.1.1.1, hSymm he.1.1.2⟩, ⟨he.1.2.1.2, ?_⟩⟩
          rw [← he.2]
          exact he.1.2.2
        · rintro ⟨⟨a₁, b₁⟩, ⟨c₁, d₁⟩⟩ h₁ ⟨⟨a₂, b₂⟩, ⟨c₂, d₂⟩⟩ h₂ heq
          simp only [O₂, Finset.mem_coe, Finset.mem_filter, Prod.mk.injEq] at h₁ h₂ heq
          rcases heq with ⟨rfl, rfl, rfl⟩
          rw [h₁.2, h₂.2]
      have hO₃ : O₃.card ≤ T3ω.card := by
        apply Finset.card_le_card_of_injOn (fun e₁₂ => (e₁₂.1.1, (e₁₂.1.2, e₁₂.2.1)))
        · intro e₁₂ he
          simp only [O₃, Eω, T3ω, Nx, Finset.mem_coe, Finset.mem_filter, Finset.mem_product,
            Finset.mem_biUnion, Finset.mem_image] at he ⊢
          refine ⟨e₁₂.1.1, he.1.1.1.1, (e₁₂.1.2, e₁₂.2.1), ?_, rfl⟩
          refine ⟨⟨he.1.1.1.2, he.1.1.2⟩, ⟨he.1.2.1.1, ?_⟩⟩
          rw [← he.2]
          exact hSymm he.1.2.2
        · rintro ⟨⟨a₁, b₁⟩, ⟨c₁, d₁⟩⟩ h₁ ⟨⟨a₂, b₂⟩, ⟨c₂, d₂⟩⟩ h₂ heq
          simp only [O₃, Finset.mem_coe, Finset.mem_filter, Prod.mk.injEq] at h₁ h₂ heq
          rcases heq with ⟨rfl, rfl, rfl⟩
          rw [h₁.2, h₂.2]
      have hO₄ : O₄.card ≤ T3ω.card := by
        apply Finset.card_le_card_of_injOn (fun e₁₂ => (e₁₂.1.2, (e₁₂.1.1, e₁₂.2.1)))
        · intro e₁₂ he
          simp only [O₄, Eω, T3ω, Nx, Finset.mem_coe, Finset.mem_filter, Finset.mem_product,
            Finset.mem_biUnion, Finset.mem_image] at he ⊢
          refine ⟨e₁₂.1.2, he.1.1.1.2, (e₁₂.1.1, e₁₂.2.1), ?_, rfl⟩
          refine ⟨⟨he.1.1.1.1, hSymm he.1.1.2⟩, ⟨he.1.2.1.1, ?_⟩⟩
          rw [← he.2]
          exact hSymm he.1.2.2
        · rintro ⟨⟨a₁, b₁⟩, ⟨c₁, d₁⟩⟩ h₁ ⟨⟨a₂, b₂⟩, ⟨c₂, d₂⟩⟩ h₂ heq
          simp only [O₄, Finset.mem_coe, Finset.mem_filter, Prod.mk.injEq] at h₁ h₂ heq
          rcases heq with ⟨rfl, rfl, rfl⟩
          rw [h₁.2, h₂.2]
      have hnat : Eω.card ^ 2 ≤
          4 * (∑ x ∈ S, (Nx x).card ^ 2) +
          (E4_d.filter (fun e₁₂ =>
            e₁₂.1.1 ∈ S ∧ e₁₂.1.2 ∈ S ∧ e₁₂.2.1 ∈ S ∧ e₁₂.2.2 ∈ S)).card := by
        have hprod : Eω.card ^ 2 = (Eω ×ˢ Eω).card := by rw [sq, Finset.card_product]
        have h0 := Finset.card_le_card hcov
        have h1 := Finset.card_union_le ((O₁ ∪ O₂) ∪ (O₃ ∪ O₄))
          ((Eω ×ˢ Eω).filter (fun e₁₂ =>
            e₁₂.2.1 ≠ e₁₂.1.1 ∧ e₁₂.2.1 ≠ e₁₂.1.2 ∧
            e₁₂.2.2 ≠ e₁₂.1.1 ∧ e₁₂.2.2 ≠ e₁₂.1.2))
        have h2 := Finset.card_union_le (O₁ ∪ O₂) (O₃ ∪ O₄)
        have h3 := Finset.card_union_le O₁ O₂
        have h4 := Finset.card_union_le O₃ O₄
        omega
      exact_mod_cast hnat
    let E4_disj := Finset.univ.filter
      (fun e₁₂ : ((Fin (2 ^ cspL C₁ * r_star) → Fin (cspQ C₁)) ×
                  (Fin (2 ^ cspL C₁ * r_star) → Fin (cspQ C₁))) ×
                 ((Fin (2 ^ cspL C₁ * r_star) → Fin (cspQ C₁)) ×
                  (Fin (2 ^ cspL C₁ * r_star) → Fin (cspQ C₁))) =>
        dHam e₁₂.1.1 e₁₂.1.2 = r_star ∧ dHam e₁₂.2.1 e₁₂.2.2 = r_star ∧
        e₁₂.2.1 ≠ e₁₂.1.1 ∧ e₁₂.2.1 ≠ e₁₂.1.2 ∧
        e₁₂.2.2 ≠ e₁₂.1.1 ∧ e₁₂.2.2 ≠ e₁₂.1.2)
    have hE4_exp : ∑ ω : cspIota (2 ^ cspL C₁ * r_star) (cspQ C₁) → Bool,
        bernWeight (cspPIota C₁ r_star) ω *
          ((E4_disj.filter (fun e₁₂ =>
            e₁₂.1.1 ∈ cspPRaw ω ∧ e₁₂.1.2 ∈ cspPRaw ω ∧
            e₁₂.2.1 ∈ cspPRaw ω ∧ e₁₂.2.2 ∈ cspPRaw ω)).card : ℝ) ≤
        2 * cspGamma r_star * (cspN0 C₁ r_star * cspDStar C₁ r_star) ^ 2 := by
      rw [h_sum_card_filter]
      have hcongr : ∑ e₁₂ ∈ E4_disj, ∑ ω : cspIota (2 ^ cspL C₁ * r_star) (cspQ C₁) → Bool,
          (if e₁₂.1.1 ∈ cspPRaw ω ∧ e₁₂.1.2 ∈ cspPRaw ω ∧
              e₁₂.2.1 ∈ cspPRaw ω ∧ e₁₂.2.2 ∈ cspPRaw ω
           then bernWeight (cspPIota C₁ r_star) ω else 0) =
        ∑ e₁₂ ∈ E4_disj,
          (cspPKeep C₁ r_star) ^ 4 *
            (cspPEdge C₁ r_star) ^
              (homQueries e₁₂.1.1 ∪ homQueries e₁₂.1.2 ∪
               homQueries e₁₂.2.1 ∪ homQueries e₁₂.2.2).card := by
        refine Finset.sum_congr rfl (fun e₁₂ he => ?_)
        simp only [E4_disj, Finset.mem_filter, Finset.mem_univ, true_and] at he
        exact h_quad_exp (hdHam_ne_of_r he.1) (hdHam_ne_of_r he.2.1)
          he.2.2.1 he.2.2.2.1 he.2.2.2.2.1 he.2.2.2.2.2
      rw [hcongr]
      exact h_s6_edge
    have hn0_ge8 : (8 : ℝ) ≤ cspN0 C₁ r_star := by
      have hexp3 : (3 : ℝ) ≤
          (99 / 100 : ℝ) * (cspBeta0 C₁ : ℝ) * (2 : ℝ) ^ (2 * cspL C₁) * (r_star : ℝ) := by
        have hmul1 : (6000 : ℝ) ≤ (cspBeta0 C₁ : ℝ) * (2 : ℝ) ^ (2 * cspL C₁) := by
          nlinarith only [hbeta0_real, h22L_real]
        nlinarith only [hmul1, hr_ge3001_real]
      have h8 : (8 : ℝ) = (2 : ℝ) ^ (3 : ℝ) := by norm_num
      rw [h8]
      exact le_trans (Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp3) hn0_low
    have hstep1 : ∑ ω : cspIota (2 ^ cspL C₁ * r_star) (cspQ C₁) → Bool,
        bernWeight (cspPIota C₁ r_star) ω *
          ((((cspPRaw ω ×ˢ cspPRaw ω).filter (fun xy => dHam xy.1 xy.2 = r_star)).card : ℝ) ^ 2) ≤
      4 * (∑ ω : cspIota (2 ^ cspL C₁ * r_star) (cspQ C₁) → Bool,
        bernWeight (cspPIota C₁ r_star) ω *
          (∑ x ∈ cspPRaw ω, (((cspPRaw ω).filter (fun y => dHam x y = r_star)).card : ℝ) ^ 2)) +
      (∑ ω : cspIota (2 ^ cspL C₁ * r_star) (cspQ C₁) → Bool,
        bernWeight (cspPIota C₁ r_star) ω *
          ((E4_disj.filter (fun e₁₂ =>
            e₁₂.1.1 ∈ cspPRaw ω ∧ e₁₂.1.2 ∈ cspPRaw ω ∧
            e₁₂.2.1 ∈ cspPRaw ω ∧ e₁₂.2.2 ∈ cspPRaw ω)).card : ℝ)) := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_le_sum (fun ω _ => ?_)
      have hp := mul_le_mul_of_nonneg_left
        (hE2_pt_gen (fun x y => dHam x y = r_star) hRel_symm (cspPRaw ω)) (hW_nn ω)
      linarith [hp]
    have hov_bound : 8 * cspGamma r_star * cspN0 C₁ r_star * (cspDStar C₁ r_star) ^ 2 ≤
        cspGamma r_star * (cspN0 C₁ r_star * cspDStar C₁ r_star) ^ 2 := by
      have hnn : 0 ≤ cspGamma r_star * cspN0 C₁ r_star * (cspDStar C₁ r_star) ^ 2 := by positivity
      have hmul := mul_le_mul_of_nonneg_left hn0_ge8 hnn
      linarith [show cspGamma r_star * cspN0 C₁ r_star * (cspDStar C₁ r_star) ^ 2 * 8 =
                  8 * cspGamma r_star * cspN0 C₁ r_star * (cspDStar C₁ r_star) ^ 2 by ring,
                show cspGamma r_star * cspN0 C₁ r_star * (cspDStar C₁ r_star) ^ 2 * cspN0 C₁ r_star =
                  cspGamma r_star * (cspN0 C₁ r_star * cspDStar C₁ r_star) ^ 2 by ring]
    linarith only [hstep1, hW2, hE4_exp, hov_bound]
  
  obtain ⟨h_s5_d3, h_s5_ch⟩ :=
    d3_and_cherry_query_sum_bounds C₁ hC₁ r_star hr hσ_pos hp_edge_pos hp_edge_lt1
      h_cal hσ_up h_binom_edge hp_keep_pos hp_keep_up
  
  have hBD3_exp : ∑ ω : cspIota (2 ^ cspL C₁ * r_star) (cspQ C₁) → Bool,
      bernWeight (cspPIota C₁ r_star) ω * ((cspBD3 C₁ r_star ω).card : ℝ) ≤
      (1 / 4 : ℝ) * cspDeltaBad C₁ r_star * cspN0 C₁ r_star := by
    let BallPairs := Finset.univ.filter
      (fun ab : (Fin (2 ^ cspL C₁ * r_star) → Fin (cspQ C₁)) ×
                (Fin (2 ^ cspL C₁ * r_star) → Fin (cspQ C₁)) =>
        ab.1 ≠ ab.2 ∧ dHam ab.1 ab.2 ≤ C₁ * r_star)
    let Z_d3 := fun x u : Fin (2 ^ cspL C₁ * r_star) → Fin (cspQ C₁) =>
      Finset.univ.filter (fun z =>
        dHam x z ≤ C₁ * r_star ∧
        r_star < cspInvEta0 C₁ * (d3Coords x u z).card)
    let Triples_d3 := BallPairs.biUnion (fun xu => (Z_d3 xu.1 xu.2).image (fun z => (xu.1, (xu.2, z))))
    have hd3_distinct : ∀ {N q : ℕ} {x u z : Fin N → Fin q},
        r_star < cspInvEta0 C₁ * (d3Coords x u z).card →
        x ≠ u ∧ x ≠ z ∧ u ≠ z := by
      intro N q x u z hlt
      have hpos : 0 < (d3Coords x u z).card := by
        by_contra h0
        have heq0 : (d3Coords x u z).card = 0 := by omega
        rw [heq0, mul_zero] at hlt
        omega
      obtain ⟨v, hv⟩ := Finset.card_pos.mp hpos
      simp only [d3Coords, Finset.mem_filter, Finset.mem_univ, true_and] at hv
      exact ⟨fun h => hv.1 (congr_fun h v),
             fun h => hv.2.1 (congr_fun h v),
             fun h => hv.2.2 (congr_fun h v)⟩
    have hpt : ∀ ω : cspIota (2 ^ cspL C₁ * r_star) (cspQ C₁) → Bool,
        (cspBD3 C₁ r_star ω).card ≤ (Triples_d3.filter (fun xuz =>
          xuz.1 ∈ cspPRaw ω ∧ xuz.2.1 ∈ cspPRaw ω ∧
          (∀ t ∈ homQueries xuz.2.2, ω (Sum.inl t) = true))).card := by
      intro ω
      have hsub : cspBD3 C₁ r_star ω ⊆ (Triples_d3.filter (fun xuz =>
          xuz.1 ∈ cspPRaw ω ∧ xuz.2.1 ∈ cspPRaw ω ∧
          (∀ t ∈ homQueries xuz.2.2, ω (Sum.inl t) = true))).image Prod.fst := by
        intro x hx
        simp only [cspBD3, Finset.mem_filter] at hx
        rcases hx with ⟨hxP, u, huP, z, hzHom, hdu, hdz, hlt⟩
        have hdist := hd3_distinct hlt
        rw [Finset.mem_image]
        refine ⟨(x, (u, z)), ?_, rfl⟩
        simp only [Triples_d3, BallPairs, Z_d3, Finset.mem_filter, Finset.mem_biUnion,
          Finset.mem_image, Finset.mem_univ, true_and]
        exact ⟨⟨(x, u), ⟨hdist.1, hdu⟩, z, ⟨hdz, hlt⟩, rfl⟩, hxP, huP, hzHom⟩
      exact le_trans (Finset.card_le_card hsub) Finset.card_image_le
    have hstep1 : ∑ ω : cspIota (2 ^ cspL C₁ * r_star) (cspQ C₁) → Bool,
        bernWeight (cspPIota C₁ r_star) ω * ((cspBD3 C₁ r_star ω).card : ℝ) ≤
        ∑ ω : cspIota (2 ^ cspL C₁ * r_star) (cspQ C₁) → Bool,
          bernWeight (cspPIota C₁ r_star) ω * ((Triples_d3.filter (fun xuz =>
            xuz.1 ∈ cspPRaw ω ∧ xuz.2.1 ∈ cspPRaw ω ∧
            (∀ t ∈ homQueries xuz.2.2, ω (Sum.inl t) = true))).card : ℝ) := by
      refine Finset.sum_le_sum (fun ω _ => mul_le_mul_of_nonneg_left ?_ (hW_nn ω))
      exact_mod_cast (hpt ω)
    rw [h_sum_card_filter] at hstep1
    have h_d3_ind_exp : ∀ {x u z : Fin (2 ^ cspL C₁ * r_star) → Fin (cspQ C₁)}, x ≠ u →
        ∑ ω : cspIota (2 ^ cspL C₁ * r_star) (cspQ C₁) → Bool,
          (if x ∈ cspPRaw ω ∧ u ∈ cspPRaw ω ∧ (∀ t ∈ homQueries z, ω (Sum.inl t) = true)
           then bernWeight (cspPIota C₁ r_star) ω else 0) =
        (cspPKeep C₁ r_star) ^ 2 *
          (cspPEdge C₁ r_star) ^ (homQueries x ∪ homQueries u ∪ homQueries z).card := by
      intro x u z hxu
      have hiff : ∀ ω : cspIota (2 ^ cspL C₁ * r_star) (cspQ C₁) → Bool,
          (x ∈ cspPRaw ω ∧ u ∈ cspPRaw ω ∧ (∀ t ∈ homQueries z, ω (Sum.inl t) = true)) ↔
          ((∀ v ∈ ({x, u} : Finset _), ω (Sum.inr v) = true) ∧
           (∀ t ∈ homQueries x ∪ homQueries u ∪ homQueries z, ω (Sum.inl t) = true)) := by
        intro ω
        simp only [cspPRaw, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
          Finset.mem_singleton, Finset.mem_union, forall_eq_or_imp, forall_eq]
        constructor
        · rintro ⟨⟨hx1, hx2⟩, ⟨hu1, hu2⟩, hz2⟩
          refine ⟨⟨hx1, hu1⟩, fun t ht => ?_⟩
          rcases ht with (ht | ht) | ht
          · exact hx2 t ht
          · exact hu2 t ht
          · exact hz2 t ht
        · rintro ⟨⟨hx1, hu1⟩, hq⟩
          exact ⟨⟨hx1, fun t ht => hq t (Or.inl (Or.inl ht))⟩,
                 ⟨hu1, fun t ht => hq t (Or.inl (Or.inr ht))⟩,
                 fun t ht => hq t (Or.inr ht)⟩
      simp_rw [hiff]
      rw [h_exp_ind, Finset.card_pair hxu]
    have hsum_bi : ∑ xuz ∈ Triples_d3, ∑ ω : cspIota (2 ^ cspL C₁ * r_star) (cspQ C₁) → Bool,
        (if xuz.1 ∈ cspPRaw ω ∧ xuz.2.1 ∈ cspPRaw ω ∧
            (∀ t ∈ homQueries xuz.2.2, ω (Sum.inl t) = true)
         then bernWeight (cspPIota C₁ r_star) ω else 0) =
      ∑ xu ∈ BallPairs, ((cspPKeep C₁ r_star) ^ 2 *
          (cspPEdge C₁ r_star) ^ (homQueries xu.1 ∪ homQueries xu.2).card) *
        (∑ z ∈ Z_d3 xu.1 xu.2,
          (cspPEdge C₁ r_star) ^ ((homQueries z \ (homQueries xu.1 ∪ homQueries xu.2)).card)) := by
      rw [Finset.sum_biUnion]
      · refine Finset.sum_congr rfl (fun xu _ => ?_)
        rw [Finset.sum_image (fun _ _ _ _ h => (Prod.mk.inj (Prod.mk.inj h).2).2), Finset.mul_sum]
        refine Finset.sum_congr rfl (fun z hz => ?_)
        simp only [Z_d3, Finset.mem_filter, Finset.mem_univ, true_and] at hz
        have hdist := hd3_distinct hz.2
        rw [h_d3_ind_exp hdist.1]
        have hunion : (homQueries xu.1 ∪ homQueries xu.2 ∪ homQueries z).card =
            (homQueries xu.1 ∪ homQueries xu.2).card +
            (homQueries z \ (homQueries xu.1 ∪ homQueries xu.2)).card := by
          rw [← Finset.union_sdiff_self_eq_union (s := homQueries xu.1 ∪ homQueries xu.2) (t := homQueries z),
            Finset.card_union_of_disjoint disjoint_sdiff_self_right]
        rw [hunion, pow_add]
        ring
      · intro xu₁ _ xu₂ _ hne
        simp only [Function.onFun, Finset.disjoint_left]
        intro p hp1 hp2
        rcases Finset.mem_image.mp hp1 with ⟨_, _, rfl⟩
        rcases Finset.mem_image.mp hp2 with ⟨_, _, hp⟩
        rcases Prod.mk.inj hp with ⟨h1, hp'⟩
        rcases Prod.mk.inj hp' with ⟨h2, _⟩
        exact hne (Prod.ext h1.symm h2.symm)
    have hstep2 : ∑ xu ∈ BallPairs, ((cspPKeep C₁ r_star) ^ 2 *
          (cspPEdge C₁ r_star) ^ (homQueries xu.1 ∪ homQueries xu.2).card) *
        (∑ z ∈ Z_d3 xu.1 xu.2,
          (cspPEdge C₁ r_star) ^ ((homQueries z \ (homQueries xu.1 ∪ homQueries xu.2)).card)) ≤
      cspN0 C₁ r_star * (2 : ℝ) ^ ((7 * (C₁ ^ 2 : ℕ) : ℝ) * (cspLam0 C₁ : ℝ) * (r_star : ℝ)) *
        (2 : ℝ) ^ (- (12 * (C₁ ^ 2 : ℕ) : ℝ) * (cspLam0 C₁ : ℝ) * (r_star : ℝ)) := by
      calc
        ∑ xu ∈ BallPairs, _
          ≤ ∑ xu ∈ BallPairs, ((cspPKeep C₁ r_star) ^ 2 *
              (cspPEdge C₁ r_star) ^ (homQueries xu.1 ∪ homQueries xu.2).card) *
              (2 : ℝ) ^ (- (12 * (C₁ ^ 2 : ℕ) : ℝ) * (cspLam0 C₁ : ℝ) * (r_star : ℝ)) := by
              refine Finset.sum_le_sum (fun xu hxu => ?_)
              simp only [BallPairs, Finset.mem_filter, Finset.mem_univ, true_and] at hxu
              exact mul_le_mul_of_nonneg_left (h_s5_d3 xu.1 xu.2 hxu.1 hxu.2) (by positivity)
        _ = (∑ xu ∈ BallPairs, (cspPKeep C₁ r_star) ^ 2 *
              (cspPEdge C₁ r_star) ^ (homQueries xu.1 ∪ homQueries xu.2).card) *
              (2 : ℝ) ^ (- (12 * (C₁ ^ 2 : ℕ) : ℝ) * (cspLam0 C₁ : ℝ) * (r_star : ℝ)) :=
              (Finset.sum_mul _ _ _).symm
        _ ≤ cspN0 C₁ r_star *
              (2 : ℝ) ^ ((7 * (C₁ ^ 2 : ℕ) : ℝ) * (cspLam0 C₁ : ℝ) * (r_star : ℝ)) *
              (2 : ℝ) ^ (- (12 * (C₁ ^ 2 : ℕ) : ℝ) * (cspLam0 C₁ : ℝ) * (r_star : ℝ)) :=
              mul_le_mul_of_nonneg_right h_ball_sum (by positivity)
    have hstep3 : cspN0 C₁ r_star *
        (2 : ℝ) ^ ((7 * (C₁ ^ 2 : ℕ) : ℝ) * (cspLam0 C₁ : ℝ) * (r_star : ℝ)) *
        (2 : ℝ) ^ (- (12 * (C₁ ^ 2 : ℕ) : ℝ) * (cspLam0 C₁ : ℝ) * (r_star : ℝ)) ≤
      (1 / 4 : ℝ) * cspDeltaBad C₁ r_star * cspN0 C₁ r_star := by
      have hcomb : (2 : ℝ) ^ ((7 * (C₁ ^ 2 : ℕ) : ℝ) * (cspLam0 C₁ : ℝ) * (r_star : ℝ)) *
          (2 : ℝ) ^ (- (12 * (C₁ ^ 2 : ℕ) : ℝ) * (cspLam0 C₁ : ℝ) * (r_star : ℝ)) ≤
          (1 / 4 : ℝ) * cspDeltaBad C₁ r_star := by
        unfold cspDeltaBad
        have hquarter : (1 / 4 : ℝ) = (2 : ℝ) ^ (- (2 : ℝ)) := by norm_num
        rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2), hquarter,
          ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
        apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
        have hprod_ge : (1 : ℝ) ≤ (cspLam0 C₁ : ℝ) * (r_star : ℝ) := by
          nlinarith only [hlam0_real, hr_ge3001_real]
        nlinarith only [hC₁_sq_real, hprod_ge]
      have hm := mul_le_mul_of_nonneg_left hcomb (le_of_lt hn0_pos)
      linarith [hm,
        show cspN0 C₁ r_star * ((1 / 4 : ℝ) * cspDeltaBad C₁ r_star) =
          (1 / 4 : ℝ) * cspDeltaBad C₁ r_star * cspN0 C₁ r_star by ring,
        mul_assoc (cspN0 C₁ r_star)
          ((2 : ℝ) ^ ((7 * (C₁ ^ 2 : ℕ) : ℝ) * (cspLam0 C₁ : ℝ) * (r_star : ℝ)))
          ((2 : ℝ) ^ (- (12 * (C₁ ^ 2 : ℕ) : ℝ) * (cspLam0 C₁ : ℝ) * (r_star : ℝ)))]
    rw [hsum_bi] at hstep1
    linarith only [hstep1, hstep2, hstep3]
  
  have hBch_exp : ∑ ω : cspIota (2 ^ cspL C₁ * r_star) (cspQ C₁) → Bool,
      bernWeight (cspPIota C₁ r_star) ω * ((cspBCh C₁ r_star ω).card : ℝ) ≤
      (1 / 4 : ℝ) * cspDeltaBad C₁ r_star * cspN0 C₁ r_star := by
    let BallPairs := Finset.univ.filter
      (fun ab : (Fin (2 ^ cspL C₁ * r_star) → Fin (cspQ C₁)) ×
                (Fin (2 ^ cspL C₁ * r_star) → Fin (cspQ C₁)) =>
        ab.1 ≠ ab.2 ∧ dHam ab.1 ab.2 ≤ C₁ * r_star)
    have hpt : ∀ ω : cspIota (2 ^ cspL C₁ * r_star) (cspQ C₁) → Bool,
        (cspBCh C₁ r_star ω).card ≤ (BallPairs.filter (fun xw =>
          (xw.1 ∈ cspPRaw ω ∧ xw.2 ∈ cspPRaw ω) ∧
          cspKCh C₁ ≤ ((cspPoolCh C₁ r_star xw.1 xw.2).filter (fun y => y ∈ cspPRaw ω)).card)).card := by
      intro ω
      have hsub : cspBCh C₁ r_star ω ⊆ (BallPairs.filter (fun xw =>
          (xw.1 ∈ cspPRaw ω ∧ xw.2 ∈ cspPRaw ω) ∧
          cspKCh C₁ ≤ ((cspPoolCh C₁ r_star xw.1 xw.2).filter
            (fun y => y ∈ cspPRaw ω)).card)).image Prod.fst := by
        intro x hx
        simp only [cspBCh, Finset.mem_filter] at hx
        rcases hx with ⟨hxP, w₀, hwP, hne, hd, hcard⟩
        rw [Finset.mem_image]
        refine ⟨(x, w₀), ?_, rfl⟩
        simp only [BallPairs, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨⟨hne, hd⟩, ⟨hxP, hwP⟩, hcard⟩
      exact le_trans (Finset.card_le_card hsub) Finset.card_image_le
    have hstep1 : ∑ ω : cspIota (2 ^ cspL C₁ * r_star) (cspQ C₁) → Bool,
        bernWeight (cspPIota C₁ r_star) ω * ((cspBCh C₁ r_star ω).card : ℝ) ≤
        ∑ ω : cspIota (2 ^ cspL C₁ * r_star) (cspQ C₁) → Bool,
          bernWeight (cspPIota C₁ r_star) ω * ((BallPairs.filter (fun xw =>
            (xw.1 ∈ cspPRaw ω ∧ xw.2 ∈ cspPRaw ω) ∧
            cspKCh C₁ ≤ ((cspPoolCh C₁ r_star xw.1 xw.2).filter
              (fun y => y ∈ cspPRaw ω)).card)).card : ℝ) := by
      refine Finset.sum_le_sum (fun ω _ => mul_le_mul_of_nonneg_left ?_ (hW_nn ω))
      exact_mod_cast (hpt ω)
    rw [h_sum_card_filter] at hstep1
    let α_ch : ℝ := (2 : ℝ) ^ (- (72 / 100 : ℝ) * (cspLam0 C₁ : ℝ) * (r_star : ℝ))
    have h_pair_ch : ∀ xw ∈ BallPairs,
        ∑ ω : cspIota (2 ^ cspL C₁ * r_star) (cspQ C₁) → Bool,
          (if (xw.1 ∈ cspPRaw ω ∧ xw.2 ∈ cspPRaw ω) ∧
              cspKCh C₁ ≤ ((cspPoolCh C₁ r_star xw.1 xw.2).filter (fun y => y ∈ cspPRaw ω)).card
           then bernWeight (cspPIota C₁ r_star) ω else 0) ≤
        ((cspPKeep C₁ r_star) ^ 2 *
          (cspPEdge C₁ r_star) ^ (homQueries xw.1 ∪ homQueries xw.2).card) *
          α_ch ^ cspKCh C₁ := by
      rintro ⟨x, w₀⟩ hxw
      simp only [BallPairs, Finset.mem_filter, Finset.mem_univ, true_and] at hxw
      let S₀ : Finset (cspIota (2 ^ cspL C₁ * r_star) (cspQ C₁)) :=
        ({x, w₀} : Finset _).image Sum.inr ∪ (homQueries x ∪ homQueries w₀).image Sum.inl
      let Q_ch : (m : ℕ) → (Fin m → (Fin (2 ^ cspL C₁ * r_star) → Fin (cspQ C₁))) →
          (Fin (2 ^ cspL C₁ * r_star) → Fin (cspQ C₁)) → Unit →
          Finset (cspIota (2 ^ cspL C₁ * r_star) (cspQ C₁)) :=
        fun m y_prev y _ =>
          (({y} : Finset _).image Sum.inr ∪ (homQueries y).image Sum.inl) \
            cspUCh x w₀ m y_prev
      have hS₀_prod : ∏ i ∈ S₀, cspPIota C₁ r_star i =
          (cspPKeep C₁ r_star) ^ 2 * (cspPEdge C₁ r_star) ^ (homQueries x ∪ homQueries w₀).card := by
        change ∏ i ∈ ({x, w₀} : Finset _).image Sum.inr ∪
            (homQueries x ∪ homQueries w₀).image Sum.inl, cspPIota C₁ r_star i = _
        rw [h_prod_iota, Finset.card_pair hxw.1]
      rw [← hS₀_prod]
      apply h_seq (Fin (2 ^ cspL C₁ * r_star) → Fin (cspQ C₁)) Unit
        (cspPoolCh C₁ r_star x w₀) (cspKCh C₁) α_ch (by positivity)
        (fun ω => x ∈ cspPRaw ω ∧ w₀ ∈ cspPRaw ω)
        (fun ω => (cspPoolCh C₁ r_star x w₀).filter (fun y => y ∈ cspPRaw ω))
        (fun _ => Finset.filter_subset _ _)
        S₀ (cspUCh x w₀) (fun _ _ _ => {()}) Q_ch
      · intro z₀ i hi
        simp only [S₀, cspUCh, Finset.mem_union, Finset.mem_image] at hi ⊢
        rcases hi with h | ⟨t, ht, rfl⟩
        · exact Or.inl (Or.inl h)
        · exact Or.inr ⟨t, Or.inl ht, rfl⟩
      · intro m _ y_prev b i hi
        simp only [cspUCh, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and,
          Finset.mem_biUnion] at hi ⊢
        rcases hi with (h | ⟨t, rfl⟩) | ⟨q_e, hq, rfl⟩
        · exact Or.inl (Or.inl h)
        · exact Or.inl (Or.inr ⟨t.castSucc, by simp [Fin.snoc_castSucc]⟩)
        · right
          refine ⟨q_e, ?_, rfl⟩
          rcases hq with hq1 | ⟨t, hqt⟩
          · exact Or.inl hq1
          · exact Or.inr ⟨t.castSucc, by simpa [Fin.snoc_castSucc] using hqt⟩
      · intro m _ y_prev _ _ y _ _ _ i hi
        simp only [Q_ch, Finset.mem_sdiff] at hi
        rw [Finset.mem_sdiff]
        refine ⟨?_, hi.2⟩
        simp only [Finset.mem_union, Finset.mem_image, Finset.mem_singleton] at hi
        simp only [cspUCh, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and,
          Finset.mem_biUnion]
        rcases hi.1 with ⟨_, rfl, rfl⟩ | ⟨t, ht, rfl⟩
        · exact Or.inl (Or.inr ⟨Fin.last m, by simp [Fin.snoc_last]⟩)
        · exact Or.inr ⟨t, Or.inr ⟨Fin.last m, by simpa [Fin.snoc_last] using ht⟩, rfl⟩
      · intro ω hBase
        refine ⟨?_, ?_⟩
        · intro i hi
          simp only [cspPRaw, Finset.mem_filter, Finset.mem_univ, true_and] at hBase
          simp only [S₀, Finset.mem_union, Finset.mem_image, Finset.mem_insert,
            Finset.mem_singleton] at hi
          rcases hi with ⟨z, rfl | rfl, rfl⟩ | ⟨t, ht | ht, rfl⟩
          · exact hBase.1.1
          · exact hBase.2.1
          · exact hBase.1.2 t ht
          · exact hBase.2.2 t ht
        · intro z _ hz m
          refine ⟨(), Finset.mem_singleton_self (), ?_⟩
          intro i hi
          have hzm := hz m
          simp only [cspPRaw, Finset.mem_filter, Finset.mem_univ, true_and] at hzm
          simp only [Q_ch, Finset.mem_sdiff, Finset.mem_union, Finset.mem_image,
            Finset.mem_singleton] at hi
          rcases hi.1 with ⟨_, rfl, rfl⟩ | ⟨t, ht, rfl⟩
          · exact hzm.2.1
          · exact hzm.2.2 t ht
      · intro m hm y_prev hinj hpool
        simp only [Finset.sum_singleton, Q_ch]
        exact h_s5_ch x w₀ hxw.1 hxw.2 m hm y_prev hinj hpool
    have hstep2 : ∑ xw ∈ BallPairs, ∑ ω : cspIota (2 ^ cspL C₁ * r_star) (cspQ C₁) → Bool,
        (if (xw.1 ∈ cspPRaw ω ∧ xw.2 ∈ cspPRaw ω) ∧
            cspKCh C₁ ≤ ((cspPoolCh C₁ r_star xw.1 xw.2).filter (fun y => y ∈ cspPRaw ω)).card
         then bernWeight (cspPIota C₁ r_star) ω else 0) ≤
      cspN0 C₁ r_star * (2 : ℝ) ^ ((7 * (C₁ ^ 2 : ℕ) : ℝ) * (cspLam0 C₁ : ℝ) * (r_star : ℝ)) *
        α_ch ^ cspKCh C₁ := by
      calc
        ∑ xw ∈ BallPairs, _
          ≤ ∑ xw ∈ BallPairs,
              ((cspPKeep C₁ r_star) ^ 2 *
                (cspPEdge C₁ r_star) ^ (homQueries xw.1 ∪ homQueries xw.2).card) *
                α_ch ^ cspKCh C₁ := Finset.sum_le_sum h_pair_ch
        _ = (∑ xw ∈ BallPairs, (cspPKeep C₁ r_star) ^ 2 *
              (cspPEdge C₁ r_star) ^ (homQueries xw.1 ∪ homQueries xw.2).card) *
              α_ch ^ cspKCh C₁ := (Finset.sum_mul _ _ _).symm
        _ ≤ cspN0 C₁ r_star *
              (2 : ℝ) ^ ((7 * (C₁ ^ 2 : ℕ) : ℝ) * (cspLam0 C₁ : ℝ) * (r_star : ℝ)) *
              α_ch ^ cspKCh C₁ :=
              mul_le_mul_of_nonneg_right h_ball_sum (by positivity)
    have hstep3 : cspN0 C₁ r_star *
        (2 : ℝ) ^ ((7 * (C₁ ^ 2 : ℕ) : ℝ) * (cspLam0 C₁ : ℝ) * (r_star : ℝ)) *
        α_ch ^ cspKCh C₁ ≤
      (1 / 4 : ℝ) * cspDeltaBad C₁ r_star * cspN0 C₁ r_star := by
      have hKch_cast : (cspKCh C₁ : ℝ) = 20 * ((C₁ ^ 2 : ℕ) : ℝ) := by
        unfold cspKCh
        push_cast
        ring
      have hcomb : (2 : ℝ) ^ ((7 * (C₁ ^ 2 : ℕ) : ℝ) * (cspLam0 C₁ : ℝ) * (r_star : ℝ)) *
          α_ch ^ cspKCh C₁ ≤
          (1 / 4 : ℝ) * cspDeltaBad C₁ r_star := by
        change (2 : ℝ) ^ ((7 * (C₁ ^ 2 : ℕ) : ℝ) * (cspLam0 C₁ : ℝ) * (r_star : ℝ)) *
          ((2 : ℝ) ^ (- (72 / 100 : ℝ) * (cspLam0 C₁ : ℝ) * (r_star : ℝ))) ^ cspKCh C₁ ≤
          (1 / 4 : ℝ) * (2 : ℝ) ^ (- (6 / 10 : ℝ) * (cspLam0 C₁ : ℝ) * (r_star : ℝ))
        have hquarter : (1 / 4 : ℝ) = (2 : ℝ) ^ (- (2 : ℝ)) := by norm_num
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),
          ← Real.rpow_add (by norm_num : (0 : ℝ) < 2), hquarter,
          ← Real.rpow_add (by norm_num : (0 : ℝ) < 2), hKch_cast]
        apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
        have hprod_ge : (1 : ℝ) ≤ (cspLam0 C₁ : ℝ) * (r_star : ℝ) := by
          nlinarith only [hlam0_real, hr_ge3001_real]
        nlinarith only [hC₁_sq_real, hprod_ge]
      have hm := mul_le_mul_of_nonneg_left hcomb (le_of_lt hn0_pos)
      linarith [hm,
        show cspN0 C₁ r_star * ((1 / 4 : ℝ) * cspDeltaBad C₁ r_star) =
          (1 / 4 : ℝ) * cspDeltaBad C₁ r_star * cspN0 C₁ r_star by ring,
        mul_assoc (cspN0 C₁ r_star)
          ((2 : ℝ) ^ ((7 * (C₁ ^ 2 : ℕ) : ℝ) * (cspLam0 C₁ : ℝ) * (r_star : ℝ)))
          (α_ch ^ cspKCh C₁)]
    linarith only [hstep1, hstep2, hstep3]
  have hBcand_exp : ∑ ω : cspIota (2 ^ cspL C₁ * r_star) (cspQ C₁) → Bool,
      bernWeight (cspPIota C₁ r_star) ω * ((cspBCand C₁ r_star ω).card : ℝ) ≤
      (1 / 4 : ℝ) * cspDeltaBad C₁ r_star * cspN0 C₁ r_star := by
    let BallPairs := Finset.univ.filter
      (fun ab : (Fin (2 ^ cspL C₁ * r_star) → Fin (cspQ C₁)) ×
                (Fin (2 ^ cspL C₁ * r_star) → Fin (cspQ C₁)) =>
        ab.1 ≠ ab.2 ∧ dHam ab.1 ab.2 ≤ C₁ * r_star)
    have hpt : ∀ ω : cspIota (2 ^ cspL C₁ * r_star) (cspQ C₁) → Bool,
        (cspBCand C₁ r_star ω).card ≤ (BallPairs.filter (fun ab =>
          (ab.1 ∈ cspPRaw ω ∧ ab.2 ∈ cspPRaw ω) ∧
          cspKMom C₁ ≤ ((cspPRaw ω).filter (fun x => x ∈ bicliqueWitnessList (symROf ω) C₁ r_star ab.1 ab.2)).card)).card := by
      intro ω
      have hsub : cspBCand C₁ r_star ω ⊆ (BallPairs.filter (fun ab =>
          (ab.1 ∈ cspPRaw ω ∧ ab.2 ∈ cspPRaw ω) ∧
          cspKMom C₁ ≤ ((cspPRaw ω).filter (fun x => x ∈ bicliqueWitnessList (symROf ω) C₁ r_star ab.1 ab.2)).card)).image
            Prod.fst := by
        intro a ha
        simp only [cspBCand, Finset.mem_filter] at ha
        rcases ha with ⟨haP, b, hbP, hne, hd, hcard⟩
        rw [Finset.mem_image]
        refine ⟨(a, b), ?_, rfl⟩
        simp only [BallPairs, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨⟨hne, hd⟩, ⟨haP, hbP⟩, hcard⟩
      exact le_trans (Finset.card_le_card hsub) Finset.card_image_le
    have hstep1 : ∑ ω : cspIota (2 ^ cspL C₁ * r_star) (cspQ C₁) → Bool,
        bernWeight (cspPIota C₁ r_star) ω * ((cspBCand C₁ r_star ω).card : ℝ) ≤
        ∑ ω : cspIota (2 ^ cspL C₁ * r_star) (cspQ C₁) → Bool,
          bernWeight (cspPIota C₁ r_star) ω * ((BallPairs.filter (fun ab =>
            (ab.1 ∈ cspPRaw ω ∧ ab.2 ∈ cspPRaw ω) ∧
            cspKMom C₁ ≤ ((cspPRaw ω).filter (fun x => x ∈ bicliqueWitnessList (symROf ω) C₁ r_star ab.1 ab.2)).card)).card : ℝ) := by
      refine Finset.sum_le_sum (fun ω _ => mul_le_mul_of_nonneg_left ?_ (hW_nn ω))
      exact_mod_cast (hpt ω)
    rw [h_sum_card_filter] at hstep1
    let α_cand : ℝ := (2 : ℝ) ^ (- (72 / 100 : ℝ) * (cspLam0 C₁ : ℝ) * (r_star : ℝ))
    have h_pair_cand : ∀ ab ∈ BallPairs,
        ∑ ω : cspIota (2 ^ cspL C₁ * r_star) (cspQ C₁) → Bool,
          (if (ab.1 ∈ cspPRaw ω ∧ ab.2 ∈ cspPRaw ω) ∧
              cspKMom C₁ ≤ ((cspPRaw ω).filter (fun x => x ∈ bicliqueWitnessList (symROf ω) C₁ r_star ab.1 ab.2)).card
           then bernWeight (cspPIota C₁ r_star) ω else 0) ≤
        ((cspPKeep C₁ r_star) ^ 2 *
          (cspPEdge C₁ r_star) ^ (homQueries ab.1 ∪ homQueries ab.2).card) *
          α_cand ^ cspKMom C₁ := by
      rintro ⟨a, b⟩ hab_mem
      simp only [BallPairs, Finset.mem_filter, Finset.mem_univ, true_and] at hab_mem
      obtain ⟨M_wit, Q_cand, hQ_fresh, hQ_wit, hQ_step⟩ :=
        witness_list_step_query_sum_bound C₁ hC₁ r_star hr hσ_pos hp_edge_pos hσ_up
          h_binom_edge hp_keep_pos hp_keep_up a b hab_mem.1 hab_mem.2
      let S₀ : Finset (cspIota (2 ^ cspL C₁ * r_star) (cspQ C₁)) :=
        ({a, b} : Finset _).image Sum.inr ∪ (homQueries a ∪ homQueries b).image Sum.inl
      have hS₀_prod : ∏ i ∈ S₀, cspPIota C₁ r_star i =
          (cspPKeep C₁ r_star) ^ 2 * (cspPEdge C₁ r_star) ^ (homQueries a ∪ homQueries b).card := by
        change ∏ i ∈ ({a, b} : Finset _).image Sum.inr ∪
            (homQueries a ∪ homQueries b).image Sum.inl, cspPIota C₁ r_star i = _
        rw [h_prod_iota, Finset.card_pair hab_mem.1]
      rw [← hS₀_prod]
      apply h_seq (Fin (2 ^ cspL C₁ * r_star) → Fin (cspQ C₁))
        (candWitType (2 ^ cspL C₁ * r_star) C₁)
        (cspPoolCand C₁ r_star a b) (cspKMom C₁) α_cand (by positivity)
        (fun ω => a ∈ cspPRaw ω ∧ b ∈ cspPRaw ω)
        (fun ω => (cspPRaw ω).filter (fun x => x ∈ bicliqueWitnessList (symROf ω) C₁ r_star a b))
        (fun _ x hx => by
          simp only [bicliqueWitnessList, Finset.mem_filter] at hx
          rcases hx.2 with ⟨_, hnea, hneb, hda, hdb, _⟩
          simp only [cspPoolCand, Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨hnea, hneb, hda, hdb⟩)
        S₀ (cspUCand a b) M_wit Q_cand
      · intro z₀ i hi
        simp only [S₀, cspUCand, cspRvc, homQueries, Finset.mem_union, Finset.mem_image,
          Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
        rcases hi with h | ⟨t, (⟨⟨u, v⟩, huv, rfl⟩ | ⟨⟨u, v⟩, huv, rfl⟩), rfl⟩
        · exact Or.inl (Or.inl h)
        · exact Or.inr ⟨(u, v, a u, a v),
            ⟨huv, Or.inl (Or.inl ⟨u, rfl⟩), Or.inl (Or.inl ⟨v, rfl⟩)⟩, rfl⟩
        · exact Or.inr ⟨(u, v, b u, b v),
            ⟨huv, Or.inl (Or.inr ⟨u, rfl⟩), Or.inl (Or.inr ⟨v, rfl⟩)⟩, rfl⟩
      · intro m _ z_prev x_new
        have hrvc_sub : cspRvc a b m z_prev ⊆ cspRvc a b (m + 1) (Fin.snoc z_prev x_new) := by
          intro vc hvc
          simp only [cspRvc, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and,
            Finset.mem_biUnion] at hvc ⊢
          rcases hvc with (h | h) | ⟨t, v, rfl⟩
          · exact Or.inl (Or.inl h)
          · exact Or.inl (Or.inr h)
          · exact Or.inr ⟨t.castSucc, v, by simp [Fin.snoc_castSucc]⟩
        intro i hi
        simp only [cspUCand, Finset.mem_union, Finset.mem_image, Finset.mem_filter,
          Finset.mem_univ, true_and] at hi ⊢
        rcases hi with (h | ⟨t, rfl⟩) | ⟨t, ⟨huv, h1, h2⟩, rfl⟩
        · exact Or.inl (Or.inl h)
        · exact Or.inl (Or.inr ⟨t.castSucc, by simp [Fin.snoc_castSucc]⟩)
        · exact Or.inr ⟨t, ⟨huv, hrvc_sub h1, hrvc_sub h2⟩, rfl⟩
      · exact hQ_fresh
      · intro ω hBase
        refine ⟨?_, ?_⟩
        · intro i hi
          simp only [cspPRaw, Finset.mem_filter, Finset.mem_univ, true_and] at hBase
          simp only [S₀, Finset.mem_union, Finset.mem_image, Finset.mem_insert,
            Finset.mem_singleton] at hi
          rcases hi with ⟨z, rfl | rfl, rfl⟩ | ⟨t, ht | ht, rfl⟩
          · exact hBase.1.1
          · exact hBase.2.1
          · exact hBase.1.2 t ht
          · exact hBase.2.2 t ht
        · intro z hinj hz m
          let z_prev : Fin m.1 → (Fin (2 ^ cspL C₁ * r_star) → Fin (cspQ C₁)) :=
            fun t => z (t.castLE (Nat.le_of_lt m.isLt))
          have hinj_prev : Function.Injective z_prev := by
            intro t₁ t₂ heq
            exact Fin.castLE_injective _ (hinj heq)
          have hpool_prev : ∀ t : Fin m.1, z_prev t ∈ cspPoolCand C₁ r_star a b := by
            intro t
            have hzt := hz (t.castLE (Nat.le_of_lt m.isLt))
            simp only [bicliqueWitnessList, Finset.mem_filter] at hzt
            rcases hzt.2 with ⟨_, hnea, hneb, hda, hdb, _⟩
            simp only [cspPoolCand, Finset.mem_filter, Finset.mem_univ, true_and]
            exact ⟨hnea, hneb, hda, hdb⟩
          have hzm := hz m
          simp only [cspPRaw, Finset.mem_filter, Finset.mem_univ, true_and] at hzm
          have hx_mem : z m ∈ cspPoolCand C₁ r_star a b \ Finset.univ.image z_prev := by
            rw [Finset.mem_sdiff]
            refine ⟨?_, ?_⟩
            · have hbw := hzm.2
              simp only [bicliqueWitnessList, Finset.mem_filter] at hbw
              rcases hbw with ⟨_, hnea, hneb, hda, hdb, _⟩
              simp only [cspPoolCand, Finset.mem_filter, Finset.mem_univ, true_and]
              exact ⟨hnea, hneb, hda, hdb⟩
            · intro himg
              rcases Finset.mem_image.mp himg with ⟨t, _, heq⟩
              have ht_eq := congr_arg Fin.val (hinj heq)
              exact absurd ht_eq (Nat.ne_of_lt t.isLt)
          exact hQ_wit ω m.1 m.isLt z_prev hinj_prev hpool_prev (z m) hx_mem hzm.1.1 hzm.2
      · exact hQ_step
    have hstep2 : ∑ ab ∈ BallPairs, ∑ ω : cspIota (2 ^ cspL C₁ * r_star) (cspQ C₁) → Bool,
        (if (ab.1 ∈ cspPRaw ω ∧ ab.2 ∈ cspPRaw ω) ∧
            cspKMom C₁ ≤ ((cspPRaw ω).filter (fun x => x ∈ bicliqueWitnessList (symROf ω) C₁ r_star ab.1 ab.2)).card
         then bernWeight (cspPIota C₁ r_star) ω else 0) ≤
      cspN0 C₁ r_star * (2 : ℝ) ^ ((7 * (C₁ ^ 2 : ℕ) : ℝ) * (cspLam0 C₁ : ℝ) * (r_star : ℝ)) *
        α_cand ^ cspKMom C₁ := by
      calc
        ∑ ab ∈ BallPairs, _
          ≤ ∑ ab ∈ BallPairs,
              ((cspPKeep C₁ r_star) ^ 2 *
                (cspPEdge C₁ r_star) ^ (homQueries ab.1 ∪ homQueries ab.2).card) *
                α_cand ^ cspKMom C₁ := Finset.sum_le_sum h_pair_cand
        _ = (∑ ab ∈ BallPairs, (cspPKeep C₁ r_star) ^ 2 *
              (cspPEdge C₁ r_star) ^ (homQueries ab.1 ∪ homQueries ab.2).card) *
              α_cand ^ cspKMom C₁ := (Finset.sum_mul _ _ _).symm
        _ ≤ cspN0 C₁ r_star *
              (2 : ℝ) ^ ((7 * (C₁ ^ 2 : ℕ) : ℝ) * (cspLam0 C₁ : ℝ) * (r_star : ℝ)) *
              α_cand ^ cspKMom C₁ :=
              mul_le_mul_of_nonneg_right h_ball_sum (by positivity)
    have hstep3 : cspN0 C₁ r_star *
        (2 : ℝ) ^ ((7 * (C₁ ^ 2 : ℕ) : ℝ) * (cspLam0 C₁ : ℝ) * (r_star : ℝ)) *
        α_cand ^ cspKMom C₁ ≤
      (1 / 4 : ℝ) * cspDeltaBad C₁ r_star * cspN0 C₁ r_star := by
      have hKmom_cast : (cspKMom C₁ : ℝ) = 20 * ((C₁ ^ 2 : ℕ) : ℝ) := by
        unfold cspKMom
        push_cast
        ring
      have hcomb : (2 : ℝ) ^ ((7 * (C₁ ^ 2 : ℕ) : ℝ) * (cspLam0 C₁ : ℝ) * (r_star : ℝ)) *
          α_cand ^ cspKMom C₁ ≤
          (1 / 4 : ℝ) * cspDeltaBad C₁ r_star := by
        change (2 : ℝ) ^ ((7 * (C₁ ^ 2 : ℕ) : ℝ) * (cspLam0 C₁ : ℝ) * (r_star : ℝ)) *
          ((2 : ℝ) ^ (- (72 / 100 : ℝ) * (cspLam0 C₁ : ℝ) * (r_star : ℝ))) ^ cspKMom C₁ ≤
          (1 / 4 : ℝ) * (2 : ℝ) ^ (- (6 / 10 : ℝ) * (cspLam0 C₁ : ℝ) * (r_star : ℝ))
        have hquarter : (1 / 4 : ℝ) = (2 : ℝ) ^ (- (2 : ℝ)) := by norm_num
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),
          ← Real.rpow_add (by norm_num : (0 : ℝ) < 2), hquarter,
          ← Real.rpow_add (by norm_num : (0 : ℝ) < 2), hKmom_cast]
        apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
        have hprod_ge : (1 : ℝ) ≤ (cspLam0 C₁ : ℝ) * (r_star : ℝ) := by
          nlinarith only [hlam0_real, hr_ge3001_real]
        nlinarith only [hC₁_sq_real, hprod_ge]
      have hm := mul_le_mul_of_nonneg_left hcomb (le_of_lt hn0_pos)
      linarith [hm,
        show cspN0 C₁ r_star * ((1 / 4 : ℝ) * cspDeltaBad C₁ r_star) =
          (1 / 4 : ℝ) * cspDeltaBad C₁ r_star * cspN0 C₁ r_star by ring,
        mul_assoc (cspN0 C₁ r_star)
          ((2 : ℝ) ^ ((7 * (C₁ ^ 2 : ℕ) : ℝ) * (cspLam0 C₁ : ℝ) * (r_star : ℝ)))
          (α_cand ^ cspKMom C₁)]
    linarith only [hstep1, hstep2, hstep3]
  have hBDist_exp : ∑ ω : cspIota (2 ^ cspL C₁ * r_star) (cspQ C₁) → Bool,
      bernWeight (cspPIota C₁ r_star) ω * ((cspBDist r_star ω).card : ℝ) ≤
      (1 / 4 : ℝ) * cspDeltaBad C₁ r_star * cspN0 C₁ r_star := by
    let ClosePairs := Finset.univ.filter
      (fun ab : (Fin (2 ^ cspL C₁ * r_star) → Fin (cspQ C₁)) ×
                (Fin (2 ^ cspL C₁ * r_star) → Fin (cspQ C₁)) =>
        ab.1 ≠ ab.2 ∧ 2 * dHam ab.1 ab.2 < r_star)
    have hpt : ∀ ω : cspIota (2 ^ cspL C₁ * r_star) (cspQ C₁) → Bool,
        (cspBDist r_star ω).card ≤ (ClosePairs.filter (fun ab =>
          ab.1 ∈ cspPRaw ω ∧ ab.2 ∈ cspPRaw ω)).card := by
      intro ω
      have hsub : cspBDist r_star ω ⊆ (ClosePairs.filter (fun ab =>
          ab.1 ∈ cspPRaw ω ∧ ab.2 ∈ cspPRaw ω)).image Prod.fst := by
        intro x hx
        simp only [cspBDist, Finset.mem_filter] at hx
        rcases hx with ⟨hxP, y, hyP, hne, hlt⟩
        rw [Finset.mem_image]
        refine ⟨(x, y), ?_, rfl⟩
        simp only [ClosePairs, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨⟨hne, hlt⟩, hxP, hyP⟩
      exact le_trans (Finset.card_le_card hsub) Finset.card_image_le
    have hstep1 : ∑ ω : cspIota (2 ^ cspL C₁ * r_star) (cspQ C₁) → Bool,
        bernWeight (cspPIota C₁ r_star) ω * ((cspBDist r_star ω).card : ℝ) ≤
        ∑ ω : cspIota (2 ^ cspL C₁ * r_star) (cspQ C₁) → Bool,
          bernWeight (cspPIota C₁ r_star) ω * ((ClosePairs.filter (fun ab =>
            ab.1 ∈ cspPRaw ω ∧ ab.2 ∈ cspPRaw ω)).card : ℝ) := by
      refine Finset.sum_le_sum (fun ω _ => mul_le_mul_of_nonneg_left ?_ (hW_nn ω))
      exact_mod_cast (hpt ω)
    rw [h_sum_card_filter] at hstep1
    have hcongr : ∑ ab ∈ ClosePairs, ∑ ω : cspIota (2 ^ cspL C₁ * r_star) (cspQ C₁) → Bool,
        (if ab.1 ∈ cspPRaw ω ∧ ab.2 ∈ cspPRaw ω
         then bernWeight (cspPIota C₁ r_star) ω else 0) =
      ∑ ab ∈ ClosePairs,
        (cspPKeep C₁ r_star) ^ 2 *
          (cspPEdge C₁ r_star) ^ (homQueries ab.1 ∪ homQueries ab.2).card := by
      refine Finset.sum_congr rfl (fun ab hab => ?_)
      simp only [ClosePairs, Finset.mem_filter, Finset.mem_univ, true_and] at hab
      exact h_pair_exp hab.1
    rw [hcongr] at hstep1
    exact le_trans hstep1
      (close_pair_query_sum_bound C₁ hC₁ r_star hr hσ_pos hp_edge_pos hσ_up hDOm_s
        hp_keep_pos hp_keep_up hn0_pos h_union_card h_sphere)

  have hBad : ∑ ω : cspIota (2 ^ cspL C₁ * r_star) (cspQ C₁) → Bool,
      bernWeight (cspPIota C₁ r_star) ω * ((cspBBad C₁ r_star ω).card : ℝ) ≤
      cspDeltaBad C₁ r_star * cspN0 C₁ r_star := by
    have hstep1 : ∑ ω : cspIota (2 ^ cspL C₁ * r_star) (cspQ C₁) → Bool,
        bernWeight (cspPIota C₁ r_star) ω * ((cspBBad C₁ r_star ω).card : ℝ) ≤
        (∑ ω : cspIota (2 ^ cspL C₁ * r_star) (cspQ C₁) → Bool,
          bernWeight (cspPIota C₁ r_star) ω * ((cspBD3 C₁ r_star ω).card : ℝ)) +
        (∑ ω : cspIota (2 ^ cspL C₁ * r_star) (cspQ C₁) → Bool,
          bernWeight (cspPIota C₁ r_star) ω * ((cspBCh C₁ r_star ω).card : ℝ)) +
        (∑ ω : cspIota (2 ^ cspL C₁ * r_star) (cspQ C₁) → Bool,
          bernWeight (cspPIota C₁ r_star) ω * ((cspBCand C₁ r_star ω).card : ℝ)) +
        (∑ ω : cspIota (2 ^ cspL C₁ * r_star) (cspQ C₁) → Bool,
          bernWeight (cspPIota C₁ r_star) ω * ((cspBDist r_star ω).card : ℝ)) := by
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_le_sum (fun ω _ => ?_)
      have h0 := Finset.card_union_le
        (cspBD3 C₁ r_star ω ∪ cspBCh C₁ r_star ω ∪ cspBCand C₁ r_star ω)
        (cspBDist r_star ω)
      have h1 := Finset.card_union_le (cspBD3 C₁ r_star ω ∪ cspBCh C₁ r_star ω) (cspBCand C₁ r_star ω)
      have h2 := Finset.card_union_le (cspBD3 C₁ r_star ω) (cspBCh C₁ r_star ω)
      have hnat : (cspBBad C₁ r_star ω).card ≤
          (cspBD3 C₁ r_star ω).card + (cspBCh C₁ r_star ω).card +
          (cspBCand C₁ r_star ω).card + (cspBDist r_star ω).card := by
        unfold cspBBad
        omega
      have hreal : ((cspBBad C₁ r_star ω).card : ℝ) ≤
          ((cspBD3 C₁ r_star ω).card : ℝ) + ((cspBCh C₁ r_star ω).card : ℝ) +
          ((cspBCand C₁ r_star ω).card : ℝ) + ((cspBDist r_star ω).card : ℝ) := by
        exact_mod_cast hnat
      have hm := mul_le_mul_of_nonneg_left hreal (hW_nn ω)
      linarith [hm]
    linarith only [hstep1, hBD3_exp, hBch_exp, hBcand_exp, hBDist_exp]
  
  have h_margin : 72 * 144 * (cspGamma r_star) ^ 3 * cspDeltaBad C₁ r_star ≤ 1 / 256 := by
    have hconst : (72 * 144 : ℝ) ≤ (2 : ℝ) ^ (14 : ℝ) := by norm_num
    have hγ3 : (cspGamma r_star) ^ 3 = (2 : ℝ) ^ (3 * (r_star : ℝ) / ((2 : ℝ) ^ (998 : ℕ))) := by
      unfold cspGamma
      rw [← Real.rpow_natCast _ 3, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
      congr 1
      push_cast
      rw [div_mul_eq_mul_div, mul_comm]
    have h1 : 72 * 144 * (cspGamma r_star) ^ 3 * cspDeltaBad C₁ r_star ≤
        (2 : ℝ) ^ ((14 : ℝ) + 3 * (r_star : ℝ) / ((2 : ℝ) ^ (998 : ℕ)) +
          (- (6 / 10 : ℝ) * (cspLam0 C₁ : ℝ) * (r_star : ℝ))) := by
      have hm : 72 * 144 * (cspGamma r_star) ^ 3 * cspDeltaBad C₁ r_star ≤
          (2 : ℝ) ^ (14 : ℝ) * (cspGamma r_star) ^ 3 * cspDeltaBad C₁ r_star := by
        have : 0 ≤ (cspGamma r_star) ^ 3 * cspDeltaBad C₁ r_star := by positivity
        nlinarith only [hconst, this]
      calc
        72 * 144 * (cspGamma r_star) ^ 3 * cspDeltaBad C₁ r_star
          ≤ (2 : ℝ) ^ (14 : ℝ) * (cspGamma r_star) ^ 3 * cspDeltaBad C₁ r_star := hm
        _ = (2 : ℝ) ^ ((14 : ℝ) + 3 * (r_star : ℝ) / ((2 : ℝ) ^ (998 : ℕ)) +
              (- (6 / 10 : ℝ) * (cspLam0 C₁ : ℝ) * (r_star : ℝ))) := by
            rw [hγ3]
            unfold cspDeltaBad
            rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2),
              ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    have h2 : (2 : ℝ) ^ ((14 : ℝ) + 3 * (r_star : ℝ) / ((2 : ℝ) ^ (998 : ℕ)) +
          (- (6 / 10 : ℝ) * (cspLam0 C₁ : ℝ) * (r_star : ℝ))) ≤ (1 / 256 : ℝ) := by
      have h256 : (1 / 256 : ℝ) = (2 : ℝ) ^ (- (8 : ℝ)) := by norm_num
      rw [h256]
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      set d998 : ℝ := 3 * (r_star : ℝ) / ((2 : ℝ) ^ (998 : ℕ))
      have hdiv_le : d998 ≤ (r_star : ℝ) := hdiv998 3 (by norm_num)
      clear_value d998
      have hlam_r : 600 * (r_star : ℝ) ≤ (6 / 10 : ℝ) * (cspLam0 C₁ : ℝ) * (r_star : ℝ) := by
        nlinarith only [hlam0_real, hr_pos_real]
      linarith only [hdiv_le, hlam_r, hr_ge3001_real]
    exact le_trans h1 h2
  
  obtain ⟨ω₀, hX_low_raw, hX_up_raw, hE_dense_raw⟩ :=
    paley_zygmund_markov_expurgation (Ω := cspIota (2 ^ cspL C₁ * r_star) (cspQ C₁) → Bool) (V := Fin (2 ^ cspL C₁ * r_star) → Fin (cspQ C₁)) (bernWeight (cspPIota C₁ r_star)) hW_nn hW_sum
      (fun x y => dHam x y = r_star) hRel_symm cspPRaw (cspBBad C₁ r_star)
      (cspN0 C₁ r_star) (cspDStar C₁ r_star) (cspGamma r_star) (cspDeltaBad C₁ r_star)
      hn0_pos hD_pos hγ_ge1 hδ_pos h_margin hM1 hE1 hE2 hW2 hBad
  refine ⟨symROf ω₀, cspPRaw ω₀ \ cspBBad C₁ r_star ω₀, h_sym_R ω₀, ?_, ⟨?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    have hxP : x ∈ cspPRaw ω₀ := (Finset.mem_sdiff.mp hx).1
    simp only [cspPRaw, Finset.mem_filter, Finset.mem_univ, true_and] at hxP
    exact (h_hom_iff ω₀ x).mp hxP.2
  · have h1024 : (1 / 1024 : ℝ) = (2 : ℝ) ^ (- (10 : ℝ)) := by norm_num
    have hγ_inv2 : (cspGamma r_star)⁻¹ ^ 2 =
        (2 : ℝ) ^ (- (2 * (r_star : ℝ) / ((2 : ℝ) ^ (998 : ℕ)))) := by
      unfold cspGamma
      rw [← Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), ← Real.rpow_natCast _ 2,
        ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
      congr 1
      push_cast
      rw [neg_mul, div_mul_eq_mul_div, mul_comm (r_star : ℝ) 2]
    have hlow1 : (2 : ℝ) ^ (- (10 : ℝ) + (- (2 * (r_star : ℝ) / ((2 : ℝ) ^ (998 : ℕ)))) +
        (99 / 100 : ℝ) * (cspBeta0 C₁ : ℝ) * (2 : ℝ) ^ (2 * cspL C₁) * (r_star : ℝ)) ≤
        (1 / 1024 : ℝ) * (cspGamma r_star)⁻¹ ^ 2 * cspN0 C₁ r_star := by
      rw [h1024, hγ_inv2, Real.rpow_add (by norm_num : (0 : ℝ) < 2),
        Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      exact mul_le_mul_of_nonneg_left hn0_low (by positivity)
    have hlow2 : (2 : ℝ) ^ ((98 / 100 : ℝ) * (cspBeta0 C₁ : ℝ) * (2 : ℝ) ^ (2 * cspL C₁) * (r_star : ℝ)) ≤
        (2 : ℝ) ^ (- (10 : ℝ) + (- (2 * (r_star : ℝ) / ((2 : ℝ) ^ (998 : ℕ)))) +
          (99 / 100 : ℝ) * (cspBeta0 C₁ : ℝ) * (2 : ℝ) ^ (2 * cspL C₁) * (r_star : ℝ)) := by
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      set d998 : ℝ := 2 * (r_star : ℝ) / ((2 : ℝ) ^ (998 : ℕ))
      have hdiv_le : d998 ≤ (r_star : ℝ) := hdiv998 2 (by norm_num)
      clear_value d998
      have hprod : 10 * (r_star : ℝ) ≤
          (1 / 100 : ℝ) * (cspBeta0 C₁ : ℝ) * (2 : ℝ) ^ (2 * cspL C₁) * (r_star : ℝ) := by
        have hm : (6000 : ℝ) ≤ (cspBeta0 C₁ : ℝ) * (2 : ℝ) ^ (2 * cspL C₁) := by
          nlinarith only [hbeta0_real, h22L_real]
        nlinarith only [hm, hr_pos_real]
      linarith only [hdiv_le, hprod, hr_ge3001_real]
    exact le_trans hlow2 (le_trans hlow1 hX_low_raw)
  
  · have h72 : (72 : ℝ) ≤ (2 : ℝ) ^ (7 : ℝ) := by norm_num
    have hup1 : 72 * cspGamma r_star * cspN0 C₁ r_star ≤
        (2 : ℝ) ^ ((7 : ℝ) + (r_star : ℝ) / ((2 : ℝ) ^ (998 : ℕ)) +
          (cspBeta0 C₁ : ℝ) * (2 : ℝ) ^ (2 * cspL C₁) * (r_star : ℝ)) := by
      have hm1 : 72 * cspGamma r_star * cspN0 C₁ r_star ≤
          (2 : ℝ) ^ (7 : ℝ) * cspGamma r_star * cspN0 C₁ r_star := by
        have : 0 ≤ cspGamma r_star * cspN0 C₁ r_star := by positivity
        nlinarith only [h72, this]
      have hm2 : (2 : ℝ) ^ (7 : ℝ) * cspGamma r_star * cspN0 C₁ r_star ≤
          (2 : ℝ) ^ (7 : ℝ) * cspGamma r_star *
            (2 : ℝ) ^ ((cspBeta0 C₁ : ℝ) * (2 : ℝ) ^ (2 * cspL C₁) * (r_star : ℝ)) :=
        mul_le_mul_of_nonneg_left hn0_up (by positivity)
      calc
        72 * cspGamma r_star * cspN0 C₁ r_star
          ≤ (2 : ℝ) ^ (7 : ℝ) * cspGamma r_star *
              (2 : ℝ) ^ ((cspBeta0 C₁ : ℝ) * (2 : ℝ) ^ (2 * cspL C₁) * (r_star : ℝ)) :=
            le_trans hm1 hm2
        _ = (2 : ℝ) ^ ((7 : ℝ) + (r_star : ℝ) / ((2 : ℝ) ^ (998 : ℕ)) +
              (cspBeta0 C₁ : ℝ) * (2 : ℝ) ^ (2 * cspL C₁) * (r_star : ℝ)) := by
            unfold cspGamma
            rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2),
              ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    have hup2 : (2 : ℝ) ^ ((7 : ℝ) + (r_star : ℝ) / ((2 : ℝ) ^ (998 : ℕ)) +
          (cspBeta0 C₁ : ℝ) * (2 : ℝ) ^ (2 * cspL C₁) * (r_star : ℝ)) ≤
        (2 : ℝ) ^ ((102 / 100 : ℝ) * (cspBeta0 C₁ : ℝ) * (2 : ℝ) ^ (2 * cspL C₁) * (r_star : ℝ)) := by
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      set d998 : ℝ := (r_star : ℝ) / ((2 : ℝ) ^ (998 : ℕ))
      have hdiv_le : d998 ≤ (r_star : ℝ) := by
        have h1 := hdiv998 1 (by norm_num); rwa [one_mul] at h1
      clear_value d998
      have hprod : 20 * (r_star : ℝ) ≤
          (2 / 100 : ℝ) * (cspBeta0 C₁ : ℝ) * (2 : ℝ) ^ (2 * cspL C₁) * (r_star : ℝ) := by
        have hm : (6000 : ℝ) ≤ (cspBeta0 C₁ : ℝ) * (2 : ℝ) ^ (2 * cspL C₁) := by
          nlinarith only [hbeta0_real, h22L_real]
        nlinarith only [hm, hr_pos_real]
      linarith only [hdiv_le, hprod, hr_ge3001_real]
    exact le_trans hX_up_raw (le_trans hup1 hup2)
  
  · have hD_div : (2 : ℝ) ^ ((1 / 5 : ℝ) * (cspLam0 C₁ : ℝ) * (r_star : ℝ)) ≤
        cspDStar C₁ r_star / cspGamma r_star := by
      unfold cspDStar cspGamma
      rw [← Real.rpow_sub (by norm_num : (0 : ℝ) < 2)]
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      set d998 : ℝ := (r_star : ℝ) / ((2 : ℝ) ^ (998 : ℕ))
      have hdiv_le : d998 ≤ (r_star : ℝ) := by
        have h1 := hdiv998 1 (by norm_num); rwa [one_mul] at h1
      clear_value d998
      have hlam_r : (r_star : ℝ) ≤ (1 / 1000 : ℝ) * (cspLam0 C₁ : ℝ) * (r_star : ℝ) := by
        nlinarith only [hlam0_real, hr_pos_real]
      linarith only [hdiv_le, hlam_r, hr_pos_real]
    exact le_trans (mul_le_mul_of_nonneg_right hD_div (Nat.cast_nonneg _)) hE_dense_raw
  · intro x hx u hu z hz hdu hdz
    by_contra hgt
    push_neg at hgt
    have hx_sdiff := Finset.mem_sdiff.mp hx
    have huP := (Finset.mem_sdiff.mp hu).1
    have hzHom : ∀ t ∈ homQueries z, ω₀ (Sum.inl t) = true := (h_hom_iff ω₀ z).mpr hz
    apply hx_sdiff.2
    simp only [cspBBad, cspBD3, Finset.mem_union, Finset.mem_filter]
    exact Or.inl (Or.inl (Or.inl ⟨hx_sdiff.1, u, huP, z, hzHom, hdu, hdz, hgt⟩))
  · intro x hx w₀ hw₀ hne hd_xw₀
    by_contra hge
    push_neg at hge
    have hx_sdiff := Finset.mem_sdiff.mp hx
    have hw₀P := (Finset.mem_sdiff.mp hw₀).1
    have hsub : (cspPRaw ω₀ \ cspBBad C₁ r_star ω₀).filter (fun y =>
        y ≠ x ∧ y ≠ w₀ ∧ dHam x y = r_star ∧
        r_star < 4 * (diffCoords x w₀ ∩ diffCoords x y).card) ⊆
      (cspPoolCh C₁ r_star x w₀).filter (fun y => y ∈ cspPRaw ω₀) := by
      intro y hy
      simp only [Finset.mem_filter] at hy ⊢
      rcases hy with ⟨hyX, hneyx, hneyw, hdy, hov⟩
      have hy_sdiff := Finset.mem_sdiff.mp hyX
      refine ⟨?_, hy_sdiff.1⟩
      simp only [cspPoolCh, Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨hneyx, hneyw, hdy, hov, ?_⟩
      have hd_xy_le : dHam x y ≤ C₁ * r_star := by
        rw [hdy]
        exact le_mul_of_one_le_left (Nat.zero_le _) (by omega)
      have hyHom : ∀ t ∈ homQueries y, ω₀ (Sum.inl t) = true := by
        have hyP := hy_sdiff.1
        simp only [cspPRaw, Finset.mem_filter, Finset.mem_univ, true_and] at hyP
        exact hyP.2
      by_contra hd3_gt
      push_neg at hd3_gt
      apply hx_sdiff.2
      simp only [cspBBad, cspBD3, Finset.mem_union, Finset.mem_filter]
      exact Or.inl (Or.inl (Or.inl ⟨hx_sdiff.1, w₀, hw₀P, y, hyHom, hd_xw₀, hd_xy_le, hd3_gt⟩))
    have hcard_ge := le_trans hge (Finset.card_le_card hsub)
    apply hx_sdiff.2
    simp only [cspBBad, cspBCh, Finset.mem_union, Finset.mem_filter]
    exact Or.inl (Or.inl (Or.inr ⟨hx_sdiff.1, w₀, hw₀P, hne, hd_xw₀, hcard_ge⟩))
  · intro a ha b hb hne hd_ab
    by_contra hge
    push_neg at hge
    have ha_sdiff := Finset.mem_sdiff.mp ha
    have hbP := (Finset.mem_sdiff.mp hb).1
    have hsub : (cspPRaw ω₀ \ cspBBad C₁ r_star ω₀).filter
        (fun x => x ∈ bicliqueWitnessList (symROf ω₀) C₁ r_star a b) ⊆
      (cspPRaw ω₀).filter (fun x => x ∈ bicliqueWitnessList (symROf ω₀) C₁ r_star a b) :=
      Finset.filter_subset_filter _ Finset.sdiff_subset
    have hcard_ge := le_trans hge (Finset.card_le_card hsub)
    apply ha_sdiff.2
    simp only [cspBBad, cspBCand, Finset.mem_union, Finset.mem_filter]
    exact Or.inl (Or.inr ⟨ha_sdiff.1, b, hbP, hne, hd_ab, hcard_ge⟩)
  · intro x hx y hy hne
    by_contra hlt
    push_neg at hlt
    have hx_sdiff := Finset.mem_sdiff.mp hx
    have hyP := (Finset.mem_sdiff.mp hy).1
    apply hx_sdiff.2
    simp only [cspBBad, cspBDist, Finset.mem_union, Finset.mem_filter]
    exact Or.inr ⟨hx_sdiff.1, y, hyP, hne, hlt⟩

end Helpers

/-- **Theorem 2.3 (Existence of Locally List-Bounded `2`-CSP Codes, Module 3)**
Takes Lemma 6.3 (`h_6_3`) as an explicit hypothesis so this module compiles independently. -/
theorem thm_2_3_from_6_3
    (h_6_3 : ∀ (N q C₁ rStar : ℕ), 2 ≤ N → 2 ≤ q → 3 ≤ C₁ → 1 ≤ rStar →
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
          ListHitCond C₁ rStar X L_X) :
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
  refine ⟨(2000000 : ℝ), by norm_num, ?_⟩
  intro C₁ hC₁
  have hL_ge2 : 2 ≤ cspL C₁ :=
    Nat.le_trans (by decide : 2 ≤ 20) (Nat.le_add_right 20 _)
  have hlam_info := lam0_ge_1000_C1 C₁ hC₁
  have hL_le : (cspL C₁ : ℝ) ≤ (2000000 : ℝ) * (C₁ : ℝ) ^ 3 * Real.logb 2 (C₁ : ℝ) :=
    hlam_info.2.2
  have hq_ge2 : 2 ≤ cspQ C₁ := by
    unfold cspQ
    exact Nat.succ_le_succ Nat.one_le_two_pow
  have hlam0_1000 : 1000 * C₁ ≤ cspLam0 C₁ := hlam_info.2.1
  have hlam0_ge : 1000 ≤ cspLam0 C₁ := by omega
  have hbeta0_ge : 6000 ≤ cspBeta0 C₁ := by unfold cspBeta0; omega
  have hbeta0_pos_real : (0 : ℝ) < (cspBeta0 C₁ : ℝ) := by
    exact_mod_cast (Nat.lt_of_lt_of_le (by decide : 0 < 6000) hbeta0_ge)
  have hμ₀_pos : 0 < (cspBeta0 C₁ : ℝ) * (2 : ℝ) ^ (2 * cspL C₁) :=
    mul_pos hbeta0_pos_real (pow_pos (by norm_num) _)
  have hR0 : 160 * C₁ < 1000 * C₁ + 1 := by omega
  have hdHam_eq : ∀ {M p : ℕ} (x y : Fin M → Fin p), dHam x y = hammingDist x y := fun _ _ => rfl
  have hexact_eq : ∀ {M p : ℕ} (S : Finset (Fin M → Fin p)) (r : ℕ),
      (S ×ˢ S).filter (fun xy => dHam xy.1 xy.2 = r) = exactDistPairs S r := fun _ _ => rfl
  refine ⟨cspL C₁, cspQ C₁, cspKMom C₁, 1000 * C₁ + 1,
    (cspBeta0 C₁ : ℝ) * (2 : ℝ) ^ (2 * cspL C₁),
    hL_ge2, hL_le, hq_ge2, rfl, hR0, hμ₀_pos, ?_⟩
  intro c rStar hrStar
  have hr : 1000 * C₁ < rStar := Nat.lt_of_lt_of_le (Nat.lt_succ_self (1000 * C₁)) hrStar
  have hr_ge1 : 1 ≤ rStar := Nat.le_trans (Nat.le_add_left 1 (1000 * C₁)) hrStar
  have hN_ge2_val : 2 ≤ 2 ^ cspL C₁ * rStar := by
    have h2L : 4 ≤ 2 ^ cspL C₁ := by
      calc
        4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ cspL C₁ := Nat.pow_le_pow_right (by norm_num) hL_ge2
    nlinarith only [h2L, hr_ge1]
  intro N
  obtain ⟨R, X, hSym, hSub, ⟨hCard_low, hCard_up⟩, hDense, hD3, hCh, hCand, hDist⟩ :=
    complete_graph_2csp_expurgated_existence C₁ hC₁ rStar hr
  let L_X : ↥X → ↥X → Finset ↥X := fun a b =>
    if 0 < hammingDist a.val b.val ∧ hammingDist a.val b.val ≤ C₁ * rStar then
      Finset.univ.filter (fun x : ↥X => x.val ∈ bicliqueWitnessList R C₁ rStar a.val b.val)
    else ∅
  have h22L_ge1 : (1 : ℝ) ≤ (2 : ℝ) ^ (2 * cspL C₁) := by
    exact_mod_cast (Nat.one_le_two_pow (n := 2 * cspL C₁))
  have hμ₀_ge : (6000 : ℝ) ≤ (cspBeta0 C₁ : ℝ) * (2 : ℝ) ^ (2 * cspL C₁) := by
    have hbeta_r : (6000 : ℝ) ≤ (cspBeta0 C₁ : ℝ) := by exact_mod_cast hbeta0_ge
    nlinarith only [hbeta_r, h22L_ge1]
  have hr_real_ge1 : (1 : ℝ) ≤ (rStar : ℝ) := by exact_mod_cast hr_ge1
  have hX_ge2 : 2 ≤ X.card := by
    have hexp : (1 : ℝ) ≤ (98 / 100 : ℝ) * (cspBeta0 C₁ : ℝ) * (2 : ℝ) ^ (2 * cspL C₁) * (rStar : ℝ) := by
      have hμr : (6000 : ℝ) ≤ ((cspBeta0 C₁ : ℝ) * (2 : ℝ) ^ (2 * cspL C₁)) * (rStar : ℝ) := by
        nlinarith only [hμ₀_ge, hr_real_ge1]
      linarith
    have h2 : (2 : ℝ) ≤ (X.card : ℝ) := by
      calc
        (2 : ℝ) = (2 : ℝ) ^ (1 : ℝ) := by norm_num
        _ ≤ (2 : ℝ) ^ ((98 / 100 : ℝ) * (cspBeta0 C₁ : ℝ) * (2 : ℝ) ^ (2 * cspL C₁) * (rStar : ℝ)) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
        _ ≤ (X.card : ℝ) := hCard_low
    exact_mod_cast h2
  have hX_pos : (0 : ℝ) < (X.card : ℝ) := by
    exact_mod_cast (Nat.lt_of_lt_of_le Nat.zero_lt_two hX_ge2)
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hlogb_pow : ∀ z : ℝ, Real.logb 2 ((2 : ℝ) ^ z) = z := by
    intro z
    unfold Real.logb
    rw [Real.log_rpow (by norm_num : (0 : ℝ) < 2), mul_div_cancel_right₀ _ (ne_of_gt hlog2_pos)]
  have hlogb_mono : ∀ x y : ℝ, 0 < x → x ≤ y → Real.logb 2 x ≤ Real.logb 2 y := by
    intro x y hx hxy
    unfold Real.logb
    exact div_le_div_of_nonneg_right (Real.log_le_log hx hxy) (le_of_lt hlog2_pos)
  refine ⟨X, L_X, hX_ge2, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have h1 := hlogb_mono _ (X.card : ℝ) (Real.rpow_pos_of_pos (by norm_num) _) hCard_low
    rw [hlogb_pow] at h1
    have hμr_nn : 0 ≤ (cspBeta0 C₁ : ℝ) * (2 : ℝ) ^ (2 * cspL C₁) * (rStar : ℝ) :=
      mul_nonneg (le_of_lt hμ₀_pos) (Nat.cast_nonneg _)
    linarith
  · have h1 := hlogb_mono (X.card : ℝ) _ hX_pos hCard_up
    rw [hlogb_pow] at h1
    have hμr_nn : 0 ≤ (cspBeta0 C₁ : ℝ) * (2 : ℝ) ^ (2 * cspL C₁) * (rStar : ℝ) :=
      mul_nonneg (le_of_lt hμ₀_pos) (Nat.cast_nonneg _)
    linarith
  · have hc_nn : 0 ≤ c := Real.rpow_nonneg (by norm_num) _
    have hpow_c : (X.card : ℝ) ^ c ≤ (2 : ℝ) ^ ((1 / 5 : ℝ) * (cspLam0 C₁ : ℝ) * (rStar : ℝ)) := by
      have h1 : (X.card : ℝ) ^ c ≤
          ((2 : ℝ) ^ ((102 / 100 : ℝ) * (cspBeta0 C₁ : ℝ) * (2 : ℝ) ^ (2 * cspL C₁) * (rStar : ℝ))) ^ c :=
        Real.rpow_le_rpow (le_of_lt hX_pos) hCard_up hc_nn
      rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)] at h1
      have h2Lc : (2 : ℝ) ^ (2 * cspL C₁) * c = 1 / 32 := by
        dsimp [c]
        rw [← Real.rpow_natCast (2 : ℝ) (2 * cspL C₁), ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
        have hexp : ((2 * cspL C₁ : ℕ) : ℝ) + (-((2 * cspL C₁ + 5 : ℕ) : ℝ)) = - (5 : ℝ) := by
          push_cast
          ring
        rw [hexp]
        norm_num
      have hbeta_eq : (cspBeta0 C₁ : ℝ) = 6 * (cspLam0 C₁ : ℝ) := by
        unfold cspBeta0; push_cast; ring
      have hexp_le : ((102 / 100 : ℝ) * (cspBeta0 C₁ : ℝ) * (2 : ℝ) ^ (2 * cspL C₁) * (rStar : ℝ)) * c ≤
          (1 / 5 : ℝ) * (cspLam0 C₁ : ℝ) * (rStar : ℝ) := by
        have hrew : ((102 / 100 : ℝ) * (cspBeta0 C₁ : ℝ) * (2 : ℝ) ^ (2 * cspL C₁) * (rStar : ℝ)) * c =
            (102 / 100 : ℝ) * 6 * ((2 : ℝ) ^ (2 * cspL C₁) * c) * ((cspLam0 C₁ : ℝ) * (rStar : ℝ)) := by
          rw [hbeta_eq]; ring
        rw [hrew, h2Lc]
        have hlr_nn : 0 ≤ (cspLam0 C₁ : ℝ) * (rStar : ℝ) :=
          mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
        linarith
      exact le_trans h1 (Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp_le)
    have h1c : (X.card : ℝ) ^ (1 + c) = (X.card : ℝ) ^ c * (X.card : ℝ) := by
      rw [Real.rpow_add hX_pos, Real.rpow_one, mul_comm]
    have hm := mul_le_mul_of_nonneg_right hpow_c (le_of_lt hX_pos)
    rw [hexact_eq X rStar] at hDense
    have htot : (X.card : ℝ) ^ (1 + c) ≤ 192 * ((exactDistPairs X rStar).card : ℝ) := by
      rw [h1c]
      exact le_trans hm hDense
    linarith
  · intro x hx y hy hne
    have hd := hDist x hx y hy hne
    rw [hdHam_eq] at hd
    have hd_r : (rStar : ℝ) ≤ 2 * (hammingDist x y : ℝ) := by exact_mod_cast hd
    linarith
  · intro a b hpos hle
    dsimp [L_X]
    rw [if_pos ⟨hpos, hle⟩]
    have hne : a.val ≠ b.val := by
      intro heq
      rw [heq, hammingDist_self] at hpos
      exact (lt_irrefl 0 hpos).elim
    have hcard_le : (Finset.univ.filter (fun x : ↥X =>
        x.val ∈ bicliqueWitnessList R C₁ rStar a.val b.val)).card ≤
        (X.filter (fun x => x ∈ bicliqueWitnessList R C₁ rStar a.val b.val)).card := by
      apply Finset.card_le_card_of_injOn Subtype.val
      · intro x hx
        simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
        exact ⟨x.prop, hx⟩
      · intro x₁ _ x₂ _ heq
        exact Subtype.ext heq
    exact lt_of_le_of_lt hcard_le (hCand a.val a.prop b.val b.prop hne hle)
  · intro x w₀ hpos hle
    have hne : x.val ≠ w₀.val := by
      intro heq
      rw [heq, hammingDist_self] at hpos
      exact (lt_irrefl 0 hpos).elim
    have hcard_le : (Finset.univ.filter (fun y : ↥X =>
        y ≠ x ∧ y ≠ w₀ ∧
        hammingDist x.val y.val = rStar ∧
        (rStar : ℝ) / 4 < ((disagreeSet x.val w₀.val ∩ disagreeSet x.val y.val).card : ℝ))).card ≤
      (X.filter (fun y =>
        y ≠ x.val ∧ y ≠ w₀.val ∧ dHam x.val y = rStar ∧
        rStar < 4 * (diffCoords x.val w₀.val ∩ diffCoords x.val y).card)).card := by
      apply Finset.card_le_card_of_injOn Subtype.val
      · intro y hy
        simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
        have hlt_r : (rStar : ℝ) < 4 * ((disagreeSet x.val w₀.val ∩ disagreeSet x.val y.val).card : ℝ) := by
          linarith [hy.2.2.2]
        have hlt_nat : rStar < 4 * (disagreeSet x.val w₀.val ∩ disagreeSet x.val y.val).card := by
          exact_mod_cast hlt_r
        exact ⟨y.prop, fun h => hy.1 (Subtype.ext h), fun h => hy.2.1 (Subtype.ext h),
          hy.2.2.1, hlt_nat⟩
      · intro y₁ _ y₂ _ heq
        exact Subtype.ext heq
    exact lt_of_le_of_lt hcard_le (hCh x.val x.prop w₀.val w₀.prop hne hle)
  · apply h_6_3 N (cspQ C₁) C₁ rStar hN_ge2_val hq_ge2 hC₁ hr_ge1 R hSym X hSub
    intro x hx u hu z hz hdu hdz
    have hd3 := hD3 x hx u hu z hz hdu hdz
    have hd3_r : ((cspInvEta0 C₁ : ℝ)) * ((threeWayDisagree x u z).card : ℝ) ≤ (rStar : ℝ) := by
      exact_mod_cast hd3
    have hinv_eq : (cspInvEta0 C₁ : ℝ) = 80 := by
      unfold cspInvEta0
      norm_num
    rw [hinv_eq] at hd3_r
    change ((threeWayDisagree x u z).card : ℝ) ≤ (1 / 80 : ℝ) * (rStar : ℝ)
    linarith only [hd3_r]

end Solution.CSP
