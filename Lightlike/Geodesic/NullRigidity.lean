import Lightlike.Geodesic.LocalCausality

/-!
# Rigidity of a causal curve ending on the null cone of its start point

In a time ball at `p`, a future causal curve from `p` whose end point `q` has `σ_p(q) = g_p(v, v) = 0`
(normal coordinate `v`) is a reparametrisation of the radial null geodesic from `p` to `q`: in
normal coordinates `v t = λ t • v b` with `λ` monotone from `0` to `1`
(`Lightlike.Geodesic.IsTimeBall.null_rigidity`). This is the local step in the proof that the
generators of `∂J⁺(S)` are null geodesics (Hawking–Ellis, section 4.5; Chruściel, section 2.4).
-/

open Set Metric Filter Topology MeasureTheory
open scoped ContDiff

noncomputable section

namespace Lightlike

variable {V : Type*} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V] {n : ℕ}
  {B : V →L[ℝ] V →L[ℝ] ℝ}

/-- **A future causal vector orthogonal to a future null vector is proportional to it**: for a
Lorentzian form `B` with `B X X < 0`, `B P P = 0`, `B P X < 0`, `B w w ≤ 0`, `B w X < 0` and
`B P w = 0` one has `w = (B w X / B P X) • P`. -/
theorem IsLorentzianForm.eq_smul_of_orthogonal_null (h : IsLorentzianForm n B) {X P w : V}
    (hX : B X X < 0) (hP : B P P = 0) (hPX : B P X < 0) (hw : B w w ≤ 0) (hwX : B w X < 0)
    (hPw : B P w = 0) : w = (B w X / B P X) • P := by
  have hsymm := h.symm
  set c : ℝ := B w X / B P X with hc
  have hcP : c * B P X = B w X := by rw [hc]; exact div_mul_cancel₀ _ hPX.ne
  have hz : (w - c • P) = 0 := by
    refine h.eq_zero_of_orthogonal_timelike (X := X) hX ?_ ?_
    · simp only [map_sub, map_smul, _root_.sub_apply, _root_.smul_apply, smul_eq_mul]
      linarith
    · simp only [map_sub, map_smul, _root_.sub_apply, _root_.smul_apply, smul_eq_mul]
      have hwP : B w P = 0 := by rw [hsymm w P]; exact hPw
      rw [hwP, hP, hPw]
      linarith
  exact sub_eq_zero.1 hz


namespace Geodesic

variable {g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ} {U : Set (Fin n → ℝ)}

/-- A Lipschitz vector function with `ℓ(F) ≥ δ > 0` and `‖F‖ ≤ R` has a Lipschitz quotient
`F / ℓ F`. -/
theorem lipschitzOnWith_div_functional {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : ℝ → E} {s : Set ℝ} {K : NNReal} (hF : LipschitzOnWith K F s) (ℓ : E →L[ℝ] ℝ) {δ R : ℝ}
    (hδ : 0 < δ) (hlb : ∀ t ∈ s, δ ≤ ℓ (F t)) (hR : ∀ t ∈ s, ‖F t‖ ≤ R) :
    ∃ K' : NNReal, LipschitzOnWith K' (fun t => (ℓ (F t))⁻¹ • F t) s := by
  set R' : ℝ := max R 0 with hR'
  have hR'0 : 0 ≤ R' := le_max_right _ _
  refine ⟨⟨K / δ + ‖ℓ‖ * K * R' / δ ^ 2, by positivity⟩, ?_⟩
  refine LipschitzOnWith.of_dist_le_mul fun x hx y hy => ?_
  have hdx : δ ≤ ℓ (F x) := hlb x hx
  have hdy : δ ≤ ℓ (F y) := hlb y hy
  have hx0 : 0 < ℓ (F x) := lt_of_lt_of_le hδ hdx
  have hy0 : 0 < ℓ (F y) := lt_of_lt_of_le hδ hdy
  have hFd : ‖F x - F y‖ ≤ K * Dist.dist x y := by
    rw [← dist_eq_norm]; exact hF.dist_le_mul x hx y hy
  have hℓd : |ℓ (F y) - ℓ (F x)| ≤ ‖ℓ‖ * (K * Dist.dist x y) := by
    have := ℓ.le_opNorm (F y - F x)
    rw [map_sub, Real.norm_eq_abs] at this
    have h2 : ‖F y - F x‖ ≤ K * Dist.dist x y := by rw [norm_sub_rev]; exact hFd
    calc |ℓ (F y) - ℓ (F x)| ≤ ‖ℓ‖ * ‖F y - F x‖ := this
      _ ≤ ‖ℓ‖ * (K * Dist.dist x y) := mul_le_mul_of_nonneg_left h2 (norm_nonneg _)
  have hsplit : (ℓ (F x))⁻¹ • F x - (ℓ (F y))⁻¹ • F y =
      (ℓ (F x))⁻¹ • (F x - F y) + ((ℓ (F x))⁻¹ - (ℓ (F y))⁻¹) • F y := by
    simp only [smul_sub, sub_smul]; abel
  have hinv : |(ℓ (F x))⁻¹ - (ℓ (F y))⁻¹| ≤ |ℓ (F y) - ℓ (F x)| / δ ^ 2 := by
    rw [inv_sub_inv hx0.ne' hy0.ne', abs_div, abs_of_pos (mul_pos hx0 hy0)]
    rw [div_le_div_iff₀ (mul_pos hx0 hy0) (by positivity)]
    have : δ ^ 2 ≤ ℓ (F x) * ℓ (F y) := by nlinarith
    have h0 := abs_nonneg (ℓ (F y) - ℓ (F x))
    nlinarith [abs_sub_comm (ℓ (F x)) (ℓ (F y))]
  rw [dist_eq_norm, hsplit]
  have hxn : ‖(ℓ (F x))⁻¹‖ ≤ δ⁻¹ := by
    rw [norm_inv, Real.norm_eq_abs, abs_of_pos hx0]
    exact inv_anti₀ hδ hdx
  calc ‖(ℓ (F x))⁻¹ • (F x - F y) + ((ℓ (F x))⁻¹ - (ℓ (F y))⁻¹) • F y‖
      ≤ ‖(ℓ (F x))⁻¹ • (F x - F y)‖ + ‖((ℓ (F x))⁻¹ - (ℓ (F y))⁻¹) • F y‖ := norm_add_le _ _
    _ ≤ δ⁻¹ * ‖F x - F y‖ + (|ℓ (F y) - ℓ (F x)| / δ ^ 2) * R' := by
        gcongr
        · rw [norm_smul]; exact mul_le_mul_of_nonneg_right hxn (norm_nonneg _)
        · rw [norm_smul, Real.norm_eq_abs]
          exact mul_le_mul hinv ((hR y hy).trans (le_max_left _ _)) (norm_nonneg _) (by positivity)
    _ ≤ δ⁻¹ * (K * Dist.dist x y) + (‖ℓ‖ * (K * Dist.dist x y) / δ ^ 2) * R' := by
        gcongr
    _ = (K / δ + ‖ℓ‖ * K * R' / δ ^ 2) * Dist.dist x y := by
        field_simp


/-- **Local rigidity of a causal curve ending on the null cone of its start point** (the local step
towards "generators of `∂J⁺(S)` are null geodesics"). In a time ball at `p`, let `v` be a Lipschitz
curve in normal coordinates from `v a = 0` with future causal velocity almost everywhere, and
`σ_p(v b) = 0`. Then `v t = lam t • v b`, with `lam` monotone from `0` to `1`: the curve is a
reparametrisation of the radial null geodesic from `p` to `φ (v b)`. -/
theorem IsTimeBall.null_rigidity (hL : IsLorentzianCoordMetric g U) {p e : Fin n → ℝ} {ρ r : ℝ}
    {φ : OpenPartialHomeomorph (Fin n → ℝ) (Fin n → ℝ)} {N : (Fin n → ℝ) → Fin n → ℝ}
    (h : IsTimeBall g U p ρ φ e r N)
    {v : ℝ → Fin n → ℝ} {a b : ℝ} {K : NNReal} (hab : a < b) (hv : LipschitzOnWith K v (Icc a b))
    (hmem : ∀ t ∈ Icc a b, v t ∈ ball (0 : Fin n → ℝ) r) (ha : v a = 0)
    (hd : ∀ᵐ t, t ∈ Ioo a b → ∃ v' : Fin n → ℝ, HasDerivAt v v' t ∧
      pairing g (φ (v t)) (fderiv ℝ φ (v t) v') (fderiv ℝ φ (v t) v') ≤ 0 ∧
      pairing g (φ (v t)) (N (v t)) (fderiv ℝ φ (v t) v') < 0)
    (hnull : pairing g p (v b) (v b) = 0) :
    ∃ lam : ℝ → ℝ, lam a = 0 ∧ lam b = 1 ∧ MonotoneOn lam (Icc a b) ∧
      ∀ t ∈ Icc a b, v t = lam t • v b := by
  have hg := hL.1
  have hp : p ∈ U := by
    have := h.map_mem (v := 0) (mem_ball_self h.pos); rwa [h.chart.map_zero] at this
  set B := matForm (g p) with hB
  have hpB : ∀ x y, pairing g p x y = B x y := fun x y => pairing_eq_matForm g p x y
  have hBsymm : ∀ x y, B x y = B y x := fun x y => by rw [← hpB, ← hpB, pairing_comm hg hp]
  set ℓ : (Fin n → ℝ) →L[ℝ] ℝ := -(B e) with hℓdef
  have hℓ : ∀ w, ℓ w = -pairing g p e w := fun w => by
    rw [hℓdef, _root_.neg_apply, hpB]
  -- `σ_p ≤ 0` on every initial segment
  have hcaus : ∀ t ∈ Icc a b, B (v t) (v t) ≤ 0 := fun t ht => by
    rw [← hpB]
    refine (h.causal_cone hL ht.1 (hv.mono (Icc_subset_Icc_right ht.2))
      (fun s hs => hmem s ⟨hs.1, hs.2.trans ht.2⟩) ha ?_).1
    filter_upwards [hd] with s hs hsm
    obtain ⟨v', hv', hc, hf⟩ := hs ⟨hsm.1, lt_of_lt_of_le hsm.2 ht.2⟩
    exact ⟨v', hv', hc, hf⟩
  have hlv : ∀ᵐ t, t ∈ Ioo a b → 0 < ℓ (deriv v t) := by
    filter_upwards [hd] with t ht hmt
    obtain ⟨v', hv', -, hf⟩ := ht hmt
    have htr := hmem t (Ioo_subset_Icc_self hmt)
    rw [hv'.deriv, hℓ, ← h.dual _ htr v']
    linarith
  have hmono := Lightlike.Causal.functional_increasing_of_ae_pos hab hv ℓ hlv
  have hℓa : ℓ (v a) = 0 := by rw [ha, map_zero]
  have hpos : ∀ t ∈ Ioc a b, 0 < ℓ (v t) := by
    intro t ht
    have hsub : Icc a t ⊆ Icc a b := Icc_subset_Icc_right ht.2
    have := (Lightlike.Causal.functional_increasing_of_ae_pos ht.1 (hv.mono hsub) ℓ (by
      filter_upwards [hlv] with s hs hsm
      exact hs ⟨hsm.1, lt_of_lt_of_le hsm.2 ht.2⟩)).2
    rwa [hℓa] at this
  have hall : ∀ᵐ t, t ∈ Ioo a b → ∃ v' : Fin n → ℝ, HasDerivAt v v' t ∧ B (v t) v' ≤ 0 ∧
      (B (v t) (v t) = 0 → B (v t) v' = 0 → ℓ (v t) • v' = ℓ v' • v t) := by
    filter_upwards [hd] with t ht hmt
    obtain ⟨v', hv', hc, hf⟩ := ht hmt
    have htr := hmem t (Ioo_subset_Icc_self hmt)
    refine ⟨v', hv', ?_⟩
    have hy : φ (v t) ∈ U := h.map_mem htr
    have hLf := isLorentzianForm_matForm hL hy
    have hq : ∀ x z, pairing g (φ (v t)) x z = matForm (g (φ (v t))) x z := fun x z =>
      pairing_eq_matForm g _ x z
    have gPX : matForm (g (φ (v t))) (fderiv ℝ φ (v t) (v t)) (fderiv ℝ φ (v t) v') = B (v t) v' := by
      rw [← hq, ← hpB]; exact IsNormalChart.gauss hg h.chart (h.mem_ball htr) v'
    have gPP : matForm (g (φ (v t))) (fderiv ℝ φ (v t) (v t)) (fderiv ℝ φ (v t) (v t)) =
        B (v t) (v t) := by
      rw [← hq, ← hpB]; exact IsNormalChart.gauss hg h.chart (h.mem_ball htr) (v t)
    have gNP : matForm (g (φ (v t))) (fderiv ℝ φ (v t) (v t)) (N (v t)) = -ℓ (v t) := by
      rw [← hq, pairing_comm hg hy, h.dual _ htr, hℓ, neg_neg]
    have gNX : matForm (g (φ (v t))) (fderiv ℝ φ (v t) v') (N (v t)) = -ℓ v' := by
      rw [← hq, pairing_comm hg hy, h.dual _ htr, hℓ, neg_neg]
    have hNN : matForm (g (φ (v t))) (N (v t)) (N (v t)) < 0 := by
      rw [← hq]; exact h.timelike _ htr
    have hXX : matForm (g (φ (v t))) (fderiv ℝ φ (v t) v') (fderiv ℝ φ (v t) v') ≤ 0 := by
      rw [← hq]; exact hc
    have hx0pos : 0 < ℓ (v t) := hpos t ⟨hmt.1, hmt.2.le⟩
    have hℓv' : 0 < ℓ v' := by rw [hℓ, ← h.dual _ htr v']; linarith
    have hPle : matForm (g (φ (v t))) (fderiv ℝ φ (v t) (v t)) (fderiv ℝ φ (v t) (v t)) ≤ 0 := by
      rw [gPP]; exact hcaus t (Ioo_subset_Icc_self hmt)
    refine ⟨?_, fun hσ hperp => ?_⟩
    · have key := hLf.nonpos_of_futureCausal hNN hPle hXX (by rw [gNP]; linarith)
        (by rw [gNX]; linarith)
      rwa [gPX] at key
    · -- the velocity is parallel to the radial vector
      have hpar := hLf.eq_smul_of_orthogonal_null (X := N (v t))
        (P := fderiv ℝ φ (v t) (v t)) (w := fderiv ℝ φ (v t) v') hNN (by rw [gPP]; exact hσ)
        (by rw [gNP]; linarith) hXX (by rw [gNX]; linarith) (by rw [gPX]; exact hperp)
      rw [gNX, gNP] at hpar
      obtain ⟨D, -, -, hDφ⟩ := h.exists_fderiv_symm htr
      have hc0 : -ℓ v' / -ℓ (v t) = ℓ v' / ℓ (v t) := neg_div_neg_eq _ _
      rw [hc0, ← map_smul] at hpar
      have := congrArg D hpar
      rw [hDφ, hDφ] at this
      calc ℓ (v t) • v' = ℓ (v t) • ((ℓ v' / ℓ (v t)) • v t) := by rw [← this]
        _ = ℓ v' • v t := by
          rw [smul_smul]; congr 1; field_simp
  have hbound : ∀ t ∈ Icc a b, ‖v t‖ ≤ r := fun t ht => (mem_ball_zero_iff.1 (hmem t ht)).le
  have hfL := lipschitzOnWith_bilin_self B hv (R := ⟨r, h.pos.le⟩) hbound
  have hσb : B (v b) (v b) = 0 := by rw [← hpB]; exact hnull
  -- `σ_p` is nonincreasing along the curve
  have hσ0 : ∀ t ∈ Icc a b, B (v t) (v t) = 0 := by
    intro t₁ ht₁
    have hsub : Icc t₁ b ⊆ Icc a b := Icc_subset_Icc_left ht₁.1
    have h0 : LipschitzOnWith 0 (fun _ : ℝ => (0 : ℝ)) (Icc t₁ b) := (LipschitzWith.const (0 : ℝ)).lipschitzOnWith
    have := Lightlike.Causal.sub_le_sub_of_ae_deriv_le (f := fun t => B (v t) (v t))
      (h := fun _ => (0 : ℝ)) ht₁.2 (hfL.mono hsub) h0 (by
        filter_upwards [hall] with t ht hmt
        obtain ⟨v', hv', hle, -⟩ := ht ⟨lt_of_le_of_lt ht₁.1 hmt.1, hmt.2⟩
        have hf' : HasDerivAt (fun t => B (v t) (v t)) (B v' (v t) + B (v t) v') t :=
          (B.hasFDerivAt.comp_hasDerivAt t hv').clm_apply hv'
        refine ⟨hf'.differentiableAt, (hasDerivAt_const t (0 : ℝ)).differentiableAt, ?_⟩
        rw [hf'.deriv, deriv_const, hBsymm v' (v t)]
        linarith)
    rw [hσb] at this
    have h2 := hcaus t₁ ht₁
    linarith
  -- the velocity is orthogonal to the position, hence parallel
  have hpar : ∀ᵐ t, t ∈ Ioo a b → ∃ v' : Fin n → ℝ, HasDerivAt v v' t ∧
      ℓ (v t) • v' = ℓ v' • v t := by
    filter_upwards [hall] with t ht hmt
    obtain ⟨v', hv', -, hpp⟩ := ht hmt
    refine ⟨v', hv', hpp (hσ0 t (Ioo_subset_Icc_self hmt)) ?_⟩
    have hf' : HasDerivAt (fun t => B (v t) (v t)) (B v' (v t) + B (v t) v') t :=
      (B.hasFDerivAt.comp_hasDerivAt t hv').clm_apply hv'
    have hev : (fun t => B (v t) (v t)) =ᶠ[𝓝 t] fun _ => (0 : ℝ) := by
      filter_upwards [Icc_mem_nhds hmt.1 hmt.2] with s hs using hσ0 s hs
    have h0 := hf'.unique ((hasDerivAt_const t (0 : ℝ)).congr_of_eventuallyEq hev)
    rw [hBsymm v' (v t)] at h0
    linarith
  have hℓb : 0 < ℓ (v b) := hpos b ⟨hab, le_rfl⟩
  -- the normalised curve is constant
  have hconst : ∀ t₁ ∈ Ioo a b, (ℓ (v t₁))⁻¹ • v t₁ = (ℓ (v b))⁻¹ • v b := by
    intro t₁ ht₁
    have hsub : Icc t₁ b ⊆ Icc a b := Icc_subset_Icc_left ht₁.1.le
    have hδ : 0 < ℓ (v t₁) := hpos t₁ ⟨ht₁.1, ht₁.2.le⟩
    obtain ⟨K', hK'⟩ := lipschitzOnWith_div_functional (hv.mono hsub) ℓ hδ
      (fun t ht => by
        have := hmono.1 t₁ ⟨ht₁.1.le, ht₁.2.le⟩ t (hsub ht) ht.1
        exact this) (fun t ht => hbound t (hsub ht)) (R := r)
    have := norm_sub_le_of_ae_cone ht₁.2.le hK' (0 : (Fin n → ℝ) →L[ℝ] ℝ) (C := 0) (by
      filter_upwards [hpar] with t ht hmt
      obtain ⟨v', hv', hpp⟩ := ht ⟨lt_of_lt_of_le ht₁.1 hmt.1.le, hmt.2⟩
      refine ⟨0, ?_, by simp⟩
      have hℓt : 0 < ℓ (v t) := hpos t ⟨lt_of_lt_of_le ht₁.1 hmt.1.le, hmt.2.le⟩
      have hℓd : HasDerivAt (fun s => ℓ (v s)) (ℓ v') t := ℓ.hasFDerivAt.comp_hasDerivAt t hv'
      have hdd := (hℓd.inv hℓt.ne').smul hv'
      refine hdd.congr_deriv ?_
      have hv'eq : v' = ((ℓ (v t))⁻¹ * ℓ v') • v t := by
        have h1 := congrArg (fun x => (ℓ (v t))⁻¹ • x) hpp
        simp only [smul_smul, inv_mul_cancel₀ hℓt.ne', one_smul] at h1
        exact h1
      generalize ℓ v' = c at hv'eq ⊢
      rw [hv'eq, smul_smul, ← add_smul]
      have : (ℓ (v t))⁻¹ * ((ℓ (v t))⁻¹ * c) + -c / ℓ (v t) ^ 2 = 0 := by
        field_simp; ring
      show ((ℓ (v t))⁻¹ * ((ℓ (v t))⁻¹ * c) + -c / ℓ (v t) ^ 2) • v t = 0
      rw [this, zero_smul])
    simp only [ContinuousLinearMap.zero_apply, sub_self, mul_zero] at this
    exact (sub_eq_zero.1 (norm_le_zero_iff.1 this)).symm
  refine ⟨fun t => ℓ (v t) / ℓ (v b), by simp [hℓa], div_self hℓb.ne', ?_, ?_⟩
  · intro s hs t ht hst
    exact div_le_div_of_nonneg_right (hmono.1 s hs t ht hst) hℓb.le
  · intro t ht
    rcases ht.1.eq_or_lt with rfl | hta
    · simp [ha, hℓa]
    rcases ht.2.eq_or_lt with rfl | htb
    · simp [div_self hℓb.ne']
    have hℓt : 0 < ℓ (v t) := hpos t ⟨hta, ht.2⟩
    calc v t = ℓ (v t) • ((ℓ (v t))⁻¹ • v t) := by rw [smul_inv_smul₀ hℓt.ne']
      _ = ℓ (v t) • ((ℓ (v b))⁻¹ • v b) := by rw [hconst t ⟨hta, htb⟩]
      _ = (ℓ (v t) / ℓ (v b)) • v b := by rw [smul_smul, div_eq_mul_inv]

end Geodesic

end Lightlike
