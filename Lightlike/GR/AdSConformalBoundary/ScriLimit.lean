import Lightlike.GR.AdSConformalBoundary.SphereConformal

/-!
# The Poincaré action on null infinity is the limit of the bulk action

The fourth layer of GE7 m1 (analysis part). Along the outgoing ray `x(s) = u e₀ + s (1, n)` (retarded time `u`,
direction `n`, `s → ∞`) the image `Λ x(s) + a` has the form `V + c (1, n')` with `c = K s`, `V = u Λ e₀ + a`, and:

* `tendsto_retarded`: `t - r → V₀ - n' · V⃗` (the retarded time of `V + c (1, n')` converges);
* `tendsto_direction`: `x⃗ / r → n'` (the direction converges);
* `scriCoord`: the retarded time and direction `(t - |x⃗|, x⃗ / |x⃗|)` of a point of Minkowski space;
* `tendsto_scriCoord_ray`: along the ray the retarded time and direction of `Λ x(s) + a` converge to
  `scriAct Λ a (u, n)`: **the action of the Poincaré group on null infinity is the limit of its action on the bulk**.
-/

open Filter Topology Real Matrix

noncomputable section

namespace Lightlike

/-- Euclidean norm of a 3-vector. -/
def eNorm (w : Fin 3 → ℝ) : ℝ := √(∑ i, w i ^ 2)

lemma eNorm_add_smul_sq (V m : Fin 3 → ℝ) (hm : ∑ i, m i ^ 2 = 1) (c : ℝ) :
    ∑ i, (V i + c * m i) ^ 2 = c ^ 2 + 2 * c * (∑ i, m i * V i) + ∑ i, V i ^ 2 := by
  have : ∀ i : Fin 3, (V i + c * m i) ^ 2 = V i ^ 2 + 2 * c * (m i * V i) + c ^ 2 * m i ^ 2 := fun i => by ring
  simp only [this, Finset.sum_add_distrib, ← Finset.mul_sum, hm]
  ring

/-- `eNorm (V + c m) / c → 1`. -/
lemma tendsto_eNorm_div (V m : Fin 3 → ℝ) (hm : ∑ i, m i ^ 2 = 1) :
    Tendsto (fun c : ℝ => eNorm (fun i => V i + c * m i) / c) atTop (𝓝 1) := by
  set b := ∑ i, m i * V i
  set d := ∑ i, V i ^ 2
  have h1 : Tendsto (fun c : ℝ => 1 + 2 * b / c + d / c ^ 2) atTop (𝓝 1) := by
    have a1 : Tendsto (fun c : ℝ => 2 * b / c) atTop (𝓝 0) := tendsto_const_nhds.div_atTop tendsto_id
    have a2 : Tendsto (fun c : ℝ => d / c ^ 2) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (tendsto_pow_atTop (by norm_num))
    simpa using (a1.const_add 1).add a2
  have h2 := (Real.continuous_sqrt.tendsto 1).comp h1
  simp only [Real.sqrt_one] at h2
  refine h2.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with c hc
  simp only [Function.comp, eNorm, eNorm_add_smul_sq V m hm]
  rw [show c ^ 2 + 2 * c * b + d = c ^ 2 * (1 + 2 * b / c + d / c ^ 2) by field_simp]
  rw [Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq hc.le]
  field_simp

/-- **The retarded time converges**: `V₀ + c - |V⃗ + c m| → V₀ - m · V⃗` as `c → ∞`, for a unit `m`. -/
theorem tendsto_retarded (V0 : ℝ) (V m : Fin 3 → ℝ) (hm : ∑ i, m i ^ 2 = 1) :
    Tendsto (fun c : ℝ => V0 + c - eNorm (fun i => V i + c * m i)) atTop
      (𝓝 (V0 - ∑ i, m i * V i)) := by
  set b := ∑ i, m i * V i
  set d := ∑ i, V i ^ 2
  have hq := tendsto_eNorm_div V m hm
  have h1 : Tendsto (fun c : ℝ => (2 * b + d / c) / (eNorm (fun i => V i + c * m i) / c + 1)) atTop
      (𝓝 ((2 * b + 0) / (1 + 1))) := by
    refine Tendsto.div ?_ (hq.add_const 1) (by norm_num)
    exact (tendsto_const_nhds.div_atTop tendsto_id).const_add (2 * b)
  have h2 : Tendsto (fun c : ℝ => V0 - (2 * b + d / c) / (eNorm (fun i => V i + c * m i) / c + 1))
      atTop (𝓝 (V0 - b)) := by
    have := h1.const_sub V0
    convert this using 2
    ring
  refine h2.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with c hc
  set r := eNorm (fun i => V i + c * m i) with hr
  have hr2 : r ^ 2 = c ^ 2 + 2 * c * b + d := by
    rw [hr, eNorm, Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _), eNorm_add_smul_sq V m hm]
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hpos : 0 < r / c + 1 := by positivity
  have : r - c = (2 * b + d / c) / (r / c + 1) := by
    rw [eq_div_iff hpos.ne']
    field_simp
    nlinarith [hr2]
  linarith

/-- **The direction converges**: `(V⃗ + c m) / |V⃗ + c m| → m` as `c → ∞`, for a unit `m`. -/
theorem tendsto_direction (V m : Fin 3 → ℝ) (hm : ∑ i, m i ^ 2 = 1) :
    Tendsto (fun c : ℝ => (eNorm (fun i => V i + c * m i))⁻¹ • (fun i => V i + c * m i)) atTop (𝓝 m) := by
  rw [tendsto_pi_nhds]
  intro i
  have hq := tendsto_eNorm_div V m hm
  have h1 : Tendsto (fun c : ℝ => (V i / c + m i) / (eNorm (fun i => V i + c * m i) / c)) atTop
      (𝓝 ((0 + m i) / 1)) := by
    refine Tendsto.div ?_ hq (by norm_num)
    exact (tendsto_const_nhds.div_atTop tendsto_id).add_const (m i)
  simp only [zero_add, div_one] at h1
  refine h1.congr' ?_
  filter_upwards [eventually_gt_atTop (2 * |∑ i, m i * V i| + 1)] with c hc'
  have hc : 0 < c := lt_of_le_of_lt (by positivity) hc'
  have hr : eNorm (fun i => V i + c * m i) ≠ 0 := by
    have : 0 < eNorm (fun i => V i + c * m i) := by
      rw [eNorm]
      apply Real.sqrt_pos.mpr
      rw [eNorm_add_smul_sq V m hm]
      have hd : 0 ≤ ∑ i, V i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
      nlinarith [neg_abs_le (∑ i, m i * V i), abs_nonneg (∑ i, m i * V i)]
    exact this.ne'
  simp only [Pi.smul_apply, smul_eq_mul]
  field_simp

/-- The retarded time and the direction of a point `x = (t, x⃗)` of Minkowski space: `(t - |x⃗|, x⃗ / |x⃗|)`. -/
def scriCoord (x : Fin 4 → ℝ) : ℝ × (Fin 3 → ℝ) :=
  (x 0 - eNorm (fun i => x i.succ), (eNorm (fun i => x i.succ))⁻¹ • fun i => x i.succ)

/-- The outgoing null ray `s ↦ u e₀ + s (1, n)`: retarded time `u` and direction `n`. -/
def scriRay (u : ℝ) (n : Fin 3 → ℝ) (s : ℝ) : Fin 4 → ℝ := u • Pi.single 0 1 + s • nullVec n

/-- **The action on null infinity is the limit of the action on the bulk**: along the outgoing ray of retarded
time `u` and direction `n`, the retarded time and direction of the image `Λ x(s) + a` converge to
`scriAct Λ a (u, n)`. -/
theorem tendsto_scriCoord_ray {Λ : Matrix (Fin 4) (Fin 4) ℝ} (hΛ : IsOrthochronous Λ) (a : Fin 4 → ℝ)
    (u : ℝ) {n : Fin 3 → ℝ} (hn : ∑ i, n i ^ 2 = 1) :
    Tendsto (fun s : ℝ => scriCoord (Λ *ᵥ scriRay u n s + a)) atTop (𝓝 (scriAct Λ a (u, n))) := by
  set K := nullDirFactor Λ n with hKdef
  have hK : 0 < K := nullDirFactor_pos hΛ.lorentz hΛ.pos hn
  set m := nullDirMap Λ n with hmdef
  have hm : ∑ i, m i ^ 2 = 1 := sum_sq_nullDirMap hΛ.lorentz hΛ.pos hn
  set V : Fin 4 → ℝ := u • (Λ *ᵥ Pi.single 0 1) + a with hV
  have himg : ∀ s : ℝ, Λ *ᵥ scriRay u n s + a = V + (K * s) • nullVec m := by
    intro s
    have h := mulVec_nullVec_eq hΛ.lorentz hΛ.pos hn
    rw [scriRay, mulVec_add, mulVec_smul, mulVec_smul, h, hV, smul_smul]
    have e : s * nullDirFactor Λ n = K * s := by rw [mul_comm]
    rw [e]
    abel
  have hcK : Tendsto (fun s : ℝ => K * s) atTop atTop := tendsto_id.const_mul_atTop hK
  have hcomp : ∀ (s : ℝ) (j : Fin 4), (Λ *ᵥ scriRay u n s + a) j = V j + K * s * nullVec m j := by
    intro s j
    rw [himg s]
    simp
  have hfst : Tendsto (fun s : ℝ => (Λ *ᵥ scriRay u n s + a) 0 -
      eNorm (fun i => (Λ *ᵥ scriRay u n s + a) i.succ)) atTop
      (𝓝 (V 0 - ∑ i, m i * V i.succ)) := by
    have := (tendsto_retarded (V 0) (fun i => V i.succ) m hm).comp hcK
    refine this.congr (fun s => ?_)
    simp only [Function.comp_apply, hcomp, nullVec, Fin.cons_zero, Fin.cons_succ, mul_one]
  have hsnd : Tendsto (fun s : ℝ => (eNorm (fun i => (Λ *ᵥ scriRay u n s + a) i.succ))⁻¹ •
      fun i => (Λ *ᵥ scriRay u n s + a) i.succ) atTop (𝓝 m) := by
    have := (tendsto_direction (fun i => V i.succ) m hm).comp hcK
    refine this.congr (fun s => ?_)
    simp only [Function.comp_apply, hcomp, nullVec, Fin.cons_succ]
  have hlim : V 0 - ∑ i, m i * V i.succ = (scriAct Λ a (u, n)).1 := by
    have hdot : nullVec m ⬝ᵥ (eta 4 *ᵥ V) = u * (nullVec m ⬝ᵥ (eta 4 *ᵥ (Λ *ᵥ Pi.single 0 1))) +
        nullVec m ⬝ᵥ (eta 4 *ᵥ a) := by
      rw [hV, mulVec_add, mulVec_smul, dotProduct_add, dotProduct_smul, smul_eq_mul]
    have he0 : K * (nullVec m ⬝ᵥ (eta 4 *ᵥ (Λ *ᵥ Pi.single 0 1))) = -1 := by
      have h := minkDot_mulVec hΛ.lorentz (nullVec n) (Pi.single 0 1)
      rw [mulVec_nullVec_eq hΛ.lorentz hΛ.pos hn, smul_dotProduct, smul_eq_mul] at h
      rw [h, nullVec_dot]
      simp
    have hv := nullVec_dot m V
    rw [scriAct_fst]
    have hKne : K ≠ 0 := hK.ne'
    have : nullVec m ⬝ᵥ (eta 4 *ᵥ (Λ *ᵥ Pi.single 0 1)) = -1 / K := by
      field_simp; linarith
    show V 0 - ∑ i, m i * V i.succ = u / K - nullVec m ⬝ᵥ (eta 4 *ᵥ a)
    rw [hdot, this] at hv
    have e2 : u * (-1 / K) = -(u / K) := by ring
    linarith
  have hfull := hfst.prodMk_nhds hsnd
  rw [hlim] at hfull
  exact hfull

end Lightlike
