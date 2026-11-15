import Lightlike.Regge.Geodesic.Jet3
import Lightlike.Regge.Geodesic.Sixth
import Lightlike.Regge.CMS.NormalCoord

/-!
# Re-expansion of the second jet about a nearby point (RC6b, step 5b)

The midpoint form of the squared distance has its jets at the midpoint `m = v + s`. To compare it
with the jets at the vertex `v`, the second derivatives of the metric and the Christoffel symbols
must be Lipschitz in the base point, uniformly on a compact set.

## Main results

* `exists_lipschitz`: for a coordinate metric on `U` and compact `K ⊆ U` there are `M` and `r > 0`
  with `|∂_l ∂_k g_ij (x + s) - ∂_l ∂_k g_ij (x)| ≤ M ‖s‖` and
  `|Γ^i_{jk}(x + s) - Γ^i_{jk}(x)| ≤ M ‖s‖` for `x ∈ K`, `‖s‖ ≤ r`.
-/

open Set Lightlike
open scoped ContDiff Matrix

namespace Lightlike.Geodesic

variable {n : ℕ} {g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ} {U : Set (Fin n → ℝ)}

/-- **The metric, its second jet and the Christoffel symbols are Lipschitz in the base point**, uniformly on a
compact set. -/
theorem exists_lipschitz (hg : IsCoordMetric g U) {K : Set (Fin n → ℝ)} (hK : IsCompact K)
    (hKU : K ⊆ U) :
    ∃ M r : ℝ, 0 < r ∧ ∀ x ∈ K, ∀ s : Fin n → ℝ, ‖s‖ ≤ r →
      (∀ i j k l, |pd l (pd k (fun y => g y i j)) (x + s) - pd l (pd k (fun y => g y i j)) x| ≤
        M * ‖s‖) ∧
      (∀ i j k, |christoffel g i j k (x + s) - christoffel g i j k x| ≤ M * ‖s‖) ∧
      (∀ i j, |g (x + s) i j - g x i j| ≤ M * ‖s‖) := by
  obtain ⟨ρ, hρ, hρU⟩ := hK.exists_cthickening_subset_open hg.isOpen hKU
  have hK' : IsCompact (Metric.cthickening ρ K) := hK.cthickening
  obtain ⟨m, hm0, hm⟩ := hg.exists_jet_bound hK' hρU
  refine ⟨n * m, ρ, hρ, fun x hx s hs => ?_⟩
  have hin : ∀ t ∈ Icc (0 : ℝ) 1, x + t • s ∈ Metric.cthickening ρ K := fun t ht =>
    Metric.closedBall_subset_cthickening hx _ (by
      rw [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg ht.1]
      nlinarith [ht.1, ht.2, norm_nonneg s])
  have hseg : ∀ t ∈ Icc (0 : ℝ) 1, x + t • s ∈ U := fun t ht => hρU (hin t ht)
  refine ⟨fun i j k l => ?_, fun i j k => ?_, fun i j => ?_⟩
  · have hf : ContDiffOn ℝ ∞ (pd l (pd k (fun y => g y i j))) U :=
      contDiffOn_pd (hg.contDiffOn_pdg k i j) hg.isOpen l
    have := taylor_one hf hg.isOpen hseg (m := m) (fun t ht p => (hm _ (hin t ht) i j k l p).2.2.2.2.1)
    simpa [mul_comm, mul_assoc, mul_left_comm] using this
  · have hf : ContDiffOn ℝ ∞ (christoffel g i j k) U := hg.contDiffOn_christoffel i j k
    have := taylor_one hf hg.isOpen hseg (m := m) (fun t ht p => (hm _ (hin t ht) i j k p p).2.2.2.2.2.2)
    simpa [mul_comm, mul_assoc, mul_left_comm] using this
  · have := taylor_one (hg.smooth i j) hg.isOpen hseg (m := m)
      (fun t ht p => (hm _ (hin t ht) i j p p p).2.2.1)
    simpa [mul_comm, mul_assoc, mul_left_comm] using this

/-- **Derivative of the inverse metric**: `∂_l (g⁻¹)_{im} = - Σ_{a,b} g^{ia} (∂_l g_{ab}) g^{bm}`. -/
theorem pd_inv (hg : IsCoordMetric g U) {x : Fin n → ℝ} (hx : x ∈ U) (l i m : Fin n) :
    pd l (fun y => (g y)⁻¹ i m) x =
      -∑ a, ∑ b, (g x)⁻¹ i a * pd l (fun y => g y a b) x * (g x)⁻¹ b m := by
  have hgd : ∀ a b, DifferentiableAt ℝ (fun y => g y a b) x := fun a b =>
    differentiableAt_of_contDiffOn (hg.smooth a b) hg.isOpen hx
  have hid : ∀ a b, DifferentiableAt ℝ (fun y => (g y)⁻¹ a b) x := fun a b =>
    differentiableAt_of_contDiffOn (hg.contDiffOn_inv a b) hg.isOpen hx
  -- the matrix of derivatives of the inverse
  set D : Matrix (Fin n) (Fin n) ℝ := Matrix.of fun b m => pd l (fun y => (g y)⁻¹ b m) x with hD
  set P : Matrix (Fin n) (Fin n) ℝ := Matrix.of fun a b => pd l (fun y => g y a b) x with hP
  have key : g x * D = -(P * (g x)⁻¹) := by
    ext a m
    have hev : (fun y => ∑ b, g y a b * (g y)⁻¹ b m) =ᶠ[nhds x] fun _ => (1 : Matrix (Fin n) (Fin n) ℝ) a m := by
      filter_upwards [hg.isOpen.mem_nhds hx] with y hy
      have := Matrix.mul_nonsing_inv (g y) (hg.isUnit_det y hy)
      have h2 := congrFun (congrFun this a) m
      rwa [Matrix.mul_apply] at h2
    have h0 := pd_congr hev l
    have hs := pd_sum (f := fun b y => g y a b * (g y)⁻¹ b m) Finset.univ (x := x)
      (fun b _ => (hgd a b).mul (hid b m)) l
    rw [hs, pd_const] at h0
    simp only [pd_mul (hgd a _) (hid _ m)] at h0
    rw [Finset.sum_add_distrib] at h0
    simp only [Matrix.mul_apply, Matrix.neg_apply, hD, hP, Matrix.of_apply]
    linarith [h0]
  have : D = -((g x)⁻¹ * P * (g x)⁻¹) := by
    have h1 : (g x)⁻¹ * (g x) = 1 := Matrix.nonsing_inv_mul _ (hg.isUnit_det x hx)
    calc D = ((g x)⁻¹ * g x) * D := by rw [h1, Matrix.one_mul]
      _ = (g x)⁻¹ * (g x * D) := by rw [Matrix.mul_assoc]
      _ = _ := by rw [key]; simp [Matrix.mul_assoc]
  have h3 := congrFun (congrFun this i) m
  simp only [hD, Matrix.of_apply, Matrix.neg_apply, Matrix.mul_apply, hP] at h3
  rw [h3]
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]

/-- **Derivative of the Christoffel symbols** in terms of the first and second jets of the metric:
`∂_l Γ^i_{jk} = dGam g A B l i j k` with `A k i j = ∂_k g_{ij}` and `B l k i j = ∂_l ∂_k g_{ij}`. -/
theorem pd_christoffel (hg : IsCoordMetric g U) {x : Fin n → ℝ} (hx : x ∈ U) (l i j k : Fin n) :
    pd l (christoffel g i j k) x =
      CMS.dGam (g x) (fun k i j => pd k (fun y => g y i j) x)
        (fun l k i j => pd l (pd k (fun y => g y i j)) x) l i j k := by
  have hgd : ∀ a b, DifferentiableAt ℝ (fun y => g y a b) x := fun a b =>
    differentiableAt_of_contDiffOn (hg.smooth a b) hg.isOpen hx
  have hpd : ∀ c a b, DifferentiableAt ℝ (pd c (fun y => g y a b)) x := fun c a b =>
    differentiableAt_of_contDiffOn (hg.contDiffOn_pdg c a b) hg.isOpen hx
  have hid : ∀ a b, DifferentiableAt ℝ (fun y => (g y)⁻¹ a b) x := fun a b =>
    differentiableAt_of_contDiffOn (hg.contDiffOn_inv a b) hg.isOpen hx
  have hcf : ∀ m, DifferentiableAt ℝ (christoffelFirst g m j k) x := fun m =>
    differentiableAt_of_contDiffOn (hg.contDiffOn_christoffelFirst m j k) hg.isOpen hx
  have hfun : christoffel g i j k = fun y => ∑ m, (g y)⁻¹ i m * christoffelFirst g m j k y :=
    funext (christoffel_eq_sum g i j k)
  have hcfd : ∀ m, pd l (christoffelFirst g m j k) x =
      (1 / 2) * (pd l (pd j (fun y => g y m k)) x + pd l (pd k (fun y => g y m j)) x
        - pd l (pd m (fun y => g y j k)) x) := by
    intro m
    have h1 := pd_const_mul (1 / 2 : ℝ) (f := fun y => pd j (fun z => g z m k) y
      + pd k (fun z => g z m j) y - pd m (fun z => g z j k) y)
      (((hpd j m k).add (hpd k m j)).sub (hpd m j k)) l
    have h2 := pd_sub (f₁ := fun y => pd j (fun z => g z m k) y + pd k (fun z => g z m j) y)
      (f₂ := pd m (fun z => g z j k)) ((hpd j m k).add (hpd k m j)) (hpd m j k) l
    have h3 := pd_add (hpd j m k) (hpd k m j) l
    unfold christoffelFirst
    rw [h1, h2, h3]
  have hs := pd_sum (f := fun m y => (g y)⁻¹ i m * christoffelFirst g m j k y) Finset.univ (x := x)
    (fun m _ => (hid i m).mul (hcf m)) l
  rw [hfun, hs]
  unfold CMS.dGam
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [pd_mul (hid i m) (hcf m), pd_inv hg hx l i m, hcfd m]
  simp only [CMS.dGamLow, CMS.gamLow, christoffelFirst]
  ring

/-- `|Σ_k Σ_l a_k b_l c_{kl}| ≤ n² A B C` for entries bounded by `A, B, C`. -/
theorem abs_sum2_le {a b : Fin n → ℝ} {c : Fin n → Fin n → ℝ} {A B C : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (ha : ∀ k, |a k| ≤ A) (hb : ∀ l, |b l| ≤ B) (hc : ∀ k l, |c k l| ≤ C) :
    |∑ k, ∑ l, a k * b l * c k l| ≤ n ^ 2 * A * B * C := by
  calc |∑ k, ∑ l, a k * b l * c k l| ≤ ∑ k, |∑ l, a k * b l * c k l| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k, ∑ l, |a k * b l * c k l| :=
        Finset.sum_le_sum fun k _ => Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k : Fin n, ∑ _l : Fin n, A * B * C := Finset.sum_le_sum fun k _ =>
        Finset.sum_le_sum fun l _ => by
          rw [abs_mul, abs_mul]
          exact mul_le_mul (mul_le_mul (ha k) (hb l) (abs_nonneg _) hA) (hc k l) (abs_nonneg _)
            (mul_nonneg hA hB)
    _ = n ^ 2 * A * B * C := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

/-- Entries of the difference of two second jets in the directions `Δ, Δ`. -/
theorem abs_ddmat_sub_le {x y Δ : Fin n → ℝ} {M : ℝ}
    (h : ∀ i j k l, |pd l (pd k (fun z => g z i j)) y - pd l (pd k (fun z => g z i j)) x| ≤ M)
    (i j : Fin n) : |ddmat g y Δ Δ i j - ddmat g x Δ Δ i j| ≤ n ^ 2 * ‖Δ‖ * ‖Δ‖ * M := by
  simp only [ddmat, Matrix.of_apply, ← Finset.sum_sub_distrib]
  have := abs_sum2_le (a := Δ) (b := Δ)
    (c := fun k l => pd l (pd k (fun z => g z i j)) y - pd l (pd k (fun z => g z i j)) x)
    (norm_nonneg Δ) (norm_nonneg Δ) (abs_le_norm_apply Δ) (abs_le_norm_apply Δ)
    (fun k l => h i j k l)
  refine le_trans (le_of_eq ?_) this
  congr 1
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring

/-- Entries of the difference of two Christoffel contractions. -/
theorem abs_chr_sub_le {x y Δ : Fin n → ℝ} {M : ℝ}
    (h : ∀ i j k, |christoffel g i j k y - christoffel g i j k x| ≤ M) (i : Fin n) :
    |chr g y Δ Δ i - chr g x Δ Δ i| ≤ n ^ 2 * ‖Δ‖ * ‖Δ‖ * M := by
  simp only [chr, ← Finset.sum_sub_distrib]
  have := abs_sum2_le (a := Δ) (b := Δ) (c := fun j k => christoffel g i j k y - christoffel g i j k x)
    (norm_nonneg Δ) (norm_nonneg Δ) (abs_le_norm_apply Δ) (abs_le_norm_apply Δ) (fun j k => h i j k)
  refine le_trans (le_of_eq ?_) this
  congr 1
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring

/-- **The midpoint jet re-expanded about the vertex.** For a Riemannian coordinate metric on `U`
and a compact `K ⊆ U` there are `C` and `r > 0` such that for `v ∈ K` and `‖s‖, ‖Δ‖ ≤ h ≤ r`, the
quartic midpoint jet `midJet g (v + s) Δ` differs from the polynomial
`g_v(Δ,Δ) + ∂_s g_v(Δ,Δ) + ½ ∂_s ∂_s g_v(Δ,Δ) + (1/24) ∂_Δ ∂_Δ g_v(Δ,Δ) - (1/12) |Γ_v(Δ,Δ)|²_{g_v}`
by at most `C h⁵`. -/
theorem IsRiemMetric.exists_midJet_reexpand (hg : IsRiemMetric g U) {K : Set (Fin n → ℝ)}
    (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ C r : ℝ, 0 < r ∧ ∀ v ∈ K, ∀ s Δ : Fin n → ℝ, ∀ h : ℝ, ‖s‖ ≤ h → ‖Δ‖ ≤ h → h ≤ r →
      |midJet g (v + s) Δ -
        (Δ ⬝ᵥ (g v *ᵥ Δ) + Δ ⬝ᵥ (dmat g v s *ᵥ Δ) + (1 / 2) * (Δ ⬝ᵥ (ddmat g v s s *ᵥ Δ))
          + (1 / 24) * (Δ ⬝ᵥ (ddmat g v Δ Δ *ᵥ Δ))
          - (1 / 12) * (chr g v Δ Δ ⬝ᵥ (g v *ᵥ chr g v Δ Δ)))| ≤ C * h ^ 5 := by
  obtain ⟨B, δ, l, hJ⟩ := hg.exists_localJet hK hKU
  obtain ⟨M, r₁, hr₁, hL⟩ := exists_lipschitz hg.coord hK hKU
  obtain ⟨M2, hM20, hM2⟩ := hg.coord.exists_jet_bound hK hKU
  rcases K.eq_empty_or_nonempty with rfl | ⟨x₀, hx₀⟩
  · exact ⟨0, 1, one_pos, fun v hv => absurd hv (Set.notMem_empty v)⟩
  have hδ := (hJ x₀ hx₀).δ_pos
  have hδ1 := (hJ x₀ hx₀).δ_le_one
  have hB1 : 1 ≤ B := (hJ x₀ hx₀).one_le
  set M' := |M| with hM'
  have hM'0 : 0 ≤ M' := abs_nonneg _
  have hLg : ∀ x ∈ K, ∀ s : Fin n → ℝ, ‖s‖ ≤ r₁ →
      (∀ i j k l, |pd l (pd k (fun y => g y i j)) (x + s) - pd l (pd k (fun y => g y i j)) x| ≤
        M' * ‖s‖) ∧
      (∀ i j k, |christoffel g i j k (x + s) - christoffel g i j k x| ≤ M' * ‖s‖) ∧
      (∀ i j, |g (x + s) i j - g x i j| ≤ M' * ‖s‖) := by
    intro x hx s hs
    obtain ⟨a, b, c⟩ := hL x hx s hs
    have hm : M * ‖s‖ ≤ M' * ‖s‖ := mul_le_mul_of_nonneg_right (le_abs_self M) (norm_nonneg s)
    exact ⟨fun i j k l => (a i j k l).trans hm, fun i j k => (b i j k).trans hm,
      fun i j => (c i j).trans hm⟩
  set N : ℝ := (n : ℝ) with hNdef
  have hN0 : 0 ≤ N := Nat.cast_nonneg n
  set Ge : ℝ := M2 + M' with hGe
  have hGe0 : 0 ≤ Ge := by positivity
  -- constants
  set K3 : ℝ := N ^ 2 * Ge * (N ^ 2 * M') * (B + N ^ 2 * M') + N ^ 2 * Ge * B * (N ^ 2 * M')
      + N ^ 2 * M' * B ^ 2 with hK3
  have hK30 : 0 ≤ K3 := by positivity
  refine ⟨B + (1 / 24) * (N ^ 4 * M') + (1 / 12) * K3, min r₁ δ, lt_min hr₁ hδ, ?_⟩
  intro v hv s Δ h hs hΔ hh
  have hh0 : 0 ≤ h := (norm_nonneg s).trans hs
  have hh1 : h ≤ 1 := hh.trans ((min_le_right _ _).trans hδ1)
  have hsr : ‖s‖ ≤ r₁ := hs.trans (hh.trans (min_le_left _ _))
  have hsδ : ‖s‖ ≤ δ := hs.trans (hh.trans (min_le_right _ _))
  obtain ⟨hL2, hLc, hLg⟩ := hLg v hv s hsr
  have J := hJ v hv
  have hs0 := norm_nonneg s
  have hΔ0 := norm_nonneg Δ
  have hs1 : ‖s‖ ≤ 1 := hs.trans hh1
  -- E1: Taylor of the metric
  have E1 : |Δ ⬝ᵥ (g (v + s) *ᵥ Δ) - (Δ ⬝ᵥ (g v *ᵥ Δ) + Δ ⬝ᵥ (dmat g v s *ᵥ Δ)
      + (1 / 2) * (Δ ⬝ᵥ (ddmat g v s s *ᵥ Δ)))| ≤ B * h ^ 5 := by
    have h1 := J.tay_le s hsδ Δ Δ
    have e : Δ ⬝ᵥ ((g (v + s) - taylorMetric g v s) *ᵥ Δ) = Δ ⬝ᵥ (g (v + s) *ᵥ Δ)
        - (Δ ⬝ᵥ (g v *ᵥ Δ) + Δ ⬝ᵥ (dmat g v s *ᵥ Δ) + (1 / 2) * (Δ ⬝ᵥ (ddmat g v s s *ᵥ Δ))) := by
      unfold taylorMetric
      simp only [Matrix.sub_mulVec, Matrix.add_mulVec, Matrix.smul_mulVec, dotProduct_sub,
        dotProduct_add, dotProduct_smul, smul_eq_mul]
    rw [e] at h1
    refine h1.trans ?_
    calc B * ‖s‖ ^ 3 * ‖Δ‖ * ‖Δ‖ ≤ B * h ^ 3 * h * h := by gcongr
      _ = B * h ^ 5 := by ring
  -- E2: second jet
  have E2 : |Δ ⬝ᵥ (ddmat g (v + s) Δ Δ *ᵥ Δ) - Δ ⬝ᵥ (ddmat g v Δ Δ *ᵥ Δ)| ≤ N ^ 4 * M' * h ^ 5 := by
    have hent : ∀ i j, |(ddmat g (v + s) Δ Δ - ddmat g v Δ Δ) i j| ≤
        N ^ 2 * ‖Δ‖ * ‖Δ‖ * (M' * ‖s‖) := fun i j =>
      abs_ddmat_sub_le (fun i j k l => hL2 i j k l) i j
    have := abs_dot_mulVec_le (by positivity) hent Δ Δ
    rw [Matrix.sub_mulVec, dotProduct_sub] at this
    refine this.trans ?_
    calc N ^ 2 * (N ^ 2 * ‖Δ‖ * ‖Δ‖ * (M' * ‖s‖)) * ‖Δ‖ * ‖Δ‖
        ≤ N ^ 2 * (N ^ 2 * h * h * (M' * h)) * h * h := by gcongr
      _ = N ^ 4 * M' * h ^ 5 := by ring
  -- E3: the quadratic Christoffel term
  set a := chr g (v + s) Δ Δ with ha
  set b := chr g v Δ Δ with hb
  have hbn : ‖b‖ ≤ B * h ^ 2 := by
    have := J.chr_le Δ Δ
    refine this.trans ?_
    calc B * ‖Δ‖ * ‖Δ‖ ≤ B * h * h := by gcongr
      _ = B * h ^ 2 := by ring
  have hdn : ‖a - b‖ ≤ N ^ 2 * M' * h ^ 3 := by
    refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
    rw [Real.norm_eq_abs]
    have := abs_chr_sub_le (g := g) (x := v) (y := v + s) (Δ := Δ) (M := M' * ‖s‖)
      (fun i j k => hLc i j k) i
    refine this.trans ?_
    calc N ^ 2 * ‖Δ‖ * ‖Δ‖ * (M' * ‖s‖) ≤ N ^ 2 * h * h * (M' * h) := by gcongr
      _ = N ^ 2 * M' * h ^ 3 := by ring
  have han : ‖a‖ ≤ (B + N ^ 2 * M') * h ^ 2 := by
    have h1 : ‖a‖ ≤ ‖b‖ + ‖a - b‖ := by
      have := norm_le_insert' a b
      simpa using this
    have h2 : N ^ 2 * M' * h ^ 3 ≤ N ^ 2 * M' * h ^ 2 := by
      have : h ^ 3 ≤ h ^ 2 := pow_le_pow_of_le_one hh0 hh1 (by norm_num)
      exact mul_le_mul_of_nonneg_left this (by positivity)
    nlinarith
  have hGm : ∀ i j, |g (v + s) i j| ≤ Ge := fun i j => by
    have h1 := hLg i j
    have h2 := (hM2 v hv i j i i i).1
    have h3 : M' * ‖s‖ ≤ M' := by nlinarith
    have : |g (v + s) i j| ≤ |g v i j| + |g (v + s) i j - g v i j| := by
      have := abs_add_le (g v i j) (g (v + s) i j - g v i j)
      simpa using this
    linarith
  have hGd : ∀ i j, |(g (v + s) - g v) i j| ≤ M' * h := fun i j => by
    rw [Matrix.sub_apply]
    exact (hLg i j).trans (mul_le_mul_of_nonneg_left hs hM'0)
  have bil : ∀ p q : Fin n → ℝ, |p ⬝ᵥ (g (v + s) *ᵥ q)| ≤ N ^ 2 * Ge * ‖p‖ * ‖q‖ := fun p q =>
    abs_dot_mulVec_le hGe0 hGm p q
  have bild : ∀ p q : Fin n → ℝ, |p ⬝ᵥ ((g (v + s) - g v) *ᵥ q)| ≤ N ^ 2 * (M' * h) * ‖p‖ * ‖q‖ :=
    fun p q => abs_dot_mulVec_le (by positivity) hGd p q
  have E3 : |a ⬝ᵥ (g (v + s) *ᵥ a) - b ⬝ᵥ (g v *ᵥ b)| ≤ K3 * h ^ 5 := by
    have e : a ⬝ᵥ (g (v + s) *ᵥ a) - b ⬝ᵥ (g v *ᵥ b) =
        (a - b) ⬝ᵥ (g (v + s) *ᵥ a) + b ⬝ᵥ (g (v + s) *ᵥ (a - b))
          + b ⬝ᵥ ((g (v + s) - g v) *ᵥ b) := by
      simp only [sub_dotProduct, Matrix.mulVec_sub, dotProduct_sub, Matrix.sub_mulVec]
      ring
    rw [e]
    have t1 := bil (a - b) a
    have t2 := bil b (a - b)
    have t3 := bild b b
    have hab : |(a - b) ⬝ᵥ (g (v + s) *ᵥ a) + b ⬝ᵥ (g (v + s) *ᵥ (a - b))
        + b ⬝ᵥ ((g (v + s) - g v) *ᵥ b)| ≤ N ^ 2 * Ge * ‖a - b‖ * ‖a‖
          + N ^ 2 * Ge * ‖b‖ * ‖a - b‖ + N ^ 2 * (M' * h) * ‖b‖ * ‖b‖ :=
      (abs_add_three _ _ _).trans (add_le_add (add_le_add t1 t2) t3)
    refine hab.trans ?_
    have f1 : N ^ 2 * Ge * ‖a - b‖ * ‖a‖ ≤
        N ^ 2 * Ge * (N ^ 2 * M' * h ^ 3) * ((B + N ^ 2 * M') * h ^ 2) := by gcongr
    have f2 : N ^ 2 * Ge * ‖b‖ * ‖a - b‖ ≤
        N ^ 2 * Ge * (B * h ^ 2) * (N ^ 2 * M' * h ^ 3) := by gcongr
    have f3 : N ^ 2 * (M' * h) * ‖b‖ * ‖b‖ ≤ N ^ 2 * (M' * h) * (B * h ^ 2) * (B * h ^ 2) := by
      gcongr
    calc _ ≤ N ^ 2 * Ge * (N ^ 2 * M' * h ^ 3) * ((B + N ^ 2 * M') * h ^ 2)
          + N ^ 2 * Ge * (B * h ^ 2) * (N ^ 2 * M' * h ^ 3)
          + N ^ 2 * (M' * h) * (B * h ^ 2) * (B * h ^ 2) := by linarith
      _ = K3 * h ^ 5 := by rw [hK3]; ring
  -- assembly
  unfold midJet
  have key : Δ ⬝ᵥ (g (v + s) *ᵥ Δ) + (1 / 24) * (Δ ⬝ᵥ (ddmat g (v + s) Δ Δ *ᵥ Δ))
      - (1 / 12) * (a ⬝ᵥ (g (v + s) *ᵥ a)) -
      (Δ ⬝ᵥ (g v *ᵥ Δ) + Δ ⬝ᵥ (dmat g v s *ᵥ Δ) + (1 / 2) * (Δ ⬝ᵥ (ddmat g v s s *ᵥ Δ))
        + (1 / 24) * (Δ ⬝ᵥ (ddmat g v Δ Δ *ᵥ Δ)) - (1 / 12) * (b ⬝ᵥ (g v *ᵥ b))) =
      (Δ ⬝ᵥ (g (v + s) *ᵥ Δ) - (Δ ⬝ᵥ (g v *ᵥ Δ) + Δ ⬝ᵥ (dmat g v s *ᵥ Δ)
        + (1 / 2) * (Δ ⬝ᵥ (ddmat g v s s *ᵥ Δ))))
      + (1 / 24) * (Δ ⬝ᵥ (ddmat g (v + s) Δ Δ *ᵥ Δ) - Δ ⬝ᵥ (ddmat g v Δ Δ *ᵥ Δ))
      - (1 / 12) * (a ⬝ᵥ (g (v + s) *ᵥ a) - b ⬝ᵥ (g v *ᵥ b)) := by ring
  rw [key]
  have h5 : 0 ≤ h ^ 5 := by positivity
  calc _ ≤ |Δ ⬝ᵥ (g (v + s) *ᵥ Δ) - (Δ ⬝ᵥ (g v *ᵥ Δ) + Δ ⬝ᵥ (dmat g v s *ᵥ Δ)
        + (1 / 2) * (Δ ⬝ᵥ (ddmat g v s s *ᵥ Δ)))|
      + |(1 / 24) * (Δ ⬝ᵥ (ddmat g (v + s) Δ Δ *ᵥ Δ) - Δ ⬝ᵥ (ddmat g v Δ Δ *ᵥ Δ))|
      + |(1 / 12) * (a ⬝ᵥ (g (v + s) *ᵥ a) - b ⬝ᵥ (g v *ᵥ b))| := by
        refine (abs_sub _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ B * h ^ 5 + (1 / 24) * (N ^ 4 * M' * h ^ 5) + (1 / 12) * (K3 * h ^ 5) := by
        rw [abs_mul, abs_mul]
        rw [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 24), abs_of_pos (by norm_num : (0 : ℝ) < 1 / 12)]
        have := mul_le_mul_of_nonneg_left E2 (by norm_num : (0 : ℝ) ≤ 1 / 24)
        have := mul_le_mul_of_nonneg_left E3 (by norm_num : (0 : ℝ) ≤ 1 / 12)
        linarith
    _ = _ := by ring

end Lightlike.Geodesic
