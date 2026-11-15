import Lightlike.Regge.CMS.Reexpand

/-!
# The squared geodesic edge length in normal coordinates (RC6b, step 5c)

Assembles the midpoint expansion (`dist_sq_expansion_midpoint`), its re-expansion about the vertex
(`exists_midJet_reexpand`) and the algebraic identities `deg3`, `deg4` of `NormalCoord.lean`.

## Main results

* `IsRiemMetric.edge_sq_normal` (dimension 2): for `v` in a compact `K ⊆ U` and `w, w'` of norm at
  most `h ≤ r`,
  `|d(v + w, v + w')² - (|u(w') - u(w)|²_{g_v} - (R_v/6)(|w|²|w'|² - ⟨w, w'⟩²))| ≤ C h⁵`,
  with the normal-coordinate displacement `u(w) = w + ½ Γ_v(w, w) + cub_v(w)`.
-/

open Set Lightlike Lightlike.CMS
open scoped ContDiff Matrix

namespace Lightlike.Geodesic

variable {n : ℕ} {g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ} {U : Set (Fin n → ℝ)}

/-- The first jet of the metric at `v`: `A k i j = ∂_k g_{ij}(v)`. -/
noncomputable def jetA (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℝ) :
    Fin n → Fin n → Fin n → ℝ := fun k i j => pd k (fun y => g y i j) v

/-- The second jet of the metric at `v`: `B l k i j = ∂_l ∂_k g_{ij}(v)`. -/
noncomputable def jetB (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℝ) :
    Fin n → Fin n → Fin n → Fin n → ℝ := fun l k i j => pd l (pd k (fun y => g y i j)) v

/-- `Γ^i_{jk}` from the first jet agrees with `christoffel`. -/
theorem gam_eq_christoffel (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℝ)
    (i j k : Fin n) : gam (g v) (jetA g v) i j k = christoffel g i j k v := by
  rw [christoffel_eq_sum]
  unfold gam
  refine Finset.sum_congr rfl fun m _ => ?_
  simp only [gamLow, christoffelFirst, jetA]
  ring

/-- `p ⬝ (M q) = ip M p q`. -/
theorem dot_mulVec_eq_ip (M : Matrix (Fin n) (Fin n) ℝ) (p q : Fin n → ℝ) :
    p ⬝ᵥ (M *ᵥ q) = ip M p q := by
  simp only [ip, dotProduct, Matrix.mulVec, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/-- The first-derivative term as a triple sum (two dimensions). -/
theorem dot_dmat_eq {g : (Fin 2 → ℝ) → Matrix (Fin 2) (Fin 2) ℝ} (v s Δ : Fin 2 → ℝ) :
    Δ ⬝ᵥ (dmat g v s *ᵥ Δ) = ∑ k, ∑ i, ∑ j, s k * jetA g v k i j * Δ i * Δ j := by
  simp only [dotProduct, Matrix.mulVec, dmat, Matrix.of_apply, jetA, Fin.sum_univ_two]
  ring

/-- The second-derivative term as `quad4` (two dimensions). -/
theorem dot_ddmat_eq {g : (Fin 2 → ℝ) → Matrix (Fin 2) (Fin 2) ℝ} (v s Δ : Fin 2 → ℝ) :
    Δ ⬝ᵥ (ddmat g v s s *ᵥ Δ) = quad4 (jetB g v) s Δ := by
  simp only [dotProduct, Matrix.mulVec, ddmat, quad4, Matrix.of_apply, jetB, Fin.sum_univ_two]
  ring

/-- The Christoffel contraction at `v` is `chrV`. -/
theorem chr_eq_chrV {g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ} (v Δ : Fin n → ℝ) :
    chr g v Δ Δ = chrV (g v) (jetA g v) Δ Δ := by
  funext i
  simp only [chr, chrV, gam_eq_christoffel]

/-- Expanding the displaced inner product `|Δ + ½ δ + c|²` (two dimensions, symmetric `g`). -/
theorem ip_du (g : Matrix (Fin 2) (Fin 2) ℝ) (hs : ∀ i j, g i j = g j i) (Δ δ c : Fin 2 → ℝ) :
    ip g (fun i => Δ i + (1 / 2) * δ i + c i) (fun i => Δ i + (1 / 2) * δ i + c i) =
      ip g Δ Δ + ip g Δ δ + (1 / 4) * ip g δ δ + 2 * ip g Δ c + ip g δ c + ip g c c := by
  simp only [ip, Fin.sum_univ_two]
  rw [hs 1 0]
  ring

/-- `|Σ_i Σ_j x_i g_ij y_j| ≤ n² G ‖x‖ ‖y‖` for entries bounded by `G`. -/
theorem abs_ip_le {g : Matrix (Fin n) (Fin n) ℝ} {G : ℝ} (hG : 0 ≤ G) (hg : ∀ i j, |g i j| ≤ G)
    (x y : Fin n → ℝ) : |ip g x y| ≤ n ^ 2 * G * ‖x‖ * ‖y‖ := by
  rw [← dot_mulVec_eq_ip]
  exact abs_dot_mulVec_le hG hg x y

/-- Entries of `Γ(u, v)` are bounded by `n² M ‖u‖ ‖v‖`. -/
theorem abs_chrV_le {g : Matrix (Fin n) (Fin n) ℝ} {A : Fin n → Fin n → Fin n → ℝ} {M : ℝ}
    (hM : ∀ i j k, |gam g A i j k| ≤ M) (u v : Fin n → ℝ) (i : Fin n) :
    |chrV g A u v i| ≤ n ^ 2 * ‖u‖ * ‖v‖ * M := by
  have := abs_sum2_le (a := u) (b := v) (c := fun j k => gam g A i j k) (norm_nonneg u)
    (norm_nonneg v) (abs_le_norm_apply u) (abs_le_norm_apply v) (fun j k => hM i j k)
  refine le_trans (le_of_eq ?_) this
  unfold chrV
  congr 1
  exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by ring

/-- Entries of the cubic correction are bounded by `(n³ M + n⁴ M²) ‖w‖³ / 6`. -/
theorem abs_cub_le {g : Matrix (Fin n) (Fin n) ℝ} {A : Fin n → Fin n → Fin n → ℝ}
    {B : Fin n → Fin n → Fin n → Fin n → ℝ} {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ i j k, |gam g A i j k| ≤ M) (hdM : ∀ l i j k, |dGam g A B l i j k| ≤ M)
    (w : Fin n → ℝ) (i : Fin n) :
    |cub g A B w i| ≤ (n ^ 3 * M + n ^ 4 * M ^ 2) * ‖w‖ ^ 3 / 6 := by
  have hw := abs_le_norm_apply w
  have hw0 := norm_nonneg w
  have t1 : |∑ j, ∑ k, ∑ l, dGam g A B l i j k * w j * w k * w l| ≤ n ^ 3 * M * ‖w‖ ^ 3 := by
    calc _ ≤ ∑ j, |∑ k, ∑ l, dGam g A B l i j k * w j * w k * w l| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j, ∑ k, |∑ l, dGam g A B l i j k * w j * w k * w l| :=
          Finset.sum_le_sum fun j _ => Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j, ∑ k, ∑ l, |dGam g A B l i j k * w j * w k * w l| :=
          Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun k _ => Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _j : Fin n, ∑ _k : Fin n, ∑ _l : Fin n, M * ‖w‖ * ‖w‖ * ‖w‖ :=
          Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun k _ => Finset.sum_le_sum fun l _ => by
            rw [abs_mul, abs_mul, abs_mul]
            gcongr
            · exact hdM l i j k
            · exact hw j
            · exact hw k
            · exact hw l
      _ = n ^ 3 * M * ‖w‖ ^ 3 := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
  have hchr : ∀ m, |chrV g A w w m| ≤ n ^ 2 * ‖w‖ * ‖w‖ * M := abs_chrV_le hM w w
  have t2 : |∑ j, ∑ m, gam g A i j m * w j * chrV g A w w m| ≤ n ^ 4 * M ^ 2 * ‖w‖ ^ 3 := by
    calc _ ≤ ∑ j, |∑ m, gam g A i j m * w j * chrV g A w w m| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j, ∑ m, |gam g A i j m * w j * chrV g A w w m| :=
          Finset.sum_le_sum fun j _ => Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _j : Fin n, ∑ _m : Fin n, M * ‖w‖ * (n ^ 2 * ‖w‖ * ‖w‖ * M) :=
          Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun m _ => by
            rw [abs_mul, abs_mul]
            gcongr
            · exact hM i j m
            · exact hw j
            · exact hchr m
      _ = n ^ 4 * M ^ 2 * ‖w‖ ^ 3 := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
  unfold cub
  rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 6)]
  have := (abs_add_le _ _).trans (add_le_add t1 t2)
  nlinarith [this]

/-- The normal-coordinate displacement `u(w) = w + ½ Γ_v(w, w) + cub_v(w)` at the vertex `v`. -/
noncomputable def normalDisp (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (v w : Fin n → ℝ) :
    Fin n → ℝ := fun i =>
  w i + (1 / 2) * chrV (g v) (jetA g v) w w i + cub (g v) (jetA g v) (jetB g v) w i

/-- Symmetries of the jets of a coordinate metric, as needed by `deg3` and `deg4`. -/
theorem jet_symm (hg : IsCoordMetric g U) {x : Fin n → ℝ} (hx : x ∈ U) :
    (∀ i j, g x i j = g x j i) ∧ (∀ k i j, jetA g x k i j = jetA g x k j i) ∧
    (∀ k l i j, jetB g x k l i j = jetB g x k l j i) ∧
    (∀ k l i j, jetB g x k l i j = jetB g x l k i j) := by
  refine ⟨fun i j => ?_, fun k i j => hg.pd_symm hx k i j, fun l k i j => ?_, fun l k i j => ?_⟩
  · rw [← Matrix.transpose_apply (g x) j i, hg.symm x hx]
  · exact pd_congr (hg.eventuallyEq_pd_symm hx k i j) l
  · exact pd_pd_comm (hg.smooth i j) hg.isOpen hx l k

set_option maxHeartbeats 4000000 in
/-- **The squared geodesic distance between two points near `v`, in normal-coordinate form**
(dimension 2). For a Riemannian coordinate metric on `U` and a compact `K ⊆ U` there are `C` and
`r > 0` such that for `v ∈ K` and `‖w‖, ‖w'‖ ≤ h ≤ r`
`|d(v + w, v + w')² - (|u(w') - u(w)|²_{g_v} - (R_v/6)(|w|²|w'|² - ⟨w, w'⟩²))| ≤ C h⁵`,
with `u = normalDisp` and `R_v` the scalar curvature of the metric jet at `v`. -/
theorem IsRiemMetric.edge_sq_normal {g : (Fin 2 → ℝ) → Matrix (Fin 2) (Fin 2) ℝ}
    {U : Set (Fin 2 → ℝ)} (hg : IsRiemMetric g U) {K : Set (Fin 2 → ℝ)} (hK : IsCompact K)
    (hKU : K ⊆ U) :
    ∃ C r : ℝ, 0 < r ∧ ∀ v ∈ K, ∀ w w' : Fin 2 → ℝ, ∀ h : ℝ, ‖w‖ ≤ h → ‖w'‖ ≤ h → h ≤ r →
      |dist g U (v + w) (v + w') ^ 2 -
        (ip (g v) (fun i => normalDisp g v w' i - normalDisp g v w i)
            (fun i => normalDisp g v w' i - normalDisp g v w i)
          - (jetScalar (g v) (jetA g v) (jetB g v) / 6) *
            (ip (g v) w w * ip (g v) w' w' - ip (g v) w w' ^ 2))| ≤ C * h ^ 5 := by
  obtain ⟨ρ, hρ, hρU⟩ := hK.exists_cthickening_subset_open hg.coord.isOpen hKU
  have hK' : IsCompact (Metric.cthickening ρ K) := hK.cthickening
  obtain ⟨C1, r1, hr1, h1⟩ := hg.dist_sq_expansion_midpoint hK' hρU
  obtain ⟨C2, r2, hr2, h2⟩ := hg.exists_midJet_reexpand hK hKU
  obtain ⟨M, hM0, hM⟩ := hg.coord.exists_jet_bound hK hKU
  set N : ℝ := ((2 : ℕ) : ℝ) with hNdef
  have hN0 : 0 ≤ N := Nat.cast_nonneg _
  set Kc : ℝ := (N ^ 3 * M + N ^ 4 * M ^ 2) / 6 with hKc
  have hKc0 : 0 ≤ Kc := by positivity
  set KE : ℝ := N ^ 2 * M * (2 * N ^ 2 * M) * (2 * Kc) + N ^ 2 * M * (2 * Kc) ^ 2 with hKE
  have hKE0 : 0 ≤ KE := by positivity
  refine ⟨|C1| * 32 + |C2| * 32 + KE, min (min (r1 / 2) (r2 / 2)) (min ρ 1),
    lt_min (lt_min (by linarith) (by linarith)) (lt_min hρ one_pos), ?_⟩
  intro v hv w w' h hw hw' hh
  have hvU : v ∈ U := hKU hv
  have hh0 : 0 ≤ h := (norm_nonneg w).trans hw
  have hhr1 : h ≤ r1 / 2 := hh.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hhr2 : h ≤ r2 / 2 := hh.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hhρ : h ≤ ρ := hh.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hh1 : h ≤ 1 := hh.trans ((min_le_right _ _).trans (min_le_right _ _))
  set s : Fin 2 → ℝ := fun i => (w i + w' i) / 2 with hs
  set Δ : Fin 2 → ℝ := w' - w with hΔ
  have hΔn : ‖Δ‖ ≤ 2 * h := (norm_sub_le w' w).trans (by linarith)
  have hsn : ‖s‖ ≤ h := by
    refine (pi_norm_le_iff_of_nonneg hh0).2 fun i => ?_
    rw [Real.norm_eq_abs, hs]
    have a1 := abs_le_norm_apply w i
    have a2 := abs_le_norm_apply w' i
    simp only [abs_le] at a1 a2 ⊢
    constructor <;> linarith [a1.1, a1.2, a2.1, a2.2, (norm_nonneg w), (norm_nonneg w')]
  have hvm : v + s ∈ Metric.cthickening ρ K :=
    Metric.closedBall_subset_cthickening hv ρ (by
      rw [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left]; exact hsn.trans hhρ)
  -- the midpoint expansion
  have e1 : v + s - (1 / 2 : ℝ) • Δ = v + w := by
    ext i; simp [hs, hΔ]; ring
  have e2 : v + s + (1 / 2 : ℝ) • Δ = v + w' := by
    ext i; simp [hs, hΔ]; ring
  have A1 := h1 (v + s) hvm Δ (by linarith)
  rw [e1, e2] at A1
  have A1' : |dist g U (v + w) (v + w') ^ 2 - midJet g (v + s) Δ| ≤ |C1| * 32 * h ^ 5 := by
    refine A1.trans ?_
    calc C1 * ‖Δ‖ ^ 5 ≤ |C1| * ‖Δ‖ ^ 5 :=
          mul_le_mul_of_nonneg_right (le_abs_self C1) (by positivity)
      _ ≤ |C1| * (2 * h) ^ 5 := by gcongr
      _ = |C1| * 32 * h ^ 5 := by ring
  -- the re-expansion about the vertex
  have B1 := h2 v hv s Δ (2 * h) (by linarith) hΔn (by linarith)
  have B1' : |midJet g (v + s) Δ -
      (Δ ⬝ᵥ (g v *ᵥ Δ) + Δ ⬝ᵥ (dmat g v s *ᵥ Δ) + (1 / 2) * (Δ ⬝ᵥ (ddmat g v s s *ᵥ Δ))
        + (1 / 24) * (Δ ⬝ᵥ (ddmat g v Δ Δ *ᵥ Δ))
        - (1 / 12) * (chr g v Δ Δ ⬝ᵥ (g v *ᵥ chr g v Δ Δ)))| ≤ |C2| * 32 * h ^ 5 := by
    refine B1.trans ?_
    calc C2 * (2 * h) ^ 5 ≤ |C2| * (2 * h) ^ 5 :=
          mul_le_mul_of_nonneg_right (le_abs_self C2) (by positivity)
      _ = |C2| * 32 * h ^ 5 := by ring
  -- the jets
  obtain ⟨hsym, hA, hB1, hB2⟩ := jet_symm hg.coord hvU
  have hdet : (g v).det ≠ 0 := (hg.coord.isUnit_det v hvU).ne_zero
  have d3 := deg3 (g v) (jetA g v) hdet hsym hA w w'
  have d4 := deg4 (g v) (jetA g v) (jetB g v) hdet hsym hA hB1 hB2 w w'
  rw [dot_mulVec_eq_ip (g v) Δ Δ, dot_dmat_eq, dot_ddmat_eq, dot_ddmat_eq, chr_eq_chrV,
    dot_mulVec_eq_ip] at B1'
  -- bounds on the corrections
  have hgam : ∀ i j k, |gam (g v) (jetA g v) i j k| ≤ M := fun i j k => by
    rw [gam_eq_christoffel]; exact (hM v hv i j k i i).2.2.2.2.2.1
  have hdgam : ∀ l i j k, |dGam (g v) (jetA g v) (jetB g v) l i j k| ≤ M := fun l i j k => by
    have e : dGam (g v) (jetA g v) (jetB g v) l i j k = pd l (christoffel g i j k) v :=
      (pd_christoffel hg.coord hvU l i j k).symm
    rw [e]; exact (hM v hv i j k l l).2.2.2.2.2.2
  have hG : ∀ i j, |g v i j| ≤ M := fun i j => (hM v hv i j i i i).1
  set δf : Fin 2 → ℝ := fun i => chrV (g v) (jetA g v) w' w' i - chrV (g v) (jetA g v) w w i with hδf
  set cf : Fin 2 → ℝ := fun i => cub (g v) (jetA g v) (jetB g v) w' i
    - cub (g v) (jetA g v) (jetB g v) w i with hcf
  have hδn : ‖δf‖ ≤ 2 * N ^ 2 * M * h ^ 2 := by
    refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
    rw [Real.norm_eq_abs]
    have t1 := abs_chrV_le hgam w' w' i
    have t2 := abs_chrV_le hgam w w i
    have u1 : N ^ 2 * ‖w'‖ * ‖w'‖ * M ≤ N ^ 2 * h * h * M := by gcongr
    have u2 : N ^ 2 * ‖w‖ * ‖w‖ * M ≤ N ^ 2 * h * h * M := by gcongr
    refine (abs_sub _ _).trans ?_
    nlinarith
  have hcn : ‖cf‖ ≤ 2 * Kc * h ^ 3 := by
    refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
    rw [Real.norm_eq_abs]
    have t1 := abs_cub_le hM0 hgam hdgam w' i
    have t2 := abs_cub_le hM0 hgam hdgam w i
    have u1 : (N ^ 3 * M + N ^ 4 * M ^ 2) * ‖w'‖ ^ 3 / 6 ≤ Kc * h ^ 3 := by
      have := pow_le_pow_left₀ (norm_nonneg w') hw' 3
      calc (N ^ 3 * M + N ^ 4 * M ^ 2) * ‖w'‖ ^ 3 / 6 = Kc * ‖w'‖ ^ 3 := by rw [hKc]; ring
        _ ≤ Kc * h ^ 3 := mul_le_mul_of_nonneg_left this hKc0
    have u2 : (N ^ 3 * M + N ^ 4 * M ^ 2) * ‖w‖ ^ 3 / 6 ≤ Kc * h ^ 3 := by
      have := pow_le_pow_left₀ (norm_nonneg w) hw 3
      calc (N ^ 3 * M + N ^ 4 * M ^ 2) * ‖w‖ ^ 3 / 6 = Kc * ‖w‖ ^ 3 := by rw [hKc]; ring
        _ ≤ Kc * h ^ 3 := mul_le_mul_of_nonneg_left this hKc0
    refine (abs_sub _ _).trans ?_
    nlinarith
  have hrest : |ip (g v) δf cf + ip (g v) cf cf| ≤ KE * h ^ 5 := by
    have t1 := abs_ip_le hM0 hG δf cf
    have t2 := abs_ip_le hM0 hG cf cf
    have f1 : N ^ 2 * M * ‖δf‖ * ‖cf‖ ≤ N ^ 2 * M * (2 * N ^ 2 * M * h ^ 2) * (2 * Kc * h ^ 3) := by
      gcongr
    have f2 : N ^ 2 * M * ‖cf‖ * ‖cf‖ ≤ N ^ 2 * M * (2 * Kc * h ^ 3) * (2 * Kc * h ^ 3) := by
      gcongr
    have h6 : h ^ 6 ≤ h ^ 5 := pow_le_pow_of_le_one hh0 hh1 (by norm_num)
    have : N ^ 2 * M * (2 * Kc * h ^ 3) * (2 * Kc * h ^ 3) ≤ N ^ 2 * M * (2 * Kc) ^ 2 * h ^ 5 := by
      have : N ^ 2 * M * (2 * Kc * h ^ 3) * (2 * Kc * h ^ 3) = N ^ 2 * M * (2 * Kc) ^ 2 * h ^ 6 := by
        ring
      rw [this]; gcongr
    have g1 : N ^ 2 * M * (2 * N ^ 2 * M * h ^ 2) * (2 * Kc * h ^ 3)
        = N ^ 2 * M * (2 * N ^ 2 * M) * (2 * Kc) * h ^ 5 := by ring
    refine (abs_add_le _ _).trans ?_
    have : KE * h ^ 5 = N ^ 2 * M * (2 * N ^ 2 * M) * (2 * Kc) * h ^ 5
        + N ^ 2 * M * (2 * Kc) ^ 2 * h ^ 5 := by rw [hKE]; ring
    linarith [t1, t2, f1, f2, ‹N ^ 2 * M * (2 * Kc * h ^ 3) * (2 * Kc * h ^ 3) ≤ _›]
  -- the displaced inner product
  have hdu : (fun i => normalDisp g v w' i - normalDisp g v w i) =
      fun i => Δ i + (1 / 2) * δf i + cf i := by
    funext i; simp only [normalDisp, hΔ, hδf, hcf, Pi.sub_apply]; ring
  rw [hdu, ip_du (g v) hsym Δ δf cf]
  -- assembly
  have d3' : (∑ k, ∑ i, ∑ j, s k * jetA g v k i j * Δ i * Δ j) = ip (g v) Δ δf := d3
  have d4' : (1 / 2) * quad4 (jetB g v) s Δ + (1 / 24) * quad4 (jetB g v) Δ Δ
      - (1 / 12) * ip (g v) (chrV (g v) (jetA g v) Δ Δ) (chrV (g v) (jetA g v) Δ Δ) =
      (1 / 4) * ip (g v) δf δf + 2 * ip (g v) Δ cf
        - (jetScalar (g v) (jetA g v) (jetB g v) / 6) *
          (ip (g v) w w * ip (g v) w' w' - ip (g v) w w' ^ 2) := d4
  set R6 := (jetScalar (g v) (jetA g v) (jetB g v) / 6) *
    (ip (g v) w w * ip (g v) w' w' - ip (g v) w w' ^ 2) with hR6
  have key : |dist g U (v + w) (v + w') ^ 2 - (ip (g v) Δ Δ + ip (g v) Δ δf + 1 / 4 * ip (g v) δf δf
      + 2 * ip (g v) Δ cf + ip (g v) δf cf + ip (g v) cf cf - R6)| ≤
      |dist g U (v + w) (v + w') ^ 2 - midJet g (v + s) Δ|
      + |midJet g (v + s) Δ - (ip (g v) Δ Δ + ∑ k, ∑ i, ∑ j, s k * jetA g v k i j * Δ i * Δ j
        + (1 / 2) * quad4 (jetB g v) s Δ + (1 / 24) * quad4 (jetB g v) Δ Δ
        - (1 / 12) * ip (g v) (chrV (g v) (jetA g v) Δ Δ) (chrV (g v) (jetA g v) Δ Δ))|
      + |ip (g v) δf cf + ip (g v) cf cf| := by
    have e : dist g U (v + w) (v + w') ^ 2 - (ip (g v) Δ Δ + ip (g v) Δ δf + 1 / 4 * ip (g v) δf δf
      + 2 * ip (g v) Δ cf + ip (g v) δf cf + ip (g v) cf cf - R6) =
      (dist g U (v + w) (v + w') ^ 2 - midJet g (v + s) Δ)
      + (midJet g (v + s) Δ - (ip (g v) Δ Δ + ∑ k, ∑ i, ∑ j, s k * jetA g v k i j * Δ i * Δ j
        + (1 / 2) * quad4 (jetB g v) s Δ + (1 / 24) * quad4 (jetB g v) Δ Δ
        - (1 / 12) * ip (g v) (chrV (g v) (jetA g v) Δ Δ) (chrV (g v) (jetA g v) Δ Δ)))
      - (ip (g v) δf cf + ip (g v) cf cf) := by
      rw [d3']
      linarith [d4']
    rw [e]
    exact (abs_sub _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
  refine key.trans ?_
  have : (|C1| * 32 + |C2| * 32 + KE) * h ^ 5 = |C1| * 32 * h ^ 5 + |C2| * 32 * h ^ 5 + KE * h ^ 5 := by
    ring
  rw [this]
  linarith [A1', B1', hrest]


/-- **The scalar curvature of the jet is the scalar curvature of the metric.** At a point of the
domain, `jetScalar` of the first and second derivatives of `g` is `Lightlike.scalarCurvature`. -/
theorem jetScalar_eq_scalarCurvature (hg : IsCoordMetric g U) {v : Fin n → ℝ} (hv : v ∈ U) :
    jetScalar (g v) (jetA g v) (jetB g v) = scalarCurvature g v := by
  unfold jetScalar scalarCurvature ricci riemann
  refine Finset.sum_congr rfl fun σ _ => Finset.sum_congr rfl fun ν _ => ?_
  congr 1
  refine Finset.sum_congr rfl fun ρ _ => ?_
  unfold jetRiem
  rw [pd_christoffel hg hv, pd_christoffel hg hv]
  simp only [gam_eq_christoffel]
  rfl

end Lightlike.Geodesic
