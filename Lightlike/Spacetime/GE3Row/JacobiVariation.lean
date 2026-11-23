import Lightlike.Spacetime.GE3Row.Jacobi
import Lightlike.Spacetime.RicciContinuous

/-!
# Jacobi fields from variations through geodesics (row G1-006, GE3)

The geodesic deviation equation for a smooth variation through geodesics: if `H (t, s)` is a `C³`
family in a chart with every `t ↦ H (t, s)` a geodesic, then `J = ∂_s H (·, 0)` is a Jacobi field
(`IsJacobiOn`, `D_t D_t J = -R(J, w) w`) along `H (·, 0)`.

## Main statements

* `Lightlike.Geodesic.exists_isJacobiOn_of_variation`: the variation lemma.
* `Lightlike.Geodesic.riemannApply_eq`: `R(J, w) w` in terms of `Γ` and `∂Γ`.
* `Lightlike.Geodesic.jacobi_algebra`: the index algebra, using the symmetry of `Γ`
  (`christoffel_symm_of_mem`).

Supporting lemmas; the catalogue entry (Jacobi equation) is for the merger.
-/

open Set Filter Topology Matrix
open scoped ContDiff

namespace Lightlike.Geodesic

variable {n : ℕ} {g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ} {U : Set (Fin n → ℝ)}

/-- The directional derivative of the connection term: `(∂_y Γ)(x)(v, u)^i = Σ ∂_y Γ^i_{jk} v^j u^k`. -/
noncomputable def gammaDeriv (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (x y v u : Fin n → ℝ) :
    Fin n → ℝ :=
  fun i => ∑ j, ∑ k, fderiv ℝ (Lightlike.christoffel g i j k) x y * v j * u k

/-- A directional derivative is the sum of the coordinate partial derivatives. -/
theorem fderiv_eq_sum_pd (f : (Fin n → ℝ) → ℝ) (x v : Fin n → ℝ) :
    fderiv ℝ f x v = ∑ m, v m * Lightlike.pd m f x := by
  have hv : v = ∑ m, v m • (Pi.single m (1 : ℝ) : Fin n → ℝ) := by
    ext i; simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [hv]
  simp [map_sum, Lightlike.pd]

section sums

variable {ι : Type*} [Fintype ι] (f : ι → ι → ι → ℝ)

theorem sum3_cyc : ∑ a, ∑ b, ∑ c, f a b c = ∑ b, ∑ c, ∑ a, f a b c := by
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_comm

theorem sum3_rev : ∑ a, ∑ b, ∑ c, f a b c = ∑ c, ∑ b, ∑ a, f a b c := by
  calc ∑ a, ∑ b, ∑ c, f a b c = ∑ b, ∑ a, ∑ c, f a b c := Finset.sum_comm
    _ = ∑ b, ∑ c, ∑ a, f a b c := Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ c, ∑ b, ∑ a, f a b c := Finset.sum_comm

variable (h : ι → ι → ι → ι → ℝ)

theorem sum4_bdca : ∑ a, ∑ b, ∑ c, ∑ d, h a b c d = ∑ b, ∑ d, ∑ c, ∑ a, h a b c d := by
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun b _ => sum3_rev (fun a c d => h a b c d)

theorem sum4_cdba : ∑ a, ∑ b, ∑ c, ∑ d, h a b c d = ∑ c, ∑ d, ∑ b, ∑ a, h a b c d := by
  calc ∑ a, ∑ b, ∑ c, ∑ d, h a b c d = ∑ a, ∑ c, ∑ b, ∑ d, h a b c d :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ c, ∑ a, ∑ b, ∑ d, h a b c d := Finset.sum_comm
    _ = ∑ c, ∑ d, ∑ b, ∑ a, h a b c d :=
        Finset.sum_congr rfl fun c _ => sum3_rev (fun a b d => h a b c d)

end sums

/-- `R(J, w) w = (∂_J Γ)(w, w) - (∂_w Γ)(J, w) + Γ(J, Γ(w, w)) - Γ(w, Γ(J, w))`. -/
theorem riemannApply_eq (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (x w J : Fin n → ℝ) :
    riemannApply g x w J = gammaDeriv g x J w w - gammaDeriv g x w J w
      + gammaApply g x J (gammaApply g x w w) - gammaApply g x w (gammaApply g x J w) := by
  funext i
  simp only [riemannApply, gammaDeriv, gammaApply, Lightlike.riemann, Pi.add_apply, Pi.sub_apply,
    fderiv_eq_sum_pd, add_mul, sub_mul, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    Finset.sum_mul, Finset.mul_sum]
  have e1 : ∑ s, ∑ m, ∑ v, Lightlike.pd m (Lightlike.christoffel g i v s) x * w s * J m * w v =
      ∑ j, ∑ k, ∑ m, J m * Lightlike.pd m (Lightlike.christoffel g i j k) x * w j * w k := by
    rw [sum3_cyc (fun j k m => J m * Lightlike.pd m (Lightlike.christoffel g i j k) x * w j * w k)]
    refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
      Finset.sum_congr rfl fun _ _ => by ring
  have e2 : ∑ s, ∑ m, ∑ v, Lightlike.pd v (Lightlike.christoffel g i m s) x * w s * J m * w v =
      ∑ j, ∑ k, ∑ m, w m * Lightlike.pd m (Lightlike.christoffel g i j k) x * J j * w k := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
      Finset.sum_congr rfl fun _ _ => by ring
  have e3 : ∑ s, ∑ m, ∑ v, ∑ l, Lightlike.christoffel g i m l x * Lightlike.christoffel g l v s x *
        w s * J m * w v =
      ∑ x_1, ∑ k, ∑ x_2, ∑ i_1, Lightlike.christoffel g i x_1 k x * J x_1 *
        (Lightlike.christoffel g k x_2 i_1 x * w x_2 * w i_1) := by
    rw [sum4_bdca (fun s m v l => Lightlike.christoffel g i m l x *
      Lightlike.christoffel g l v s x * w s * J m * w v)]
    refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
      Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  have e4 : ∑ s, ∑ m, ∑ v, ∑ l, Lightlike.christoffel g i v l x * Lightlike.christoffel g l m s x *
        w s * J m * w v =
      ∑ x_1, ∑ k, ∑ x_2, ∑ i_1, Lightlike.christoffel g i x_1 k x * w x_1 *
        (Lightlike.christoffel g k x_2 i_1 x * J x_2 * w i_1) := by
    rw [sum4_cdba (fun s m v l => Lightlike.christoffel g i v l x *
      Lightlike.christoffel g l m s x * w s * J m * w v)]
    refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
      Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  rw [e1, e2, e3, e4]
  ring

/-- The Christoffel symbols of a coordinate metric are symmetric in the lower indices on `U`. -/
theorem christoffel_symm_of_mem (hg : Lightlike.IsCoordMetric g U) {y : Fin n → ℝ} (hy : y ∈ U)
    (i j k : Fin n) :
    Lightlike.christoffel g i j k y = Lightlike.christoffel g i k j y := by
  have hs : ∀ a b, (fun z => g z a b) =ᶠ[𝓝 y] (fun z => g z b a) := fun a b =>
    Filter.eventuallyEq_of_mem (hg.isOpen.mem_nhds hy) fun z hz => by
      have := congrFun (congrFun (hg.symm z hz) b) a
      simpa using this
  unfold Lightlike.christoffel
  refine congrArg _ (Finset.sum_congr rfl fun l _ => ?_)
  have h3 : Lightlike.pd l (fun z => g z j k) y = Lightlike.pd l (fun z => g z k j) y := by
    unfold Lightlike.pd
    rw [(hs j k).fderiv_eq]
  rw [h3]
  ring

/-- Symmetric lower indices: `Γ(v, u) = Γ(u, v)`. -/
theorem gammaApply_comm (hg : Lightlike.IsCoordMetric g U) {x : Fin n → ℝ} (hx : x ∈ U)
    (v u : Fin n → ℝ) : gammaApply g x v u = gammaApply g x u v := by
  funext i
  simp only [gammaApply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
  rw [christoffel_symm_of_mem hg hx i k j]
  ring

/-- Symmetric lower indices: `(∂_y Γ)(v, u) = (∂_y Γ)(u, v)`. -/
theorem gammaDeriv_comm (hg : Lightlike.IsCoordMetric g U) {x : Fin n → ℝ} (hx : x ∈ U)
    (y v u : Fin n → ℝ) : gammaDeriv g x y v u = gammaDeriv g x y u v := by
  funext i
  simp only [gammaDeriv]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
  have : Lightlike.christoffel g i k j =ᶠ[𝓝 x] Lightlike.christoffel g i j k :=
    Filter.eventuallyEq_of_mem (hg.isOpen.mem_nhds hx) fun z hz =>
      christoffel_symm_of_mem hg hz i k j
  rw [this.fderiv_eq]
  ring

theorem gammaApply_add_right (x v u u' : Fin n → ℝ) :
    gammaApply g x v (u + u') = gammaApply g x v u + gammaApply g x v u' := by
  funext i
  simp [gammaApply, mul_add, Finset.sum_add_distrib]

theorem gammaApply_neg_left (x v u : Fin n → ℝ) :
    gammaApply g x (-v) u = -gammaApply g x v u := by
  funext i
  simp [gammaApply, Finset.sum_neg_distrib]

theorem accel_eq_neg_gammaApply (x v : Fin n → ℝ) : accel g x v = -gammaApply g x v v := by
  funext i
  simp [accel, gammaApply, mul_assoc]

/-- Product rule for the connection term along curves. -/
theorem hasDerivAt_gammaApply {γ w u : ℝ → Fin n → ℝ} {γ' w' u' : Fin n → ℝ} {t : ℝ}
    (hc : ∀ i j k, DifferentiableAt ℝ (Lightlike.christoffel g i j k) (γ t))
    (hγ : HasDerivAt γ γ' t) (hw : HasDerivAt w w' t) (hu : HasDerivAt u u' t) :
    HasDerivAt (fun r => gammaApply g (γ r) (w r) (u r))
      (gammaDeriv g (γ t) γ' (w t) (u t) + gammaApply g (γ t) w' (u t) +
        gammaApply g (γ t) (w t) u') t := by
  rw [hasDerivAt_pi]
  intro i
  have hj : ∀ j k, HasDerivAt (fun r => Lightlike.christoffel g i j k (γ r) * w r j * u r k)
      (fderiv ℝ (Lightlike.christoffel g i j k) (γ t) γ' * w t j * u t k +
        Lightlike.christoffel g i j k (γ t) * w' j * u t k +
        Lightlike.christoffel g i j k (γ t) * w t j * u' k) t := by
    intro j k
    have h1 : HasDerivAt (fun r => Lightlike.christoffel g i j k (γ r))
        (fderiv ℝ (Lightlike.christoffel g i j k) (γ t) γ') t :=
      (hc i j k).hasFDerivAt.comp_hasDerivAt t hγ
    have h2 : HasDerivAt (fun r => w r j) (w' j) t := (hasDerivAt_pi.mp hw) j
    have h3 : HasDerivAt (fun r => u r k) (u' k) t := (hasDerivAt_pi.mp hu) k
    have := (h1.mul h2).mul h3
    convert this using 1
    simp only [Pi.mul_apply]
    ring
  have := HasDerivAt.fun_sum (u := Finset.univ) fun j _ =>
    HasDerivAt.fun_sum (u := Finset.univ) fun k _ => hj j k
  refine HasDerivAt.congr_deriv this ?_
  simp only [Pi.add_apply, gammaDeriv, gammaApply, ← Finset.sum_add_distrib]

/-- The algebra of the Jacobi equation: with `K = ∂_s ∂_t F`, `K' = -(∂_J Γ)(w,w) - Γ(K,w) - Γ(w,K)`
and `P = K + Γ(w, J)` one gets `P' = -Γ(w, P) - R(J, w) w`. -/
theorem jacobi_algebra (hg : Lightlike.IsCoordMetric g U) {x : Fin n → ℝ} (hx : x ∈ U)
    (w J K : Fin n → ℝ) :
    -(gammaDeriv g x J w w + gammaApply g x K w + gammaApply g x w K) +
        (gammaDeriv g x w w J + gammaApply g x (accel g x w) J + gammaApply g x w K) =
      -gammaApply g x w (K + gammaApply g x w J) - riemannApply g x w J := by
  rw [riemannApply_eq, gammaApply_add_right, accel_eq_neg_gammaApply, gammaApply_neg_left,
    gammaApply_comm hg hx K w, gammaApply_comm hg hx J w,
    gammaApply_comm hg hx (gammaApply g x w w) J, gammaDeriv_comm hg hx w w J]
  funext i
  simp only [Pi.add_apply, Pi.sub_apply, Pi.neg_apply]
  ring

/-- Derivative of a directional derivative along a curve (chain rule). -/
theorem hasDerivAt_fderiv_comp {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : ℝ × ℝ → F} {q : ℝ → ℝ × ℝ} {q' : ℝ × ℝ} {r : ℝ}
    (hf : DifferentiableAt ℝ (fderiv ℝ f) (q r)) (hq : HasDerivAt q q' r) (v : ℝ × ℝ) :
    HasDerivAt (fun r => fderiv ℝ f (q r) v) (fderiv ℝ (fderiv ℝ f) (q r) q' v) r := by
  have h := hf.hasFDerivAt.comp_hasDerivAt r hq
  simpa using h.clm_apply (hasDerivAt_const r v)

/-- Second derivatives of a `C²` function on `ℝ²` are symmetric. -/
theorem isSymm_of_contDiff_two {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : ℝ × ℝ → F} (hf : ContDiff ℝ 2 f) (p : ℝ × ℝ) : IsSymmSndFDerivAt ℝ f p :=
  hf.contDiffAt.isSymmSndFDerivAt (by simp [minSmoothness_of_isRCLikeNormedField])

/-- **Jacobi fields from variations.** Let `H (t, s)` be a `C³` family of curves in a chart, each
`t ↦ H (t, s)` (for `s` near `0`) a geodesic on `I` with velocity `∂_t H`, and the base geodesic
`s = 0` inside `U`. Then `J = ∂_s H (·, 0)` is a Jacobi field along `H (·, 0)`
(`IsJacobiOn`), with `P = D_t J = ∂_t ∂_s H + Γ(w, J)`. -/
theorem exists_isJacobiOn_of_variation (hg : Lightlike.IsCoordMetric g U)
    {H : ℝ × ℝ → Fin n → ℝ} (hH : ContDiff ℝ 3 H) {I : Set ℝ} (hU : ∀ t ∈ I, H (t, 0) ∈ U)
    (hgeo : ∀ᶠ s in 𝓝 (0 : ℝ),
      IsGeodesicOn g (fun t => H (t, s)) (fun t => fderiv ℝ H (t, s) (1, 0)) I) :
    ∃ P, IsJacobiOn g (fun t => H (t, 0)) (fun t => fderiv ℝ H (t, 0) (1, 0))
      (fun t => fderiv ℝ H (t, 0) (0, 1)) P I := by
  have hf2 : ContDiff ℝ 2 (fderiv ℝ H) := hH.fderiv_right (by norm_num)
  have hf1 : ContDiff ℝ 1 (fderiv ℝ (fderiv ℝ H)) := hf2.fderiv_right (by norm_num)
  have hdH : ∀ p, DifferentiableAt ℝ H p := fun p => (hH.differentiable (by norm_num)) p
  have hd1 : ∀ p, DifferentiableAt ℝ (fderiv ℝ H) p := fun p => (hf2.differentiable (by norm_num)) p
  have hd2 : ∀ p, DifferentiableAt ℝ (fderiv ℝ (fderiv ℝ H)) p :=
    fun p => (hf1.differentiable (by norm_num)) p
  have hsH := isSymm_of_contDiff_two (hH.of_le (by norm_num : (2 : WithTop ℕ∞) ≤ 3))
  have hsf := isSymm_of_contDiff_two hf2
  have hq0 : ∀ t : ℝ, HasDerivAt (fun t : ℝ => ((t, 0) : ℝ × ℝ)) ((1, 0) : ℝ × ℝ) t := fun t => by
    simpa using (hasDerivAt_id t).prodMk (hasDerivAt_const t (0 : ℝ))
  have hqs : ∀ t s : ℝ, HasDerivAt (fun s : ℝ => ((t, s) : ℝ × ℝ)) ((0, 1) : ℝ × ℝ) s :=
    fun t s => by
      simpa using (hasDerivAt_const s t).prodMk (hasDerivAt_id s)
  refine ⟨fun t => fderiv ℝ (fderiv ℝ H) (t, 0) (0, 1) (1, 0) +
    gammaApply g (H (t, 0)) (fderiv ℝ H (t, 0) (1, 0)) (fderiv ℝ H (t, 0) (0, 1)), ?_, ?_, ?_⟩
  · exact hgeo.self_of_nhds
  · intro t ht
    have h := hasDerivAt_fderiv_comp (f := H) (hd1 _) (hq0 t) (0, 1)
    refine h.congr_deriv ?_
    simp only [add_sub_cancel_right]
    exact hsH (t, 0) (1, 0) (0, 1)
  · intro t ht
    have hΓ : ∀ i j k, DifferentiableAt ℝ (Lightlike.christoffel g i j k) (H (t, 0)) := fun i j k =>
      ((Lightlike.contDiffOn_christoffel hg i j k).contDiffAt
        (hg.isOpen.mem_nhds (hU t ht))).differentiableAt (by simp)
    have hγ : HasDerivAt (fun t : ℝ => H (t, 0)) (fderiv ℝ H (t, 0) (1, 0)) t :=
      (hdH (t, 0)).hasFDerivAt.comp_hasDerivAt t (hq0 t)
    have hw : HasDerivAt (fun t : ℝ => fderiv ℝ H (t, 0) (1, 0))
        (accel g (H (t, 0)) (fderiv ℝ H (t, 0) (1, 0))) t :=
      (hgeo.self_of_nhds).vel t ht
    have hJ : HasDerivAt (fun t : ℝ => fderiv ℝ H (t, 0) (0, 1))
        (fderiv ℝ (fderiv ℝ H) (t, 0) (0, 1) (1, 0)) t := by
      have h := hasDerivAt_fderiv_comp (f := H) (hd1 _) (hq0 t) (0, 1)
      refine h.congr_deriv ?_
      exact hsH (t, 0) (1, 0) (0, 1)
    have hK : HasDerivAt (fun t : ℝ => fderiv ℝ (fderiv ℝ H) (t, 0) (0, 1) (1, 0))
        (fderiv ℝ (fderiv ℝ (fderiv ℝ H)) (t, 0) (1, 0) (0, 1) (1, 0)) t := by
      have h := hasDerivAt_fderiv_comp (f := fderiv ℝ H) (hd2 _) (hq0 t) (0, 1)
      simpa using h.clm_apply (hasDerivAt_const t ((1, 0) : ℝ × ℝ))
    have hKval : fderiv ℝ (fderiv ℝ (fderiv ℝ H)) (t, 0) (0, 1) (1, 0) (1, 0) =
        -(gammaDeriv g (H (t, 0)) (fderiv ℝ H (t, 0) (0, 1)) (fderiv ℝ H (t, 0) (1, 0))
            (fderiv ℝ H (t, 0) (1, 0)) +
          gammaApply g (H (t, 0)) (fderiv ℝ (fderiv ℝ H) (t, 0) (0, 1) (1, 0))
            (fderiv ℝ H (t, 0) (1, 0)) +
          gammaApply g (H (t, 0)) (fderiv ℝ H (t, 0) (1, 0))
            (fderiv ℝ (fderiv ℝ H) (t, 0) (0, 1) (1, 0))) := by
      have hφ : HasDerivAt (fun s : ℝ => fderiv ℝ (fderiv ℝ H) (t, s) (1, 0) (1, 0))
          (fderiv ℝ (fderiv ℝ (fderiv ℝ H)) (t, 0) (0, 1) (1, 0) (1, 0)) 0 := by
        have h := hasDerivAt_fderiv_comp (f := fderiv ℝ H) (hd2 _) (hqs t 0) (1, 0)
        simpa using h.clm_apply (hasDerivAt_const (0 : ℝ) ((1, 0) : ℝ × ℝ))
      have hws : HasDerivAt (fun s : ℝ => fderiv ℝ H (t, s) (1, 0))
          (fderiv ℝ (fderiv ℝ H) (t, 0) (0, 1) (1, 0)) 0 :=
        hasDerivAt_fderiv_comp (f := H) (hd1 _) (hqs t 0) (1, 0)
      have hγs : HasDerivAt (fun s : ℝ => H (t, s)) (fderiv ℝ H (t, 0) (0, 1)) 0 :=
        (hdH (t, 0)).hasFDerivAt.comp_hasDerivAt 0 (hqs t 0)
      have hψ := (hasDerivAt_gammaApply hΓ hγs hws hws).neg
      have hev : (fun s : ℝ => fderiv ℝ (fderiv ℝ H) (t, s) (1, 0) (1, 0))
          =ᶠ[𝓝 0] (fun s : ℝ => -gammaApply g (H (t, s)) (fderiv ℝ H (t, s) (1, 0))
            (fderiv ℝ H (t, s) (1, 0))) := by
        filter_upwards [hgeo] with s hs
        have h1 := hs.vel t ht
        have hq1 : HasDerivAt (fun t' : ℝ => ((t', s) : ℝ × ℝ)) ((1, 0) : ℝ × ℝ) t := by
          simpa using (hasDerivAt_id t).prodMk (hasDerivAt_const t s)
        have h2 := hasDerivAt_fderiv_comp (f := H) (hd1 _) hq1 (1, 0)
        rw [← accel_eq_neg_gammaApply]
        exact h2.unique h1
      exact (hφ.unique (hψ.congr_of_eventuallyEq hev))
    have hP := hK.add (hasDerivAt_gammaApply hΓ hγ hw hJ)
    refine hP.congr_deriv ?_
    have e := congrArg (fun L : ℝ × ℝ →L[ℝ] Fin n → ℝ => L (1, 0))
      (hsf (t, 0) (1, 0) (0, 1))
    rw [e, hKval]
    exact jacobi_algebra hg (hU t ht) _ _ _

end Lightlike.Geodesic
