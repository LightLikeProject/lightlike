import Lightlike.Geodesic.TwoPoint
import Lightlike.Geodesic.GaussMaximal
import Lightlike.Geodesic.Radial

/-!
# The squared geodesic distance near the diagonal and the eikonal equation

For a coordinate metric `g` on an open `U ⊆ ℝⁿ` (any signature) and `x ∈ U`, near `(x, x)` two points `p, y` are joined
by a unique short geodesic, with initial velocity `V(p, y)` depending smoothly on `(p, y)`
(`exists_twoPoint_diffeo`). The **world function** (Synge) or squared geodesic distance

`σ(p, y) = g_p(V(p, y), V(p, y))`

is smooth near the diagonal, vanishes on it, and satisfies the **eikonal equation**

`g^{ij}(y) ∂_{y_i} σ(p, y) ∂_{y_j} σ(p, y) = 4 σ(p, y)`

(`exists_sqDist_eikonal`). The proof: differentiating `σ(p, exp_p u) = g_p(u, u)` in `u` gives
`∂_y σ (Dexp_p(v) w) = 2 g_p(v, w)`; the Gauss lemma `g_y(Dexp_p(v) v, Dexp_p(v) w) = g_p(v, w)`
(`exists_expMap_along_gauss`) turns this into `∂_y σ = 2 g_y(T, ·)` with `T = Dexp_p(v) v`, and
`g_y(T, T) = g_p(v, v) = σ`. For a Riemannian metric `σ = d²` is the square of the distance; the eikonal equation is
the equation the phase `e^{-σ/4t}` of the Minakshisundaram–Pleijel parametrix needs.

## References

* `kunzinger-steinbauer-2020`: M. Kunzinger and R. Steinbauer, *Riemannian Geometry*, lecture notes, University of
  Vienna (version of 11 December 2025), Theorem 2.1.21 (Gauss lemma) and Theorem 2.2.6. The eikonal equation is the
  corollary `|grad r| = 1` of the Gauss lemma; comparison pending (not read at a location stating it).
* `rosenberg-1997`: S. Rosenberg, *The Laplacian on a Riemannian Manifold* (1997), §3.2, where `d²` near the diagonal
  enters the parametrix. Comparison pending.
-/

open Set Metric Filter Topology Matrix
open scoped NNReal ContDiff

noncomputable section

namespace Lightlike.Geodesic

variable {n : ℕ} {g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ} {U : Set (Fin n → ℝ)}

/-- `∂_{yᵢ} F(p, y)`: the partial derivative in the `i`-th coordinate of the second variable. -/
def pd₂ (F : (Fin n → ℝ) × (Fin n → ℝ) → ℝ) (q : (Fin n → ℝ) × (Fin n → ℝ)) (i : Fin n) : ℝ :=
  fderiv ℝ (fun y => F (q.1, y)) q.2 (Pi.single i 1)

/-- **The eikonal identity from the gradient form**: if `c = 2 g(T, ·)` then `c · g⁻¹ c = 4 g(T, T)`. -/
lemma dotProduct_inv_mulVec_of_lower (hg : Lightlike.IsCoordMetric g U) {y : Fin n → ℝ} (hy : y ∈ U)
    (T c : Fin n → ℝ) (hc : ∀ i, c i = 2 * pairing g y T (Pi.single i 1)) :
    c ⬝ᵥ ((g y)⁻¹ *ᵥ c) = 4 * pairing g y T T := by
  have hcv : c = (2 : ℝ) • (g y *ᵥ T) := by
    funext i
    rw [hc i, Pi.smul_apply, smul_eq_mul, pairing_comm hg hy, pairing_eq_dotProduct]
    simp [Matrix.mulVec, dotProduct, Pi.single_apply, Finset.sum_ite_eq']
  have hunit := hg.isUnit_det y hy
  rw [hcv, Matrix.mulVec_smul, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hunit, Matrix.one_mulVec,
    smul_dotProduct, smul_eq_mul, pairing_eq_dotProduct, dotProduct_smul, smul_eq_mul, dotProduct_comm]
  ring

/-- The derivative of `u ↦ g_p(u, u)` at `v` is `w ↦ 2 g_p(v, w)`. -/
lemma fderiv_pairing_self (hg : Lightlike.IsCoordMetric g U) {p : Fin n → ℝ} (hp : p ∈ U) (v w : Fin n → ℝ) :
    fderiv ℝ (fun u => pairing g p u u) v w = 2 * pairing g p v w := by
  have hdiff : DifferentiableAt ℝ (fun u => pairing g p u u) v := by unfold pairing; fun_prop
  rw [← hdiff.lineDeriv_eq_fderiv]
  have hterm : ∀ i j, HasDerivAt (fun t : ℝ => (v + t • w) i * (g p i j * (v + t • w) j))
      (w i * (g p i j * v j) + v i * (g p i j * w j)) 0 := by
    intro i j
    have h1 : ∀ k, HasDerivAt (fun t : ℝ => (v + t • w) k) (w k) 0 := fun k => by
      simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (w k)).const_add (v k)
    have := (h1 i).mul ((h1 j).const_mul (g p i j))
    convert this using 1 <;> simp
  have hsum : HasDerivAt (fun t : ℝ => pairing g p (v + t • w) (v + t • w))
      (∑ i, ∑ j, (w i * (g p i j * v j) + v i * (g p i j * w j))) 0 := by
    unfold pairing
    exact HasDerivAt.fun_sum fun i _ => HasDerivAt.fun_sum fun j _ => hterm i j
  rw [lineDeriv, hsum.deriv]
  have hc := pairing_comm hg hp w v
  simp only [pairing] at hc
  simp only [pairing, Finset.sum_add_distrib, hc]
  ring

/-- **The squared geodesic distance near the diagonal satisfies the eikonal equation.** Near `(x, x)` there is a smooth
`V(p, y)`, the initial velocity of the geodesic from `p` to `y` (reaching `y` at time `1` and staying in `U`), with
`V(p, p) = 0`; the world function `σ(p, y) = g_p(V, V)` is smooth and `g^{ij}(y) ∂_{yᵢ}σ ∂_{yⱼ}σ = 4σ`. -/
theorem exists_sqDist_eikonal (hg : Lightlike.IsCoordMetric g U) {x : Fin n → ℝ} (hx : x ∈ U) :
    ∃ (W : Set ((Fin n → ℝ) × (Fin n → ℝ))) (V : (Fin n → ℝ) × (Fin n → ℝ) → (Fin n → ℝ)),
      IsOpen W ∧ (x, x) ∈ W ∧ ContDiffOn ℝ ∞ V W ∧
      (∀ q ∈ W, q.1 ∈ U ∧ q.2 ∈ U) ∧
      (∀ p, (p, p) ∈ W → V (p, p) = 0) ∧
      (∀ q ∈ W, ∃ γ w : ℝ → Fin n → ℝ, γ 0 = q.1 ∧ w 0 = V q ∧ γ 1 = q.2 ∧
        IsGeodesicOn g γ w (Ioo (-1) 2) ∧ ∀ t ∈ Icc (0 : ℝ) 1, γ t ∈ U) ∧
      ContDiffOn ℝ ∞ (fun q => pairing g q.1 (V q) (V q)) W ∧
      ∀ q ∈ W, (fun i => pd₂ (fun q' => pairing g q'.1 (V q') (V q')) q i) ⬝ᵥ
          ((g q.2)⁻¹ *ᵥ fun i => pd₂ (fun q' => pairing g q'.1 (V q') (V q')) q i) =
        4 * pairing g q.1 (V q) (V q) := by
  obtain ⟨ρ, E, Θ, hρ, hE0, hEs, hEU, hEg, hx0, hΘs, hΘ, hΘc, hΘic⟩ := exists_twoPoint_diffeo hg hx
  have hBo : IsOpen (ball x ρ ×ˢ ball (0 : Fin n → ℝ) ρ) := isOpen_ball.prod isOpen_ball
  set W := Θ.target ∩ {q | (q.1, (0 : Fin n → ℝ)) ∈ Θ.source} with hW
  have hWo : IsOpen W := Θ.open_target.inter
    (Θ.open_source.preimage (continuous_fst.prodMk continuous_const))
  set V := fun q => (Θ.symm q).2 with hV
  -- the basic facts about a point of `W`
  have hr : ∀ q ∈ W, Θ.symm q ∈ Θ.source := fun q hq => Θ.map_target hq.1
  have hq12 : ∀ q ∈ W, q.1 = (Θ.symm q).1 ∧ q.2 = E (Θ.symm q) := by
    intro q hq
    have h := Θ.right_inv hq.1
    rw [hΘ _ (hr q hq)] at h
    exact ⟨(congrArg Prod.fst h).symm, (congrArg Prod.snd h).symm⟩
  have hrB : ∀ q ∈ W, (Θ.symm q).1 ∈ ball x ρ ∧ (Θ.symm q).2 ∈ ball (0 : Fin n → ℝ) ρ := fun q hq =>
    hΘs (hr q hq)
  have hrq : ∀ q ∈ W, Θ.symm q = (q.1, V q) := fun q hq => by
    ext <;> simp [hV, (hq12 q hq).1]
  have hU1 : ∀ q ∈ W, q.1 ∈ U := fun q hq => by
    rw [(hq12 q hq).1, ← hE0 _ (hrB q hq).1]; exact hEU _ (hrB q hq).1 0 (mem_ball_self hρ)
  have hU2 : ∀ q ∈ W, q.2 ∈ U := fun q hq => by
    rw [(hq12 q hq).2]; exact hEU _ (hrB q hq).1 _ (hrB q hq).2
  have hVs : ContDiffOn ℝ ∞ V W := contDiffOn_snd.comp (hΘic.mono inter_subset_left) (mapsTo_univ _ _)
  have hσs : ContDiffOn ℝ ∞ (fun q => pairing g q.1 (V q) (V q)) W := by
    simp only [pairing]
    refine ContDiffOn.sum fun i _ => ContDiffOn.sum fun j _ => ?_
    refine ((contDiffOn_pi.1 hVs i).mul (((hg.smooth i j).comp contDiffOn_fst fun q hq => hU1 q hq).mul
      (contDiffOn_pi.1 hVs j)))
  refine ⟨W, V, hWo, ⟨?_, ?_⟩, hVs, fun q hq => ⟨hU1 q hq, hU2 q hq⟩, ?_, ?_, hσs, ?_⟩
  · -- `(x, x) ∈ Θ.target`
    have := Θ.map_source hx0
    rwa [hΘ _ hx0, hE0 x (mem_ball_self hρ)] at this
  · exact hx0
  · -- `V(p, p) = 0`
    intro p hp
    have hp0 : (p, (0 : Fin n → ℝ)) ∈ Θ.source := hp.2
    have hΘp : Θ (p, 0) = (p, p) := by rw [hΘ _ hp0, hE0 p (hΘs hp0).1]
    simp only [hV]
    rw [← hΘp, Θ.left_inv hp0]
  · -- the geodesic from `p` to `y`
    intro q hq
    obtain ⟨γ, w, hγ0, hw0, hgeo, hγE⟩ := hEg _ (hrB q hq).1 _ (hrB q hq).2
    refine ⟨γ, w, ?_, ?_, ?_, hgeo, fun t ht => ?_⟩
    · rw [hγ0, ← (hq12 q hq).1]
    · exact hw0
    · rw [hγE 1 ⟨by norm_num, le_rfl⟩, one_smul, ← (hq12 q hq).2]
    · rw [hγE t ⟨by linarith [ht.1], ht.2⟩]
      refine hEU _ (hrB q hq).1 _ ?_
      rw [mem_ball_zero_iff, norm_smul]
      have := mem_ball_zero_iff.1 (hrB q hq).2
      calc ‖t‖ * ‖(Θ.symm q).2‖ ≤ 1 * ‖(Θ.symm q).2‖ := by
            gcongr; rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith [ht.1, ht.2]
        _ < ρ := by rwa [one_mul]
  · -- the eikonal equation
    intro q hq
    set p := q.1 with hp
    set y := q.2 with hy
    set v := V q with hv
    have hrpv : Θ.symm q = (p, v) := hrq q hq
    have hsrc : (p, v) ∈ Θ.source := hrpv ▸ hr q hq
    have hyE : y = E (p, v) := by rw [hy, (hq12 q hq).2, hrpv]
    have hpU : p ∈ U := hU1 q hq
    have hyU : y ∈ U := hU2 q hq
    set F : (Fin n → ℝ) → (Fin n → ℝ) := fun u => E (p, u) with hF
    set σ := fun q' : (Fin n → ℝ) × (Fin n → ℝ) => pairing g q'.1 (V q') (V q') with hσ
    -- step 1: `σ(p, F u) = g_p(u, u)` near `v`
    have hS : IsOpen {u | (p, u) ∈ Θ.source} := Θ.open_source.preimage (continuous_const.prodMk continuous_id)
    have hstep1 : (fun u => σ (p, F u)) =ᶠ[𝓝 v] fun u => pairing g p u u := by
      filter_upwards [hS.mem_nhds hsrc] with u hu
      have hmem : (p, F u) ∈ W := by
        refine ⟨?_, ?_⟩
        · have := Θ.map_source hu; rwa [hΘ _ hu] at this
        · exact hq.2
      have hinv : Θ.symm (p, F u) = (p, u) := by
        rw [show (p, F u) = Θ (p, u) from (hΘ _ hu).symm, Θ.left_inv hu]
      simp only [hσ, hV, hinv]
    -- differentiability
    have hEd : DifferentiableAt ℝ E (p, v) :=
      (hEs.contDiffAt (hBo.mem_nhds (hΘs hsrc))).differentiableAt (by simp)
    have hFd : DifferentiableAt ℝ F v :=
      hEd.comp v ((differentiableAt_const p).prodMk differentiableAt_id)
    have hσy : DifferentiableAt ℝ (fun y' => σ (p, y')) y := by
      have h1 : DifferentiableAt ℝ σ (p, y) :=
        (hσs.contDiffAt (hWo.mem_nhds (by simpa [hp, hy] using hq))).differentiableAt (by simp)
      exact h1.comp y ((differentiableAt_const p).prodMk differentiableAt_id)
    -- step 2: `Dσ_y (A w) = 2 g_p(v, w)`
    set A := fderiv ℝ F v with hA
    have hstep2 : ∀ w, fderiv ℝ (fun y' => σ (p, y')) y (A w) = 2 * pairing g p v w := by
      intro w
      have hc := fderiv_comp v (hyE ▸ hσy) hFd
      have h1 : fderiv ℝ (fun u => σ (p, F u)) v = fderiv ℝ (fun u => pairing g p u u) v := hstep1.fderiv_eq
      have h2 : fderiv ℝ ((fun y' => σ (p, y')) ∘ F) v w = fderiv ℝ (fun u => pairing g p u u) v w := by
        rw [← h1]; rfl
      rw [hc, ContinuousLinearMap.comp_apply, show F v = y from hyE.symm] at h2
      rw [h2, fderiv_pairing_self hg hpU]
    -- step 3: the Gauss lemma at `v` along the geodesic from `p`
    obtain ⟨γ, w, hγ0, hw0, hgeo, hγE⟩ := hEg _ (hrB q hq).1 _ (hrB q hq).2
    rw [hrpv] at hγ0 hw0 hγE
    have hγU : ∀ t ∈ Icc (0 : ℝ) 1, γ t ∈ U := by
      intro t ht
      rw [hγE t ⟨by linarith [ht.1], ht.2⟩]
      refine hEU _ (hΘs hsrc).1 _ ?_
      rw [mem_ball_zero_iff, norm_smul]
      have := mem_ball_zero_iff.1 (hΘs hsrc).2
      calc ‖t‖ * ‖v‖ ≤ 1 * ‖v‖ := by
            gcongr; rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith [ht.1, ht.2]
        _ < ρ := by rwa [one_mul]
    obtain ⟨δ, E', hδ, hE's, hE'v, hE'g, hgauss⟩ :=
      exists_expMap_along_gauss hg (I := Ioo (-1) 2) (fun t ht => ⟨by linarith [ht.1], by linarith [ht.2]⟩)
        hgeo hγU
    simp only [hw0] at hE's hE'v hE'g hgauss
    rw [hγ0] at hgauss
    have hγ1 : γ 1 = y := by rw [hγE 1 ⟨by norm_num, le_rfl⟩, one_smul, hyE]
    rw [hγ1] at hE'v
    -- step 4: `E' = F` near `v`, by uniqueness of geodesics
    have hEF : E' =ᶠ[𝓝 v] F := by
      filter_upwards [isOpen_ball.mem_nhds (mem_ball_self hδ), isOpen_ball.mem_nhds (hΘs hsrc).2]
        with u hu1 hu2
      obtain ⟨η, γ', w', hη, hγ'0, hw'0, hγ'1, hgeo', hγ'U⟩ := hE'g u hu1
      obtain ⟨γ'', w'', hγ''0, hw''0, hgeo'', hγ''E⟩ := hEg p (hΘs hsrc).1 u hu2
      have huniq := IsGeodesicOn.eqOn_Icc hg isOpen_Ioo isOpen_Ioo
        (fun t ht => ⟨by linarith [ht.1], by linarith [ht.2]⟩)
        (fun t ht => ⟨by linarith [ht.1], by linarith [ht.2]⟩) hgeo' hgeo'' hγ'U
        (by rw [hγ'0, hγ0, hγ''0]) (by rw [hw'0, hw''0]) 1 ⟨zero_le_one, le_rfl⟩
      rw [← hγ'1, huniq.1, hγ''E 1 ⟨by norm_num, le_rfl⟩, one_smul]
    have hAeq : fderiv ℝ E' v = A := hEF.fderiv_eq
    rw [hE'v, hAeq] at hgauss
    -- step 5: `A` is surjective, since `Θ⁻¹` is a differentiable inverse of `Θ = (fst, E)` near `q`
    have hsurj : ∀ w₀ : Fin n → ℝ, ∃ w, A w = w₀ := by
      intro w₀
      have hq' : (p, y) ∈ Θ.target := by simpa [hp, hy] using hq.1
      have hΘsd : DifferentiableAt ℝ Θ.symm (p, y) :=
        (hΘic.contDiffAt (Θ.open_target.mem_nhds hq')).differentiableAt (by simp)
      have hΘd : DifferentiableAt ℝ Θ (p, v) :=
        (hΘc.contDiffAt (Θ.open_source.mem_nhds hsrc)).differentiableAt (by simp)
      have hid : Θ ∘ Θ.symm =ᶠ[𝓝 (p, y)] id := by
        filter_upwards [Θ.open_target.mem_nhds hq'] with z hz using Θ.right_inv hz
      have hsym : Θ.symm (p, y) = (p, v) := by simpa [hp, hy] using hrpv
      have hc := fderiv_comp (p, y) (hsym ▸ hΘd) hΘsd
      rw [hid.fderiv_eq, fderiv_id, hsym] at hc
      set ab := fderiv ℝ Θ.symm (p, y) (0, w₀) with hab
      have h1 : fderiv ℝ Θ (p, v) ab = (0, w₀) := by
        have := congrArg (fun L : ((Fin n → ℝ) × (Fin n → ℝ)) →L[ℝ] _ => L (0, w₀)) hc
        simpa using this.symm
      have hΘE : Θ =ᶠ[𝓝 (p, v)] fun q' => (q'.1, E q') := by
        filter_upwards [Θ.open_source.mem_nhds hsrc] with z hz using hΘ z hz
      have hDΘ : fderiv ℝ Θ (p, v) ab = (ab.1, fderiv ℝ E (p, v) ab) := by
        rw [hΘE.fderiv_eq, DifferentiableAt.fderiv_prodMk differentiableAt_fst hEd, fderiv_fst]
        simp
      rw [hDΘ] at h1
      have ha : ab.1 = 0 := congrArg Prod.fst h1
      refine ⟨ab.2, ?_⟩
      have hFE : A ab.2 = fderiv ℝ E (p, v) (0, ab.2) := by
        have hd : HasFDerivAt (fun u : Fin n → ℝ => (p, u))
            ((0 : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)).prod (ContinuousLinearMap.id ℝ (Fin n → ℝ))) v :=
          (hasFDerivAt_const p v).prodMk (hasFDerivAt_id v)
        rw [hA, hF, fderiv_fun_comp v hEd ((differentiableAt_const p).prodMk differentiableAt_id)]
        rw [show (Prod.mk p : (Fin n → ℝ) → _) = fun u => (p, u) from rfl, hd.fderiv]
        simp
      rw [hFE, show ((0 : Fin n → ℝ), ab.2) = ab from Prod.ext ha.symm rfl]
      exact congrArg Prod.snd h1
    -- step 6: the gradient form and the eikonal identity
    have hgrad : ∀ i, pd₂ σ q i = 2 * pairing g y (A v) (Pi.single i 1) := by
      intro i
      obtain ⟨w₁, hw₁⟩ := hsurj (Pi.single i 1)
      have := hstep2 w₁
      rw [hw₁] at this
      unfold pd₂
      rw [← hp, ← hy, this, ← hgauss w₁, hw₁]
    rw [dotProduct_inv_mulVec_of_lower hg hyU (A v) _ hgrad, hgauss v]

end Lightlike.Geodesic
