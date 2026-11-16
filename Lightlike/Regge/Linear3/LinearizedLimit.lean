import Lightlike.Regge.Linear3.LinearizedExpansion
import Lightlike.Regge.Conv3.LatticeSum
import Lightlike.Regge.Conv3.RiemannSumCont
import Lightlike.Regge.Conv3.ReggeConvergence

/-!
# The coefficient of the linearized Regge action of the torus converges to the Saint-Venant form

For a smooth symmetric field `h` of matrices on `ℝ³` invariant under integer translations, the coefficient
`Q_n (h) = Σ_e (a_e / (2 ℓ_e)) δ_e'(0)` of `ε²/2` in the Regge action of the periodic Kuhn complex of mesh `1/n`
with the interpolated lengths `ℓ_e² + ε μ_e (h)` (Christiansen 2011, eq. (5)) tends, as `n → ∞`, to
`∫_{[0,1]³} -¼ Σ h_ij ε_ikl ε_jmn ∂_k ∂_m h_ln` (`Qn_converges`), that is `-¼ ⟨curl^t curl h, h⟩` with
`curl^t curl` defined as in Christiansen's section 2 (the curl of the rows, transposed, the curl of the rows).

The proof writes `Q_n` as a lattice sum of hinge densities (`Qn_lattice`), expands the unit-scale degrees of freedom to
second order uniformly on the unit cube (`atilV_expansion`), kills the zeroth and first order terms by
the vanishing of the class sums (`class_A0`, `class_A1`), identifies the sum of the class densities with the
Saint-Venant density by the pointwise identity `sv_pointwise` (`sum_clsDens`), bounds each hinge term by
`ε⁴` (`term_close`), and applies the convergence of Riemann sums with sample points in the cells
(`riemann_sum_tendsto`). No rate is claimed.

## Main results

* `clsDens`, `sum_clsDens`: the class densities and their sum `-¼ svPair`.
* `hAt_close`: the hinge degree of freedom is `qf H w` up to `O(ε)`.
* `Qn_converges`: the convergence.

**Limits.** Convergence only, no rate; one smooth periodic field on the standard cubical Kuhn complex of the
torus; the second variation of the Regge action in the interpolated lengths, not in the geodesic lengths (the two
have the same first variation at `ε = 0`; that equality is not formalized). The identification of
`-¼ ⟨curl^t curl h, h⟩` with the Fierz–Pauli form (the second variation of `∫ (R/2) √det g`) is by an
integration by parts on the torus that is not proved here (numerically checked in
`scripts/regge/regge3d_linearized_check.py`); the sign of the paper's deficit angle (a holonomy rotation angle)
relative to `2π - Σ θ` is fixed by that check, not by the paper.
-/

open Real Finset Filter Topology Matrix
namespace Lightlike.Regge.Linear3
open Lightlike.Regge Lightlike.Regge.Conv3

theorem pd2_symm {F : (Fin 3 → ℝ) → ℝ} (hF : ContDiff ℝ 3 F) (v : Fin 3 → ℝ) (k l : Fin 3) :
    pd2 F v k l = pd2 F v l k := by
  have h := (hF.contDiffAt (x := v)).isSymmSndFDerivAt (by simp; norm_num)
  exact h _ _

theorem pd2_continuous {F : (Fin 3 → ℝ) → ℝ} (hF : ContDiff ℝ 3 F) (k l : Fin 3) :
    Continuous fun v => pd2 F v k l := by
  have h1 : ContDiff ℝ 2 (fderiv ℝ F) := hF.fderiv_right (by norm_num)
  have h2 : ContDiff ℝ 1 (fderiv ℝ (fderiv ℝ F)) := h1.fderiv_right (by norm_num)
  have h3 : Continuous (fderiv ℝ (fderiv ℝ F)) := h2.continuous
  unfold pd2
  exact (h3.clm_apply continuous_const).clm_apply continuous_const


open Classical in
/-- The density of the edge class `k` at `v` in the limit `ε → 0`. -/
noncomputable def clsDens (hf : (Fin 3 → ℝ) → Matrix (Fin 3) (Fin 3) ℝ) (k : Fin 7) (v : Fin 3 → ℝ) : ℝ :=
  (qf (Hm hf v) (dirs k) / (2 * wn k)) *
    (-(clsSum (dirs k) (fun σ h => dth h (lenR (dd2 hf v) σ h))) / wn k)

theorem hinge_cond : ∀ σ h : Fin 6, ∃ k : Fin 7, Cond (dirsN k) σ h := by
  unfold Cond; decide

/-- Every incidence lies in exactly one edge class. -/
theorem inClass_unique (σ h : Fin 6) : ∃ k : Fin 7, InClass (dirs k) σ h ∧ ∀ k', InClass (dirs k') σ h → k' = k := by
  obtain ⟨k, hc⟩ := hinge_cond σ h
  have hk : ∀ i, koff (hQ h) (perms σ i) = koff (hP h) (perms σ i) + dirsN k i := hc
  refine ⟨k, (cond_iff_inClass k σ h).1 hc, fun k' hk' => ?_⟩
  have hc' := (cond_iff_inClass k' σ h).2 hk'
  have hd : dirsN k' = dirsN k := by
    funext i
    have a := hc' i
    have b := hk i
    omega
  exact dirsN_inj hd


open Classical in
/-- **The class densities add up to the Saint-Venant density.** -/
theorem sum_clsDens {hf : (Fin 3 → ℝ) → Matrix (Fin 3) (Fin 3) ℝ}
    (hsm : ∀ i j, ContDiff ℝ 3 (fun y => hf y i j)) (hsymm : ∀ y i j, hf y i j = hf y j i)
    (v : Fin 3 → ℝ) :
    ∑ k : Fin 7, clsDens hf k v = -(1 / 4) * svPair (Hm hf v) (dd2 hf v) := by
  have hHs : ∀ i j, Hm hf v i j = Hm hf v j i := fun i j => hsymm v i j
  have hd1 : ∀ k l i j, dd2 hf v k l i j = dd2 hf v l k i j := fun k l i j =>
    pd2_symm (hsm i j) v k l
  have hd2 : ∀ k l i j, dd2 hf v k l i j = dd2 hf v k l j i := fun k l i j => by
    unfold dd2 pd2
    have : (fun y => hf y i j) = fun y => hf y j i := by funext y; exact hsymm y i j
    rw [this]
  rw [← sv_pointwise (Hm hf v) (dd2 hf v) hHs hd1 hd2]
  unfold clsDens clsSum
  simp only [neg_div, Finset.sum_div, Finset.mul_sum, mul_neg, ← Finset.sum_neg_distrib]
  rw [Finset.sum_comm]
  refine sum_congr rfl fun σ _ => ?_
  rw [Finset.sum_comm]
  refine sum_congr rfl fun h _ => ?_
  obtain ⟨k0, hk0, huniq⟩ := inClass_unique σ h
  rw [Finset.sum_eq_single k0]
  · simp only [hk0, if_true]
    have hc : Cond (dirsN k0) σ h := (cond_iff_inClass k0 σ h).2 hk0
    have hw : wn k0 = √(hbase h 0) := (hbase_wn k0 σ h hc).symm
    have hsq : wn k0 ^ 2 = hbase h 0 := by rw [hw]; exact Real.sq_sqrt (hbase_pos h).le
    have hwpos : 0 < wn k0 := by rw [hw]; exact Real.sqrt_pos.2 (hbase_pos h)
    have hv : dirs k0 = hvec σ h := by
      funext i; exact (hk0 i).symm
    rw [hv, ← hsq]
    field_simp
  · intro k _ hk
    have : ¬ InClass (dirs k) σ h := fun hh => hk (huniq k hh)
    simp [this]
  · intro h; exact absurd (Finset.mem_univ k0) h


theorem qf_eq_dot (H : Matrix (Fin 3) (Fin 3) ℝ) (x : Fin 3 → ℝ) : qf (fun i j => H i j) x = x ⬝ᵥ (H *ᵥ x) := by
  simp only [qf, dotProduct, Matrix.mulVec, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem dirs_nonneg' (k : Fin 7) (i : Fin 3) : 0 ≤ dirs k i := by
  rw [← dirsN_cast]; positivity

theorem dirs_le_one' (k : Fin 7) (i : Fin 3) : dirs k i ≤ 1 := by
  rw [← dirsN_cast]; exact_mod_cast dirsN_le k i

theorem dirs_norm_le' (k : Fin 7) : ‖dirs k‖ ≤ 1 := by
  refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun i => ?_
  rw [Real.norm_eq_abs, abs_of_nonneg (dirs_nonneg' k i)]; exact dirs_le_one' k i

/-- The box `[-1, 2]³`. -/
def boxB : Set (Fin 3 → ℝ) := Set.pi Set.univ fun _ => Set.Icc (-1 : ℝ) 2

/-- **The hinge degree of freedom is `qf H w` up to `O(ε)`**, uniformly on the unit cube. -/
theorem hAt_close {hf : (Fin 3 → ℝ) → Matrix (Fin 3) (Fin 3) ℝ}
    (hsm : ∀ i j, ContDiff ℝ 3 (fun y => hf y i j)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ v ∈ unitCube, ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ k : Fin 7,
      |hAt hf ε v k - qf (Hm hf v) (dirs k)| ≤ C * ε := by
  have hBc : IsCompact boxB := isCompact_univ_pi fun _ => isCompact_Icc
  have hBv : Convex ℝ boxB := convex_pi fun _ _ => convex_Icc _ _
  have hL : ∀ i j, ∃ K : NNReal, LipschitzOnWith K (fun y => hf y i j) boxB := fun i j =>
    ((hsm i j).contDiffOn).exists_lipschitzOnWith (by norm_num) hBv hBc
  choose L hLip using hL
  refine ⟨∑ i, ∑ j, (L i j : ℝ), by positivity, fun v hv ε hε hε1 k => ?_⟩
  have hw : ∀ i, |dirs k i| ≤ 1 := fun i => by
    rw [abs_le]; constructor <;> linarith [dirs_nonneg' k i, dirs_le_one' k i]
  have hvB : v ∈ boxB := fun i _ => ⟨by linarith [(hv i (Set.mem_univ _)).1], by linarith [(hv i (Set.mem_univ _)).2]⟩
  have hcont : Continuous fun t : ℝ => dirs k ⬝ᵥ (hf (v + ε • ((t - 1 / 2) • dirs k)) *ᵥ dirs k) := by
    have : ∀ i j, Continuous fun y => hf y i j := fun i j => (hsm i j).continuous
    simp only [dotProduct, Matrix.mulVec]
    fun_prop
  have hq : qf (Hm hf v) (dirs k) = ∫ t in (0 : ℝ)..1, dirs k ⬝ᵥ (hf v *ᵥ dirs k) := by
    rw [intervalIntegral.integral_const, sub_zero, one_smul]; exact qf_eq_dot (hf v) (dirs k)
  rw [hq, hAt, ← intervalIntegral.integral_sub (hcont.intervalIntegrable _ _) intervalIntegrable_const]
  have hbd : ∀ t ∈ Set.uIoc (0 : ℝ) 1, ‖dirs k ⬝ᵥ (hf (v + ε • ((t - 1 / 2) • dirs k)) *ᵥ dirs k) -
      dirs k ⬝ᵥ (hf v *ᵥ dirs k)‖ ≤ (∑ i, ∑ j, (L i j : ℝ)) * ε := by
    intro t ht
    rw [Set.uIoc_of_le zero_le_one] at ht
    have hdy : ‖ε • ((t - 1 / 2) • dirs k)‖ ≤ ε := by
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hε]
      have hd : ‖dirs k‖ ≤ 1 := dirs_norm_le' k
      have : |t - 1 / 2| ≤ 1 := by rw [abs_le]; constructor <;> linarith [ht.1, ht.2]
      calc ε * (|t - 1 / 2| * ‖dirs k‖) ≤ ε * (1 * 1) := by
            apply mul_le_mul_of_nonneg_left _ hε.le
            exact mul_le_mul this hd (norm_nonneg _) zero_le_one
        _ = ε := by ring
    have hyB : v + ε • ((t - 1 / 2) • dirs k) ∈ boxB := fun i _ => by
      have h1 := hv i (Set.mem_univ _)
      have h2 : |(ε • ((t - 1 / 2) • dirs k)) i| ≤ ε := by simpa [Real.norm_eq_abs] using (norm_le_pi_norm (ε • ((t - 1 / 2) • dirs k)) i).trans hdy
      have h3 := abs_le.1 h2
      simp only [Pi.add_apply]
      constructor <;> linarith [h1.1, h1.2, h3.1, h3.2]
    have hdist : ‖(v + ε • ((t - 1 / 2) • dirs k)) - v‖ ≤ ε := by simpa using hdy
    have hentry : ∀ i j, |hf (v + ε • ((t - 1 / 2) • dirs k)) i j - hf v i j| ≤ (L i j : ℝ) * ε := fun i j => by
      have := (hLip i j).dist_le_mul _ hyB v hvB
      rw [Real.dist_eq, dist_eq_norm] at this
      exact this.trans (mul_le_mul_of_nonneg_left hdist (NNReal.coe_nonneg _))
    rw [Real.norm_eq_abs]
    have : dirs k ⬝ᵥ (hf (v + ε • ((t - 1 / 2) • dirs k)) *ᵥ dirs k) - dirs k ⬝ᵥ (hf v *ᵥ dirs k) =
        ∑ i, ∑ j, dirs k i * dirs k j * (hf (v + ε • ((t - 1 / 2) • dirs k)) i j - hf v i j) := by
      simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
    rw [this]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ i, |∑ j, dirs k i * dirs k j * (hf (v + ε • ((t - 1 / 2) • dirs k)) i j - hf v i j)|
        ≤ ∑ i, ∑ j, (L i j : ℝ) * ε := by
          refine Finset.sum_le_sum fun i _ => ?_
          refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
          rw [abs_mul, abs_mul]
          have h1 : |dirs k i| * |dirs k j| ≤ 1 := by
            have := hw i; have := hw j
            nlinarith [abs_nonneg (dirs k i), abs_nonneg (dirs k j)]
          calc |dirs k i| * |dirs k j| * |hf (v + ε • ((t - 1 / 2) • dirs k)) i j - hf v i j|
              ≤ 1 * ((L i j : ℝ) * ε) := mul_le_mul h1 (hentry i j) (abs_nonneg _) zero_le_one
            _ = (L i j : ℝ) * ε := one_mul _
      _ = (∑ i, ∑ j, (L i j : ℝ)) * ε := by
          rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun i _ => by rw [Finset.sum_mul]
  have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := 1) hbd
  simpa [Real.norm_eq_abs] using this


/-- **The pointwise estimate of a hinge term**, a pure inequality. -/
theorem term_close (hA q c2 S Cd M B B' ε wn : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) (hwn : 1 ≤ wn)
    (h1 : |hA - q| ≤ Cd * ε) (h2 : |S - ε ^ 2 * c2| ≤ M * ε ^ 3) (h3 : |c2| ≤ B) (h4 : |q| ≤ B')
    (hM : 0 ≤ M) (hC : 0 ≤ Cd) (hB : 0 ≤ B) (hB' : 0 ≤ B') :
    |ε * (hA / (2 * wn)) * (-S / wn) - ε ^ 3 * ((q / (2 * wn)) * (-c2 / wn))| ≤
      ε ^ 4 * (Cd * (B + M) + B' * M) := by
  have hwn0 : 0 < wn := by linarith
  have hS : |S| ≤ ε ^ 2 * (B + M) := by
    have : S = (S - ε ^ 2 * c2) + ε ^ 2 * c2 := by ring
    calc |S| = |(S - ε ^ 2 * c2) + ε ^ 2 * c2| := by rw [← this]
      _ ≤ |S - ε ^ 2 * c2| + |ε ^ 2 * c2| := abs_add_le _ _
      _ ≤ M * ε ^ 3 + ε ^ 2 * B := by
          rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ ε ^ 2)]
          exact add_le_add h2 (mul_le_mul_of_nonneg_left h3 (by positivity))
      _ ≤ ε ^ 2 * (B + M) := by nlinarith [pow_pos hε 2, mul_nonneg hM (pow_pos hε 2).le]
  have key : ε * (hA / (2 * wn)) * (-S / wn) - ε ^ 3 * ((q / (2 * wn)) * (-c2 / wn)) =
      -(ε / (2 * wn ^ 2)) * ((hA - q) * S + q * (S - ε ^ 2 * c2)) := by
    field_simp; ring
  rw [key, abs_mul]
  have hfac : |-(ε / (2 * wn ^ 2))| ≤ ε := by
    rw [abs_neg, abs_of_nonneg (by positivity)]
    have : 1 ≤ 2 * wn ^ 2 := by nlinarith
    calc ε / (2 * wn ^ 2) ≤ ε / 1 := div_le_div_of_nonneg_left hε.le one_pos this
      _ = ε := by ring
  have hin : |(hA - q) * S + q * (S - ε ^ 2 * c2)| ≤ ε ^ 3 * (Cd * (B + M) + B' * M) := by
    calc |(hA - q) * S + q * (S - ε ^ 2 * c2)| ≤ |(hA - q) * S| + |q * (S - ε ^ 2 * c2)| := abs_add_le _ _
      _ ≤ (Cd * ε) * (ε ^ 2 * (B + M)) + B' * (M * ε ^ 3) := by
          rw [abs_mul, abs_mul]
          exact add_le_add (mul_le_mul h1 hS (abs_nonneg _) (by positivity))
            (mul_le_mul h4 h2 (abs_nonneg _) hB')
      _ = ε ^ 3 * (Cd * (B + M) + B' * M) := by ring
  calc |-(ε / (2 * wn ^ 2))| * |(hA - q) * S + q * (S - ε ^ 2 * c2)| ≤ ε * (ε ^ 3 * (Cd * (B + M) + B' * M)) :=
        mul_le_mul hfac hin (abs_nonneg _) hε.le
    _ = ε ^ 4 * (Cd * (B + M) + B' * M) := by ring


theorem one_le_wn (k : Fin 7) : 1 ≤ wn k := by
  unfold wn
  rw [Real.one_le_sqrt]
  fin_cases k <;> simp [dirs, Fin.sum_univ_three] <;> norm_num

open Classical in
/-- The second-order class sum at `v`. -/
noncomputable def c2fun (hf : (Fin 3 → ℝ) → Matrix (Fin 3) (Fin 3) ℝ) (k : Fin 7) (v : Fin 3 → ℝ) : ℝ :=
  clsSum (dirs k) (fun σ h => dth h (lenR (dd2 hf v) σ h))

theorem continuous_dd2 {hf : (Fin 3 → ℝ) → Matrix (Fin 3) (Fin 3) ℝ}
    (hsm : ∀ i j, ContDiff ℝ 3 (fun y => hf y i j)) (k l i j : Fin 3) :
    Continuous fun v => dd2 hf v k l i j := pd2_continuous (hsm i j) k l

theorem continuous_c2fun {hf : (Fin 3 → ℝ) → Matrix (Fin 3) (Fin 3) ℝ}
    (hsm : ∀ i j, ContDiff ℝ 3 (fun y => hf y i j)) (k : Fin 7) : Continuous (c2fun hf k) := by
  have hc := continuous_dd2 hsm
  unfold c2fun clsSum
  refine continuous_finset_sum _ fun σ _ => continuous_finset_sum _ fun h _ => ?_
  split_ifs
  · have hrf : ∀ s Δ : Fin 3 → ℝ, Continuous fun v => rf (dd2 hf v) s Δ := fun s Δ => by
      unfold rf ddq
      simp only [Fin.sum_univ_three]
      fun_prop
    have hlen : Continuous fun v => lenR (dd2 hf v) σ h := by
      refine continuous_pi fun i => ?_
      unfold lenR incVec
      fin_cases i <;> exact hrf _ _
    have hdth : Continuous fun x : Fin 6 → ℝ => dth h x := by
      fin_cases h <;> simp [dth] <;> fun_prop
    exact hdth.comp hlen
  · exact continuous_const


theorem latticeCell_subset_unitCube {N : ℕ} (hN : 0 < N) (z : Fin 3 → Fin N) :
    latticeCell N z ⊆ unitCube := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  intro y hy i hi
  have h := hy i hi
  simp only [Set.mem_Ico] at h
  have h2 : (z i : ℝ) + 1 ≤ N := by exact_mod_cast (z i).2
  refine ⟨le_trans (by positivity) h.1, ?_⟩
  have : (z i : ℝ) / N + 1 / N ≤ 1 := by rw [← add_div, div_le_one hN']; exact h2
  linarith [h.2]

theorem continuous_clsDens {hf : (Fin 3 → ℝ) → Matrix (Fin 3) (Fin 3) ℝ}
    (hsm : ∀ i j, ContDiff ℝ 3 (fun y => hf y i j)) (k : Fin 7) : Continuous (clsDens hf k) := by
  have hq : Continuous fun v => qf (Hm hf v) (dirs k) := by
    simp only [qf, Hm, Fin.sum_univ_three]
    have : ∀ i j, Continuous fun y => hf y i j := fun i j => (hsm i j).continuous
    fun_prop
  have hc := continuous_c2fun hsm k
  unfold clsDens
  have : (fun v => (qf (Hm hf v) (dirs k) / (2 * wn k)) * (-(clsSum (dirs k) (fun σ h => dth h (lenR (dd2 hf v) σ h))) / wn k)) =
      fun v => (qf (Hm hf v) (dirs k) / (2 * wn k)) * (-(c2fun hf k v) / wn k) := rfl
  rw [this]
  exact (hq.div_const _).mul ((hc.neg).div_const _)


open Classical in
/-- **The coefficient of the linearized Regge action of the periodic Kuhn complex converges to the
Saint-Venant form.** For a smooth symmetric field `hf` of matrices on `ℝ³` invariant under integer translations,
`Q_n (h) → ∫_{[0,1]³} -¼ Σ h_ij ε_ikl ε_jmn ∂_k ∂_m h_ln` as `n → ∞`. -/
theorem Qn_converges {hf : (Fin 3 → ℝ) → Matrix (Fin 3) (Fin 3) ℝ}
    (hsm : ∀ i j, ContDiff ℝ 3 (fun y => hf y i j)) (hsymm : ∀ y i j, hf y i j = hf y j i)
    (hper : ∀ (p : Fin 3 → ℝ) (e : Fin 3 → ℤ), hf (p + fun i => (e i : ℝ)) = hf p) :
    ∀ δ : ℝ, 0 < δ → ∃ N0 : ℕ, ∀ (N : ℕ) [NeZero N] (hN : 3 ≤ N), N0 ≤ N →
      |Qn N (by omega) hf - ∫ y in unitCube, -(1 / 4) * svPair (Hm hf y) (dd2 hf y)| < δ := by
  intro δ hδ
  have hKc : IsCompact unitCube := isCompact_univ_pi fun _ => isCompact_Icc
  obtain ⟨M, r, hr, hcl⟩ := class_expansion hsm hsymm hKc
  obtain ⟨Cd, hCd0, hAc⟩ := hAt_close hsm
  -- bounds
  have hb1 : ∀ k : Fin 7, ∃ C : ℝ, ∀ v ∈ unitCube, |c2fun hf k v| ≤ C := fun k => by
    obtain ⟨C, hC⟩ := hKc.exists_bound_of_continuousOn (continuous_c2fun hsm k).continuousOn
    exact ⟨C, fun v hv => by simpa [Real.norm_eq_abs] using hC v hv⟩
  have hb2 : ∀ k : Fin 7, ∃ C : ℝ, ∀ v ∈ unitCube, |qf (Hm hf v) (dirs k)| ≤ C := fun k => by
    have hq : Continuous fun v => qf (Hm hf v) (dirs k) := by
      simp only [qf, Hm, Fin.sum_univ_three]
      have : ∀ i j, Continuous fun y => hf y i j := fun i j => (hsm i j).continuous
      fun_prop
    obtain ⟨C, hC⟩ := hKc.exists_bound_of_continuousOn hq.continuousOn
    exact ⟨C, fun v hv => by simpa [Real.norm_eq_abs] using hC v hv⟩
  choose C1 hC1 using hb1
  choose C2 hC2 using hb2
  set B : ℝ := ∑ k, (|C1 k| + |C2 k|) with hB
  have hB0 : 0 ≤ B := by positivity
  have hBk : ∀ k, |C1 k| + |C2 k| ≤ B := fun k =>
    Finset.single_le_sum (f := fun k => |C1 k| + |C2 k|) (fun j _ => by positivity) (Finset.mem_univ k)
  have hc2B : ∀ v ∈ unitCube, ∀ k, |c2fun hf k v| ≤ B := fun v hv k =>
    (hC1 k v hv).trans ((le_abs_self _).trans (by linarith [hBk k, abs_nonneg (C2 k)]))
  have hqB : ∀ v ∈ unitCube, ∀ k, |qf (Hm hf v) (dirs k)| ≤ B := fun v hv k =>
    (hC2 k v hv).trans ((le_abs_self _).trans (by linarith [hBk k, abs_nonneg (C1 k)]))
  set C4 : ℝ := Cd * (B + |M|) + B * |M| with hC4
  have hC40 : 0 ≤ C4 := by positivity
  -- the Riemann sum limit
  have hlim : Tendsto (fun N : ℕ => ∑ k : Fin 7, (∑ z : Fin 3 → Fin N, clsDens hf k (hingeMid N k z)) *
      (1 / (N : ℝ)) ^ 3) atTop (𝓝 (∑ k : Fin 7, ∫ y in unitCube, clsDens hf k y)) := by
    refine tendsto_finset_sum _ fun k _ => ?_
    exact riemann_sum_tendsto (continuous_clsDens hsm k).continuousOn (fun N z => hingeMid N k z)
      (fun N z => hingeMid_mem_cell (Fin.pos (z 0)) k z)
  have hint : ∑ k : Fin 7, ∫ y in unitCube, clsDens hf k y = ∫ y in unitCube, -(1 / 4) * svPair (Hm hf y) (dd2 hf y) := by
    rw [← MeasureTheory.integral_finset_sum _ (fun k _ => (continuous_clsDens hsm k).continuousOn.integrableOn_compact hKc)]
    refine MeasureTheory.setIntegral_congr_fun hKc.measurableSet fun y _ => ?_
    exact sum_clsDens hsm hsymm y
  rw [hint] at hlim
  obtain ⟨N1, hN1⟩ := Metric.tendsto_atTop.1 hlim (δ / 2) (half_pos hδ)
  obtain ⟨N2, hN2⟩ := exists_nat_gt (1 / r)
  obtain ⟨N3, hN3⟩ := exists_nat_gt (14 * C4 / δ)
  refine ⟨max (max N1 N2) (max N3 3), fun N _ hN hNN => ?_⟩
  have hN1' : N1 ≤ N := (le_max_left _ _).trans ((le_max_left _ _).trans hNN)
  have hN2' : N2 ≤ N := (le_max_right _ _).trans ((le_max_left _ _).trans hNN)
  have hN3' : N3 ≤ N := (le_max_left _ _).trans ((le_max_right _ _).trans hNN)
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hNr : 1 / r < N := lt_of_lt_of_le hN2 (by exact_mod_cast hN2')
  have hεr : 1 / (N : ℝ) ≤ r := by
    rw [div_le_iff₀ hNpos]; rw [div_lt_iff₀ hr] at hNr; linarith
  have hε1 : 1 / (N : ℝ) ≤ 1 := by
    rw [div_le_one hNpos]; exact_mod_cast (by omega : 1 ≤ N)
  have hε : 0 < 1 / (N : ℝ) := by positivity
  set ε : ℝ := 1 / (N : ℝ) with hεdef
  -- the pointwise estimate
  have hterm : ∀ (k : Fin 7) (z : Fin 3 → Fin N),
      |ε * (hAt hf ε (hingeMid N k z) k / (2 * wn k)) *
          (-(clsSum (dirs k) (fun σ h => dth h (atilV hf ε (hingeMid N k z) σ h))) / wn k) -
        ε ^ 3 * clsDens hf k (hingeMid N k z)| ≤ ε ^ 4 * C4 := by
    intro k z
    have hv : hingeMid N k z ∈ unitCube :=
      latticeCell_subset_unitCube (by omega) z (hingeMid_mem_cell (by omega) k z)
    have h1 := hAc _ hv ε hε hε1 k
    have h2 := hcl _ hv ε hε hεr k
    have h2' : |clsSum (dirs k) (fun σ h => dth h (atilV hf ε (hingeMid N k z) σ h)) -
        ε ^ 2 * c2fun hf k (hingeMid N k z)| ≤ |M| * ε ^ 3 :=
      h2.trans (mul_le_mul_of_nonneg_right (le_abs_self M) (by positivity))
    exact term_close _ _ _ _ Cd |M| B B ε (wn k) hε hε1 (one_le_wn k) h1 h2' (hc2B _ hv k)
      (hqB _ hv k) (abs_nonneg M) hCd0 hB0 hB0
  have hQ := Qn_lattice N hN hf hper
  have hcard : (Fintype.card (Fin 3 → Fin N) : ℝ) = (N : ℝ) ^ 3 := by simp
  have hsum : |Qn N (by omega) hf - ∑ k : Fin 7, (∑ z : Fin 3 → Fin N, clsDens hf k (hingeMid N k z)) * ε ^ 3| ≤
      7 * C4 * ε := by
    have e1 : Qn N (by omega) hf - ∑ k : Fin 7, (∑ z : Fin 3 → Fin N, clsDens hf k (hingeMid N k z)) * ε ^ 3 =
        ∑ k : Fin 7, ∑ z : Fin 3 → Fin N,
          (ε * (hAt hf ε (hingeMid N k z) k / (2 * wn k)) *
            (-(clsSum (dirs k) (fun σ h => dth h (atilV hf ε (hingeMid N k z) σ h))) / wn k) -
          ε ^ 3 * clsDens hf k (hingeMid N k z)) := by
      rw [hQ]
      simp only [Finset.sum_mul, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun z _ => ?_
      unfold clsSum
      ring
    rw [e1]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ k : Fin 7, |∑ z : Fin 3 → Fin N, (ε * (hAt hf ε (hingeMid N k z) k / (2 * wn k)) *
            (-(clsSum (dirs k) (fun σ h => dth h (atilV hf ε (hingeMid N k z) σ h))) / wn k) -
          ε ^ 3 * clsDens hf k (hingeMid N k z))|
        ≤ ∑ k : Fin 7, ∑ z : Fin 3 → Fin N, ε ^ 4 * C4 := by
          refine Finset.sum_le_sum fun k _ => ?_
          refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun z _ => hterm k z)
      _ = 7 * C4 * ε := by
          simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
          rw [hcard]
          have : (N : ℝ) ^ 3 * ε ^ 4 = ε := by
            rw [hεdef]; field_simp
          have h7 : (Fintype.card (Fin 7) : ℝ) = 7 := by simp
          rw [h7]
          calc (7 : ℝ) * ((N : ℝ) ^ 3 * (ε ^ 4 * C4)) = 7 * ((N : ℝ) ^ 3 * ε ^ 4) * C4 := by ring
            _ = 7 * C4 * ε := by rw [this]; ring
  have hsmall : 7 * C4 * ε < δ / 2 := by
    have : 14 * C4 / δ < N := lt_of_lt_of_le hN3 (by exact_mod_cast hN3')
    rw [div_lt_iff₀ hδ] at this
    rw [hεdef]
    rw [show 7 * C4 * (1 / (N : ℝ)) = 7 * C4 / N by ring, div_lt_iff₀ hNpos]
    linarith
  have h3 := hN1 N hN1'
  rw [Real.dist_eq] at h3
  have : |Qn N (by omega) hf - ∫ y in unitCube, -(1 / 4) * svPair (Hm hf y) (dd2 hf y)| ≤
      |Qn N (by omega) hf - ∑ k : Fin 7, (∑ z : Fin 3 → Fin N, clsDens hf k (hingeMid N k z)) * ε ^ 3| +
      |∑ k : Fin 7, (∑ z : Fin 3 → Fin N, clsDens hf k (hingeMid N k z)) * ε ^ 3 -
        ∫ y in unitCube, -(1 / 4) * svPair (Hm hf y) (dd2 hf y)| := by
    refine le_trans (le_of_eq ?_) (abs_add_le _ _)
    congr 1; ring
  linarith