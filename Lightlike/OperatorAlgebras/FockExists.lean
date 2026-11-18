import Lightlike.OperatorAlgebras.FockKernel
import Lightlike.OperatorAlgebras.GramUnitary
import Mathlib.Analysis.InnerProductSpace.Reproducing

/-!
# Existence of the Fock representation

Helper lemmas for `T-OP2-P1` (`Tasks/OP/T_OP2_P1.lean`).
-/

open scoped InnerProductSpace ComplexOrder ComplexConjugate

universe u

namespace Lightlike.OperatorAlgebras

variable {h : Type u} [NormedAddCommGroup h] [InnerProductSpace ℂ h]

/-- The Fock kernel as a matrix with entries in `ℂ →L[ℂ] ℂ`, for Mathlib's reproducing kernel Hilbert
spaces. -/
noncomputable def fockKer (h : Type u) [NormedAddCommGroup h] [InnerProductSpace ℂ h] :
    Matrix h h (ℂ →L[ℂ] ℂ) :=
  Matrix.of fun f g => fockGram f g • ContinuousLinearMap.id ℂ ℂ

lemma fockGram_conj' (f g : h) : fockGram g f = (starRingEnd ℂ) (fockGram f g) := by
  have h3 : (⟪g, f⟫_ℂ).im = -(⟪f, g⟫_ℂ).im := by
    have := inner_conj_symm (𝕜 := ℂ) g f
    rw [← this, Complex.conj_im]
  have h1 : symp h (-g) f = -symp h (-f) g := by
    simp only [symp, inner_neg_left, Complex.neg_im, h3]
  have h2 : ‖-g + f‖ = ‖-f + g‖ := by
    rw [← norm_neg]; congr 1; abel
  unfold fockGram
  rw [h1, h2]
  simp only [map_mul, ← Complex.exp_conj, map_neg, Complex.conj_I, Complex.conj_ofReal,
    map_ofNat, Complex.ofReal_neg]
  congr 2
  push_cast
  ring

theorem posSemidef_fockKer : (fockKer h).PosSemidef := by
  rw [RKHS.posSemidef_iff_re_sum_kernel']
  refine ⟨?_, fun vv => ?_⟩
  · ext i j
    simp only [Matrix.conjTranspose_apply, fockKer, Matrix.of_apply, star_smul, star_one]
    have hs : star (ContinuousLinearMap.id ℂ ℂ) = ContinuousLinearMap.id ℂ ℂ :=
      star_one (ℂ →L[ℂ] ℂ)
    simp only [hs, RCLike.star_def]
    rw [← fockGram_conj' j i]
  · have hq := (posSemidef_fockMat (h := h)).2 vv
    have : (vv.sum fun x w => vv.sum fun x' w' => ⟪fockKer h x' x w, w'⟫_ℂ) =
        vv.sum fun i a => vv.sum fun j b => star a * fockMat h i j * b := by
      refine Finsupp.sum_congr fun x _ => Finsupp.sum_congr fun x' _ => ?_
      simp only [fockKer, fockMat, Matrix.of_apply, ContinuousLinearMap.smul_apply,
        ContinuousLinearMap.id_apply, RCLike.inner_apply, smul_eq_mul, map_mul, RCLike.star_def]
      rw [fockGram_conj' x x']
      simp only [starRingEnd_self_apply]
      ring
    rw [this]
    exact (Complex.nonneg_iff.1 hq).1

instance fockFact : Fact (fockKer h).PosSemidef := ⟨posSemidef_fockKer⟩

/-- **The Fock space**: the reproducing kernel Hilbert space of the Fock kernel (Mathlib: `RKHS.OfKernel`). -/
abbrev FockSpace (h : Type u) [NormedAddCommGroup h] [InnerProductSpace ℂ h] : Type u :=
  RKHS.OfKernel (fockKer h)

noncomputable example : NormedAddCommGroup (FockSpace h) := inferInstance
noncomputable example : InnerProductSpace ℂ (FockSpace h) := inferInstance
example : CompleteSpace (FockSpace h) := inferInstance

/-- The kernel vector `k_f`, the image of `f` in the Fock space (`W f Ω` in the Fock representation). -/
noncomputable def kf (f : h) : FockSpace h := RKHS.kerFun (FockSpace h) f (1 : ℂ)

lemma inner_kf (f g : h) : ⟪kf f, kf g⟫_ℂ = fockGram f g := by
  have := RKHS.kernel_inner (FockSpace h) g f 1 1
  rw [RKHS.OfKernel.kernel_ofKernel] at this
  simp only [fockKer, Matrix.of_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.id_apply, smul_eq_mul, RCLike.inner_apply, map_one, mul_one, one_mul] at this
  have h2 : ⟪kf f, kf g⟫_ℂ = (starRingEnd ℂ) (fockGram g f) := by
    rw [kf, kf]; exact this.symm
  rw [h2, ← fockGram_conj']

/-- The Weyl phase `exp (-i σ(g, f) / 2)`. -/
noncomputable def fockPhase (g f : h) : ℂ := Complex.exp (-(Complex.I * (symp h g f / 2 : ℝ)))

lemma symp_add_left (f f' g : h) : symp h (f + f') g = symp h f g + symp h f' g := by
  simp [symp, inner_add_left]

lemma symp_add_right (f g g' : h) : symp h f (g + g') = symp h f g + symp h f g' := by
  simp [symp, inner_add_right]

lemma symp_zero_left (g : h) : symp h 0 g = 0 := by simp [symp]

lemma symp_zero_right (f : h) : symp h f 0 = 0 := by simp [symp]

lemma symp_antisymm (f g : h) : symp h f g = -symp h g f := by
  have := inner_conj_symm (𝕜 := ℂ) f g
  simp only [symp]
  rw [← this, Complex.conj_im]

/-- **The Weyl phase is a cocycle**: `ω(g, x) ω(f, x + g) = exp (-i σ(f, g) / 2) ω(f + g, x)`. -/
lemma fockPhase_cocycle (f g x : h) :
    fockPhase g x * fockPhase f (x + g) =
      Complex.exp (-(Complex.I * (symp h f g / 2 : ℝ))) * fockPhase (f + g) x := by
  unfold fockPhase
  rw [← Complex.exp_add, ← Complex.exp_add]
  congr 1
  rw [symp_add_right, symp_add_left]
  push_cast
  ring

/-- **The Gram matrix is invariant under the Weyl shift**:
`conj ω(g, f) ω(g, f') ⟪k_{f+g}, k_{f'+g}⟫ = ⟪k_f, k_{f'}⟫`. -/
lemma fockGram_shift (g f f' : h) :
    (starRingEnd ℂ) (fockPhase g f) * fockPhase g f' * fockGram (f + g) (f' + g) = fockGram f f' := by
  rw [fockGram_eq, fockGram_eq]
  unfold fockPhase gaussE
  rw [← Complex.exp_conj]
  simp only [Complex.ofReal_exp]
  simp only [mul_assoc, ← Complex.exp_add]
  congr 1
  have e1 : ‖f + g‖ ^ 2 = ‖f‖ ^ 2 + 2 * (⟪f, g⟫_ℂ).re + ‖g‖ ^ 2 := by
    have := norm_add_sq (𝕜 := ℂ) f g
    simpa using this
  have e2 : ‖f' + g‖ ^ 2 = ‖f'‖ ^ 2 + 2 * (⟪g, f'⟫_ℂ).re + ‖g‖ ^ 2 := by
    have := norm_add_sq (𝕜 := ℂ) f' g
    have h3 : RCLike.re ⟪f', g⟫_ℂ = (⟪g, f'⟫_ℂ).re := by rw [inner_re_symm]; rfl
    simpa [h3] using this
  have e6 : ⟪g, g⟫_ℂ = ((‖g‖ ^ 2 : ℝ) : ℂ) := by
    have := inner_self_eq_norm_sq_to_K (𝕜 := ℂ) g
    rw [this]; push_cast; rfl
  have e3 : ⟪f + g, f' + g⟫_ℂ = ⟪f, f'⟫_ℂ + ⟪f, g⟫_ℂ + ⟪g, f'⟫_ℂ + ((‖g‖ ^ 2 : ℝ) : ℂ) := by
    rw [inner_add_left, inner_add_right, inner_add_right, e6]; ring
  have e4 : symp h g f = -(⟪f, g⟫_ℂ).im := by rw [symp_antisymm]; simp [symp]
  have e5 : symp h g f' = (⟪g, f'⟫_ℂ).im := rfl
  rw [e3, e4, e5, e1, e2]
  generalize ⟪f, g⟫_ℂ = a
  generalize ⟪g, f'⟫_ℂ = b
  generalize ⟪f, f'⟫_ℂ = c
  obtain ⟨x1, y1⟩ := a
  obtain ⟨x2, y2⟩ := b
  have ha : (⟨x1, y1⟩ : ℂ) = (x1 : ℂ) + (y1 : ℂ) * Complex.I := by apply Complex.ext <;> simp
  have hb : (⟨x2, y2⟩ : ℂ) = (x2 : ℂ) + (y2 : ℂ) * Complex.I := by apply Complex.ext <;> simp
  dsimp only
  push_cast
  rw [ha, hb]
  ring_nf
  simp only [map_mul, Complex.conj_I, Complex.conj_ofReal, map_div₀, map_one, map_ofNat]
  ring

/-- The linear map `c ↦ ∑ c f • k_f` from finitely supported coefficients to the Fock space. -/
noncomputable def fockPhi (h : Type u) [NormedAddCommGroup h] [InnerProductSpace ℂ h] :
    (h →₀ ℂ) →ₗ[ℂ] FockSpace h := Finsupp.linearCombination ℂ kf

lemma fockPhi_single (f : h) : fockPhi h (Finsupp.single f 1) = kf f := by
  simp [fockPhi]

/-- The kernel vectors span a dense subspace of the Fock space. -/
lemma dense_range_fockPhi : Dense ((LinearMap.range (fockPhi h) : Submodule ℂ (FockSpace h)) : Set (FockSpace h)) := by
  have hd := RKHS.kerFun_dense (FockSpace h)
  rw [Submodule.dense_iff_topologicalClosure_eq_top]
  refine eq_top_iff.2 (hd ▸ Submodule.topologicalClosure_mono ?_)
  refine Submodule.span_le.2 ?_
  rintro _ ⟨x, v, rfl⟩
  have : RKHS.kerFun (FockSpace h) x v = v • kf x := by
    rw [kf, ← map_smul]; simp
  rw [this]
  exact Submodule.smul_mem _ _ ⟨Finsupp.single x 1, fockPhi_single x⟩

/-- The Weyl shift on finitely supported coefficients: `e_f ↦ ω(g, f) e_{f+g}`. -/
noncomputable def fockTau (g : h) : (h →₀ ℂ) →ₗ[ℂ] (h →₀ ℂ) :=
  Finsupp.linearCombination ℂ fun f => fockPhase g f • Finsupp.single (f + g) (1 : ℂ)

lemma fockTau_single (g f : h) :
    fockTau g (Finsupp.single f 1) = fockPhase g f • Finsupp.single (f + g) (1 : ℂ) := by
  simp [fockTau]

lemma fockPhi_tau_single (g f : h) :
    fockPhi h (fockTau g (Finsupp.single f 1)) = fockPhase g f • kf (f + g) := by
  rw [fockTau_single, map_smul, fockPhi_single]

lemma fockPhase_ne_zero (g f : h) : fockPhase g f ≠ 0 := Complex.exp_ne_zero _

lemma dense_range_fockPhi_tau (g : h) :
    Dense ((LinearMap.range ((fockPhi h).comp (fockTau g)) : Submodule ℂ (FockSpace h)) : Set (FockSpace h)) := by
  refine (dense_range_fockPhi (h := h)).mono ?_
  have hsub : LinearMap.range (fockPhi h) ≤ LinearMap.range ((fockPhi h).comp (fockTau g)) := by
    have hr : LinearMap.range (fockPhi h) = Submodule.span ℂ (Set.range kf) :=
      Finsupp.range_linearCombination _
    rw [hr, Submodule.span_le]
    rintro _ ⟨x, rfl⟩
    refine ⟨(fockPhase g (x - g))⁻¹ • Finsupp.single (x - g) (1 : ℂ), ?_⟩
    simp only [LinearMap.comp_apply, map_smul, fockTau_single, fockPhi_single, smul_smul, sub_add_cancel]
    rw [inv_mul_cancel₀ (fockPhase_ne_zero g _), one_smul]
  exact fun x hx => hsub hx

/-- **The Weyl unitary** `W g`: the unitary of the Fock space with `W g k_f = ω(g, f) k_{f+g}`. -/
theorem exists_fockWeyl (g : h) :
    ∃ U : FockSpace h ≃ₗᵢ[ℂ] FockSpace h, ∀ c, U (fockPhi h c) = fockPhi h (fockTau g c) := by
  refine exists_unitary_of_gram_eq (Φ₁ := fockPhi h) (Φ₂ := (fockPhi h).comp (fockTau g)) ?_
    dense_range_fockPhi (dense_range_fockPhi_tau g)
  intro f f'
  simp only [LinearMap.comp_apply, fockPhi_single, fockPhi_tau_single, inner_smul_left,
    inner_smul_right, inner_kf]
  rw [← fockGram_shift g f f']
  ring

/-- The Weyl unitary of `g` (a choice). -/
noncomputable def fockW (g : h) : FockSpace h ≃ₗᵢ[ℂ] FockSpace h := Classical.choose (exists_fockWeyl g)

lemma fockW_phi (g : h) (c : h →₀ ℂ) : fockW g (fockPhi h c) = fockPhi h (fockTau g c) :=
  Classical.choose_spec (exists_fockWeyl g) c

lemma fockW_kf (g f : h) : fockW g (kf f) = fockPhase g f • kf (f + g) := by
  rw [← fockPhi_single, fockW_phi, fockPhi_tau_single]

lemma fockPhase_zero_left (f : h) : fockPhase 0 f = 1 := by simp [fockPhase, symp_zero_left]

lemma fockPhase_zero_right (g : h) : fockPhase g 0 = 1 := by simp [fockPhase, symp_zero_right]

lemma fockTau_zero : fockTau (0 : h) = LinearMap.id := by
  refine Finsupp.lhom_ext fun f a => ?_
  rw [← Finsupp.smul_single_one, map_smul, fockTau_single, fockPhase_zero_left]
  simp

lemma fockTau_comp (f g : h) :
    (fockTau f).comp (fockTau g) =
      Complex.exp (-(Complex.I * (symp h f g / 2 : ℝ))) • fockTau (f + g) := by
  refine Finsupp.lhom_ext fun x a => ?_
  rw [← Finsupp.smul_single_one]
  simp only [LinearMap.comp_apply, map_smul, fockTau_single, LinearMap.smul_apply]
  simp only [smul_smul]
  rw [fockPhase_cocycle f g x, show x + (f + g) = x + g + f by abel]

lemma fockW_zero : fockW (0 : h) = LinearIsometryEquiv.refl ℂ (FockSpace h) := by
  refine LinearIsometryEquiv.ext fun ψ => ?_
  have hc1 : Continuous fun x : FockSpace h => fockW (0 : h) x := (fockW 0).continuous
  have := Continuous.ext_on (dense_range_fockPhi (h := h)) hc1 continuous_id (fun x hx => by
    obtain ⟨c, rfl⟩ := hx
    simp only [fockW_phi, fockTau_zero, LinearMap.id_apply, id_eq])
  exact congrFun this ψ

lemma fockW_weyl (f g : h) (ψ : FockSpace h) :
    fockW f (fockW g ψ) = Complex.exp (-(Complex.I * (symp h f g / 2 : ℝ))) • fockW (f + g) ψ := by
  have hc1 : Continuous fun x : FockSpace h => fockW f (fockW g x) :=
    (fockW f).continuous.comp (fockW g).continuous
  have hc2 : Continuous fun x : FockSpace h =>
      Complex.exp (-(Complex.I * (symp h f g / 2 : ℝ))) • fockW (f + g) x :=
    (fockW (f + g)).continuous.const_smul (Complex.exp (-(Complex.I * (symp h f g / 2 : ℝ))))
  have := Continuous.ext_on (dense_range_fockPhi (h := h)) hc1 hc2 (fun x hx => by
    obtain ⟨c, rfl⟩ := hx
    have h1 : fockTau f (fockTau g c) =
        Complex.exp (-(Complex.I * (symp h f g / 2 : ℝ))) • fockTau (f + g) c := by
      have := congrArg (fun L => L c) (fockTau_comp f g)
      simpa using this
    simp only [fockW_phi, map_smul, h1])
  exact congrFun this ψ

lemma fockW_kf_zero (f : h) : fockW f (kf 0) = kf f := by
  rw [fockW_kf, fockPhase_zero_right, one_smul, zero_add]

lemma fockGram_self (a : h) : fockGram a a = 1 := by
  unfold fockGram
  rw [symp_neg_self]
  simp

lemma continuous_fockGram : Continuous fun p : h × h => fockGram p.1 p.2 := by
  unfold fockGram symp
  fun_prop

lemma norm_sq_kf_sub (a b : h) : ‖kf a - kf b‖ ^ 2 = 2 - 2 * (fockGram a b).re := by
  have h1 : ⟪kf a - kf b, kf a - kf b⟫_ℂ =
      fockGram a a + fockGram b b - fockGram a b - fockGram b a := by
    simp only [inner_sub_left, inner_sub_right, inner_kf]; ring
  have h2 : ‖kf a - kf b‖ ^ 2 = (⟪kf a - kf b, kf a - kf b⟫_ℂ).re := by
    rw [inner_self_eq_norm_sq_to_K]; norm_cast
  rw [h2, h1, fockGram_self, fockGram_self, fockGram_conj' b a]
  simp; ring

lemma continuous_kf : Continuous (kf : h → FockSpace h) := by
  rw [continuous_iff_continuousAt]
  intro a
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  have hc : Continuous fun b : h => Real.sqrt (2 - 2 * (fockGram b a).re) := by
    have := continuous_fockGram.comp (continuous_id.prodMk (continuous_const (y := a)))
    exact (continuous_const.sub (continuous_const.mul (Complex.continuous_re.comp this))).sqrt
  have h0 : Real.sqrt (2 - 2 * (fockGram a a).re) = 0 := by simp [fockGram_self]
  have := hc.tendsto a
  rw [h0] at this
  refine this.congr fun b => ?_
  rw [← Real.sqrt_sq (norm_nonneg (kf b - kf a)), norm_sq_kf_sub]

/-- A family of isometries that is continuous on a dense set is strongly continuous. -/
lemma continuous_of_dense_isometries {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    {ι : Type*} [TopologicalSpace ι] (U : ι → K ≃ₗᵢ[ℂ] K) {D : Set K} (hd : Dense D)
    (hc : ∀ ψ ∈ D, Continuous fun t => U t ψ) (ψ : K) : Continuous fun t => U t ψ := by
  obtain ⟨u, hu, hlim⟩ := mem_closure_iff_seq_limit.1 (hd ψ)
  refine TendstoUniformly.continuous (F := fun n t => U t (u n)) (p := Filter.atTop)
    ?_ (Filter.Eventually.of_forall fun n => hc _ (hu n)).frequently
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  have := (Metric.tendsto_nhds.1 hlim) ε hε
  filter_upwards [this] with n hn t
  rw [dist_comm, LinearIsometryEquiv.dist_map]
  exact hn

lemma continuous_fockPhase_left (x : h) : Continuous fun g : h => fockPhase g x := by
  unfold fockPhase symp
  fun_prop

lemma continuous_fockW_line_kf (f x : h) : Continuous fun t : ℝ => fockW ((t : ℂ) • f) (kf x) := by
  simp only [fockW_kf]
  have hl : Continuous fun t : ℝ => (t : ℂ) • f := Complex.continuous_ofReal.smul continuous_const
  exact ((continuous_fockPhase_left x).comp hl).smul (continuous_kf.comp (continuous_const.add hl))

lemma continuous_fockW_line (f : h) (ψ : FockSpace h) : Continuous fun t : ℝ => fockW ((t : ℂ) • f) ψ := by
  refine continuous_of_dense_isometries (fun t : ℝ => fockW ((t : ℂ) • f))
    (dense_range_fockPhi (h := h)) (fun ψ hψ => ?_) ψ
  have hr : LinearMap.range (fockPhi h) = Submodule.span ℂ (Set.range kf) :=
    Finsupp.range_linearCombination _
  have hψ' : ψ ∈ Submodule.span ℂ (Set.range kf) := hr ▸ hψ
  clear hψ
  induction hψ' using Submodule.span_induction with
  | mem x hx => obtain ⟨y, rfl⟩ := hx; exact continuous_fockW_line_kf f y
  | zero => simp only [map_zero]; exact continuous_const
  | add x y _ _ hx hy => simp only [map_add]; exact hx.add hy
  | smul a x _ hx => simp only [map_smul]; exact hx.const_smul a

end Lightlike.OperatorAlgebras
