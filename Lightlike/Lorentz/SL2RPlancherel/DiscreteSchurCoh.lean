module

public import Lightlike.Lorentz.SL2RPlancherel.DiscreteSchurK

/-!
# The angular Fourier series of `⟨u, D_n(k_θ) y⟩`

For `u, y ∈ A²_n` the function `θ ↦ ⟨u, D_n(k_θ) y⟩` is the absolutely convergent trigonometric series
`Σ_l ⟨u, ê_l⟩ ⟨ê_l, y⟩ e^{-i(n+2l)θ}` in the orthonormal basis `ê_l = e_l/‖e_l‖` (`hasSum_inner_rot`).
-/

@[expose] public section

open MeasureTheory Set Complex Real UpperHalfPlane Lightlike.Lorentz.SL2R Lightlike.Lorentz
open scoped InnerProductSpace Manifold

noncomputable section

namespace Lightlike.Lorentz.SL2RPlancherel

lemma discreteAction_rot_kUnit {n : ℕ} (hn : 2 ≤ n) (l : ℕ) (θ : ℝ) :
    discreteAction n (rot θ) ((kUnit hn l : holoSubmodule n) : Hn n) =
      Complex.exp (-(((n + 2 * l : ℕ) : ℂ) * (θ : ℂ) * Complex.I)) • ((kUnit hn l : holoSubmodule n) : Hn n) := by
  show discreteAction n (rot θ) (((‖kClass hn l‖⁻¹ : ℝ) : ℂ) • kClass hn l) = _
  rw [map_smul, discreteAction_rot_kClass hn l θ]
  show _ = Complex.exp _ • (((‖kClass hn l‖⁻¹ : ℝ) : ℂ) • kClass hn l)
  rw [smul_comm]

/-- **The angular Fourier series of a matrix coefficient**: `⟨u, D(k_θ) y⟩ = Σ_l ⟨u, ê_l⟩ e^{-i(n+2l)θ} ⟨ê_l, y⟩`. -/
theorem hasSum_inner_rot {n : ℕ} (hn : 2 ≤ n) (u y : holoSubmodule n) (θ : ℝ) :
    HasSum (fun l : ℕ => ⟪(u : Hn n), (kUnit hn l : holoSubmodule n)⟫_ℂ *
        (Complex.exp (-(((n + 2 * l : ℕ) : ℂ) * (θ : ℂ) * Complex.I)) *
          ⟪((kUnit hn l : holoSubmodule n) : Hn n), (y : Hn n)⟫_ℂ))
      ⟪(u : Hn n), discreteAction n (rot θ) (y : Hn n)⟫_ℂ := by
  have hy' : discreteAction n (rot θ) (y : Hn n) ∈ holoSubmodule n :=
    discreteAction_mem_holoSubmodule n _ y.2
  have h := (kBasis hn).hasSum_inner_mul_inner u ⟨_, hy'⟩
  have hb : ∀ l, (kBasis hn) l = kUnit hn l := fun l =>
    congrFun (HilbertBasis.coe_mk (kUnit_orthonormal hn) (kUnit_span_top hn)) l
  simp only [hb] at h
  convert h using 1
  · funext l
    congr 1
    simp only [Submodule.coe_inner]
    show _ = ⟪((kUnit hn l : holoSubmodule n) : Hn n), discreteAction n (rot θ) (y : Hn n)⟫_ℂ
    rw [inner_discreteAction_rot, discreteAction_rot_kUnit hn l (-θ), inner_smul_left]
    have h1 : (starRingEnd ℂ) (Complex.exp (-(((n + 2 * l : ℕ) : ℂ) * ((-θ : ℝ) : ℂ) * Complex.I))) =
        Complex.exp (-(((n + 2 * l : ℕ) : ℂ) * (θ : ℂ) * Complex.I)) := by
      rw [← Complex.exp_conj]
      congr 1
      simp only [map_neg, map_mul, Complex.conj_natCast, Complex.conj_ofReal, Complex.conj_I]
      push_cast; ring
    rw [h1]
  · rw [Submodule.coe_inner]

lemma rot_neg_mul_rot (α : ℝ) : rot (-α) * rot α = 1 := by
  rw [← rot_add, neg_add_cancel, rot_zero]

lemma rot_inv' (α : ℝ) : (rot α)⁻¹ = rot (-α) :=
  inv_eq_of_mul_eq_one_right (by rw [← rot_add, add_neg_cancel, rot_zero])

lemma inner_discreteAction_inv (n : ℕ) (g : SL2R) (x y : Hn n) :
    ⟪x, discreteAction n g y⟫_ℂ = ⟪discreteAction n g⁻¹ x, y⟫_ℂ := by
  have h := discreteAction_inner n g⁻¹ x (discreteAction n g y)
  rw [← discreteAction_mul', inv_mul_cancel, discreteAction_one'] at h
  exact h.symm

/-- The coefficient of `e_l` in the coherent vector `D_n(diag(A, 1/A)) e₀`. -/
def cohCoeff (n : ℕ) (A : ℝ) (l : ℕ) : ℂ :=
  (gam n A : ℂ) * ((Nat.choose (n - 1 + l) (n - 1) : ℂ) * (-(tpar A : ℂ)) ^ l)

/-- **The angular series of the coherent matrix coefficient**: with `E = D_n(diag(A, 1/A)) e₀` and `α = 2π x₀`,
`θ = 2π x₁`, `⟨e_j, D(k_α a(ξ) k_θ) E⟩ = Σ_l e^{-i(n+2j)α} e^{-i(n+2l)θ} γ_A C_l (-t_A)^l ⟨e_j, D(a(ξ)) e_l⟩`. -/
theorem hasSum_kkProfile_coh {n : ℕ} (hn : 2 ≤ n) (j : ℕ) {A : ℝ} (hA : 0 < A) (ξ : ℝ) (x : Fin 2 → ℝ) :
    HasSum (fun l : ℕ => Complex.exp (-(2 * π * Complex.I * ∑ i, ((kkWeight n j l) i : ℂ) * (x i : ℂ))) *
        (cohCoeff n A l * mcoef n (kClass hn j) (kClass hn l) (aR ξ)))
      (kkProfile (mcoef n (kClass hn j) (discreteAction n (diagSL A hA.ne') (lowestClass hn))) ξ x) := by
  set E : holoSubmodule n := ⟨discreteAction n (diagSL A hA.ne') (lowestClass hn),
    discreteAction_mem_holoSubmodule n _ (lowestClass_mem hn)⟩ with hE
  set α : ℝ := 2 * π * x 0 with hα
  set θ : ℝ := 2 * π * x 1 with hθ
  set g : SL2R := rot α * aR ξ with hg
  have hgmem : discreteAction n g⁻¹ (kClass hn j) ∈ holoSubmodule n :=
    discreteAction_mem_holoSubmodule n _ (kClass_mem hn j)
  set u : holoSubmodule n := ⟨discreteAction n g⁻¹ (kClass hn j), hgmem⟩ with hu
  have h := hasSum_inner_rot hn u E θ
  have hval : ⟪(u : Hn n), discreteAction n (rot θ) (E : Hn n)⟫_ℂ =
      kkProfile (mcoef n (kClass hn j) (discreteAction n (diagSL A hA.ne') (lowestClass hn))) ξ x := by
    unfold kkProfile mcoef
    show _ = ⟪kClass hn j, discreteAction n (rot α * aR ξ * rot θ) _⟫_ℂ
    rw [discreteAction_mul' n (rot α * aR ξ) (rot θ), inner_discreteAction_inv n (rot α * aR ξ)]
  rw [← hval]
  convert h using 1
  funext l
  have hne : ((‖kClass hn l‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (norm_kClass_pos hn l).ne'
  -- the pairing of `u` with `ê_l`
  have hT1 : ⟪(u : Hn n), ((kUnit hn l : holoSubmodule n) : Hn n)⟫_ℂ =
      ((‖kClass hn l‖⁻¹ : ℝ) : ℂ) * (Complex.exp (-(((n + 2 * j : ℕ) : ℂ) * (α : ℂ) * Complex.I)) *
        mcoef n (kClass hn j) (kClass hn l) (aR ξ)) := by
    show ⟪discreteAction n g⁻¹ (kClass hn j), ((‖kClass hn l‖⁻¹ : ℝ) : ℂ) • kClass hn l⟫_ℂ = _
    rw [← inner_discreteAction_inv, map_smul, inner_smul_right]
    congr 1
    have := mcoef_rot hn j l α 0 (aR ξ)
    rw [rot_zero, mul_one] at this
    unfold mcoef at this ⊢
    rw [hg, this]
    simp
  have hT2 : ⟪((kUnit hn l : holoSubmodule n) : Hn n), (E : Hn n)⟫_ℂ =
      ((‖kClass hn l‖⁻¹ : ℝ) : ℂ) * (cohCoeff n A l * ((‖kClass hn l‖ ^ 2 : ℝ) : ℂ)) := by
    show ⟪((‖kClass hn l‖⁻¹ : ℝ) : ℂ) • kClass hn l, discreteAction n (diagSL A hA.ne') (lowestClass hn)⟫_ℂ = _
    rw [inner_smul_left, Complex.conj_ofReal, inner_kClass_diag_lowest hn hA l]
    rfl
  have hexp : Complex.exp (-(2 * π * Complex.I * ∑ i, ((kkWeight n j l) i : ℂ) * (x i : ℂ))) =
      Complex.exp (-(((n + 2 * j : ℕ) : ℂ) * (α : ℂ) * Complex.I)) *
        Complex.exp (-(((n + 2 * l : ℕ) : ℂ) * (θ : ℂ) * Complex.I)) := by
    rw [← Complex.exp_add]
    congr 1
    simp only [kkWeight, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, hα, hθ]
    push_cast
    ring
  rw [hexp]
  try simp only [Submodule.coe_inner] at hT1 hT2 ⊢
  rw [hT1, hT2]
  have hr : ((‖kClass hn l‖⁻¹ : ℝ) : ℂ) * ((‖kClass hn l‖⁻¹ : ℝ) : ℂ) * ((‖kClass hn l‖ ^ 2 : ℝ) : ℂ) = 1 := by
    push_cast
    field_simp
  linear_combination (-(Complex.exp (-(((n + 2 * j : ℕ) : ℂ) * (α : ℂ) * Complex.I)) *
    Complex.exp (-(((n + 2 * l : ℕ) : ℂ) * (θ : ℂ) * Complex.I)) * cohCoeff n A l *
    mcoef n (kClass hn j) (kClass hn l) (aR ξ))) * hr

lemma norm_exp_char (m : Fin 2 → ℤ) (x : Fin 2 → ℝ) :
    ‖Complex.exp (-(2 * π * Complex.I * ∑ i, (m i : ℂ) * (x i : ℂ)))‖ = 1 := by
  have : -(2 * π * Complex.I * ∑ i, (m i : ℂ) * (x i : ℂ)) =
      ((-(2 * π * ∑ i, (m i : ℝ) * x i) : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [this, Complex.norm_exp_ofReal_mul_I]

lemma kkWeight_injective (n j : ℕ) : Function.Injective fun l : ℕ => -kkWeight n j l := by
  intro l l' h
  have h1 := congrFun h 1
  simp [kkWeight] at h1
  omega

lemma kkWeight_add_eq_zero (n j l l' : ℕ) : -kkWeight n j l + kkWeight n j l' = 0 ↔ l = l' := by
  constructor
  · intro h
    exact kkWeight_injective n j (by
      have : kkWeight n j l' = kkWeight n j l := by
        have := congrArg (fun z => z + kkWeight n j l) h
        simpa [add_assoc] using this
      show -kkWeight n j l = -kkWeight n j l'
      rw [this])
  · rintro rfl; simp

/-- **The `K × K`-Fourier components of the coherent matrix coefficient**:
`F_{(m, m')}(ξ) = Σ_l [m = -(n+2j, n+2l)] γ_A C_l (-t_A)^l ⟨e_j, D(a(ξ)) e_l⟩`. -/
theorem kkCoeff_coh {n : ℕ} (hn : 2 ≤ n) (j : ℕ) {A : ℝ} (hA : 0 < A) (ξ : ℝ) (m : Fin 2 → ℤ) :
    kkCoeff (mcoef n (kClass hn j) (discreteAction n (diagSL A hA.ne') (lowestClass hn))) m ξ =
      ∑' l : ℕ, (if m + kkWeight n j l = 0 then
        cohCoeff n A l * mcoef n (kClass hn j) (kClass hn l) (aR ξ) else 0) := by
  set c : ℕ → ℂ := fun l => cohCoeff n A l * mcoef n (kClass hn j) (kClass hn l) (aR ξ) with hc
  have hsumm : Summable (fun l => ‖c l‖) := by
    have h0 := (hasSum_kkProfile_coh hn j hA ξ 0).summable
    have h1 := summable_norm_iff.2 h0
    refine h1.congr (fun l => ?_)
    rw [norm_mul, norm_exp_char, one_mul]
  unfold kkCoeff
  set F : ℕ → (Fin 2 → ℝ) → ℂ := fun l x =>
    Complex.exp (-(2 * π * Complex.I * ∑ i, (m i : ℂ) * (x i : ℂ))) *
      (Complex.exp (-(2 * π * Complex.I * ∑ i, ((kkWeight n j l) i : ℂ) * (x i : ℂ))) * c l) with hF
  have hFc : ∀ l, Continuous (F l) := fun l => by
    simp only [hF]
    fun_prop
  have hbox : MeasurableSet box := by
    have : box = Set.pi univ (fun _ : Fin 2 => Ioc (0 : ℝ) (0 + 1)) := by
      ext x; simp [box]
    rw [this]; exact MeasurableSet.univ_pi (fun _ => measurableSet_Ioc)
  have hboxsub : box ⊆ Icc (0 : Fin 2 → ℝ) 1 := by
    intro x hx
    constructor <;> intro i
    · exact le_of_lt (by simpa using (hx i).1)
    · simpa using (hx i).2
  have hint : ∀ l, Integrable (F l) (volume.restrict box) := fun l =>
    ((hFc l).integrableOn_Icc).mono_set hboxsub
  have hnormF : ∀ l x, ‖F l x‖ = ‖c l‖ := fun l x => by
    simp only [hF, norm_mul, norm_exp_char, one_mul]
  have hsum2 : Summable fun l => ∫ x in box, ‖F l x‖ := by
    have : (fun l => ∫ x in box, ‖F l x‖) = fun l => ‖c l‖ * (volume box).toReal := by
      funext l
      simp only [hnormF, setIntegral_const, smul_eq_mul, Measure.real, mul_comm]
    rw [this]
    exact hsumm.mul_right _
  have hS := hasSum_integral_of_summable_integral_norm hint hsum2
  have hpt : ∀ x, ∑' l, F l x = Complex.exp (-(2 * π * Complex.I * ∑ i, (m i : ℂ) * (x i : ℂ))) *
      kkProfile (mcoef n (kClass hn j) (discreteAction n (diagSL A hA.ne') (lowestClass hn))) ξ x := by
    intro x
    exact ((hasSum_kkProfile_coh hn j hA ξ x).mul_left _).tsum_eq
  have hFl : ∀ l, ∫ x in box, F l x = if m + kkWeight n j l = 0 then c l else 0 := by
    intro l
    have h1 : ∀ x : Fin 2 → ℝ, F l x = c l *
        Complex.exp (-(2 * π * Complex.I * ∑ i, (((m + kkWeight n j l) i : ℤ) : ℂ) * (x i : ℂ))) := by
      intro x
      simp only [hF]
      have hexp : Complex.exp (-(2 * π * Complex.I * ∑ i, (((m + kkWeight n j l) i : ℤ) : ℂ) * (x i : ℂ))) =
          Complex.exp (-(2 * π * Complex.I * ∑ i, (m i : ℂ) * (x i : ℂ))) *
            Complex.exp (-(2 * π * Complex.I * ∑ i, ((kkWeight n j l) i : ℂ) * (x i : ℂ))) := by
        rw [← Complex.exp_add]
        congr 1
        simp only [Pi.add_apply, Int.cast_add, add_mul, Finset.sum_add_distrib]
        ring
      rw [hexp]
      ring
    simp_rw [h1]
    rw [integral_const_mul, integral_box_char]
    by_cases h : m + kkWeight n j l = 0
    · simp [h]
    · simp [h]
  simp_rw [hpt] at hS
  have := hS.tsum_eq
  simp_rw [hFl] at this
  exact this.symm

end Lightlike.Lorentz.SL2RPlancherel
