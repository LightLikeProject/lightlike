import Lightlike.OperatorAlgebras.FockExists
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Irreducibility of the Fock representation

Helper lemmas for `T-OP2-P4` (`Tasks/OP/T_OP2_P4.lean`): every nonzero vector of a Fock representation is
cyclic for the Weyl unitaries. The route is in the plan note: for a bounded operator `C` commuting with all
`W f`, the function `F_χ(x) = ⟪W x Ω, χ⟫ / exp (-‖x‖² / 4)` of `χ = C Ω` is antiholomorphic along complex
lines, and so is that of `C* Ω`; but `F_χ(-b) = conj (F_{C* Ω}(b))`, so `F_χ` is holomorphic and antiholomorphic
along complex lines, hence constant, hence `C Ω` is a multiple of `Ω` and `C` is a scalar.
-/

open scoped InnerProductSpace ComplexConjugate
open Filter Topology

universe u

namespace Lightlike.OperatorAlgebras

/-- **A function on `ℂ` that is holomorphic and antiholomorphic is constant.** -/
lemma const_of_holo_antiholo {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hg : Differentiable ℂ fun z => (starRingEnd ℂ) (f z)) : ∀ z w, f z = f w := by
  have hd : ∀ z, deriv f z = 0 := by
    intro z
    set a := deriv f z with ha
    have h1 : HasDerivAt f a (z + ((0 : ℝ) : ℂ)) := by
      rw [Complex.ofReal_zero, add_zero]; exact (hf z).hasDerivAt
    set b := deriv (fun z => (starRingEnd ℂ) (f z)) z with hb
    have h2 : HasDerivAt (fun z => (starRingEnd ℂ) (f z)) b (z + ((0 : ℝ) : ℂ)) := by
      rw [Complex.ofReal_zero, add_zero]; exact (hg z).hasDerivAt
    have hr : HasDerivAt (fun t : ℝ => z + (t : ℂ)) 1 0 :=
      ((hasDerivAt_id (0 : ℝ)).ofReal_comp).const_add z
    have hi : HasDerivAt (fun t : ℝ => z + Complex.I * (t : ℂ)) Complex.I 0 := by
      simpa using (((hasDerivAt_id (0 : ℝ)).ofReal_comp).const_mul Complex.I).const_add z
    have hi1 : HasDerivAt (fun t : ℝ => z + Complex.I * (t : ℂ)) Complex.I 0 := hi
    -- real direction
    have r1 : HasDerivAt (fun t : ℝ => f (z + (t : ℂ))) a 0 := by
      have := h1.scomp (0 : ℝ) hr
      rw [one_smul] at this
      exact this
    have r2 : HasDerivAt (fun t : ℝ => (starRingEnd ℂ) (f (z + (t : ℂ)))) b 0 := by
      have := h2.scomp (0 : ℝ) hr
      rw [one_smul] at this
      exact this
    have r3 : HasDerivAt (fun t : ℝ => (starRingEnd ℂ) (f (z + (t : ℂ)))) ((starRingEnd ℂ) a) 0 :=
      r1.star
    have hba : b = (starRingEnd ℂ) a := r2.unique r3
    -- imaginary direction
    have h1i : HasDerivAt f a (z + Complex.I * ((0 : ℝ) : ℂ)) := by
      rw [Complex.ofReal_zero, mul_zero, add_zero]; exact (hf z).hasDerivAt
    have h2i : HasDerivAt (fun z => (starRingEnd ℂ) (f z)) b (z + Complex.I * ((0 : ℝ) : ℂ)) := by
      rw [Complex.ofReal_zero, mul_zero, add_zero]; exact (hg z).hasDerivAt
    have i1 : HasDerivAt (fun t : ℝ => f (z + Complex.I * (t : ℂ))) (Complex.I * a) 0 := by
      have := h1i.scomp (0 : ℝ) hi1
      rw [smul_eq_mul] at this
      exact this
    have i2 : HasDerivAt (fun t : ℝ => (starRingEnd ℂ) (f (z + Complex.I * (t : ℂ)))) (Complex.I * b) 0 := by
      have := h2i.scomp (0 : ℝ) hi1
      rw [smul_eq_mul] at this
      exact this
    have i3 : HasDerivAt (fun t : ℝ => (starRingEnd ℂ) (f (z + Complex.I * (t : ℂ))))
        ((starRingEnd ℂ) (Complex.I * a)) 0 := i1.star
    have hba' : Complex.I * b = (starRingEnd ℂ) (Complex.I * a) := i2.unique i3
    rw [map_mul, Complex.conj_I, hba] at hba'
    have : (starRingEnd ℂ) a = 0 := by
      have h3 : Complex.I * (starRingEnd ℂ) a = -Complex.I * (starRingEnd ℂ) a := hba'
      have h4 : (2 * Complex.I) * (starRingEnd ℂ) a = 0 := by linear_combination h3
      have h5 : (2 * Complex.I) ≠ 0 := by simp
      exact (mul_eq_zero.1 h4).resolve_left h5
    simpa using this
  intro z w
  exact is_const_of_deriv_eq_zero hf hd z w

variable {h : Type u} [NormedAddCommGroup h] [InnerProductSpace ℂ h]
  {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K]

/-- The vectors `k_f = W f Ω` of a Fock representation. -/
def kv (R : FockRep h K) (f : h) : K := R.W f R.Ω

lemma inner_kv (R : FockRep h K) (a b : h) : ⟪kv R a, kv R b⟫_ℂ = fockGram a b := R.inner_W_Ω a b

/-- The function `F_χ(x) = ⟪k_x, χ⟫ / exp (-‖x‖² / 4)`. -/
noncomputable def FF (R : FockRep h K) (χ : K) (x : h) : ℂ := ⟪kv R x, χ⟫_ℂ / (gaussE x : ℂ)

omit [InnerProductSpace ℂ h] in
lemma gaussE_pos (x : h) : 0 < gaussE x := Real.exp_pos _

lemma gaussE_ne (x : h) : (gaussE x : ℂ) ≠ 0 := by
  have := (gaussE_pos x).ne'
  exact_mod_cast this

/-- For `χ = k_f`: `F_χ(x) = e(f) exp (⟪x, f⟫ / 2)`. -/
lemma FF_kv (R : FockRep h K) (f x : h) :
    FF R (kv R f) x = (gaussE f : ℂ) * Complex.exp (⟪x, f⟫_ℂ / 2) := by
  unfold FF
  rw [inner_kv, fockGram_eq]
  field_simp [gaussE_ne x]

/-- **`F_{k_f}` is antiholomorphic along complex lines.** -/
lemma differentiable_conj_FF_kv (R : FockRep h K) (f x v : h) :
    Differentiable ℂ fun z : ℂ => (starRingEnd ℂ) (FF R (kv R f) (x + z • v)) := by
  have : (fun z : ℂ => (starRingEnd ℂ) (FF R (kv R f) (x + z • v))) =
      fun z : ℂ => (gaussE f : ℂ) * Complex.exp ((⟪f, x⟫_ℂ + z * ⟪f, v⟫_ℂ) / 2) := by
    funext z
    rw [FF_kv, map_mul, Complex.conj_ofReal, ← Complex.exp_conj]
    congr 2
    rw [map_div₀, inner_add_left, inner_smul_left]
    simp [inner_conj_symm, map_ofNat]
  rw [this]
  fun_prop

lemma differentiable_conj_FF_span (R : FockRep h K) {χ : K}
    (hχ : χ ∈ Submodule.span ℂ (Set.range (kv R))) (x v : h) :
    Differentiable ℂ fun z : ℂ => (starRingEnd ℂ) (FF R χ (x + z • v)) := by
  induction hχ using Submodule.span_induction with
  | mem y hy => obtain ⟨f, rfl⟩ := hy; exact differentiable_conj_FF_kv R f x v
  | zero => simp [FF]
  | add a b _ _ ha hb =>
    have : (fun z : ℂ => (starRingEnd ℂ) (FF R (a + b) (x + z • v))) =
        fun z => (starRingEnd ℂ) (FF R a (x + z • v)) + (starRingEnd ℂ) (FF R b (x + z • v)) := by
      funext z; simp [FF, inner_add_right, add_div]
    rw [this]; exact ha.add hb
  | smul c a _ ha =>
    have : (fun z : ℂ => (starRingEnd ℂ) (FF R (c • a) (x + z • v))) =
        fun z => (starRingEnd ℂ) c * (starRingEnd ℂ) (FF R a (x + z • v)) := by
      funext z; simp [FF, inner_smul_right, mul_div_assoc]
    rw [this]; exact ha.const_mul _

lemma norm_kv (R : FockRep h K) (f : h) : ‖kv R f‖ = 1 := by
  unfold kv
  rw [(R.W f).norm_map, R.norm_Ω]

lemma norm_FF_sub_le (R : FockRep h K) (χ u : K) (y : h) :
    ‖FF R χ y - FF R u y‖ ≤ ‖χ - u‖ / gaussE y := by
  unfold FF
  rw [← sub_div, ← inner_sub_right, norm_div, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (gaussE_pos y)]
  refine div_le_div_of_nonneg_right ?_ (gaussE_pos y).le
  calc ‖⟪kv R y, χ - u⟫_ℂ‖ ≤ ‖kv R y‖ * ‖χ - u‖ := norm_inner_le_norm _ _
    _ = ‖χ - u‖ := by rw [norm_kv, one_mul]

/-- **`F_χ` is antiholomorphic along complex lines** for every vector `χ`: a locally uniform limit of the
antiholomorphic `F_u`, `u` in the span of the `k_f`, since `|F_χ(y) - F_u(y)| ≤ ‖χ - u‖ exp (‖y‖² / 4)`. -/
theorem differentiable_conj_FF (R : FockRep h K) (χ : K) (x v : h) :
    Differentiable ℂ fun z : ℂ => (starRingEnd ℂ) (FF R χ (x + z • v)) := by
  have hmem : χ ∈ closure ((Submodule.span ℂ (Set.range (kv R)) : Submodule ℂ K) : Set K) := by
    have this : (Submodule.span ℂ (Set.range (kv R))).topologicalClosure = ⊤ := R.cyclic
    rw [← Submodule.topologicalClosure_coe, this]; trivial
  obtain ⟨u, hu, hlim⟩ := mem_closure_iff_seq_limit.1 hmem
  have hF : ∀ n, Differentiable ℂ fun z : ℂ => (starRingEnd ℂ) (FF R (u n) (x + z • v)) :=
    fun n => differentiable_conj_FF_span R (hu n) x v
  have hloc : TendstoLocallyUniformlyOn (fun (n : ℕ) (z : ℂ) => (starRingEnd ℂ) (FF R (u n) (x + z • v)))
      (fun z : ℂ => (starRingEnd ℂ) (FF R χ (x + z • v))) atTop Set.univ := by
    rw [tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_univ]
    intro Kc _ hKc
    obtain ⟨r, hr⟩ := (Metric.isBounded_iff_subset_closedBall (0 : ℂ)).1 hKc.isBounded
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    set ρ : ℝ := ‖x‖ + r * ‖v‖ with hρ
    set M : ℝ := Real.exp (ρ ^ 2 / 4) + 1 with hM
    have hMpos : 0 < M := by positivity
    have h1 := (Metric.tendsto_nhds.1 hlim) (ε / M) (by positivity)
    filter_upwards [h1] with n hn z hz
    have hzr : ‖z‖ ≤ r := by simpa using hr hz
    have hy : ‖x + z • v‖ ≤ ρ := by
      calc ‖x + z • v‖ ≤ ‖x‖ + ‖z • v‖ := norm_add_le _ _
        _ = ‖x‖ + ‖z‖ * ‖v‖ := by rw [norm_smul]
        _ ≤ ‖x‖ + r * ‖v‖ := by gcongr
    have hg : (gaussE (x + z • v))⁻¹ ≤ Real.exp (ρ ^ 2 / 4) := by
      unfold gaussE
      rw [← Real.exp_neg, neg_neg]
      refine Real.exp_le_exp.2 ?_
      have : ‖x + z • v‖ ^ 2 ≤ ρ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hy 2
      linarith
    have hdist : ‖χ - u n‖ < ε / M := by rw [← dist_eq_norm, dist_comm]; exact hn
    calc dist ((starRingEnd ℂ) (FF R χ (x + z • v))) ((starRingEnd ℂ) (FF R (u n) (x + z • v)))
        = ‖FF R χ (x + z • v) - FF R (u n) (x + z • v)‖ := by
          rw [dist_eq_norm, ← map_sub]; exact RCLike.norm_conj _
      _ ≤ ‖χ - u n‖ / gaussE (x + z • v) := norm_FF_sub_le R χ (u n) _
      _ = ‖χ - u n‖ * (gaussE (x + z • v))⁻¹ := div_eq_mul_inv _ _
      _ ≤ ‖χ - u n‖ * Real.exp (ρ ^ 2 / 4) := by gcongr
      _ ≤ ‖χ - u n‖ * M := by gcongr; linarith
      _ < ε := by
        calc ‖χ - u n‖ * M < ε / M * M := by gcongr
          _ = ε := by field_simp
  have := hloc.differentiableOn (Eventually.of_forall fun n => (hF n).differentiableOn) isOpen_univ
  exact differentiableOn_univ.1 this

section Commutant

omit [InnerProductSpace ℂ h] in
lemma gaussE_neg' (x : h) : gaussE (-x) = gaussE x := by simp [gaussE]

variable [CompleteSpace K]

lemma kv_zero (R : FockRep h K) : kv R 0 = R.Ω := by
  unfold kv; rw [R.W_zero]; rfl

lemma FF_zero (R : FockRep h K) (χ : K) : FF R χ 0 = ⟪R.Ω, χ⟫_ℂ := by
  unfold FF; rw [kv_zero]; simp [gaussE]

/-- For `C` commuting with the Weyl unitaries, `F_{C Ω}(-b) = conj F_{C† Ω}(b)`. -/
lemma FF_commutant (R : FockRep h K) (C : K →L[ℂ] K) (hC : ∀ f ψ, C (R.W f ψ) = R.W f (C ψ)) (b : h) :
    FF R (C R.Ω) (-b) = (starRingEnd ℂ) (FF R ((ContinuousLinearMap.adjoint C) R.Ω) b) := by
  have h1 : ⟪R.Ω, C (kv R b)⟫_ℂ = ⟪kv R (-b), C R.Ω⟫_ℂ := by
    unfold kv
    rw [hC, ← (R.W (-b)).inner_map_map, R.toCCRRep.W_neg_W]
  have h2 : ⟪R.Ω, C (kv R b)⟫_ℂ = (starRingEnd ℂ) ⟪kv R b, (ContinuousLinearMap.adjoint C) R.Ω⟫_ℂ := by
    rw [inner_conj_symm (𝕜 := ℂ), ContinuousLinearMap.adjoint_inner_left]
  unfold FF
  rw [← h1, h2, map_div₀, Complex.conj_ofReal, gaussE_neg']

/-- **`F_{C Ω}` is constant**, by holomorphy and antiholomorphy along complex lines. -/
lemma FF_const (R : FockRep h K) (C : K →L[ℂ] K) (hC : ∀ f ψ, C (R.W f ψ) = R.W f (C ψ)) (x : h) :
    FF R (C R.Ω) x = ⟪R.Ω, C R.Ω⟫_ℂ := by
  have key : ∀ x₀ v : h, FF R (C R.Ω) x₀ = FF R (C R.Ω) (x₀ + v) := by
    intro x₀ v
    have h1 := differentiable_conj_FF R (C R.Ω) x₀ v
    have h2 : Differentiable ℂ fun z : ℂ => FF R (C R.Ω) (x₀ + z • v) := by
      have e : (fun z : ℂ => FF R (C R.Ω) (x₀ + z • v)) =
          fun z : ℂ => (starRingEnd ℂ) (FF R ((ContinuousLinearMap.adjoint C) R.Ω) (-x₀ + z • (-v))) := by
        funext z
        have := FF_commutant R C hC (-x₀ + z • (-v))
        rw [show -(-x₀ + z • (-v)) = x₀ + z • v by rw [smul_neg, neg_add, neg_neg, neg_neg]] at this
        exact this
      rw [e]
      exact differentiable_conj_FF R ((ContinuousLinearMap.adjoint C) R.Ω) (-x₀) (-v)
    have := const_of_holo_antiholo h2 h1 0 1
    simpa using this
  have := key 0 x
  rw [zero_add, FF_zero] at this
  exact this.symm

/-- `C Ω` is a multiple of `Ω`. -/
lemma commutant_apply_Omega (R : FockRep h K) (C : K →L[ℂ] K)
    (hC : ∀ f ψ, C (R.W f ψ) = R.W f (C ψ)) : C R.Ω = ⟪R.Ω, C R.Ω⟫_ℂ • R.Ω := by
  set c := ⟪R.Ω, C R.Ω⟫_ℂ with hc
  have horth : ∀ x : h, ⟪kv R x, C R.Ω - c • R.Ω⟫_ℂ = 0 := by
    intro x
    have h1 : ⟪kv R x, C R.Ω⟫_ℂ = c * (gaussE x : ℂ) := by
      have := FF_const R C hC x
      unfold FF at this
      rw [div_eq_iff (gaussE_ne x)] at this
      rw [this]
    have h2 : ⟪kv R x, R.Ω⟫_ℂ = (gaussE x : ℂ) := by
      have := inner_kv R x 0
      rw [kv_zero] at this
      rw [this, fockGram_eq]
      simp [gaussE]
    rw [inner_sub_right, inner_smul_right, h1, h2]; ring
  have hspan : ∀ u ∈ Submodule.span ℂ (Set.range (kv R)), ⟪u, C R.Ω - c • R.Ω⟫_ℂ = 0 := by
    intro u hu
    induction hu using Submodule.span_induction with
    | mem y hy => obtain ⟨x, rfl⟩ := hy; exact horth x
    | zero => simp
    | add a b _ _ ha hb => rw [inner_add_left, ha, hb, add_zero]
    | smul a y _ hy => rw [inner_smul_left, hy, mul_zero]
  have hall : ∀ u : K, ⟪u, C R.Ω - c • R.Ω⟫_ℂ = 0 := by
    intro u
    have hmem : u ∈ closure ((Submodule.span ℂ (Set.range (kv R)) : Submodule ℂ K) : Set K) := by
      have this : (Submodule.span ℂ (Set.range (kv R))).topologicalClosure = ⊤ := R.cyclic
      rw [← Submodule.topologicalClosure_coe, this]; trivial
    have hc1 : Continuous fun w : K => ⟪w, C R.Ω - c • R.Ω⟫_ℂ := continuous_id.inner continuous_const
    have := Continuous.ext_on (f := fun w : K => ⟪w, C R.Ω - c • R.Ω⟫_ℂ) (g := fun _ => (0 : ℂ))
      (s := ((Submodule.span ℂ (Set.range (kv R)) : Submodule ℂ K) : Set K))
      (by
        rw [dense_iff_closure_eq]
        have this : (Submodule.span ℂ (Set.range (kv R))).topologicalClosure = ⊤ := R.cyclic
        rw [← Submodule.topologicalClosure_coe, this]; rfl)
      hc1 continuous_const hspan
    exact congrFun this u
  have := hall (C R.Ω - c • R.Ω)
  rw [inner_self_eq_zero] at this
  exact sub_eq_zero.1 this

/-- **The commutant of a Fock representation is trivial**: a bounded operator commuting with all `W f` is a
scalar. -/
theorem commutant_scalar (R : FockRep h K) (C : K →L[ℂ] K) (hC : ∀ f ψ, C (R.W f ψ) = R.W f (C ψ)) :
    ∃ c : ℂ, ∀ ψ, C ψ = c • ψ := by
  refine ⟨⟪R.Ω, C R.Ω⟫_ℂ, fun ψ => ?_⟩
  set c := ⟪R.Ω, C R.Ω⟫_ℂ with hc
  have hdense : Dense ((Submodule.span ℂ (Set.range (kv R)) : Submodule ℂ K) : Set K) := by
    rw [Submodule.dense_iff_topologicalClosure_eq_top]; exact R.cyclic
  have hcont1 : Continuous fun w : K => C w := C.continuous
  have hcont2 : Continuous fun w : K => c • w := continuous_const.smul continuous_id
  have := Continuous.ext_on hdense hcont1 hcont2 (fun u hu => by
    induction hu using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨x, rfl⟩ := hy
      show C (R.W x R.Ω) = c • R.W x R.Ω
      rw [hC, commutant_apply_Omega R C hC, map_smul]
    | zero => simp
    | add a b _ _ ha hb => simp only [map_add, smul_add, ha, hb]
    | smul a y _ hy => rw [map_smul, hy, smul_comm])
  exact congrFun this ψ

/-- **Every nonzero vector of a Fock representation is cyclic** (irreducibility): the projection onto the closed
span of the `W f ψ` commutes with the Weyl unitaries, so it is a scalar by `commutant_scalar`, hence `1`. -/
theorem fockRep_cyclic (R : FockRep h K) {ψ : K} (hψ : ψ ≠ 0) :
    (Submodule.span ℂ (Set.range fun f => R.W f ψ)).topologicalClosure = ⊤ := by
  set S : Submodule ℂ K := Submodule.span ℂ (Set.range fun f => R.W f ψ) with hS
  set M : Submodule ℂ K := S.topologicalClosure with hM
  -- invariance under every `W f`
  have hSinv : ∀ f, ∀ m ∈ S, R.W f m ∈ S := by
    intro f m hm
    induction hm using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨g, rfl⟩ := hy
      rw [R.weyl]
      exact S.smul_mem _ (Submodule.subset_span ⟨f + g, rfl⟩)
    | zero => simp
    | add a b _ _ ha hb => rw [map_add]; exact S.add_mem ha hb
    | smul c a _ ha => rw [map_smul]; exact S.smul_mem c ha
  have hMinv : ∀ f, ∀ m ∈ M, R.W f m ∈ M := by
    intro f m hm
    have hm' : m ∈ closure (S : Set K) := hm
    exact map_mem_closure (R.W f).continuous hm' (fun s hs => hSinv f s hs)
  haveI : CompleteSpace M := (Submodule.isClosed_topologicalClosure S).completeSpace_coe
  have hψM : ψ ∈ M := by
    have : ψ ∈ S := by
      have := Submodule.subset_span (R := ℂ) (s := Set.range fun f => R.W f ψ) ⟨0, rfl⟩
      simpa [R.toCCRRep.W_zero_apply] using this
    exact Submodule.le_topologicalClosure _ this
  set P : K →L[ℂ] K := M.starProjection with hP
  have hcomm : ∀ f x, P (R.W f x) = R.W f (P x) := by
    intro f x
    refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero (hMinv f _ (M.starProjection_apply_mem x)) ?_
    intro w hw
    have h1 : ⟪R.W f x - R.W f (M.starProjection x), w⟫_ℂ =
        ⟪x - M.starProjection x, R.W (-f) w⟫_ℂ := by
      rw [← map_sub, ← (R.W (-f)).inner_map_map, R.toCCRRep.W_neg_W]
    rw [h1]
    exact Submodule.starProjection_inner_eq_zero x _ (hMinv (-f) w hw)
  obtain ⟨c, hc⟩ := commutant_scalar R P hcomm
  have hPψ : P ψ = ψ := (Submodule.starProjection_eq_self_iff).2 hψM
  have hc1 : c = 1 := by
    have h := hc ψ
    rw [hPψ] at h
    have : (1 - c) • ψ = 0 := by rw [sub_smul, one_smul, ← h, sub_self]
    have := (smul_eq_zero.1 this).resolve_right hψ
    linear_combination -this
  rw [eq_top_iff]
  intro x _
  have : P x = x := by rw [hc x, hc1, one_smul]
  rw [← this]
  exact M.starProjection_apply_mem x

end Commutant

end Lightlike.OperatorAlgebras
