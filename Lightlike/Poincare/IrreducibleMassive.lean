import Lightlike.Poincare.CommutantDecomposition
import Lightlike.Poincare.RestSpin
import Lightlike.Lorentz.Schur
import Mathlib.Dynamics.Ergodic.Action.Regular

/-!
# The massive one-particle representations are irreducible

On `L²(μ; ℂ^{n+1})` over the mass shell, for every `SL(2,ℂ)`-invariant σ-finite measure `μ`, every bounded operator
commuting with the translations and with the induced action `U(A)` is a scalar (`commutant_eq_scalar`), and every
closed subspace invariant under both is `0` or everything (`irreducible_massive`). Steps:

0. `μ` has the null sets of the image `shellMeasure` of the Haar measure under the orbit map `A ↦ A · (m, 0, 0, 0)`:
   `μ(S) · haar(SL(2,ℂ)) = shellMeasure(S) · μ(shell)` (`measure_mul_haar_univ`), and `haar(SL(2,ℂ)) = ∞`;

1. it is the multiplication by a measurable matrix field `M` (`exists_matField_of_commute_transl`);
2. `M` is covariant: `M(Q) D(W(A, A⁻¹Q)) = D(W(A, A⁻¹Q)) M(A⁻¹Q)` almost everywhere, for each `A`
   (`matField_covariant`);
3. on `SL(2,ℂ)` the field `Φ(A) = D(k(A))⁻¹ M(A q) D(k(A))`, `k(A) = W(A, q)` at the rest momentum `q`, is
   almost everywhere invariant under every left translation, hence almost everywhere a constant `N₀` (ergodicity of the
   left regular action, `ae_eq_const_of_forall_ae_eq_mul_left`);
4. right translation by a rotation `u` gives `N₀ = D(u)⁻¹ N₀ D(u)` (the Haar measure is right-invariant), so `N₀` is
   a scalar by Schur's lemma for `SU(2)`, and so is `M`.

## References

* E. Freitag, *Unitary representations of the Poincaré group, Wigner classification* (lecture notes, Heidelberg),
  Chapter V, §6, Theorem 6.2 (Mackey: the representation induced from an irreducible representation of the little
  group is irreducible), page 149.
-/

open MeasureTheory Matrix Lightlike.Lorentz Lightlike.SU2 Filter Topology
open scoped InnerProductSpace

namespace Lightlike.Poincare

noncomputable section

/-! ## Ergodicity of the left regular action, for functions -/

/-- A measurable function on a group, almost everywhere invariant under every left translation, is almost
everywhere constant. -/
lemma ae_eq_const_of_forall_ae_eq_mul_left {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul₂ G]
    [MeasurableInv G] {ν : Measure G} [SFinite ν] [ν.IsMulLeftInvariant] {φ : G → ℂ} (hφ : Measurable φ)
    (h : ∀ g : G, (fun x => φ (g * x)) =ᵐ[ν] φ) : ∃ c : ℂ, φ =ᵐ[ν] fun _ => c := by
  refine exists_eventuallyEq_const_of_forall_separating MeasurableSet fun U hU => ?_
  refine eventuallyEmptyOrUniv_iff.1 (aeconst_of_forall_preimage_smul_ae_eq G (μ := ν)
    (hφ hU).nullMeasurableSet fun g => ?_)
  refine ((h g).mono fun x hx => ?_).set_eq
  change φ (g * x) ∈ U ↔ φ x ∈ U
  rw [show φ (g * x) = φ x from hx]

/-! ## Covariance of the matrix field -/

variable {m : ℝ} (hm : 0 < m) {μ : Measure (MassShell m)} {n : ℕ}

/-- **Covariance**: if `B` commutes with every `U(A)` and is the multiplication by `M`, then
`M(Q) D(W(A, A⁻¹Q)) = D(W(A, A⁻¹Q)) M(A⁻¹Q)` almost everywhere. -/
lemma matField_covariant [SigmaFinite μ] (hμ : ∀ A : SL2C, MeasurePreserving (shellAct A) μ μ)
    (B : Lp (Spinor n) 2 μ →L[ℂ] Lp (Spinor n) 2 μ) (M : MassShell m → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (hM : ∀ f : Lp (Spinor n) 2 μ, (B f : MassShell m → Spinor n) =ᵐ[μ] fun Q => matAct (M Q) (f Q))
    (hU : ∀ A f, B (inducedL2 hm n hμ A f) = inducedL2 hm n hμ A (B f)) (A : SL2C) :
    ∀ᵐ Q ∂μ, M Q * (wigField hm n A Q : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) =
      (wigField hm n A Q : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) * M (shellAct A⁻¹ Q) := by
  obtain ⟨W⟩ := exists_posWeight (μ := μ)
  have hj : ∀ j : Fin (n + 1), ∀ᵐ Q ∂μ,
      (M Q * (wigField hm n A Q : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)) *ᵥ Pi.single j 1 =
      ((wigField hm n A Q : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) * M (shellAct A⁻¹ Q)) *ᵥ Pi.single j 1 := by
    intro j
    have h1 := hM (inducedL2 hm n hμ A (wvec W j))
    have h3 := coeFn_inducedL2 hm n hμ A (wvec W j)
    have h4 := coeFn_inducedL2 hm n hμ A (B (wvec W j))
    have h5 := (hμ A⁻¹).quasiMeasurePreserving.ae_eq_comp (hM (wvec W j))
    have h6 := (hμ A⁻¹).quasiMeasurePreserving.ae_eq_comp (coeFn_wvec W j)
    filter_upwards [h1, h3, h4, h5, h6] with Q e1 e3 e4 e5 e6
    rw [hU, e4, e3] at e1
    simp only [Function.comp_apply] at e5 e6
    rw [e5, e6] at e1
    have e := congrArg WithLp.ofLp e1
    simp only [uAct, matAct, wvecFun, WithLp.ofLp_smul, EuclideanSpace.single, PiLp.ofLp_single,
      Matrix.mulVec_smul, Matrix.mulVec_mulVec] at e
    have hw : ((W.w (shellAct A⁻¹ Q) : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (W.pos _).ne'
    exact (smul_right_injective _ hw e).symm
  filter_upwards [ae_all_iff.2 hj] with Q hQ
  ext i j
  have := congrFun (hQ j) i
  simpa [Matrix.mulVec_single_one] using this

/-! ## The field on `SL(2,ℂ)` -/

local instance (k : ℕ) : TopologicalSpace.PseudoMetrizableSpace (Matrix (Fin k) (Fin k) ℂ) :=
  inferInstanceAs (TopologicalSpace.PseudoMetrizableSpace (Fin k → Fin k → ℂ))

local instance (k : ℕ) : SecondCountableTopology (Matrix (Fin k) (Fin k) ℂ) :=
  inferInstanceAs (SecondCountableTopology (Fin k → Fin k → ℂ))

instance sigmaFinite_shellMeasure : SigmaFinite (shellMeasure hm) := by
  haveI := locallyCompactSpace_massShell hm
  infer_instance

/-- The spin matrix `D(u)`. -/
abbrev spinM (n : ℕ) (u : Lightlike.SU2) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ := (spinRep n u : _)

lemma star_spinM_mul (u : Lightlike.SU2) : star (spinM n u) * spinM n u = 1 :=
  Matrix.mem_unitaryGroup_iff'.1 (spinRep n u).2

lemma spinM_mul_star (u : Lightlike.SU2) : spinM n u * star (spinM n u) = 1 :=
  Matrix.mem_unitaryGroup_iff.1 (spinRep n u).2

lemma spinM_mul (u v : Lightlike.SU2) : spinM n (u * v) = spinM n u * spinM n v := by
  simp only [spinM, map_mul]; rfl

/-- The rotation `k(A) = W(A, q)` at the rest momentum `q`. -/
def kRot (A : SL2C) : Lightlike.SU2 := wignerSU2 hm A (restShell hm)

lemma kRot_mul (A' A : SL2C) : kRot hm (A' * A) = wignerSU2 hm A' (orbitMap hm A) * kRot hm A :=
  wignerSU2_mul hm A' A (restShell hm)

lemma orbitMap_mul (A' A : SL2C) : orbitMap hm (A' * A) = shellAct A' (orbitMap hm A) :=
  shellAct_mul A' A (restShell hm)

lemma kRot_mul_ofSU2 (A : SL2C) (u : Lightlike.SU2) : kRot hm (A * SL2C.ofSU2 u) = kRot hm A * u := by
  rw [kRot_mul]
  unfold kRot
  rw [show orbitMap hm (SL2C.ofSU2 u) = restShell hm from shellAct_rest hm u, wignerSU2_rest]

lemma orbitMap_mul_ofSU2 (A : SL2C) (u : Lightlike.SU2) : orbitMap hm (A * SL2C.ofSU2 u) = orbitMap hm A := by
  rw [orbitMap_mul, show orbitMap hm (SL2C.ofSU2 u) = restShell hm from shellAct_rest hm u]
  rfl

lemma continuous_kRot : Continuous fun A => (kRot hm A : Matrix (Fin 2) (Fin 2) ℂ) := by
  have h1 : Continuous fun A : SL2C => (stdLift hm (orbitMap hm A))⁻¹ * A * stdLift hm (restShell hm) :=
    (((continuous_stdLift hm).comp (continuous_orbitMap hm)).inv.mul continuous_id).mul continuous_const
  change Continuous fun A => ((wigner hm A (restShell hm) : SL2C) : Matrix (Fin 2) (Fin 2) ℂ)
  exact continuous_subtype_val.comp h1

lemma continuous_spinM_kRot : Continuous fun A => spinM n (kRot hm A) := by
  change Continuous ((fun g => spinMat n g) ∘ fun A => (kRot hm A : Matrix (Fin 2) (Fin 2) ℂ))
  exact (continuous_spinMat (n := n)).comp (continuous_kRot hm)

/-- `Φ(A) = D(k(A))⁻¹ M(A q) D(k(A))`. -/
def restField (M : MassShell m → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (A : SL2C) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ :=
  star (spinM n (kRot hm A)) * M (orbitMap hm A) * spinM n (kRot hm A)

lemma stronglyMeasurable_restField {M : MassShell m → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    (hM : StronglyMeasurable M) : StronglyMeasurable (restField hm M) := by
  have h1 := (continuous_spinM_kRot (n := n) hm).star.stronglyMeasurable
  have h2 := hM.comp_measurable (continuous_orbitMap hm).measurable
  exact (h1.mul h2).mul (continuous_spinM_kRot hm).stronglyMeasurable

lemma restField_mul_ofSU2 (M : MassShell m → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (A : SL2C)
    (u : Lightlike.SU2) :
    restField hm M (A * SL2C.ofSU2 u) = star (spinM n u) * restField hm M A * spinM n u := by
  simp only [restField, kRot_mul_ofSU2, orbitMap_mul_ofSU2, spinM_mul, star_mul]
  noncomm_ring

lemma shellAct_inv_shellAct (A : SL2C) (P : MassShell m) : shellAct A⁻¹ (shellAct A P) = P := by
  rw [← shellAct_mul, inv_mul_cancel, shellAct_one]

/-- **`Φ` is almost everywhere invariant under left translations.** -/
lemma restField_mul_ae {M : MassShell m → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    (hcov : ∀ A : SL2C, ∀ᵐ P ∂(shellMeasure hm),
      star (spinM n (wignerSU2 hm A P)) * M (shellAct A P) * spinM n (wignerSU2 hm A P) = M P) (A' : SL2C) :
    (fun A => restField hm M (A' * A)) =ᵐ[SL2C.haar] restField hm M := by
  have h := ae_of_ae_map (continuous_orbitMap hm).aemeasurable (hcov A')
  filter_upwards [h] with A hA
  simp only [restField, kRot_mul, orbitMap_mul, spinM_mul, star_mul]
  rw [← hA]
  noncomm_ring

/-! ## Invariant measures have the null sets of `shellMeasure` -/

lemma continuous_shellAct_prod : Continuous fun z : SL2C × MassShell m => shellAct z.1 z.2 := by
  refine Continuous.subtype_mk ?_ _
  unfold actP
  have h1 : Continuous fun z : SL2C × MassShell m => ((z.1 : SL2C) : Matrix (Fin 2) (Fin 2) ℂ) :=
    continuous_subtype_val.comp continuous_fst
  have h2 : Continuous fun z : SL2C × MassShell m => (z.2.1 : Matrix (Fin 2) (Fin 2) ℂ) :=
    continuous_subtype_val.comp continuous_snd
  exact (h1.matrix_mul h2).matrix_mul h1.matrix_conjTranspose

lemma orbitMap_stdLift (P : MassShell m) : orbitMap hm (stdLift hm P) = P :=
  Subtype.ext (stdLift_act_rest hm P)

lemma indicator_one_comp {α : Type*} (f : α → MassShell m) (S : Set (MassShell m)) :
    (fun x => S.indicator (fun _ => (1 : ENNReal)) (f x)) = (f ⁻¹' S).indicator (fun _ => 1) := by
  funext x
  by_cases h : f x ∈ S
  · rw [Set.indicator_of_mem h, Set.indicator_of_mem (show x ∈ f ⁻¹' S from h)]
  · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem (show x ∉ f ⁻¹' S from h)]

/-- **`μ(S) · haar(G) = shellMeasure(S) · μ(shell)`** for every invariant s-finite measure `μ` (Tonelli, the
invariance of `μ` and the right invariance of the Haar measure). -/
lemma measure_mul_haar_univ {μ : Measure (MassShell m)} [SFinite μ]
    (hμ : ∀ A : SL2C, MeasurePreserving (shellAct A) μ μ) {S : Set (MassShell m)} (hS : MeasurableSet S) :
    μ S * SL2C.haar Set.univ = shellMeasure hm S * μ Set.univ := by
  have hF : Measurable fun z : SL2C × MassShell m => S.indicator (fun _ => (1 : ENNReal)) (shellAct z.1 z.2) :=
    (measurable_const.indicator hS).comp continuous_shellAct_prod.measurable
  have h1 : ∫⁻ A, ∫⁻ P, S.indicator (fun _ => (1 : ENNReal)) (shellAct A P) ∂μ ∂SL2C.haar =
      μ S * SL2C.haar Set.univ := by
    have : ∀ A : SL2C, ∫⁻ P, S.indicator (fun _ => (1 : ENNReal)) (shellAct A P) ∂μ = μ S := by
      intro A
      rw [indicator_one_comp, lintegral_indicator_const ((continuous_shellAct A).measurable hS), one_mul,
        (hμ A).measure_preimage hS.nullMeasurableSet]
    simp_rw [this, lintegral_const]
  have h2 : ∫⁻ P, ∫⁻ A, S.indicator (fun _ => (1 : ENNReal)) (shellAct A P) ∂SL2C.haar ∂μ =
      shellMeasure hm S * μ Set.univ := by
    have : ∀ P : MassShell m, ∫⁻ A, S.indicator (fun _ => (1 : ENNReal)) (shellAct A P) ∂SL2C.haar =
        shellMeasure hm S := by
      intro P
      have hc : Continuous fun A : SL2C => shellAct A P := by
        refine Continuous.subtype_mk ?_ _
        unfold actP
        have h1 : Continuous fun A : SL2C => ((A : SL2C) : Matrix (Fin 2) (Fin 2) ℂ) := continuous_subtype_val
        exact (h1.matrix_mul continuous_const).matrix_mul h1.matrix_conjTranspose
      have e : (fun A : SL2C => shellAct A P) ⁻¹' S = (fun A => A * stdLift hm P) ⁻¹' (orbitMap hm ⁻¹' S) := by
        ext A
        show shellAct A P ∈ S ↔ orbitMap hm (A * stdLift hm P) ∈ S
        rw [orbitMap_mul, orbitMap_stdLift]
      rw [indicator_one_comp (fun A : SL2C => shellAct A P), lintegral_indicator_const (hc.measurable hS),
        one_mul, e, measure_preimage_mul_right, shellMeasure,
        Measure.map_apply (continuous_orbitMap hm).measurable hS]
    simp_rw [this, lintegral_const]
  rw [← h1, ← h2]
  exact lintegral_lintegral_swap (f := fun (A : SL2C) (P : MassShell m) =>
    S.indicator (fun _ => (1 : ENNReal)) (shellAct A P)) hF.aemeasurable

lemma shellMeasure_absolutelyContinuous {μ : Measure (MassShell m)} [SFinite μ]
    (hμ : ∀ A : SL2C, MeasurePreserving (shellAct A) μ μ) (hμ0 : μ ≠ 0) : shellMeasure hm ≪ μ := by
  refine Measure.AbsolutelyContinuous.mk fun S hS h0 => ?_
  have h := measure_mul_haar_univ hm hμ hS
  rw [h0, zero_mul] at h
  exact (mul_eq_zero.1 h.symm).resolve_right (Measure.measure_univ_ne_zero.2 hμ0)

lemma absolutelyContinuous_shellMeasure {μ : Measure (MassShell m)} [SFinite μ]
    (hμ : ∀ A : SL2C, MeasurePreserving (shellAct A) μ μ) : μ ≪ shellMeasure hm := by
  refine Measure.AbsolutelyContinuous.mk fun S hS h0 => ?_
  have h := measure_mul_haar_univ hm hμ hS
  rw [h0, zero_mul, SL2C.haar_univ] at h
  exact (mul_eq_zero.1 h).resolve_right ENNReal.top_ne_zero

/-! ## The commutant -/

/-- **Irreducibility of the massive one-particle representations (Schur form)**: on `L²` of the mass shell for an
invariant σ-finite measure, every bounded operator commuting with the translations `T(a)` and with the induced
action `U(A)` of spin `n/2` is a scalar. -/
theorem commutant_eq_scalar [SigmaFinite μ] (hμ : ∀ A : SL2C, MeasurePreserving (shellAct A) μ μ)
    (B : Lp (Spinor n) 2 μ →L[ℂ] Lp (Spinor n) 2 μ)
    (hT : ∀ a f, B (translL2 n a f) = translL2 n a (B f))
    (hU : ∀ A f, B (inducedL2 hm n hμ A f) = inducedL2 hm n hμ A (B f)) :
    ∃ c : ℂ, B = c • ContinuousLinearMap.id ℂ _ := by
  by_cases hμ0 : μ = 0
  · subst hμ0
    refine ⟨0, ?_⟩
    ext f : 1
    apply Lp.ext
    rw [EventuallyEq, ae_zero]
    exact Filter.eventually_bot
  obtain ⟨M, hMm, hM⟩ := exists_matField_of_commute_transl B hm hT
  -- the covariance on the shell
  have hcov' : ∀ A : SL2C, ∀ᵐ P ∂μ,
      star (spinM n (wignerSU2 hm A P)) * M (shellAct A P) * spinM n (wignerSU2 hm A P) = M P := by
    intro A
    have h := (hμ A).quasiMeasurePreserving.ae (matField_covariant hm hμ B M hM hU A)
    filter_upwards [h] with P hP
    simp only [wigField, shellAct_inv_shellAct] at hP
    change M (shellAct A P) * spinM n (wignerSU2 hm A P) = spinM n (wignerSU2 hm A P) * M P at hP
    rw [Matrix.mul_assoc, hP, ← Matrix.mul_assoc, star_spinM_mul, Matrix.one_mul]
  have hcov : ∀ A : SL2C, ∀ᵐ P ∂(shellMeasure hm),
      star (spinM n (wignerSU2 hm A P)) * M (shellAct A P) * spinM n (wignerSU2 hm A P) = M P := fun A =>
    (shellMeasure_absolutelyContinuous hm hμ hμ0).ae_le (hcov' A)
  -- `Φ` is almost everywhere a constant `N₀`
  have hΦm := stronglyMeasurable_restField (n := n) hm hMm
  have hentry : ∀ i j, ∃ c : ℂ, (fun A => restField hm M A i j) =ᵐ[SL2C.haar] fun _ => c := by
    intro i j
    refine ae_eq_const_of_forall_ae_eq_mul_left ?_ fun A' => ?_
    · exact (((continuous_apply j).comp (continuous_apply i)).comp_stronglyMeasurable hΦm).measurable
    · filter_upwards [restField_mul_ae hm hcov A'] with A hA
      simp only [hA]
  choose c hc using hentry
  set N₀ : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ := Matrix.of c with hN₀def
  have hΦ : restField hm M =ᵐ[SL2C.haar] fun _ => N₀ := by
    filter_upwards [ae_all_iff.2 fun i => ae_all_iff.2 fun j => hc i j] with A hA
    ext i j
    exact hA i j
  -- `N₀` commutes with the spin matrices
  have hcomm : ∀ u : Lightlike.SU2, N₀ * spinM n u = spinM n u * N₀ := by
    intro u
    have h1 := (quasiMeasurePreserving_mul_right SL2C.haar (SL2C.ofSU2 u)).ae_eq_comp hΦ
    obtain ⟨A, hA1, hA2⟩ := (h1.and hΦ).exists
    simp only [Function.comp_apply] at hA1
    rw [restField_mul_ofSU2, hA2] at hA1
    calc N₀ * spinM n u = spinM n u * (star (spinM n u) * N₀ * spinM n u) := by
          rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, spinM_mul_star, Matrix.one_mul]
      _ = spinM n u * N₀ := by rw [hA1]
  -- Schur's lemma
  obtain ⟨c0, hc0⟩ := schur_eq_smul (m := n) (S := Matrix.toLin' N₀) (fun u x => by
    have h := hcomm u
    change N₀ * spinMat n u = spinMat n u * N₀ at h
    simp only [Matrix.toLin'_apply, Matrix.mulVec_mulVec, h])
  have hN₀ : N₀ = c0 • 1 := by
    apply Matrix.toLin'.injective
    rw [hc0, map_smul, Matrix.toLin'_one]
  -- `M` is almost everywhere the scalar `c0`
  have hMA : ∀ᵐ A ∂SL2C.haar, M (orbitMap hm A) = c0 • 1 := by
    filter_upwards [hΦ] with A hA
    simp only [restField] at hA
    rw [hN₀] at hA
    set D := spinM n (kRot hm A)
    calc M (orbitMap hm A) = (D * star D) * M (orbitMap hm A) * (D * star D) := by
          rw [spinM_mul_star, Matrix.one_mul, Matrix.mul_one]
      _ = D * (star D * M (orbitMap hm A) * D) * star D := by noncomm_ring
      _ = D * (c0 • 1) * star D := by rw [hA]
      _ = c0 • 1 := by rw [Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, spinM_mul_star]
  have hset : MeasurableSet {P | M P = c0 • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)} := by
    have e : {P | M P = c0 • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)} =
        ⋂ i, ⋂ j, (fun P => M P i j) ⁻¹' {(c0 • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)) i j} := by
      ext P
      simp only [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_preimage, Set.mem_singleton_iff]
      exact Matrix.ext_iff.symm
    have hent : ∀ i j : Fin (n + 1), Measurable fun P => M P i j := fun i j =>
      (Continuous.comp_stronglyMeasurable (g := fun X : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ => X i j)
        ((continuous_apply j).comp (continuous_apply i)) hMm).measurable
    rw [e]
    exact MeasurableSet.iInter fun i => MeasurableSet.iInter fun j => hent i j (measurableSet_singleton _)
  have hMQ : ∀ᵐ P ∂μ, M P = c0 • 1 := (absolutelyContinuous_shellMeasure hm hμ).ae_le
    ((ae_map_iff (continuous_orbitMap hm).aemeasurable hset).2 hMA)
  refine ⟨c0, ?_⟩
  ext f : 1
  rw [_root_.smul_apply, ContinuousLinearMap.id_apply]
  apply Lp.ext
  filter_upwards [hM f, hMQ, Lp.coeFn_smul c0 f] with Q h1 h2 h3
  rw [h1, h2, h3]
  ext i
  simp [matAct, Matrix.smul_mulVec, Matrix.one_mulVec]

/-! ## Irreducibility -/

/-- An isometry `V` with an isometric left inverse `V'`, both preserving a closed subspace `K`, commutes with the
orthogonal projection onto `K`. -/
lemma starProjection_map_eq {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] (K : Submodule ℂ E)
    [K.HasOrthogonalProjection] (V V' : E →ₗᵢ[ℂ] E) (hVV : ∀ x, V' (V x) = x) (hV : ∀ x ∈ K, V x ∈ K)
    (hV' : ∀ x ∈ K, V' x ∈ K) (x : E) : K.starProjection (V x) = V (K.starProjection x) := by
  refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero (hV _ (K.starProjection_apply_mem x))
    fun w hw => ?_
  rw [← map_sub, ← V'.inner_map_map, hVV]
  exact (Submodule.mem_orthogonal' _ _).1 (K.sub_starProjection_mem_orthogonal x) _ (hV' w hw)

/-- **The massive one-particle representations are irreducible**: on `L²` of the mass shell for an invariant
σ-finite measure, a closed subspace invariant under every translation `T(a)` and every `U(A)` is `0` or
everything. -/
theorem irreducible_massive [SigmaFinite μ] (hμ : ∀ A : SL2C, MeasurePreserving (shellAct A) μ μ)
    (K : Submodule ℂ (Lp (Spinor n) 2 μ)) (hK : IsClosed (K : Set (Lp (Spinor n) 2 μ)))
    (hT : ∀ a, ∀ f ∈ K, translL2 n a f ∈ K)
    (hU : ∀ A, ∀ f ∈ K, inducedL2 hm n hμ A f ∈ K) : K = ⊥ ∨ K = ⊤ := by
  haveI : CompleteSpace K := hK.completeSpace_coe
  obtain ⟨c, hc⟩ := commutant_eq_scalar hm hμ K.starProjection
    (fun a f => starProjection_map_eq K (translL2 n a) (translL2 n (-a))
      (fun x => by rw [← translL2_add, neg_add_cancel, translL2_zero]) (hT a) (hT (-a)) f)
    (fun A f => starProjection_map_eq K (inducedL2 hm n hμ A) (inducedL2 hm n hμ A⁻¹)
      (fun x => by rw [← inducedL2_mul, inv_mul_cancel, inducedL2_one]) (hU A) (hU A⁻¹) f)
  by_cases hc0 : c = 0
  · left
    rw [Submodule.eq_bot_iff]
    intro k hk
    have h := K.starProjection_eq_self_iff.2 hk
    rw [hc, hc0] at h
    simpa using h.symm
  · right
    rw [Submodule.eq_top_iff']
    intro x
    have hx := K.starProjection_apply_mem (c⁻¹ • x)
    rw [hc] at hx
    simpa [smul_smul, inv_mul_cancel₀ hc0] using hx

end

end Lightlike.Poincare
