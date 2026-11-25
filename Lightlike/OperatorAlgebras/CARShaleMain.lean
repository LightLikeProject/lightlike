import Lightlike.OperatorAlgebras.CARShaleVac
import Lightlike.OperatorAlgebras.CARProduct
import Lightlike.OperatorAlgebras.CARShaleHeavy

/-!
# Fermionic Shale, the Hilbert-Schmidt case: the decoupling estimate

In an eigenbasis `e` of `K = β*β` the transformed modes `annV (e k)`, `creV (e k)` form a CAR system, and for a vector
`PF D (W Ω₀)` built from modes of other eigenvalue classes, `‖annV (e k) (PF D (W Ω₀))‖² ≤ μ k ‖PF D (W Ω₀)‖²`
(`decoupling`), because `annV (e k) Ω₀ = a*(β e k) Ω₀` and `a*(β e k)` (anti)commutes with the modes of other classes.
-/

open scoped InnerProductSpace ComplexConjugate

namespace Lightlike.OperatorAlgebras.CARShale

open CARProjections

variable {ι : Type*} [LinearOrder ι] {Γ : Type*} [NormedAddCommGroup Γ] [InnerProductSpace ℂ Γ] [CompleteSpace Γ]
  (B : HilbertBasis (Finset ι) ℂ Γ) {Z : Type*} [NormedAddCommGroup Z] [InnerProductSpace ℂ Z] [CompleteSpace Z]
  (b : HilbertBasis ι ℂ Z) (R : Z →ₗ[ℝ] Z)
  (hR : ∀ w w', (⟪R w, R w'⟫_ℂ).re = (⟪w, w'⟫_ℂ).re) (hRs : Function.Surjective R)
  {s : Set Z} (e : HilbertBasis s ℂ Z) (μ : s → ℝ)
  (heig : ∀ k, KL R hR hRs (e k) = (μ k : ℂ) • e k) (hnorm : ∀ k, ‖betaPart R (e k)‖ ^ 2 = μ k)

include hR in
/-- Auxiliary lemma `fam_hca` for the fermionic Shale theorem. -/
lemma fam_hca [DecidableEq s] (i j : s) :
    annV B b R (e i) * creV B b R (e j) + creV B b R (e j) * annV B b R (e i) =
      if i = j then (1 : Γ →L[ℂ] Γ) else 0 := by
  rw [annV_creV_anticomm B b R hR, orthonormal_iff_ite.1 e.orthonormal i j]
  split_ifs <;> simp

include hR in
/-- Auxiliary lemma `fam_hcc` for the fermionic Shale theorem. -/
lemma fam_hcc (i j : s) :
    creV B b R (e i) * creV B b R (e j) + creV B b R (e j) * creV B b R (e i) = 0 :=
  creV_anticomm B b R hR _ _

include hR in
/-- Auxiliary lemma `fam_haa` for the fermionic Shale theorem. -/
lemma fam_haa (i j : s) :
    annV B b R (e i) * annV B b R (e j) + annV B b R (e j) * annV B b R (e i) = 0 :=
  annV_anticomm B b R hR _ _

/-- Auxiliary lemma `fam_hadj` for the fermionic Shale theorem. -/
lemma fam_hadj (j : s) (x y : Γ) : ⟪annV B b R (e j) x, y⟫_ℂ = ⟪x, creV B b R (e j) y⟫_ℂ :=
  inner_annV_creV B b R _ x y

include hR in
/-- The number operators of the eigenmodes form a family of commuting symmetric idempotents. -/
theorem famProj [DecidableEq s] :
    IsProjFamily (fun k : s => creV B b R (e k) * annV B b R (e k)) :=
  isProjFamily_of_car (fun k : s => annV B b R (e k)) (fun k : s => creV B b R (e k)) (fam_hcc B b R hR e)
    (fam_haa B b R hR e) (fam_hca B b R hR e) (fam_hadj B b R e)

include hR hRs heig in
/-- `a*(β eₖ)` anticommutes with the modes `l` whose eigenvalue differs from that of `k`. -/
lemma creW_anticomm_mode {k l : s} (hne : μ l ≠ μ k) :
    annV B b R (e l) * creW B b (betaPart R (e k)) + creW B b (betaPart R (e k)) * annV B b R (e l) = 0 ∧
    creV B b R (e l) * creW B b (betaPart R (e k)) + creW B b (betaPart R (e k)) * creV B b R (e l) = 0 := by
  classical
  constructor
  · rw [annV_creW_anticomm B b R, inner_alpha_beta_eq_zero R hR hRs (heig l) (heig k) hne, zero_smul]
  · rw [creV_creW_anticomm B b R, inner_beta_beta R hR hRs, heig k, inner_smul_left]
    have hlk : l ≠ k := fun h => hne (by rw [h])
    have : ⟪e k, e l⟫_ℂ = 0 := by
      have := orthonormal_iff_ite.1 e.orthonormal k l
      rwa [if_neg (Ne.symm hlk)] at this
    simp [this]

/-- The family of transformed annihilation operators of the eigenmodes. -/
noncomputable abbrev aFam : s → (Γ →L[ℂ] Γ) := fun k => annV B b R (e k)

/-- The family of transformed creation operators of the eigenmodes. -/
noncomputable abbrev cFam : s → (Γ →L[ℂ] Γ) := fun k => creV B b R (e k)

include hR hRs heig hnorm in
/-- **The decoupling estimate**: `‖a_k (PF D (W Ω₀))‖² ≤ μ_k ‖PF D (W Ω₀)‖²` when no mode of `D` and no flipped mode of `J`
has the eigenvalue of `k`. -/
theorem decoupling [DecidableEq s] (k : s) (D : Finset s) (J : List s) (hD : ∀ l ∈ D, μ l ≠ μ k)
    (hJ : ∀ j ∈ J, μ j ≠ μ k) :
    ‖aFam B b R e k (PF (famProj B b R hR e) D (Wlist (a := aFam B b R e) (c := cFam B b R e) J (B ∅)))‖ ^ 2 ≤
      μ k * ‖PF (famProj B b R hR e) D (Wlist (a := aFam B b R e) (c := cFam B b R e) J (B ∅))‖ ^ 2 := by
  have hcc := fam_hcc B b R hR e
  have haa := fam_haa B b R hR e
  have hca := fam_hca B b R hR e
  set A := aFam B b R e k with hAdef
  set Ak := creW B b (betaPart R (e k)) with hAkdef
  -- A anticommutes with the modes `l ≠ k`
  have hA_a : ∀ l, l ≠ k → A * aFam B b R e l + aFam B b R e l * A = 0 := fun l _ => haa k l
  have hA_c : ∀ l, l ≠ k → A * cFam B b R e l + cFam B b R e l * A = 0 := fun l hl => by
    have := hca k l
    rw [if_neg (Ne.symm hl)] at this; exact this
  have hlk : ∀ l, μ l ≠ μ k → l ≠ k := fun l h e' => h (by rw [e'])
  -- the Fock creation operator anticommutes with the modes of other class
  have hK_a : ∀ l, μ l ≠ μ k → Ak * aFam B b R e l + aFam B b R e l * Ak = 0 := fun l hl => by
    have := (creW_anticomm_mode B b R hR hRs e μ heig hl).1
    rw [add_comm]; exact this
  have hK_c : ∀ l, μ l ≠ μ k → Ak * cFam B b R e l + cFam B b R e l * Ak = 0 := fun l hl => by
    have := (creW_anticomm_mode B b R hR hRs e μ heig hl).2
    rw [add_comm]; exact this
  have hPA : A * PF (famProj B b R hR e) D = PF (famProj B b R hR e) D * A :=
    comm_PF (famProj B b R hR e) A D (fun l hl =>
      commute_of_anticomm (hA_c l (hlk l (hD l hl))) (hA_a l (hlk l (hD l hl))))
  have hPK : Ak * PF (famProj B b R hR e) D = PF (famProj B b R hR e) D * Ak :=
    comm_PF (famProj B b R hR e) Ak D (fun l hl =>
      commute_of_anticomm (hK_c l (hD l hl)) (hK_a l (hD l hl)))
  have hWA := comm_Wlist (a := aFam B b R e) (c := cFam B b R e) A J (fun j hj => by
    unfold pOp
    have h1 := hA_a j (hlk j (hJ j hj))
    have h2 := hA_c j (hlk j (hJ j hj))
    calc A * (aFam B b R e j + cFam B b R e j) + (aFam B b R e j + cFam B b R e j) * A =
        (A * aFam B b R e j + aFam B b R e j * A) + (A * cFam B b R e j + cFam B b R e j * A) := by noncomm_ring
      _ = 0 := by rw [h1, h2, add_zero])
  have hWK := comm_Wlist (a := aFam B b R e) (c := cFam B b R e) Ak J (fun j hj => by
    unfold pOp
    have h1 := hK_a j (hJ j hj)
    have h2 := hK_c j (hJ j hj)
    calc Ak * (aFam B b R e j + cFam B b R e j) + (aFam B b R e j + cFam B b R e j) * Ak =
        (Ak * aFam B b R e j + aFam B b R e j * Ak) + (Ak * cFam B b R e j + cFam B b R e j * Ak) := by noncomm_ring
      _ = 0 := by rw [h1, h2, add_zero])
  have hε : ‖(-1 : ℂ) ^ J.length‖ = 1 := by simp
  have hAY : A * (PF (famProj B b R hR e) D * Wlist (a := aFam B b R e) (c := cFam B b R e) J) =
      (-1 : ℂ) ^ J.length • ((PF (famProj B b R hR e) D * Wlist (a := aFam B b R e) (c := cFam B b R e) J) * A) := by
    rw [← mul_assoc, hPA, mul_assoc, hWA, mul_smul_comm, mul_assoc]
  have hKY : Ak * (PF (famProj B b R hR e) D * Wlist (a := aFam B b R e) (c := cFam B b R e) J) =
      (-1 : ℂ) ^ J.length • ((PF (famProj B b R hR e) D * Wlist (a := aFam B b R e) (c := cFam B b R e) J) * Ak) := by
    rw [← mul_assoc, hPK, mul_assoc, hWK, mul_smul_comm, mul_assoc]
  have hΩ : A (B ∅) = Ak (B ∅) := annV_vac B b R (e k)
  have hr : ∀ v, ‖Ak v‖ ≤ ‖betaPart R (e k)‖ * ‖v‖ := fun v =>
    (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul_of_nonneg_right (norm_creW_le B b _) (norm_nonneg _))
  have hstep := norm_step hε hε hAY hKY hΩ hr
  have h2 : ‖A ((PF (famProj B b R hR e) D * Wlist (a := aFam B b R e) (c := cFam B b R e) J) (B ∅))‖ ^ 2 ≤
      (‖betaPart R (e k)‖ * ‖(PF (famProj B b R hR e) D * Wlist (a := aFam B b R e) (c := cFam B b R e) J) (B ∅)‖) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hstep 2
  rw [mul_pow, hnorm k] at h2
  exact h2

include hR hRs heig hnorm in
/-- **The uniform lower bound** for the vacuum projections of the eigenmodes, on a flipped vacuum. -/
theorem exists_flipped_lower_bound [DecidableEq s] {h : ℝ} (hsum : HasSum μ h) :
    ∃ (J : List s) (c₁ : ℝ), 0 < c₁ ∧ ∀ F : Finset s,
      c₁ ≤ ‖PF (famProj B b R hR e) F (Wlist (a := aFam B b R e) (c := cFam B b R e) J (B ∅))‖ ^ 2 := by
  have hμ0 : ∀ k, 0 ≤ μ k := fun k => by rw [← hnorm k]; positivity
  have hfin := finite_heavy hμ0 hsum
  set D0 : Finset s := hfin.toFinset with hD0
  have hmemD0 : ∀ k, k ∈ D0 ↔ ∃ F : Finset s, (∀ l ∈ F, μ l = μ k) ∧ 1 / 2 < ∑ l ∈ F, μ l := fun k => by
    rw [hD0, Set.Finite.mem_toFinset]; rfl
  have hcc := fam_hcc B b R hR e
  have haa := fam_haa B b R hR e
  have hca := fam_hca B b R hR e
  have hadj := fam_hadj B b R e
  have hP := famProj B b R hR e
  have hB : ‖B ∅‖ = 1 := B.orthonormal.1 ∅
  obtain ⟨J, hJ, hflip⟩ := exists_flip (a := aFam B b R e) (c := cFam B b R e) hcc haa hca hadj hP D0 (B ∅)
  refine ⟨J, Real.exp (-2 * h) * (1 / 2 ^ D0.card), by positivity, fun F => ?_⟩
  set v := Wlist (a := aFam B b R e) (c := cFam B b R e) J (B ∅) with hv
  -- saturation: a mode of the same class as a heavy mode is heavy
  have hsat : ∀ l k, l ∈ D0 → μ l = μ k → k ∈ D0 := fun l k hl hlk => by
    obtain ⟨F', hF1, hF2⟩ := (hmemD0 l).1 hl
    exact (hmemD0 k).2 ⟨F', fun x hx => (hF1 x hx).trans hlk, hF2⟩
  set s' := F \ D0 with hs'
  have hsep : ∀ l ∈ D0, ∀ k ∈ s', μ l ≠ μ k := fun l hl k hk e' =>
    (Finset.mem_sdiff.1 hk).2 (hsat l k hl e')
  have hH : ∀ k ∈ s', ∀ D : Finset s, (∀ l ∈ D, μ l ≠ μ k) →
      ‖aFam B b R e k (PF hP D v)‖ ^ 2 ≤ μ k * ‖PF hP D v‖ ^ 2 := fun k hk D hD =>
    decoupling B b R hR hRs e μ heig hnorm k D J hD (fun j hj e' =>
      (Finset.mem_sdiff.1 hk).2 (hsat j k (hJ j hj) e'))
  have hT : ∀ m, ∑ k ∈ s'.filter (fun k => μ k = m), μ k ≤ 1 / 2 := fun m => by
    by_cases hne : (s'.filter (fun k => μ k = m)).Nonempty
    · obtain ⟨k0, hk0⟩ := hne
      have hk0' := Finset.mem_filter.1 hk0
      by_contra hlt
      push_neg at hlt
      exact (Finset.mem_sdiff.1 hk0'.1).2 ((hmemD0 k0).2 ⟨s'.filter (fun k => μ k = m),
        fun l hl => (Finset.mem_filter.1 hl).2.trans hk0'.2.symm, hlt⟩)
    · rw [Finset.not_nonempty_iff_eq_empty.1 hne]; simp
  have hlow := norm_sq_PF_union_ge hcc haa hca hadj hP μ μ v hμ0 D0 s' hsep hH hT
  have hsum' : ∑ k ∈ s', μ k ≤ h := sum_le_of_hasSum hμ0 hsum s'
  have hFsub : F ⊆ D0 ∪ s' := fun x hx => by
    by_cases hx0 : x ∈ D0
    · exact Finset.mem_union_left _ hx0
    · exact Finset.mem_union_right _ (Finset.mem_sdiff.2 ⟨hx, hx0⟩)
  have hmono : ‖PF hP (D0 ∪ s') v‖ ≤ ‖PF hP F v‖ := by
    have hdisj : Disjoint F ((D0 ∪ s') \ F) := Finset.disjoint_sdiff
    have hun : F ∪ ((D0 ∪ s') \ F) = D0 ∪ s' := Finset.union_sdiff_of_subset hFsub
    rw [← hun, PF_union hP hdisj, ContinuousLinearMap.mul_apply]
    exact norm_PF_le hP _ _
  have hexp : Real.exp (-2 * h) ≤ Real.exp (-2 * ∑ k ∈ s', μ k) := Real.exp_le_exp.2 (by linarith)
  have hB2 : ‖B ∅‖ ^ 2 / 2 ^ D0.card = 1 / 2 ^ D0.card := by rw [hB]; simp
  rw [hB2] at hflip
  have h1 : Real.exp (-2 * h) * (1 / 2 ^ D0.card) ≤ Real.exp (-2 * ∑ k ∈ s', μ k) * ‖PF hP D0 v‖ ^ 2 :=
    mul_le_mul hexp hflip (by positivity) (Real.exp_nonneg _)
  have h2 : ‖PF hP (D0 ∪ s') v‖ ^ 2 ≤ ‖PF hP F v‖ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hmono 2
  linarith

include hR hRs in
/-- **The vacuum exists when `β` is Hilbert-Schmidt**: a unit vector killed by all the transformed annihilation operators
of the Fock basis. -/
theorem exists_vacuum_of_HS
    (hHS : ∃ (w : Set Z) (c : HilbertBasis w ℂ Z), Summable fun i : w => ‖betaPart R (c i)‖ ^ 2) :
    ∃ Ω : Γ, ⟪Ω, Ω⟫_ℂ = 1 ∧ ∀ j, annR B b R j Ω = 0 := by
  classical
  obtain ⟨s, e, μ, h, heig, hnorm, hsum⟩ := exists_eigenbasis R hR hRs hHS
  obtain ⟨J, c₁, hc₁, hlow⟩ := exists_flipped_lower_bound B b R hR hRs e μ heig hnorm hsum
  have hcc := fam_hcc B b R hR e
  have haa := fam_haa B b R hR e
  have hca := fam_hca B b R hR e
  have hadj := fam_hadj B b R e
  have hP := famProj B b R hR e
  obtain ⟨Ω', hlow', hfix⟩ := exists_fixed_of_decreasing_projections (K := Γ)
    (fun F : Finset s => PF hP F)
    (fun F φ ψ => PF_symm hP F φ ψ)
    (fun F ψ => by
      show (PF hP F * PF hP F) ψ = _
      rw [PF_idem hP])
    (fun F φ ψ => map_sub _ _ _)
    (fun F ψ => norm_PF_le hP F ψ)
    (fun F G hFG ψ hψ => PF_fix_of_subset hP (Finset.le_iff_subset.1 hFG) hψ)
    (Wlist (a := aFam B b R e) (c := cFam B b R e) J (B ∅)) c₁ hlow
  have hpos : 0 < ‖Ω'‖ := by
    have : 0 < ‖Ω'‖ ^ 2 := lt_of_lt_of_le hc₁ hlow'
    exact lt_of_le_of_ne (norm_nonneg _) (fun e => by rw [← e] at this; simp at this)
  have hann : ∀ k, annV B b R (e k) Ω' = 0 := fun k => by
    have h1 := Q_fix hP (t := {k}) (hfix {k}) (Finset.mem_singleton_self k)
    have h2 : (creV B b R (e k) * annV B b R (e k)) Ω' = 0 := by
      have : Q (fun k => creV B b R (e k) * annV B b R (e k)) k Ω' =
          Ω' - (creV B b R (e k) * annV B b R (e k)) Ω' := by simp [Q]
      rw [this] at h1
      exact sub_eq_self.1 h1
    have h3 := norm_sq_cre_ann (fun k => annV B b R (e k)) (fun k => creV B b R (e k)) hcc haa hca hadj k Ω'
    have h4 : ‖annV B b R (e k) Ω'‖ ^ 2 = 0 := by
      rw [← h3]
      have : (creV B b R (e k)) ((annV B b R (e k)) Ω') = 0 := h2
      rw [this]; simp
    exact norm_eq_zero.1 (pow_eq_zero_iff (two_ne_zero) |>.1 h4)
  have hall := annV_kill_of_basis B b R hR e Ω' hann
  refine ⟨((‖Ω'‖⁻¹ : ℝ) : ℂ) • Ω', ?_, fun j => ?_⟩
  · rw [inner_smul_left, inner_smul_right, inner_self_eq_norm_sq_to_K]
    simp only [Complex.conj_ofReal]
    have hne : ((‖Ω'‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hpos.ne'
    push_cast
    field_simp
    rfl
  · rw [annR_eq_annV, map_smul, hall (b j), smul_zero]

include hR hRs in
/-- **Fermionic Shale, sufficiency in every number of modes**: a surjective real-linear map `R` of a Hilbert space `Z`
preserving `Re⟪·,·⟫`, whose antilinear part `β` is Hilbert-Schmidt (`∑ ‖β cᵢ‖²` converges in some Hilbert basis), is
implemented by a unitary of the fermionic Fock space, `U φ(w) = φ(R w) U`. -/
theorem fermionic_shale_of_HS
    (hHS : ∃ (w : Set Z) (c : HilbertBasis w ℂ Z), Summable fun i : w => ‖betaPart R (c i)‖ ^ 2) :
    ∃ U : Γ ≃ₗᵢ[ℂ] Γ, ∀ w x, U (fockField B b w x) = fockField B b (R w) (U x) := by
  obtain ⟨Ω, hn, hvac⟩ := exists_vacuum_of_HS B b R hR hRs hHS
  exact exists_implementer B b R hR hRs Ω hn hvac

end Lightlike.OperatorAlgebras.CARShale
