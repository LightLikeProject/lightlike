import Lightlike.HarmonicAnalysis.Unitarisable
import Lightlike.HarmonicAnalysis.SU2Complete

/-!
# An irreducible finite-dimensional invariant subspace of an `SU(2)`-representation is a spin representation

If `W` is a finite-dimensional subspace of a Hilbert space `H` invariant under a strongly continuous unitary
representation `ρ` of `SU(2)`, it contains a minimal nonzero invariant subspace `W₀` (`exists_minimal_invariant`);
an orthonormal basis of `W₀` gives a continuous unitary matrix representation, irreducible
(`subrepMatrix_isIrreducible`), hence equivalent to a spin representation (`su2_irreducible_classification`), hence,
since equivalent unitary representations are unitarily equivalent (Schur), `W₀` has an orthonormal basis
`e₀, …, e_n` with `ρ(k) e_j = ∑_i spin_n(k)_{ij} e_i` (`exists_spin_basis`).

Supporting results for the converse of the Wigner classification; no catalogue entry.
-/

open scoped InnerProductSpace
open Lightlike.HarmonicAnalysis Matrix

namespace Lightlike.HarmonicAnalysis

noncomputable section

variable {G : Type*} [Group G] [TopologicalSpace G]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- A minimal nonzero invariant subspace inside a nonzero finite-dimensional invariant subspace. -/
theorem exists_minimal_invariant (ρ : G →* (H ≃ₗᵢ[ℂ] H)) (W : Submodule ℂ H) [FiniteDimensional ℂ W]
    (hW0 : W ≠ ⊥) (hW : ∀ g, ∀ x ∈ W, ρ g x ∈ W) :
    ∃ W₀ : Submodule ℂ H, W₀ ≠ ⊥ ∧ W₀ ≤ W ∧ (∀ g, ∀ x ∈ W₀, ρ g x ∈ W₀) ∧
      ∀ W' : Submodule ℂ H, W' ≤ W₀ → (∀ g, ∀ x ∈ W', ρ g x ∈ W') → W' = ⊥ ∨ W' = W₀ := by
  induction' hn : Module.finrank ℂ W using Nat.strong_induction_on with n ih generalizing W
  by_cases hmin : ∀ W' : Submodule ℂ H, W' ≤ W → (∀ g, ∀ x ∈ W', ρ g x ∈ W') → W' = ⊥ ∨ W' = W
  · exact ⟨W, hW0, le_rfl, hW, hmin⟩
  · push Not at hmin
    obtain ⟨W', hle, hinv, hnebot, hneW⟩ := hmin
    have hlt : W' < W := lt_of_le_of_ne hle hneW
    haveI : FiniteDimensional ℂ W' := Module.Finite.of_injective (Submodule.inclusion hle) (Submodule.inclusion_injective hle)
    have hfin : Module.finrank ℂ W' < n := hn ▸ Submodule.finrank_lt_finrank_of_lt hlt
    obtain ⟨W₀, h0, hle0, hinv0, hmin0⟩ := ih _ hfin W' hnebot hinv rfl
    exact ⟨W₀, h0, hle0.trans hle, hinv0, hmin0⟩

section Subrep

variable (ρ : G →* (H ≃ₗᵢ[ℂ] H)) {W₀ : Submodule ℂ H} {d : ℕ} (b : OrthonormalBasis (Fin d) ℂ W₀)
  (hinv : ∀ g, ∀ x ∈ W₀, ρ g x ∈ W₀)

/-- The matrix `⟪b_i, ρ(g) b_j⟫` of `ρ(g)` on the invariant subspace `W₀` in an orthonormal basis. -/
def subrepMat (g : G) : Matrix (Fin d) (Fin d) ℂ := fun i j => ⟪(b i : H), ρ g (b j)⟫_ℂ

include hinv in
lemma subrep_expand (g : G) (j : Fin d) : ρ g (b j) = ∑ i, subrepMat ρ b g i j • (b i : H) := by
  have h := b.sum_repr' (⟨ρ g (b j), hinv g _ (b j).2⟩ : W₀)
  have := congrArg (fun x : W₀ => (x : H)) h
  simp only [Submodule.coe_sum, Submodule.coe_smul, Submodule.coe_inner] at this
  exact this.symm

include hinv in
lemma subrepMat_mul (g h : G) : subrepMat ρ b (g * h) = subrepMat ρ b g * subrepMat ρ b h := by
  ext i j
  rw [Matrix.mul_apply]
  have e1 : ρ (g * h) (b j) = ρ g (ρ h (b j)) := by simp
  rw [subrepMat, e1, subrep_expand ρ b hinv h j, map_sum]
  simp only [map_smul, subrep_expand ρ b hinv g, inner_sum, inner_smul_right, Finset.smul_sum, smul_smul]
  have horth : ∀ i k : Fin d, ⟪(b i : H), (b k : H)⟫_ℂ = if i = k then 1 else 0 := fun i k => by
    rw [← Submodule.coe_inner, b.inner_eq_ite]
  simp only [horth, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  refine Finset.sum_congr rfl fun x _ => ?_
  ring

lemma inner_basis (i k : Fin d) : ⟪(b i : H), (b k : H)⟫_ℂ = if i = k then 1 else 0 := by
  rw [← Submodule.coe_inner, b.inner_eq_ite]

lemma subrepMat_one : subrepMat ρ b 1 = 1 := by
  ext i j
  simp [subrepMat, inner_basis b, Matrix.one_apply]

include hinv in
lemma subrepMat_star_mul (g : G) : (subrepMat ρ b g)ᴴ * subrepMat ρ b g = 1 := by
  ext i j
  have h1 : ⟪ρ g (b i), ρ g (b j)⟫_ℂ = if i = j then 1 else 0 := by
    rw [LinearIsometryEquiv.inner_map_map, inner_basis b]
  rw [subrep_expand ρ b hinv g i, subrep_expand ρ b hinv g j, sum_inner] at h1
  simp only [inner_sum, inner_smul_left, inner_smul_right, inner_basis b, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq, Finset.mem_univ, if_true] at h1
  rw [Matrix.mul_apply, Matrix.one_apply]
  simp only [Matrix.conjTranspose_apply, Complex.star_def]
  rw [← h1]
  exact Finset.sum_congr rfl fun x _ => mul_comm _ _

include hinv in
/-- The continuous unitary matrix representation on an invariant subspace in an orthonormal basis. -/
def subrepRep (hρc : ∀ x, Continuous fun g => ρ g x) : UnitaryMatrixRep G (Fin d) where
  toHom :=
    { toFun := fun g => ⟨subrepMat ρ b g, Matrix.mem_unitaryGroup_iff'.2 (by
        simpa [Matrix.star_eq_conjTranspose] using subrepMat_star_mul ρ b hinv g)⟩
      map_one' := Subtype.ext (subrepMat_one ρ b)
      map_mul' := fun g h => Subtype.ext (subrepMat_mul ρ b hinv g h) }
  continuous_toHom := by
    refine continuous_pi fun i => continuous_pi fun j => ?_
    exact (continuous_const.inner ((hρc (b j : H))))

/-- The synthesis map `c ↦ ∑ c_i b_i`. -/
def synth : (Fin d → ℂ) →ₗ[ℂ] H := ∑ i, (LinearMap.proj i : (Fin d → ℂ) →ₗ[ℂ] ℂ).smulRight (b i : H)

lemma synth_apply (c : Fin d → ℂ) : synth b c = ∑ i, c i • (b i : H) := by
  simp [synth]

lemma inner_synth (j : Fin d) (c : Fin d → ℂ) : ⟪(b j : H), synth b c⟫_ℂ = c j := by
  rw [synth_apply, inner_sum]
  simp [inner_smul_right, inner_basis b, mul_ite]

lemma inner_synth_synth (c c' : Fin d → ℂ) :
    ⟪synth b c, synth b c'⟫_ℂ = ∑ l, (starRingEnd ℂ) (c l) * c' l := by
  rw [synth_apply, synth_apply, sum_inner]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [inner_sum]
  simp [inner_smul_left, inner_smul_right, inner_basis b, mul_ite, mul_comm]

lemma synth_injective : Function.Injective (synth b) := by
  intro c c' h
  funext j
  rw [← inner_synth b j c, h, inner_synth]

lemma synth_mem (c : Fin d → ℂ) : synth b c ∈ W₀ := by
  rw [synth_apply]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (b i).2

lemma mem_range_synth {w : H} (hw : w ∈ W₀) : ∃ c, synth b c = w := by
  refine ⟨fun i => ⟪(b i : H), w⟫_ℂ, ?_⟩
  have := b.sum_repr' (⟨w, hw⟩ : W₀)
  have h2 := congrArg (fun x : W₀ => (x : H)) this
  simp only [Submodule.coe_sum, Submodule.coe_smul, Submodule.coe_inner] at h2
  rw [synth_apply]
  exact h2

include hinv in
lemma synth_intertwine (g : G) (c : Fin d → ℂ) :
    ρ g (synth b c) = synth b ((subrepMat ρ b g).mulVec c) := by
  rw [synth_apply, synth_apply, map_sum]
  simp only [map_smul, subrep_expand ρ b hinv g, Finset.smul_sum, smul_smul, Matrix.mulVec, dotProduct]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_smul]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [mul_comm]

include hinv in
lemma subrepRep_isIrreducible (hρc : ∀ x, Continuous fun g => ρ g x) (hW₀ : W₀ ≠ ⊥)
    (hmin : ∀ W' : Submodule ℂ H, W' ≤ W₀ → (∀ g, ∀ x ∈ W', ρ g x ∈ W') → W' = ⊥ ∨ W' = W₀) :
    (subrepRep ρ b hinv hρc).IsIrreducible := by
  refine ⟨?_, fun Wm hWm => ?_⟩
  · by_contra hne
    rw [not_nonempty_iff] at hne
    apply hW₀
    rw [eq_bot_iff]
    intro w hw
    obtain ⟨c, rfl⟩ := mem_range_synth b hw
    have : c = 0 := Subsingleton.elim _ _
    simp [this]
  · have hY : ∀ g, ∀ x ∈ Wm.map (synth b), ρ g x ∈ Wm.map (synth b) := by
      rintro g _ ⟨c, hc, rfl⟩
      exact ⟨_, hWm g c hc, (synth_intertwine ρ b hinv g c).symm⟩
    have hYle : Wm.map (synth b) ≤ W₀ := by
      rintro _ ⟨c, -, rfl⟩
      exact synth_mem b c
    rcases hmin _ hYle hY with h | h
    · left
      rw [eq_bot_iff]
      intro c hc
      have : synth b c ∈ Wm.map (synth b) := ⟨c, hc, rfl⟩
      rw [h, Submodule.mem_bot] at this
      have h0 : synth b c = synth b 0 := by rw [this, map_zero]
      exact (Submodule.mem_bot ℂ).2 (synth_injective b h0)
    · right
      rw [eq_top_iff]
      intro c _
      have : synth b c ∈ Wm.map (synth b) := by rw [h]; exact synth_mem b c
      obtain ⟨c', hc', hcc'⟩ := this
      rwa [← synth_injective b hcc']

end Subrep

section Unitary

variable {N : ℕ}

/-- **Equivalent unitary representations, one of them irreducible, are unitarily equivalent.** -/
lemma exists_unitary_intertwiner (σ ρ' : UnitaryMatrixRep G (Fin N)) (hσ : σ.IsIrreducible)
    (M : Matrix (Fin N) (Fin N) ℂ) (hM : ∀ g, ρ'.mat g * M = M * σ.mat g) (hMu : IsUnit M) :
    ∃ X : Matrix (Fin N) (Fin N) ℂ, Xᴴ * X = 1 ∧ ∀ g, σ.mat g * X = X * ρ'.mat g := by
  have hdag : ∀ g, σ.mat g * Mᴴ = Mᴴ * ρ'.mat g := fun g => by
    have h1 : Mᴴ * (ρ'.mat g)ᴴ = (σ.mat g)ᴴ * Mᴴ := by
      rw [← Matrix.conjTranspose_mul, ← Matrix.conjTranspose_mul, hM g]
    calc σ.mat g * Mᴴ = σ.mat g * (Mᴴ * ((ρ'.mat g)ᴴ * ρ'.mat g)) := by
          rw [ρ'.star_mat_mul_mat g, mul_one]
      _ = σ.mat g * ((Mᴴ * (ρ'.mat g)ᴴ) * ρ'.mat g) := by rw [Matrix.mul_assoc Mᴴ]
      _ = σ.mat g * (((σ.mat g)ᴴ * Mᴴ) * ρ'.mat g) := by rw [h1]
      _ = ((σ.mat g * (σ.mat g)ᴴ) * Mᴴ) * ρ'.mat g := by simp only [Matrix.mul_assoc]
      _ = Mᴴ * ρ'.mat g := by rw [σ.mat_mul_star_mat g, Matrix.one_mul]
  have hP : ∀ g, σ.mat g * (Mᴴ * M) = (Mᴴ * M) * σ.mat g := fun g => by
    calc σ.mat g * (Mᴴ * M) = (σ.mat g * Mᴴ) * M := (Matrix.mul_assoc _ _ _).symm
      _ = (Mᴴ * ρ'.mat g) * M := by rw [hdag g]
      _ = Mᴴ * (ρ'.mat g * M) := Matrix.mul_assoc _ _ _
      _ = Mᴴ * (M * σ.mat g) := by rw [hM g]
      _ = (Mᴴ * M) * σ.mat g := (Matrix.mul_assoc _ _ _).symm
  obtain ⟨c, hc⟩ := UnitaryMatrixRep.schur_scalar hσ _ hP
  haveI : Nonempty (Fin N) := hσ.1
  obtain ⟨i₀⟩ := (inferInstance : Nonempty (Fin N))
  set r : ℝ := ∑ k, ‖M k i₀‖ ^ 2 with hr
  have hcr : c = (r : ℂ) := by
    have := congrFun (congrFun hc i₀) i₀
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.smul_apply, Matrix.one_apply_eq,
      smul_eq_mul, mul_one] at this
    rw [← this, hr]
    push_cast
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Complex.star_def, Complex.conj_mul']
  have hrpos : 0 < r := by
    have hnn : 0 ≤ r := Finset.sum_nonneg fun k _ => by positivity
    rcases hnn.lt_or_eq with h | h
    · exact h
    · exfalso
      have h0 : ∀ k, M k i₀ = 0 := by
        intro k
        have := (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => by positivity)).1 h.symm k (Finset.mem_univ k)
        simpa using this
      have hcol : M.mulVec (Pi.single i₀ 1) = 0 := by
        funext k; simp [Matrix.mulVec_single_one, h0 k]
      have := (Matrix.isUnit_iff_isUnit_det M |>.1 hMu)
      have hinj := (Matrix.mulVec_injective_iff_isUnit.2 hMu)
      have := hinj (hcol.trans (Matrix.mulVec_zero M).symm)
      have h1 := congrFun this i₀
      simp at h1
  have hinv : ((r : ℂ)⁻¹ • Mᴴ) * M = 1 := by
    rw [Matrix.smul_mul, hc, hcr, smul_smul, inv_mul_cancel₀ (by exact_mod_cast hrpos.ne'), one_smul]
  have hinv' : M * ((r : ℂ)⁻¹ • Mᴴ) = 1 := mul_eq_one_comm.1 hinv
  have hMM : M * Mᴴ = (r : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ) := by
    have : (r : ℂ)⁻¹ • (M * Mᴴ) = 1 := by rwa [Matrix.mul_smul] at hinv'
    have h2 := congrArg (fun A => (r : ℂ) • A) this
    simpa [smul_smul, mul_inv_cancel₀ (show (r : ℂ) ≠ 0 by exact_mod_cast hrpos.ne')] using h2
  refine ⟨(((Real.sqrt r)⁻¹ : ℝ) : ℂ) • Mᴴ, ?_, fun g => ?_⟩
  · rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_conjTranspose, Matrix.smul_mul, Matrix.mul_smul,
      smul_smul, hMM, smul_smul]
    have : (star (((Real.sqrt r)⁻¹ : ℝ) : ℂ)) * (((Real.sqrt r)⁻¹ : ℝ) : ℂ) * (r : ℂ) = 1 := by
      rw [Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul, ← Complex.ofReal_mul]
      have hs : Real.sqrt r * Real.sqrt r = r := Real.mul_self_sqrt hrpos.le
      have hs0 : Real.sqrt r ≠ 0 := (Real.sqrt_pos.2 hrpos).ne'
      exact_mod_cast (by field_simp; linarith : (Real.sqrt r)⁻¹ * (Real.sqrt r)⁻¹ * r = 1)
    rw [this, one_smul]
  · rw [Matrix.mul_smul, Matrix.smul_mul, hdag g]

end Unitary

/-- **An `SU(2)`-invariant finite-dimensional subspace contains an orthonormal spin multiplet**: an orthonormal family
`f₀, …, f_n` in `W` with `ρ(k) f_j = ∑_i spin_n(k)_{ij} f_i`. -/
theorem exists_spin_basis (ρ : SU2 →* (H ≃ₗᵢ[ℂ] H)) (hρc : ∀ x, Continuous fun g => ρ g x)
    (W : Submodule ℂ H) [FiniteDimensional ℂ W] (hW0 : W ≠ ⊥) (hW : ∀ g, ∀ x ∈ W, ρ g x ∈ W) :
    ∃ (n : ℕ) (f : Fin (n + 1) → H), Orthonormal ℂ f ∧ (∀ j, f j ∈ W) ∧
      ∀ k j, ρ k (f j) = ∑ i, SU2.spinMat n k i j • f i := by
  obtain ⟨W₀, h0, hle, hinv, hmin⟩ := exists_minimal_invariant ρ W hW0 hW
  haveI : FiniteDimensional ℂ W₀ :=
    Module.Finite.of_injective (Submodule.inclusion hle) (Submodule.inclusion_injective hle)
  obtain ⟨d, ⟨b⟩⟩ : ∃ d, Nonempty (OrthonormalBasis (Fin d) ℂ W₀) :=
    ⟨_, ⟨stdOrthonormalBasis ℂ W₀⟩⟩
  have hσ : (subrepRep ρ b hinv hρc).IsIrreducible := subrepRep_isIrreducible ρ b hinv hρc h0 hmin
  obtain ⟨n, ⟨e, he⟩, hcard⟩ := su2_irreducible_classification hσ
  have hd : d = n + 1 := by simpa using hcard
  subst hd
  set σ := subrepRep ρ b hinv hρc with hσdef
  set M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ := LinearMap.toMatrix' (e : (Fin (n + 1) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ)) with hMdef
  have hMe : ∀ w, M.mulVec w = e w := fun w => by
    rw [hMdef, LinearMap.toMatrix'_mulVec]
    rfl
  have hM : ∀ g, (su2Spin n).mat g * M = M * σ.mat g := fun g => by
    refine Matrix.toLin'.injective (LinearMap.ext fun w => ?_)
    rw [Matrix.toLin'_mul_apply, Matrix.toLin'_mul_apply]
    simp only [Matrix.toLin'_apply', Matrix.mulVecLin_apply, hMe, he]
  have hMu : IsUnit M := by
    have h1 : M * LinearMap.toMatrix' (e.symm : (Fin (n + 1) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ)) = 1 := by
      refine Matrix.toLin'.injective (LinearMap.ext fun w => ?_)
      simp [Matrix.toLin'_mul, hMdef, Matrix.toLin'_toMatrix']
    exact IsUnit.of_mul_eq_one _ h1
  obtain ⟨X, hX1, hX⟩ := exists_unitary_intertwiner σ (su2Spin n) hσ M hM hMu
  refine ⟨n, fun j => synth b (fun l => X l j), ?_, fun j => hle (synth_mem b _), fun k j => ?_⟩
  · rw [orthonormal_iff_ite]
    intro i j
    rw [inner_synth_synth b]
    have := congrFun (congrFun hX1 i) j
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply, Complex.star_def] at this
    exact this
  · rw [synth_intertwine ρ b hinv k]
    have h1 : (subrepMat ρ b k).mulVec (fun l => X l j) = fun m => ∑ i, (su2Spin n).mat k i j * X m i := by
      funext m
      have := congrFun (congrFun (hX k) m) j
      simp only [Matrix.mul_apply] at this
      simp only [Matrix.mulVec, dotProduct]
      rw [show (subrepMat ρ b k) = σ.mat k from rfl]
      rw [this]
      refine Finset.sum_congr rfl fun i _ => mul_comm _ _
    rw [h1]
    simp only [synth_apply, Finset.sum_smul, Finset.smul_sum, smul_smul, su2Spin_mat]
    rw [Finset.sum_comm]

end

end Lightlike.HarmonicAnalysis
