import Lightlike.Spacetime.PenroseSingularity.GeneratorNormal
import Lightlike.Spacetime.PenroseSingularity.TrappedNormals
import Lightlike.Spacetime.PenroseSingularity.FocalLength
import Lightlike.Spacetime.PenroseSingularity.FocalChron
import Lightlike.Spacetime.PenroseSingularity.UniformBound

/-!
# The normalised focal bound from focusing (G1-012, step D3b assembly)

Given `FocalImpliesChron` and the chart null energy condition, the affine length of a generator of
`∂J⁺(S)` from a closed trapped spacelike surface `S` is bounded by the inverse expansion of the null normal
(`generator_focal_bound`). With a uniform bound `Λ` on these quantities for the two null normal fields, the
normalised focal bound `NormalisedFocalBound` holds.
-/

open Set Filter Topology Manifold
open scoped ContDiff Manifold

noncomputable section

namespace Lightlike.Penrose

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Fin n → ℝ) M]
  [IsManifold 𝓘(ℝ, Fin n → ℝ) ∞ M] [SecondCountableTopology M] [T2Space M]
  [IsManifold 𝓘(ℝ, Fin n → ℝ) 2 M] [MeasurableSpace M] [BorelSpace M]

open Lightlike.Causal NullNormal in
/-- **Two global null normal fields for a regular level set**, with every future null normal a positive
multiple of one of them. -/
theorem exists_null_normal_fields {g : LorentzianMetric 𝓘(ℝ, Fin n → ℝ) M n} (T : TimeOrientation g)
    {S : Set M} (hc : IsCompact S) {f : M → Fin 2 → ℝ}
    (hf : ContMDiff 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin 2 → ℝ) ∞ f) (hS : S = f ⁻¹' {0})
    (hsub : ∀ x ∈ S, Function.Surjective (mfderiv 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin 2 → ℝ) f x))
    (hsp : ∀ x ∈ S, ∀ v : TangentSpace 𝓘(ℝ, Fin n → ℝ) x,
      mfderiv 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin 2 → ℝ) f x v = 0 → v ≠ 0 → 0 < g.g x v v) :
    ∃ k₁ k₂ : (x : M) → TangentSpace 𝓘(ℝ, Fin n → ℝ) x,
      ContMDiff 𝓘(ℝ, Fin n → ℝ) (𝓘(ℝ, Fin n → ℝ).prod 𝓘(ℝ, Fin n → ℝ)) ∞
        (fun q : M => (⟨q, k₁ q⟩ : TangentBundle 𝓘(ℝ, Fin n → ℝ) M)) ∧
      ContMDiff 𝓘(ℝ, Fin n → ℝ) (𝓘(ℝ, Fin n → ℝ).prod 𝓘(ℝ, Fin n → ℝ)) ∞
        (fun q : M => (⟨q, k₂ q⟩ : TangentBundle 𝓘(ℝ, Fin n → ℝ) M)) ∧
      (∀ x ∈ S, IsFutureNullNormalAt g T f x (k₁ x) ∧ IsFutureNullNormalAt g T f x (k₂ x)) ∧
      (∀ x ∈ S, ∀ ν : TangentSpace 𝓘(ℝ, Fin n → ℝ) x, IsFutureNullNormalAt g T f x ν →
        (∃ μ : ℝ, 0 < μ ∧ ν = μ • k₁ x) ∨ ∃ μ : ℝ, 0 < μ ∧ ν = μ • k₂ x) := by
  classical
  obtain ⟨X, hXs, hX⟩ := exists_smooth_field T
  obtain ⟨k₁, hk₁s, hk₁n, hk₁e⟩ :=
    exists_global_null_normal T hc hf hS hsub hsp hXs hX 1 (by norm_num)
  obtain ⟨k₂, hk₂s, hk₂n, hk₂e⟩ :=
    exists_global_null_normal T hc hf hS hsub hsp hXs hX (-1) (by norm_num)
  refine ⟨k₁, k₂, hk₁s, hk₂s, fun x hx => ⟨hk₁n x hx, hk₂n x hx⟩, ?_⟩
  intro x hx ν hν
  obtain ⟨s, hs, μ, hμ, hνk⟩ := nullField_classify T hf (hsub x hx) (hsp x hx) (hX x).1 (hX x).2 hν
  have hs' : s = 1 ∨ s = -1 := by
    have : (s - 1) * (s + 1) = 0 := by linear_combination hs
    rcases mul_eq_zero.1 this with h | h
    · left; linarith
    · right; linarith
  rcases hs' with rfl | rfl
  · left; exact ⟨μ, hμ, by rw [hνk, hk₁e x hx]⟩
  · right; exact ⟨μ, hμ, by rw [hνk, hk₂e x hx]⟩

/-- The expansion is homogeneous in the field. -/
theorem frameExpansion_smul (g : LorentzianMetric 𝓘(ℝ, Fin n → ℝ) M n) (cov : Connection 𝓘(ℝ, Fin n → ℝ) M)
    (k : Π p : M, TangentSpace 𝓘(ℝ, Fin n → ℝ) p) (x : M)
    (hk : MDifferentiableAt 𝓘(ℝ, Fin n → ℝ) (𝓘(ℝ, Fin n → ℝ).prod 𝓘(ℝ, Fin n → ℝ))
      (fun q : M => (⟨q, k q⟩ : TangentBundle 𝓘(ℝ, Fin n → ℝ) M)) x)
    (μ : ℝ) (e : Fin (n - 2) → TangentSpace 𝓘(ℝ, Fin n → ℝ) x) :
    frameExpansion g cov (fun y => μ • k y) x e = μ * frameExpansion g cov k x e := by
  have h := cov.isCovariantDerivativeOn.smul_const (σ := k) (x := x) μ hk
  unfold frameExpansion
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h' : cov (fun y => μ • k y) x = μ • cov k x := h
  rw [h']
  simp

/-- **The normalised focal bound from focusing**, given the second-variation fact `FocalImpliesChron`, the
chart null energy condition, two null normal fields for which the normalised expansion bounds are bounded by
`Λ`. -/
theorem normalisedFocalBound_of_chron (g : LorentzianMetric 𝓘(ℝ, Fin n → ℝ) M n)
    {cov : Connection 𝓘(ℝ, Fin n → ℝ) M} [LocallySmoothConnection cov]
    (hLC : cov.IsLeviCivita g.toNondegMetric) (T : Causal.TimeOrientation g) {S : Set M} (hn : 3 ≤ n)
    {f : M → Fin 2 → ℝ} (hf : ContMDiff 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin 2 → ℝ) ∞ f) (hS : S = f ⁻¹' {0})
    (hsub : ∀ x ∈ S, Function.Surjective (mfderiv 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin 2 → ℝ) f x))
    (hsp : ∀ x ∈ S, ∀ v : TangentSpace 𝓘(ℝ, Fin n → ℝ) x,
      mfderiv 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin 2 → ℝ) f x v = 0 → v ≠ 0 → 0 < g.g x v v)
    (hexp : ∀ k : Π p : M, TangentSpace 𝓘(ℝ, Fin n → ℝ) p,
      ContMDiff 𝓘(ℝ, Fin n → ℝ) (𝓘(ℝ, Fin n → ℝ).prod 𝓘(ℝ, Fin n → ℝ)) ∞
        (fun q : M => (⟨q, k q⟩ : TangentBundle 𝓘(ℝ, Fin n → ℝ) M)) →
      (∀ x ∈ S, IsFutureNullNormalAt g T f x (k x)) →
      ∀ x ∈ S, ∀ e : Fin (n - 2) → TangentSpace 𝓘(ℝ, Fin n → ℝ) x,
        (∀ i, mfderiv 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin 2 → ℝ) f x (e i) = 0) →
        (∀ i j, g.g x (e i) (e j) = if i = j then 1 else 0) → frameExpansion g cov k x e < 0)
    {k₁ k₂ : Π p : M, TangentSpace 𝓘(ℝ, Fin n → ℝ) p}
    (hk₁ : ContMDiff 𝓘(ℝ, Fin n → ℝ) (𝓘(ℝ, Fin n → ℝ).prod 𝓘(ℝ, Fin n → ℝ)) ∞
      (fun q : M => (⟨q, k₁ q⟩ : TangentBundle 𝓘(ℝ, Fin n → ℝ) M)))
    (hk₂ : ContMDiff 𝓘(ℝ, Fin n → ℝ) (𝓘(ℝ, Fin n → ℝ).prod 𝓘(ℝ, Fin n → ℝ)) ∞
      (fun q : M => (⟨q, k₂ q⟩ : TangentBundle 𝓘(ℝ, Fin n → ℝ) M)))
    (hkN : ∀ x ∈ S, IsFutureNullNormalAt g T f x (k₁ x) ∧ IsFutureNullNormalAt g T f x (k₂ x))
    (hcls : ∀ x ∈ S, ∀ ν : TangentSpace 𝓘(ℝ, Fin n → ℝ) x, IsFutureNullNormalAt g T f x ν →
      (∃ μ : ℝ, 0 < μ ∧ ν = μ • k₁ x) ∨ ∃ μ : ℝ, 0 < μ ∧ ν = μ • k₂ x)
    (hChron : FocalImpliesChron g T S) (hNEC : ChartNEC g) {Λ : ℝ}
    (hΛ₁ : ExpansionBound g cov T S f k₁ Λ) (hΛ₂ : ExpansionBound g cov T S f k₂ Λ) :
    NormalisedFocalBound T S Λ := by
  classical
  intro γ L hL hγ hx hfar
  have hN := generator_isFutureNullNormal g T (by omega) hf hS hsub hL hγ hx hfar
  have hvel := velocity_eq_phase g hL hγ.1
  have key : ∀ (k : Π p : M, TangentSpace 𝓘(ℝ, Fin n → ℝ) p),
      ContMDiff 𝓘(ℝ, Fin n → ℝ) (𝓘(ℝ, Fin n → ℝ).prod 𝓘(ℝ, Fin n → ℝ)) ∞
        (fun q : M => (⟨q, k q⟩ : TangentBundle 𝓘(ℝ, Fin n → ℝ) M)) →
      (∀ x ∈ S, IsFutureNullNormalAt g T f x (k x)) → ExpansionBound g cov T S f k Λ → ∀ μ : ℝ, 0 < μ →
      (phase (n := n) γ 0).snd = μ • k (γ 0) →
      -(g.g (γ 0) (Causal.velocity 𝓘(ℝ, Fin n → ℝ) γ (Icc 0 L) 0) (T.X (γ 0))) * L ≤ Λ := by
    intro k hk hkN' hΛ μ hμ hv
    obtain ⟨e, heK, hortho, hneg, hbound⟩ := generator_focal_bound g hLC T hn hf hS hsub hsp (hexp) hk hkN'
      hChron hNEC hL hγ hx hfar hμ hv
    have hFE := frameExpansion_smul g cov k (γ 0) ((hk.contMDiffAt).mdifferentiableAt (by simp)) μ e
    rw [hFE] at hneg hbound
    have hkx := hkN' (γ 0) hx
    have hgneg := hkx.2.2.2
    have hΛk := hΛ (γ 0) hx e heK hortho
    have hb : 0 < |frameExpansion g cov k (γ 0) e| := by
      refine abs_pos.2 fun h0 => ?_
      rw [h0] at hneg; simp at hneg
    rw [abs_mul, abs_of_pos hμ] at hbound
    rw [hvel, hv]
    simp only [map_smul, ContinuousLinearMap.smul_apply]
    set a : ℝ := -(g.g (γ 0) (k (γ 0)) (T.X (γ 0))) with ha
    have hapos : 0 < a := by rw [ha]; linarith
    have hmb : 0 < μ * |frameExpansion g cov k (γ 0) e| := mul_pos hμ hb
    have h1 : L * (μ * |frameExpansion g cov k (γ 0) e|) ≤ ((n - 2 : ℕ) : ℝ) := by
      rwa [le_div_iff₀ hmb] at hbound
    have h2 : μ * L ≤ ((n - 2 : ℕ) : ℝ) / |frameExpansion g cov k (γ 0) e| := by
      rw [le_div_iff₀ hb]; linarith
    calc -(μ • g.g (γ 0) (k (γ 0)) (T.X (γ 0))) * L = a * (μ * L) := by rw [ha, smul_eq_mul]; ring
      _ ≤ a * (((n - 2 : ℕ) : ℝ) / |frameExpansion g cov k (γ 0) e|) := by
          exact mul_le_mul_of_nonneg_left h2 hapos.le
      _ ≤ Λ := hΛk
  rcases hcls (γ 0) hx _ hN with ⟨μ, hμ, hv⟩ | ⟨μ, hμ, hv⟩
  · exact key k₁ hk₁ (fun x hx' => (hkN x hx').1) hΛ₁ μ hμ hv
  · exact key k₂ hk₂ (fun x hx' => (hkN x hx').2) hΛ₂ μ hμ hv

end Lightlike.Penrose
