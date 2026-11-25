import Lightlike.Spacetime.PenroseSingularity.NullNormalPlane
import Lightlike.Spacetime.PenroseSingularity.TrappedSpacelike
import Lightlike.Canonical.FoliationSmooth

/-!
# Smooth future null normal fields of a spacelike codimension-two surface (G1-012, step D2)
-/

open Bundle Manifold Set
open scoped Manifold ContDiff

noncomputable section

namespace Lightlike.Penrose.NullNormal

theorem contDiffAt_kα (s : ℝ) {v₀ : ℝ × ℝ × ℝ × ℝ × ℝ}
    (h : 0 < Dd v₀.1 v₀.2.1 v₀.2.2.1) :
    ContDiffAt ℝ ∞ (fun v : ℝ × ℝ × ℝ × ℝ × ℝ => kα v.1 v.2.1 v.2.2.1 v.2.2.2.1 v.2.2.2.2 s) v₀ := by
  unfold kα Dd at *
  have hD : (fun v : ℝ × ℝ × ℝ × ℝ × ℝ => v.2.1 ^ 2 - v.1 * v.2.2.1) v₀ ≠ 0 := h.ne'
  have hDc : ContDiffAt ℝ ∞ (fun v : ℝ × ℝ × ℝ × ℝ × ℝ => v.2.1 ^ 2 - v.1 * v.2.2.1) v₀ := by fun_prop
  refine ContDiffAt.sub (ContDiffAt.mul (hDc.sqrt hD) (ContDiffAt.div (by fun_prop) hDc hD)) (by fun_prop)

theorem contDiffAt_kβ (s : ℝ) {v₀ : ℝ × ℝ × ℝ × ℝ × ℝ}
    (h : 0 < Dd v₀.1 v₀.2.1 v₀.2.2.1) :
    ContDiffAt ℝ ∞ (fun v : ℝ × ℝ × ℝ × ℝ × ℝ => kβ v.1 v.2.1 v.2.2.1 v.2.2.2.1 v.2.2.2.2 s) v₀ := by
  unfold kβ Dd at *
  have hD : (fun v : ℝ × ℝ × ℝ × ℝ × ℝ => v.2.1 ^ 2 - v.1 * v.2.2.1) v₀ ≠ 0 := h.ne'
  have hDc : ContDiffAt ℝ ∞ (fun v : ℝ × ℝ × ℝ × ℝ × ℝ => v.2.1 ^ 2 - v.1 * v.2.2.1) v₀ := by fun_prop
  refine ContDiffAt.add (ContDiffAt.mul (hDc.sqrt hD) (ContDiffAt.div (by fun_prop) hDc hD)) (by fun_prop)

section Manifold

open Lightlike.Canonical Lightlike

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Fin n → ℝ) M]
  [IsManifold 𝓘(ℝ, Fin n → ℝ) ∞ M] [IsManifold 𝓘(ℝ, Fin n → ℝ) 2 M] [T2Space M]
  (g : LorentzianMetric 𝓘(ℝ, Fin n → ℝ) M n) (f : M → Fin 2 → ℝ)
  (X : (x : M) → TangentSpace 𝓘(ℝ, Fin n → ℝ) x)

/-- The metric duals `∇fⁱ` of the components of `f`. -/
def gradN (i : Fin 2) (x : M) : TangentSpace 𝓘(ℝ, Fin n → ℝ) x :=
  timeGrad g.toNondegMetric (fun y => f y i) x

/-- The Gram entries `g(∇fⁱ, ∇fʲ)`. -/
def Gm (i j : Fin 2) (x : M) : ℝ := g.g x (gradN g f i x) (gradN g f j x)

/-- The pairings `g(∇fⁱ, X)`. -/
def Bm (i : Fin 2) (x : M) : ℝ := g.g x (gradN g f i x) (X x)

/-- The null normal field `kα ∇f⁰ + kβ ∇f¹`. -/
def nullField (s : ℝ) (x : M) : TangentSpace 𝓘(ℝ, Fin n → ℝ) x :=
  kα (Gm g f 0 0 x) (Gm g f 0 1 x) (Gm g f 1 1 x) (Bm g f X 0 x) (Bm g f X 1 x) s • gradN g f 0 x +
    kβ (Gm g f 0 0 x) (Gm g f 0 1 x) (Gm g f 1 1 x) (Bm g f X 0 x) (Bm g f X 1 x) s • gradN g f 1 x

variable {g f X}

theorem contMDiffAt_nullField (hf : ContMDiff 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin 2 → ℝ) ∞ f)
    (hX : ContMDiff 𝓘(ℝ, Fin n → ℝ) (𝓘(ℝ, Fin n → ℝ).prod 𝓘(ℝ, Fin n → ℝ)) ∞
      (fun x ↦ (⟨x, X x⟩ : TangentBundle 𝓘(ℝ, Fin n → ℝ) M))) (s : ℝ) {q : M}
    (hq : 0 < Dd (Gm g f 0 0 q) (Gm g f 0 1 q) (Gm g f 1 1 q)) :
    ContMDiffAt 𝓘(ℝ, Fin n → ℝ) (𝓘(ℝ, Fin n → ℝ).prod 𝓘(ℝ, Fin n → ℝ)) ∞
      (fun x : M => (⟨x, nullField g f X s x⟩ : TangentBundle 𝓘(ℝ, Fin n → ℝ) M)) q := by
  have hfi : ∀ i : Fin 2, ContMDiff 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, ℝ) ∞ (fun y => f y i) := fun i =>
    ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) i).contDiff.contMDiff).comp hf
  have hN : ∀ i : Fin 2, ContMDiffAt 𝓘(ℝ, Fin n → ℝ) (𝓘(ℝ, Fin n → ℝ).prod 𝓘(ℝ, Fin n → ℝ)) ∞
      (fun x : M => (⟨x, gradN g f i x⟩ : TangentBundle 𝓘(ℝ, Fin n → ℝ) M)) q := fun i =>
    contMDiffAt_timeGrad g.toNondegMetric (hfi i) q
  have hG : ∀ i j : Fin 2, ContMDiffAt 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, ℝ) ∞ (Gm g f i j) q := fun i j =>
    contMDiffAt_gpair g.toNondegMetric (hN i) (hN j)
  have hB : ∀ i : Fin 2, ContMDiffAt 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, ℝ) ∞ (Bm g f X i) q := fun i =>
    contMDiffAt_gpair g.toNondegMetric (hN i) (hX q)
  have hT : ContMDiffAt 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, ℝ × ℝ × ℝ × ℝ × ℝ) ∞
      (fun x => (Gm g f 0 0 x, Gm g f 0 1 x, Gm g f 1 1 x, Bm g f X 0 x, Bm g f X 1 x)) q :=
    (hG 0 0).prodMk_space ((hG 0 1).prodMk_space ((hG 1 1).prodMk_space
      ((hB 0).prodMk_space (hB 1))))
  have hα : ContMDiffAt 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, ℝ) ∞
      (fun x : M => kα (Gm g f 0 0 x) (Gm g f 0 1 x) (Gm g f 1 1 x) (Bm g f X 0 x) (Bm g f X 1 x) s) q :=
    ContDiffAt.comp_contMDiffAt (x := q)
      (f := fun x : M => (Gm g f 0 0 x, Gm g f 0 1 x, Gm g f 1 1 x, Bm g f X 0 x, Bm g f X 1 x))
      (g := fun v : ℝ × ℝ × ℝ × ℝ × ℝ => kα v.1 v.2.1 v.2.2.1 v.2.2.2.1 v.2.2.2.2 s)
      (contDiffAt_kα (s := s) (v₀ := (Gm g f 0 0 q, Gm g f 0 1 q, Gm g f 1 1 q, Bm g f X 0 q, Bm g f X 1 q)) hq) hT
  have hβ : ContMDiffAt 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, ℝ) ∞
      (fun x : M => kβ (Gm g f 0 0 x) (Gm g f 0 1 x) (Gm g f 1 1 x) (Bm g f X 0 x) (Bm g f X 1 x) s) q :=
    ContDiffAt.comp_contMDiffAt (x := q)
      (f := fun x : M => (Gm g f 0 0 x, Gm g f 0 1 x, Gm g f 1 1 x, Bm g f X 0 x, Bm g f X 1 x))
      (g := fun v : ℝ × ℝ × ℝ × ℝ × ℝ => kβ v.1 v.2.1 v.2.2.1 v.2.2.2.1 v.2.2.2.2 s)
      (contDiffAt_kβ (s := s) (v₀ := (Gm g f 0 0 q, Gm g f 0 1 q, Gm g f 1 1 q, Bm g f X 0 q, Bm g f X 1 q)) hq) hT
  exact (hα.smul_section (hN 0)).add_section (hβ.smul_section (hN 1))

theorem mfderiv_component (hf : ContMDiff 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin 2 → ℝ) ∞ f) (i : Fin 2) (x : M)
    (v : TangentSpace 𝓘(ℝ, Fin n → ℝ) x) :
    mfderiv 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, ℝ) (fun y => f y i) x v = mfderiv 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin 2 → ℝ) f x v i := by
  have hfx : MDifferentiableAt 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin 2 → ℝ) f x :=
    (hf x).mdifferentiableAt (by simp)
  have hp : MDifferentiableAt 𝓘(ℝ, Fin 2 → ℝ) 𝓘(ℝ, ℝ)
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) i) (f x) :=
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) i).differentiableAt.mdifferentiableAt
  have h := mfderiv_comp x hp hfx
  have e : (fun y => f y i) = (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) i) ∘ f := rfl
  rw [e, h]
  simp [mfderiv_eq_fderiv]
  rfl

theorem g_gradN (hf : ContMDiff 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin 2 → ℝ) ∞ f) (i : Fin 2) (x : M)
    (v : TangentSpace 𝓘(ℝ, Fin n → ℝ) x) :
    g.g x (gradN g f i x) v = mfderiv 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin 2 → ℝ) f x v i := by
  unfold gradN
  rw [g_timeGrad]
  exact mfderiv_component hf i x v

theorem nullField_spec (hf : ContMDiff 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin 2 → ℝ) ∞ f) {x : M}
    (hDf : Function.Surjective (mfderiv 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin 2 → ℝ) f x))
    (hsp : ∀ v : TangentSpace 𝓘(ℝ, Fin n → ℝ) x,
      mfderiv 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin 2 → ℝ) f x v = 0 → v ≠ 0 → 0 < g.g x v v)
    (hXt : g.g x (X x) (X x) < 0) :
    0 < Dd (Gm g f 0 0 x) (Gm g f 0 1 x) (Gm g f 1 1 x) ∧
      ∀ s : ℝ, s ^ 2 = 1 →
        g.g x (nullField g f X s x) (nullField g f X s x) = 0 ∧
        (∀ v : TangentSpace 𝓘(ℝ, Fin n → ℝ) x,
          mfderiv 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin 2 → ℝ) f x v = 0 → g.g x (nullField g f X s x) v = 0) ∧
        g.g x (nullField g f X s x) (X x) < 0 := by
  have hpd := planeData_of_df (g.lorentzian x) (mfderiv 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin 2 → ℝ) f x) hDf
    (gradN g f 0 x) (gradN g f 1 x) (fun v => g_gradN hf 0 x v) (fun v => g_gradN hf 1 x v) hsp hXt
  obtain ⟨hD, hQ⟩ := hpd.D_pos_Q_pos
  simp only [ContinuousLinearMap.toBilinForm_apply] at hD hQ
  have h21 : g.g x (gradN g f 1 x) (gradN g f 0 x) = Gm g f 0 1 x := g.symm x _ _
  have hD' : 0 < Dd (Gm g f 0 0 x) (Gm g f 0 1 x) (Gm g f 1 1 x) := hD
  have e00 : g.g x (gradN g f 0 x) (gradN g f 0 x) = Gm g f 0 0 x := rfl
  have e01 : g.g x (gradN g f 0 x) (gradN g f 1 x) = Gm g f 0 1 x := rfl
  have e11 : g.g x (gradN g f 1 x) (gradN g f 1 x) = Gm g f 1 1 x := rfl
  have eB0 : g.g x (gradN g f 0 x) (X x) = Bm g f X 0 x := rfl
  have eB1 : g.g x (gradN g f 1 x) (X x) = Bm g f X 1 x := rfl
  have expand : ∀ (a b : ℝ) (w : TangentSpace 𝓘(ℝ, Fin n → ℝ) x),
      g.g x (a • gradN g f 0 x + b • gradN g f 1 x) w =
        a * g.g x (gradN g f 0 x) w + b * g.g x (gradN g f 1 x) w := fun a b w => by
    simp [map_add, map_smul]
  have expand2 : ∀ (a b c d : ℝ), g.g x (a • gradN g f 0 x + b • gradN g f 1 x)
      (c • gradN g f 0 x + d • gradN g f 1 x) =
        a * c * Gm g f 0 0 x + (a * d + b * c) * Gm g f 0 1 x + b * d * Gm g f 1 1 x := by
    intro a b c d
    rw [expand]
    simp only [map_add, map_smul, smul_eq_mul, e00, e01, h21, e11]
    ring
  refine ⟨hD', fun s hs => ⟨?_, ?_, ?_⟩⟩
  · have hn := kα_kβ_null (b1 := Bm g f X 0 x) (b2 := Bm g f X 1 x) hD' hs
    show g.g x _ _ = 0
    unfold nullField
    rw [expand2]
    linarith
  · intro v hv
    unfold nullField
    rw [expand]
    have e0 := g_gradN (g := g) hf 0 x v
    have e1 := g_gradN (g := g) hf 1 x v
    have e0' : g.g x (gradN g f 0 x) v = 0 := by rw [e0, hv]; rfl
    have e1' : g.g x (gradN g f 1 x) v = 0 := by rw [e1, hv]; rfl
    rw [e0', e1']; ring
  · unfold nullField
    rw [expand, eB0, eB1]
    rw [kα_mul_add_kβ_mul hD']
    have hQ' : 0 < Qq (Gm g f 0 0 x) (Gm g f 0 1 x) (Gm g f 1 1 x) (Bm g f X 0 x) (Bm g f X 1 x) := hQ
    have : 0 < Real.sqrt (Dd (Gm g f 0 0 x) (Gm g f 0 1 x) (Gm g f 1 1 x)) *
        Qq (Gm g f 0 0 x) (Gm g f 0 1 x) (Gm g f 1 1 x) (Bm g f X 0 x) (Bm g f X 1 x) /
          Dd (Gm g f 0 0 x) (Gm g f 0 1 x) (Gm g f 1 1 x) :=
      div_pos (mul_pos (Real.sqrt_pos.2 hD') hQ') hD'
    linarith

set_option maxHeartbeats 1600000 in
theorem nullField_classify (T : Causal.TimeOrientation g)
    (hf : ContMDiff 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin 2 → ℝ) ∞ f) {x : M}
    (hDf : Function.Surjective (mfderiv 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin 2 → ℝ) f x))
    (hsp : ∀ v : TangentSpace 𝓘(ℝ, Fin n → ℝ) x,
      mfderiv 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin 2 → ℝ) f x v = 0 → v ≠ 0 → 0 < g.g x v v)
    (hXt : g.g x (X x) (X x) < 0) (hXT : g.g x (X x) (T.X x) < 0)
    {ν : TangentSpace 𝓘(ℝ, Fin n → ℝ) x}
    (hν : ν ≠ 0 ∧ g.g x ν ν = 0 ∧
      (∀ v : TangentSpace 𝓘(ℝ, Fin n → ℝ) x,
        mfderiv 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin 2 → ℝ) f x v = 0 → g.g x ν v = 0) ∧ g.g x ν (T.X x) < 0) :
    ∃ s : ℝ, s ^ 2 = 1 ∧ ∃ μ : ℝ, 0 < μ ∧ ν = μ • nullField g f X s x := by
  have hpd := planeData_of_df (g.lorentzian x) (mfderiv 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin 2 → ℝ) f x) hDf
    (gradN g f 0 x) (gradN g f 1 x) (fun v => g_gradN hf 0 x v) (fun v => g_gradN hf 1 x v) hsp hXt
  obtain ⟨hD, hQ⟩ := hpd.D_pos_Q_pos
  simp only [ContinuousLinearMap.toBilinForm_apply] at hD hQ
  have hD' : 0 < Dd (Gm g f 0 0 x) (Gm g f 0 1 x) (Gm g f 1 1 x) := hD
  have h21 : g.g x (gradN g f 1 x) (gradN g f 0 x) = Gm g f 0 1 x := g.symm x _ _
  have e00 : g.g x (gradN g f 0 x) (gradN g f 0 x) = Gm g f 0 0 x := rfl
  have e01 : g.g x (gradN g f 0 x) (gradN g f 1 x) = Gm g f 0 1 x := rfl
  have e11 : g.g x (gradN g f 1 x) (gradN g f 1 x) = Gm g f 1 1 x := rfl
  have expand : ∀ (a b : ℝ) (w : TangentSpace 𝓘(ℝ, Fin n → ℝ) x),
      g.g x (a • gradN g f 0 x + b • gradN g f 1 x) w =
        a * g.g x (gradN g f 0 x) w + b * g.g x (gradN g f 1 x) w := fun a b w => by
    simp [map_add, map_smul]
  have expand2 : ∀ (a b c d : ℝ), g.g x (a • gradN g f 0 x + b • gradN g f 1 x)
      (c • gradN g f 0 x + d • gradN g f 1 x) =
        a * c * Gm g f 0 0 x + (a * d + b * c) * Gm g f 0 1 x + b * d * Gm g f 1 1 x := by
    intro a b c d
    rw [expand]
    simp only [map_add, map_smul, smul_eq_mul, e00, e01, h21, e11]
    ring
  -- ν lies in the plane
  obtain ⟨a, b, hab⟩ := hpd.exists_decomp ν (fun v h1 h2 => by
    simp only [ContinuousLinearMap.toBilinForm_apply] at h1 h2 ⊢
    refine hν.2.2.1 v ?_
    funext i
    fin_cases i
    · have := g_gradN (g := g) hf 0 x v; rw [h1] at this; exact this.symm
    · have := g_gradN (g := g) hf 1 x v; rw [h2] at this; exact this.symm)
  have hquad : Gm g f 0 0 x * a ^ 2 + 2 * Gm g f 0 1 x * a * b + Gm g f 1 1 x * b ^ 2 = 0 := by
    have := hν.2.1
    rw [hab, expand2] at this
    linarith
  obtain ⟨s, hs, hpar⟩ := exists_sign_parallel (b1 := Bm g f X 0 x) (b2 := Bm g f X 1 x) hD' hquad
  have hspec := (nullField_spec hf hDf hsp hXt).2 s hs
  set α := kα (Gm g f 0 0 x) (Gm g f 0 1 x) (Gm g f 1 1 x) (Bm g f X 0 x) (Bm g f X 1 x) s with hα
  set β := kβ (Gm g f 0 0 x) (Gm g f 0 1 x) (Gm g f 1 1 x) (Bm g f X 0 x) (Bm g f X 1 x) s with hβ
  have hkX : g.g x (nullField g f X s x) (X x) < 0 := hspec.2.2
  have hkα : α * Bm g f X 0 x + β * Bm g f X 1 x < 0 := by
    have : g.g x (nullField g f X s x) (X x) = α * Bm g f X 0 x + β * Bm g f X 1 x := by
      unfold nullField; rw [expand]; rfl
    linarith
  have hαβ : 0 < α ^ 2 + β ^ 2 := by
    by_contra hcon
    have h1 : α ^ 2 = 0 := by nlinarith [sq_nonneg α, sq_nonneg β, not_lt.1 hcon]
    have h2 : β ^ 2 = 0 := by nlinarith [sq_nonneg α, sq_nonneg β, not_lt.1 hcon]
    have h1' : α = 0 := pow_eq_zero_iff (two_ne_zero) |>.1 h1
    have h2' : β = 0 := pow_eq_zero_iff (two_ne_zero) |>.1 h2
    rw [h1', h2'] at hkα; simp at hkα
  set μ : ℝ := (a * α + b * β) / (α ^ 2 + β ^ 2) with hμ
  have ha : a = μ * α := by
    rw [hμ, div_mul_eq_mul_div, eq_div_iff hαβ.ne']; linear_combination β * hpar
  have hb : b = μ * β := by
    rw [hμ, div_mul_eq_mul_div, eq_div_iff hαβ.ne']; linear_combination (-α) * hpar
  have hνk : ν = μ • nullField g f X s x := by
    rw [hab]; unfold nullField
    rw [smul_add, smul_smul, smul_smul, ← ha, ← hb]
  have hνX : g.g x ν (X x) < 0 := by
    have := null_neg_of_coorient (g.lorentzian x) (T.timelike x) hXt (by rw [g.symm]; exact hXT)
      hν.2.1 hν.2.2.2
    exact this
  have hμpos : 0 < μ := by
    rw [hνk, map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul] at hνX
    by_contra hc
    nlinarith [hkX, not_lt.1 hc]
  exact ⟨s, hs, μ, hμpos, hνk⟩


end Manifold

section Global

open Lightlike.Canonical Lightlike Lightlike.Causal

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Fin n → ℝ) M]
  [IsManifold 𝓘(ℝ, Fin n → ℝ) ∞ M] [IsManifold 𝓘(ℝ, Fin n → ℝ) 2 M] [T2Space M]
  [SecondCountableTopology M]
  {g : LorentzianMetric 𝓘(ℝ, Fin n → ℝ) M n}

/-- **A global smooth future null normal field of a closed spacelike surface**: for `S = f⁻¹(0)` compact
with `df` surjective and `ker df` spacelike along `S`, and each sign `s = ±1`, there is a smooth field on
all of `M` which is a future null normal of `S` at each point of `S`. -/
theorem exists_global_null_normal (T : TimeOrientation g) {S : Set M} (hSc : IsCompact S)
    {f : M → Fin 2 → ℝ} (hf : ContMDiff 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin 2 → ℝ) ∞ f)
    (hSf : S = f ⁻¹' {0})
    (hDf : ∀ x ∈ S, Function.Surjective (mfderiv 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin 2 → ℝ) f x))
    (hsp : ∀ x ∈ S, ∀ v : TangentSpace 𝓘(ℝ, Fin n → ℝ) x,
      mfderiv 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin 2 → ℝ) f x v = 0 → v ≠ 0 → 0 < g.g x v v)
    {X : (x : M) → TangentSpace 𝓘(ℝ, Fin n → ℝ) x}
    (hXs : ContMDiff 𝓘(ℝ, Fin n → ℝ) (𝓘(ℝ, Fin n → ℝ).prod 𝓘(ℝ, Fin n → ℝ)) ∞
      (fun x ↦ TotalSpace.mk' (Fin n → ℝ) (E := fun x : M ↦ TangentSpace 𝓘(ℝ, Fin n → ℝ) x) x (X x)))
    (hX : ∀ x, g.g x (X x) (X x) < 0 ∧ g.g x (X x) (T.X x) < 0)
    (s : ℝ) (hs : s ^ 2 = 1) :
    ∃ k : (x : M) → TangentSpace 𝓘(ℝ, Fin n → ℝ) x,
      ContMDiff 𝓘(ℝ, Fin n → ℝ) (𝓘(ℝ, Fin n → ℝ).prod 𝓘(ℝ, Fin n → ℝ)) ∞
        (fun q : M => (⟨q, k q⟩ : TangentBundle 𝓘(ℝ, Fin n → ℝ) M)) ∧
      (∀ x ∈ S, IsFutureNullNormalAt g T f x (k x)) ∧ ∀ x ∈ S, k x = nullField g f X s x := by
  classical
  haveI : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace (Fin n → ℝ) M
  haveI : SigmaCompactSpace M := inferInstance
  have hXt : ∀ x, g.g x (X x) (X x) < 0 := fun x => (hX x).1
  -- the open set where the Gram determinant is negative
  have hGc : ∀ i j : Fin 2, Continuous (Gm g f i j) := fun i j => by
    have hfi : ∀ i : Fin 2, ContMDiff 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, ℝ) ∞ (fun y => f y i) := fun i =>
      ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) i).contDiff.contMDiff).comp hf
    refine continuous_iff_continuousAt.2 fun q => ?_
    exact (contMDiffAt_gpair g.toNondegMetric (contMDiffAt_timeGrad g.toNondegMetric (hfi i) q)
      (contMDiffAt_timeGrad g.toNondegMetric (hfi j) q)).continuousAt
  set U : Set M := {x | 0 < Dd (Gm g f 0 0 x) (Gm g f 0 1 x) (Gm g f 1 1 x)} with hU
  have hUo : IsOpen U := by
    have : Continuous fun x => Dd (Gm g f 0 0 x) (Gm g f 0 1 x) (Gm g f 1 1 x) := by
      unfold Dd
      exact ((hGc 0 1).pow 2).sub ((hGc 0 0).mul (hGc 1 1))
    exact isOpen_lt continuous_const this
  have hspec : ∀ x ∈ S, 0 < Dd (Gm g f 0 0 x) (Gm g f 0 1 x) (Gm g f 1 1 x) ∧
      ∀ s : ℝ, s ^ 2 = 1 →
        g.g x (nullField g f X s x) (nullField g f X s x) = 0 ∧
        (∀ v : TangentSpace 𝓘(ℝ, Fin n → ℝ) x,
          mfderiv 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin 2 → ℝ) f x v = 0 → g.g x (nullField g f X s x) v = 0) ∧
        g.g x (nullField g f X s x) (X x) < 0 := fun x hx =>
    nullField_spec hf (hDf x hx) (hsp x hx) (hXt x)
  have hSU : S ⊆ U := fun x hx => (hspec x hx).1
  obtain ⟨L, hLc, hSL, hLU⟩ := exists_compact_between hSc hUo hSU
  obtain ⟨φ, hφs, -, hφ0, hφ1⟩ := exists_contMDiff_zero_iff_one_iff_of_isClosed
    (I := 𝓘(ℝ, Fin n → ℝ)) (n := (⊤ : ℕ∞)) (M := M) (s := (interior L)ᶜ) (t := S)
    isOpen_interior.isClosed_compl (hSf ▸ (isClosed_singleton.preimage hf.continuous))
    (disjoint_compl_left_iff.2 hSL)
  refine ⟨fun x => φ x • nullField g f X s x, ?_, ?_⟩
  · intro q
    by_cases hqU : q ∈ U
    · exact ContMDiffAt.smul_section (hφs.contMDiffAt) (contMDiffAt_nullField hf hXs s hqU)
    · have hqL : q ∉ L := fun h => hqU (hLU h)
      have hev : (fun x : M => (⟨x, φ x • nullField g f X s x⟩ : TangentBundle 𝓘(ℝ, Fin n → ℝ) M)) =ᶠ[nhds q]
          (zeroSection (Fin n → ℝ) (TangentSpace 𝓘(ℝ, Fin n → ℝ) : M → Type _)) := by
        filter_upwards [(hLc.isClosed.isOpen_compl).mem_nhds hqL] with x hx
        have : φ x = 0 := (hφ0 x).1 (fun hxi => hx (interior_subset hxi))
        simp [this, zeroSection]
      exact (contMDiffAt_zeroSection _ _).congr_of_eventuallyEq hev
  · refine ⟨fun x hx => ?_, fun x hx => by show φ x • nullField g f X s x = _; rw [(hφ1 x).1 hx, one_smul]⟩
    have hφx : φ x = 1 := (hφ1 x).1 hx
    obtain ⟨hD, hsp'⟩ := hspec x hx
    obtain ⟨hnull, hnorm, hfut⟩ := hsp' s hs
    have hk : φ x • nullField g f X s x = nullField g f X s x := by rw [hφx, one_smul]
    show IsFutureNullNormalAt g T f x (φ x • nullField g f X s x)
    rw [hk]
    refine ⟨?_, hnull, hnorm, ?_⟩
    · intro h0
      rw [h0] at hfut
      simp at hfut
    · exact null_neg_of_coorient (g.lorentzian x) (hXt x) (T.timelike x) (hX x).2 hnull hfut


end Global


end Lightlike.Penrose.NullNormal
