import Lightlike.Rows.G1_044.KKDiff

/-!
# Invariance under translation in the fifth coordinate (G1-044)

The Kaluza-Klein metric is invariant under `y ↦ y + t e₅`; hence so are its Christoffel symbols and the difference
tensor `kkDiff`, and their derivative `∂_n` along the last coordinate vanishes (`pd_last_kkDiff`).  This needs no explicit
formula for the components.

Supporting file for the row G1-044 (Kaluza-Klein reduction).
-/

open Matrix

noncomputable section

namespace Lightlike

namespace KK

variable {n : ℕ}

/-- The unit vector along the fifth coordinate. -/
def e5 (n : ℕ) : Fin (n + 1) → ℝ := Pi.single (Fin.last n) 1

theorem proj_add_smul_e5 (y : Fin (n + 1) → ℝ) (t : ℝ) : proj (y + t • e5 n) = proj y := by
  funext i
  simp [proj, e5, (Fin.castSucc_lt_last i).ne]

theorem kkMetric_add_smul_e5 (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (A : (Fin n → ℝ) → Fin n → ℝ)
    (φ : (Fin n → ℝ) → ℝ) (y : Fin (n + 1) → ℝ) (t : ℝ) :
    kkMetric g A φ (y + t • e5 n) = kkMetric g A φ y := by
  simp only [kkMetric, proj_add_smul_e5]

/-- A partial derivative of a function invariant under a translation is invariant under it. -/
theorem pd_add_of_invariant {m : ℕ} (f : (Fin m → ℝ) → ℝ) (v y : Fin m → ℝ) (hf : ∀ z, f (z + v) = f z)
    (k : Fin m) : pd k f (y + v) = pd k f y := by
  unfold pd
  have h : (fun z => f (z + v)) = f := funext hf
  have := fderiv_comp_add_right (𝕜 := ℝ) (f := f) (x := y) v
  rw [h] at this
  rw [← this]

/-- A function invariant under translations in the fifth direction has vanishing `∂_n`. -/
theorem pd_last_of_invariant (f : (Fin (n + 1) → ℝ) → ℝ) (hf : ∀ (t : ℝ) y, f (y + t • e5 n) = f y)
    (y : Fin (n + 1) → ℝ) : pd (Fin.last n) f y = 0 := by
  unfold pd
  by_cases hd : DifferentiableAt ℝ f y
  · have h1 : HasDerivAt (fun t : ℝ => y + t • e5 n) (e5 n) 0 := by
      simpa using ((hasDerivAt_id' (0 : ℝ)).smul_const (e5 n)).const_add y
    have h2 : HasDerivAt (fun t : ℝ => f (y + t • e5 n)) (fderiv ℝ f y (e5 n)) 0 :=
      HasFDerivAt.comp_hasDerivAt (l := f) (0 : ℝ) (by simpa using hd.hasFDerivAt) h1
    have h3 : HasDerivAt (fun t : ℝ => f (y + t • e5 n)) 0 0 := by
      simp only [hf]
      exact hasDerivAt_const _ _
    exact h2.unique h3
  · rw [fderiv_zero_of_not_differentiableAt hd]
    rfl

/-- The Christoffel symbols of the Kaluza-Klein metric are invariant under translations in the fifth direction. -/
theorem christoffel_kk_add_smul_e5 (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (A : (Fin n → ℝ) → Fin n → ℝ)
    (φ : (Fin n → ℝ) → ℝ) (i j k : Fin (n + 1)) (y : Fin (n + 1) → ℝ) (t : ℝ) :
    christoffel (kkMetric g A φ) i j k (y + t • e5 n) = christoffel (kkMetric g A φ) i j k y := by
  have hp : ∀ (a b l : Fin (n + 1)),
      pd l (fun z => kkMetric g A φ z a b) (y + t • e5 n) = pd l (fun z => kkMetric g A φ z a b) y :=
    fun a b l => pd_add_of_invariant _ _ _ (fun z => by rw [kkMetric_add_smul_e5]) l
  unfold christoffel
  simp only [hp, kkMetric_add_smul_e5]

/-- The product metric is a Kaluza-Klein metric. -/
theorem christoffel_kkRef_add_smul_e5 (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (i j k : Fin (n + 1))
    (y : Fin (n + 1) → ℝ) (t : ℝ) :
    christoffel (kkRef g) i j k (y + t • e5 n) = christoffel (kkRef g) i j k y :=
  christoffel_kk_add_smul_e5 g _ _ i j k y t

/-- The difference tensor has vanishing derivative along the fifth coordinate. -/
theorem pd_last_kkDiff (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (A : (Fin n → ℝ) → Fin n → ℝ)
    (φ : (Fin n → ℝ) → ℝ) (i j k : Fin (n + 1)) (y : Fin (n + 1) → ℝ) :
    pd (Fin.last n) (kkDiff g A φ i j k) y = 0 :=
  pd_last_of_invariant _ (fun t z => by
    unfold kkDiff
    rw [christoffel_kk_add_smul_e5, christoffel_kkRef_add_smul_e5]) y

end KK

end Lightlike
