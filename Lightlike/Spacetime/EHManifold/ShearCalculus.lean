import Lightlike.Spacetime.Curvature
import Lightlike.Spacetime.EHManifold.ShearMap

/-!
# Calculus of the shear that flattens a graph

* `shearFwd_eq`: `shearFwd γ i x = x + γ(x') • e_i`;
* `contDiff_shearFwd`: the shear is `C¹` when `γ` is;
* `pd_comp_shearFwd_same`, `pd_comp_shearFwd_succAbove`: the chain rule for partial derivatives of
  `H ∘ shearFwd γ i`: `∂_i (H ∘ Ψ) = (∂_i H) ∘ Ψ` and
  `∂_{k'} (H ∘ Ψ) = (∂_{k'} H) ∘ Ψ + ∂_k γ · (∂_i H) ∘ Ψ` for the `k`-th other coordinate `k'`.

Supporting lemmas for the divergence theorem on a domain bounded by a graph; no catalogue entry.
-/

open Set
open scoped ContDiff

noncomputable section

namespace Lightlike

variable {n : ℕ}

/-- Removing the `i`-th coordinate, as a continuous linear map. -/
def removeNthL (i : Fin (n + 1)) : (Fin (n + 1) → ℝ) →L[ℝ] (Fin n → ℝ) :=
  ContinuousLinearMap.pi fun k => ContinuousLinearMap.proj (i.succAbove k)

@[simp] lemma removeNthL_apply (i : Fin (n + 1)) (x : Fin (n + 1) → ℝ) :
    removeNthL i x = i.removeNth x := rfl

lemma removeNthL_single_same (i : Fin (n + 1)) : removeNthL i (Pi.single i (1 : ℝ)) = 0 := by
  ext k
  simp [removeNthL, Fin.removeNth, Pi.single_apply, Fin.succAbove_ne]

lemma removeNthL_single_succAbove (i : Fin (n + 1)) (k : Fin n) :
    removeNthL i (Pi.single (i.succAbove k) (1 : ℝ)) = Pi.single k 1 := by
  ext l
  simp [removeNthL, Fin.removeNth, Pi.single_apply, Fin.succAbove_right_inj]

lemma removeNth_single_same (i : Fin (n + 1)) :
    i.removeNth (Pi.single i (1 : ℝ) : Fin (n + 1) → ℝ) = 0 :=
  removeNthL_single_same i

lemma removeNth_single_succAbove (i : Fin (n + 1)) (k : Fin n) :
    i.removeNth (Pi.single (i.succAbove k) (1 : ℝ) : Fin (n + 1) → ℝ) = Pi.single k 1 :=
  removeNthL_single_succAbove i k

/-- The shear adds `γ(x')` times the `i`-th basis vector. -/
lemma shearFwd_eq (γ : (Fin n → ℝ) → ℝ) (i : Fin (n + 1)) (x : Fin (n + 1) → ℝ) :
    shearFwd γ i x = x + γ (i.removeNth x) • (Pi.single i (1 : ℝ) : Fin (n + 1) → ℝ) := by
  ext j
  rcases Fin.eq_self_or_eq_succAbove i j with rfl | ⟨k, rfl⟩
  · simp [shearFwd]
  · simp [shearFwd, Fin.removeNth, Fin.succAbove_ne]

/-- The derivative of the shear. -/
lemma hasFDerivAt_shearFwd (γ : (Fin n → ℝ) → ℝ) (i : Fin (n + 1)) (x : Fin (n + 1) → ℝ)
    (hγ : DifferentiableAt ℝ γ (i.removeNth x)) :
    HasFDerivAt (shearFwd γ i)
      (ContinuousLinearMap.id ℝ (Fin (n + 1) → ℝ) +
        ((fderiv ℝ γ (i.removeNth x)).comp (removeNthL i)).smulRight
          (Pi.single i (1 : ℝ) : Fin (n + 1) → ℝ)) x := by
  have hfun : shearFwd γ i = fun x => x + γ (removeNthL i x) • (Pi.single i (1 : ℝ) : Fin (n + 1) → ℝ) :=
    funext fun x => shearFwd_eq γ i x
  rw [hfun]
  have h1 : HasFDerivAt (fun x => γ (removeNthL i x))
      ((fderiv ℝ γ (i.removeNth x)).comp (removeNthL i)) x :=
    HasFDerivAt.comp x (by rw [removeNthL_apply]; exact hγ.hasFDerivAt) (removeNthL i).hasFDerivAt
  exact (hasFDerivAt_id x).add (h1.smul_const _)

/-- The shear is `C¹` when `γ` is. -/
lemma contDiff_shearFwd (γ : (Fin n → ℝ) → ℝ) (hγ : ContDiff ℝ 1 γ) (i : Fin (n + 1)) :
    ContDiff ℝ 1 (shearFwd γ i) := by
  have hfun : shearFwd γ i = fun x => x + γ (removeNthL i x) • (Pi.single i (1 : ℝ) : Fin (n + 1) → ℝ) :=
    funext fun x => shearFwd_eq γ i x
  rw [hfun]
  exact contDiff_id.add ((hγ.comp (removeNthL i).contDiff).smul contDiff_const)

/-- **Chain rule, normal direction**: `∂_i (H ∘ Ψ) = (∂_i H) ∘ Ψ`. -/
theorem pd_comp_shearFwd_same (γ : (Fin n → ℝ) → ℝ) (i : Fin (n + 1)) (H : (Fin (n + 1) → ℝ) → ℝ)
    (x : Fin (n + 1) → ℝ) (hγ : DifferentiableAt ℝ γ (i.removeNth x))
    (hH : DifferentiableAt ℝ H (shearFwd γ i x)) :
    pd i (fun z => H (shearFwd γ i z)) x = pd i H (shearFwd γ i x) := by
  unfold pd
  have hc := (hH.hasFDerivAt.comp x (hasFDerivAt_shearFwd γ i x hγ)).fderiv
  have hc' : fderiv ℝ (fun z => H (shearFwd γ i z)) x = _ := hc
  rw [hc']
  simp [removeNth_single_same]

/-- **Chain rule, tangential directions**:
`∂_{k'} (H ∘ Ψ) = (∂_{k'} H) ∘ Ψ + ∂_k γ · (∂_i H) ∘ Ψ`. -/
theorem pd_comp_shearFwd_succAbove (γ : (Fin n → ℝ) → ℝ) (i : Fin (n + 1)) (k : Fin n)
    (H : (Fin (n + 1) → ℝ) → ℝ) (x : Fin (n + 1) → ℝ)
    (hγ : DifferentiableAt ℝ γ (i.removeNth x)) (hH : DifferentiableAt ℝ H (shearFwd γ i x)) :
    pd (i.succAbove k) (fun z => H (shearFwd γ i z)) x =
      pd (i.succAbove k) H (shearFwd γ i x) + pd k γ (i.removeNth x) * pd i H (shearFwd γ i x) := by
  unfold pd
  have hc := (hH.hasFDerivAt.comp x (hasFDerivAt_shearFwd γ i x hγ)).fderiv
  have hc' : fderiv ℝ (fun z => H (shearFwd γ i z)) x = _ := hc
  rw [hc']
  simp [removeNth_single_succAbove]

end Lightlike
