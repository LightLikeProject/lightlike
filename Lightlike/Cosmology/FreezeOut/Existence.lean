module

public import Mathlib
public import Lightlike.Cosmology.FreezeOut.Basic

/-!
# Global existence for forward ODEs with a bounded, globally Lipschitz right-hand side

Row G1-034 (milestone CO7).  Step 1 of existence: a generic gluing of the local Picard–Lindelöf
solutions on `[t₀, t₀ + n]` into one global forward solution.

* `exists_global_forward`: if `f t` is `Lc`-Lipschitz and bounded by `B` for all `t ≥ t₀`, and
  `t ↦ f t y` is continuous on `[t₀, ∞)`, there is `Y` with `Y t₀ = y₀` and
  `HasDerivWithinAt Y (f t (Y t)) (Ici t₀) t` for all `t ≥ t₀`.
-/

@[expose] public section

namespace Lightlike.Cosmology.FreezeOut

open Set Metric
open scoped NNReal

/-- `[t₀, b]` is a neighbourhood of `t` within `[s, ∞)` when `t₀ ≤ s ≤ t < b`. -/
lemma Icc_mem_nhdsWithin_Ici {t₀ s t b : ℝ} (h0 : t₀ ≤ s) (_hst : s ≤ t) (htb : t < b) :
    Icc t₀ b ∈ nhdsWithin t (Ici s) :=
  mem_nhdsWithin.2 ⟨Iio b, isOpen_Iio, htb, fun _ hx => ⟨h0.trans hx.2, hx.1.le⟩⟩

/-- Local solutions on `[t₀, t₀ + n]` for a bounded globally Lipschitz field. -/
lemma exists_local_forward {f : ℝ → ℝ → ℝ} {t₀ y₀ : ℝ} {Lc B : ℝ≥0}
    (hlip : ∀ t, t₀ ≤ t → LipschitzWith Lc (f t))
    (hcont : ∀ y, ContinuousOn (fun t => f t y) (Ici t₀))
    (hb : ∀ t, t₀ ≤ t → ∀ y, ‖f t y‖ ≤ B) (n : ℕ) :
    ∃ α : ℝ → ℝ, α t₀ = y₀ ∧ ∀ t ∈ Icc t₀ (t₀ + n),
      HasDerivWithinAt α (f t (α t)) (Icc t₀ (t₀ + n)) t := by
  have hpl : IsPicardLindelof f (tmin := t₀) (tmax := t₀ + n) ⟨t₀, by simp, by simp⟩ y₀
      (B * n) 0 B Lc :=
    { lipschitzOnWith := fun t ht => (hlip t ht.1).lipschitzOnWith
      continuousOn := fun y _ => (hcont y).mono (fun t ht => ht.1)
      norm_le := fun t ht y _ => hb t ht.1 y
      mul_max_le := by simp }
  obtain ⟨α, h1, h2⟩ := hpl.exists_eq_forall_mem_Icc_hasDerivWithinAt₀
  exact ⟨α, h1, h2⟩

/-- **Global forward existence** for a bounded, globally Lipschitz field (gluing of local
solutions). -/
theorem exists_global_forward {f : ℝ → ℝ → ℝ} {t₀ y₀ : ℝ} {Lc B : ℝ≥0}
    (hlip : ∀ t, t₀ ≤ t → LipschitzWith Lc (f t))
    (hcont : ∀ y, ContinuousOn (fun t => f t y) (Ici t₀))
    (hb : ∀ t, t₀ ≤ t → ∀ y, ‖f t y‖ ≤ B) :
    ∃ Y : ℝ → ℝ, Y t₀ = y₀ ∧ ∀ t, t₀ ≤ t → HasDerivWithinAt Y (f t (Y t)) (Ici t₀) t := by
  choose α hα0 hα using exists_local_forward hlip hcont hb (y₀ := y₀)
  -- consistency of the local solutions
  have cons : ∀ n m : ℕ, n ≤ m → EqOn (α n) (α m) (Icc t₀ (t₀ + n)) := by
    intro n m hnm
    have hnm' : (n : ℝ) ≤ m := by exact_mod_cast hnm
    have hsub : Icc t₀ (t₀ + n) ⊆ Icc t₀ (t₀ + m) := Icc_subset_Icc_right (by linarith)
    refine ODE_solution_unique_of_mem_Icc_right (v := f) (s := fun _ => univ) (K := Lc)
      (a := t₀) (b := t₀ + n) (fun t ht => (hlip t ht.1).lipschitzOnWith)
      (fun t ht => (hα n t ht).continuousWithinAt) ?_ (fun _ _ => mem_univ _)
      (fun t ht => ((hα m t (hsub ht)).continuousWithinAt.mono hsub)) ?_
      (fun _ _ => mem_univ _) ((hα0 n).trans (hα0 m).symm)
    · intro t ht
      exact (hα n t (Ico_subset_Icc_self ht)).mono_of_mem_nhdsWithin
        (Icc_mem_nhdsWithin_Ici ht.1 le_rfl ht.2)
    · intro t ht
      exact (hα m t (hsub (Ico_subset_Icc_self ht))).mono_of_mem_nhdsWithin
        (Icc_mem_nhdsWithin_Ici ht.1 le_rfl (by
          have := ht.2
          linarith))
  -- the glued function
  refine ⟨fun x => α ⌈x - t₀⌉₊ x, by simpa using hα0 0, fun t ht => ?_⟩
  set N : ℕ := ⌈t - t₀⌉₊ + 1 with hN
  have htN : t < t₀ + N := by
    have := Nat.le_ceil (t - t₀)
    rw [hN]; push_cast; linarith
  have heq : EqOn (fun x => α ⌈x - t₀⌉₊ x) (α N) (Icc t₀ (t₀ + N)) := by
    intro x hx
    have hx0 : 0 ≤ x - t₀ := by linarith [hx.1]
    have hle : ⌈x - t₀⌉₊ ≤ N := by
      rw [Nat.ceil_le]
      have : x - t₀ ≤ N := by linarith [hx.2]
      exact this
    have hmem : x ∈ Icc t₀ (t₀ + (⌈x - t₀⌉₊ : ℕ)) :=
      ⟨hx.1, by linarith [Nat.le_ceil (x - t₀)]⟩
    exact cons _ _ hle hmem
  have hd := (hα N t ⟨ht, htN.le⟩).mono_of_mem_nhdsWithin
    (Icc_mem_nhdsWithin_Ici le_rfl ht htN)
  have hYt : α ⌈t - t₀⌉₊ t = α N t := heq ⟨ht, htN.le⟩
  have hd2 : HasDerivWithinAt (fun x => α ⌈x - t₀⌉₊ x) (f t (α N t)) (Ici t₀) t :=
    hd.congr_of_eventuallyEq
      (by filter_upwards [Icc_mem_nhdsWithin_Ici le_rfl ht htN] with x hx using heq hx) hYt
  simpa only [hYt] using hd2

end Lightlike.Cosmology.FreezeOut

/-! Deprecated names (kept for one release) -/

@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_034.Icc_mem_nhdsWithin_Ici := _root_.Lightlike.Cosmology.FreezeOut.Icc_mem_nhdsWithin_Ici
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_034.exists_global_forward := _root_.Lightlike.Cosmology.FreezeOut.exists_global_forward
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_034.exists_local_forward := _root_.Lightlike.Cosmology.FreezeOut.exists_local_forward
