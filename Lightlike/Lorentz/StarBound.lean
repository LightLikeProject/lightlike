module

public import Lightlike.Lorentz.KernelBound
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Integral.MeanInequalities
public import Mathlib.MeasureTheory.Group.LIntegral

/-!
# The star bound for the 4-simplex graph

The Lorentzian EPRL vertex amplitude integrates a product of ten matrix coefficients, one for each
link `a < b` of the complete graph on five vertices, over five copies of SL(2,ℂ) of which one is
fixed to the identity (Engle and Pereira 2009, eq. (22)):

  `∫ dV₀ ⋯ dV₃ ∏_{a<b} K(V_a⁻¹ V_b)`,   `V₄ = 1`.

This file proves that this integral is finite whenever `K` is invariant under `g ↦ g⁻¹` and in
`L^{5/2}` of the Haar measure, by a *star Hölder inequality*. Each link meets two vertices, so

  `∏_{a<b} K(V_a⁻¹ V_b) = ∏_a (∏_{b ≠ a} K(V_a⁻¹ V_b)^{5/2})^{1/5}`,

and Hölder's inequality with the five exponents `1/5` bounds the integral by the product of the
five *star integrals* `∫ ∏_{b ≠ a} K(V_a⁻¹ V_b)^{5/2}`. Each star integral factorises: after a
left translation by `V_a` the four links at `a` become independent, and the star integral equals
`(∫ K^{5/2} dg)^4` (`lintegral_star`). Hence

  `∫ ∏_{a<b} K(V_a⁻¹ V_b) ≤ (∫ K^{5/2} dg)^4`   (`lintegral_linkProd_le`).

Applied to the kernel `I(g)` of `KernelBound.lean`, which is in `L^{5/2}`, this gives the
finiteness of the integral of the product of the ten kernels (`lintegral_linkProd_kernelE_lt_top`).

The method differs from Engle and Pereira's (their appendix A, adapting Baez and Barrett 2001),
who bound each matrix coefficient by `C e^{-(1-ε) r}` and integrate out the vertices one at a time
(their Lemma 5 and Theorem 2). The star Hölder inequality needs only the single-variable fact
`I ∈ L^{5/2}`. On the complete graph with `n` vertices the same argument needs `K ∈ L^{n/2}`; for
`n = 4` that is `L²`, which `I` misses (`lintegral_kernelE_sq_eq_top`), so the argument uses that
the 4-simplex has five vertices.

## Main results

* `lintegral_pi_prod`: Tonelli for a product of functions of separate variables.
* `lintegral_star`: the star integral at any vertex equals `(∫ h dg)^4`.
* `prod_star_eq_linkProd_sq`: the product of the five stars counts each link twice.
* `lintegral_linkProd_le`: the star Hölder bound.
* `lintegral_linkProd_kernelE_lt_top`: finiteness for the kernel `I`.

## References

* J. Engle and R. Pereira, *Regularization and finiteness of the Lorentzian loop quantum gravity
  vertices*, Phys. Rev. D 79 (2009) 084034, arXiv:0805.4696, eq. (22), Sec. 4 and App. A.
* J. C. Baez and J. W. Barrett, *Integrability for relativistic spin networks*, Class. Quantum
  Grav. 18 (2001) 4683, arXiv:gr-qc/0101107.
-/

@[expose] public section

namespace Lightlike.Lorentz

open MeasureTheory Finset
open scoped ENNReal

/-- **Tonelli for products of functions of separate variables**: the integral over `αⁿ` of
`∏ᵢ fᵢ(xᵢ)` is the product of the integrals. -/
theorem lintegral_pi_prod {α : Type*} [MeasurableSpace α] (μ : Measure α) [SigmaFinite μ] :
    ∀ {n : ℕ} (f : Fin n → α → ℝ≥0∞), (∀ i, Measurable (f i)) →
      ∫⁻ x, ∏ i, f i (x i) ∂(Measure.pi fun _ : Fin n => μ) = ∏ i, ∫⁻ y, f i y ∂μ
  | 0, f, _ => by simp
  | n + 1, f, hf => by
    have e := measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => μ) 0
    rw [← e.symm.lintegral_comp_emb (MeasurableEquiv.measurableEmbedding _)]
    simp only [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
      Fin.prod_univ_succ, Fin.insertNth_zero, Equiv.coe_fn_mk, Fin.cons_succ,
      Fin.zero_succAbove, cast_eq, Fin.cons_zero]
    rw [lintegral_prod_mul (f := f 0) (g := fun z : Fin n → α => ∏ i : Fin n, f i.succ (z i))
      (hf 0).aemeasurable
      (Finset.measurable_prod _ fun i _ => (hf i.succ).comp (measurable_pi_apply i)).aemeasurable,
      lintegral_pi_prod μ (fun i => f i.succ) (fun i => hf i.succ)]

/-- The gauge-fixed vertex variables of the 4-simplex: `V a = x a` for `a < 4` and `V 4 = 1`. -/
def gauge (x : Fin 4 → SL2C) : Fin 5 → SL2C := Fin.snoc (α := fun _ => SL2C) x 1

@[simp] lemma gauge_castSucc (x : Fin 4 → SL2C) (i : Fin 4) : gauge x i.castSucc = x i :=
  Fin.snoc_castSucc (α := fun _ => SL2C) ..

@[simp] lemma gauge_last (x : Fin 4 → SL2C) : gauge x (Fin.last 4) = 1 :=
  Fin.snoc_last (α := fun _ => SL2C) ..

lemma measurable_gauge_apply (a : Fin 5) : Measurable fun x : Fin 4 → SL2C => gauge x a := by
  induction a using Fin.lastCases with
  | last => simp only [gauge_last]; exact measurable_const
  | cast i => simp only [gauge_castSucc]; exact measurable_pi_apply i

/-- The Haar measure on the four free vertex variables. -/
noncomputable abbrev haar4 : Measure (Fin 4 → SL2C) := Measure.pi fun _ => haarC

/-- **The star integral.** For `h` invariant under inversion, the integral over the four free
vertex variables of the product of `h` over the four links at a vertex `a` is `(∫ h dg)^4`. -/
theorem lintegral_star {h : SL2C → ℝ≥0∞} (hm : Measurable h) (hinv : ∀ g, h g⁻¹ = h g)
    (a : Fin 5) :
    ∫⁻ x, ∏ j : Fin 4, h ((gauge x a)⁻¹ * gauge x (a.succAbove j)) ∂haar4 =
      (∫⁻ g, h g ∂haarC) ^ 4 := by
  induction a using Fin.lastCases with
  | last =>
    simp only [gauge_last, inv_one, one_mul, Fin.succAbove_last_apply, gauge_castSucc]
    rw [lintegral_pi_prod haarC (fun _ => h) (fun _ => hm)]
    simp
  | cast i =>
    have hsplit : ∀ x : Fin 4 → SL2C,
        ∏ j : Fin 4, h ((gauge x i.castSucc)⁻¹ * gauge x (i.castSucc.succAbove j)) =
          h (x i) * ∏ j : Fin 3, h ((x i)⁻¹ * x (i.succAbove j)) := by
      intro x
      rw [Fin.prod_univ_castSucc, Fin.succAbove_of_le_castSucc _ _
        (Fin.castSucc_le_castSucc_iff.2 (Fin.le_last i)), Fin.succ_last]
      simp only [Fin.castSucc_succAbove_castSucc, gauge_castSucc, gauge_last, mul_one, hinv]
      rw [mul_comm]
    simp_rw [hsplit]
    set Ψ : SL2C × (Fin 3 → SL2C) → ℝ≥0∞ :=
      fun p => h p.1 * ∏ j : Fin 3, h ((p.1)⁻¹ * p.2 j) with hΨ
    have hΨm : Measurable Ψ :=
      (hm.comp measurable_fst).mul (Finset.measurable_prod _ fun j _ =>
        hm.comp (measurable_fst.inv.mul ((measurable_pi_apply j).comp measurable_snd)))
    have e := measurePreserving_piFinSuccAbove (fun _ : Fin 4 => haarC) i
    calc ∫⁻ x, h (x i) * ∏ j : Fin 3, h ((x i)⁻¹ * x (i.succAbove j)) ∂haar4
        = ∫⁻ x, Ψ (MeasurableEquiv.piFinSuccAbove (fun _ => SL2C) i x) ∂haar4 := rfl
      _ = ∫⁻ p, Ψ p ∂(haarC.prod (Measure.pi fun _ : Fin 3 => haarC)) :=
        e.lintegral_comp_emb (MeasurableEquiv.measurableEmbedding _) Ψ
      _ = ∫⁻ y, ∫⁻ z, Ψ (y, z) ∂(Measure.pi fun _ : Fin 3 => haarC) ∂haarC :=
        lintegral_prod Ψ hΨm.aemeasurable
      _ = ∫⁻ y, h y * (∫⁻ g, h g ∂haarC) ^ 3 ∂haarC := by
        refine lintegral_congr fun y => ?_
        show ∫⁻ z, h y * ∏ j : Fin 3, h (y⁻¹ * z j) ∂(Measure.pi fun _ : Fin 3 => haarC) = _
        rw [lintegral_const_mul (h y) (f := fun z : Fin 3 → SL2C => ∏ j : Fin 3, h (y⁻¹ * z j))
          (Finset.measurable_prod _ fun j _ =>
          hm.comp (measurable_const.mul (measurable_pi_apply j)))]
        rw [lintegral_pi_prod haarC (fun (_ : Fin 3) (w : SL2C) => h (y⁻¹ * w))
          (fun _ => hm.comp (measurable_const.mul measurable_id))]
        simp [lintegral_mul_left_eq_self]
      _ = (∫⁻ g, h g ∂haarC) ^ 4 := by
        rw [lintegral_mul_const _ hm, pow_succ' _ 3]

/-- The product over the ten links `a < b` of the complete graph on five vertices. -/
def linkProd {M : Type*} [CommMonoid M] (f : Fin 5 → Fin 5 → M) : M :=
  ∏ a : Fin 5, ∏ b ∈ Ioi a, f a b

/-- The product of the five stars counts each link twice. -/
theorem prod_star_eq_linkProd_sq {M : Type*} [CommSemiring M] (k : Fin 5 → Fin 5 → M)
    (hk : ∀ a b, k a b = k b a) :
    ∏ a : Fin 5, ∏ j : Fin 4, k a (a.succAbove j) = linkProd fun a b => k a b ^ 2 := by
  unfold linkProd
  simp only [Fin.prod_univ_five]
  rw [show Ioi (0 : Fin 5) = {1, 2, 3, 4} by decide, show Ioi (1 : Fin 5) = {2, 3, 4} by decide,
    show Ioi (2 : Fin 5) = {3, 4} by decide, show Ioi (3 : Fin 5) = {4} by decide,
    show Ioi (4 : Fin 5) = ∅ by decide]
  simp only [Fin.prod_univ_four, Fin.succAbove]
  simp
  simp only [hk 1 0, hk 2 0, hk 2 1, hk 3 0, hk 3 1, hk 3 2, hk 4 0, hk 4 1, hk 4 2, hk 4 3]
  ring

/-- **The star Hölder bound.** For `K` invariant under inversion,
`∫ ∏_{a<b} K(V_a⁻¹ V_b) dV₀ ⋯ dV₃ ≤ (∫ K^{5/2} dg)^4` with `V₄ = 1`. -/
theorem lintegral_linkProd_le {K : SL2C → ℝ≥0∞} (hm : Measurable K) (hinv : ∀ g, K g⁻¹ = K g) :
    ∫⁻ x, linkProd (fun a b => K ((gauge x a)⁻¹ * gauge x b)) ∂haar4 ≤
      (∫⁻ g, K g ^ (5 / 2 : ℝ) ∂haarC) ^ 4 := by
  have hmeas : ∀ a b : Fin 5, Measurable fun x : Fin 4 → SL2C => K ((gauge x a)⁻¹ * gauge x b) :=
    fun a b => hm.comp ((measurable_gauge_apply a).inv.mul (measurable_gauge_apply b))
  have key : ∀ x : Fin 4 → SL2C, linkProd (fun a b => K ((gauge x a)⁻¹ * gauge x b)) =
      ∏ a : Fin 5, (∏ j : Fin 4,
        K ((gauge x a)⁻¹ * gauge x (a.succAbove j)) ^ (5 / 2 : ℝ)) ^ (1 / 5 : ℝ) := by
    intro x
    have hk : ∀ a b : Fin 5, K ((gauge x a)⁻¹ * gauge x b) ^ (1 / 2 : ℝ) =
        K ((gauge x b)⁻¹ * gauge x a) ^ (1 / 2 : ℝ) := by
      intro a b; rw [← hinv]; simp [mul_inv_rev]
    calc linkProd (fun a b => K ((gauge x a)⁻¹ * gauge x b))
        = linkProd (fun a b => (K ((gauge x a)⁻¹ * gauge x b) ^ (1 / 2 : ℝ)) ^ 2) := by
          unfold linkProd
          refine prod_congr rfl fun a _ => prod_congr rfl fun b _ => ?_
          dsimp only
          rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]; norm_num
      _ = ∏ a : Fin 5, ∏ j : Fin 4,
            K ((gauge x a)⁻¹ * gauge x (a.succAbove j)) ^ (1 / 2 : ℝ) :=
          (prod_star_eq_linkProd_sq _ hk).symm
      _ = _ := by
          refine prod_congr rfl fun a _ => ?_
          rw [← ENNReal.prod_rpow_of_nonneg (by norm_num)]
          refine prod_congr rfl fun j _ => ?_
          rw [← ENNReal.rpow_mul]; norm_num
  simp_rw [key]
  calc ∫⁻ x, ∏ a : Fin 5, (∏ j : Fin 4,
        K ((gauge x a)⁻¹ * gauge x (a.succAbove j)) ^ (5 / 2 : ℝ)) ^ (1 / 5 : ℝ) ∂haar4
      ≤ ∏ a : Fin 5, (∫⁻ x, ∏ j : Fin 4,
          K ((gauge x a)⁻¹ * gauge x (a.succAbove j)) ^ (5 / 2 : ℝ) ∂haar4) ^ (1 / 5 : ℝ) :=
        ENNReal.lintegral_prod_norm_pow_le univ
          (fun a _ => (Finset.measurable_prod _ fun j _ =>
            (hmeas a (a.succAbove j)).pow_const _).aemeasurable)
          (by simp) (fun _ _ => by norm_num)
    _ = ∏ _a : Fin 5, ((∫⁻ g, K g ^ (5 / 2 : ℝ) ∂haarC) ^ 4) ^ (1 / 5 : ℝ) := by
        refine prod_congr rfl fun a _ => ?_
        rw [lintegral_star (hm.pow_const _) (fun g => by rw [hinv]) a]
    _ = (∫⁻ g, K g ^ (5 / 2 : ℝ) ∂haarC) ^ 4 := by
        rw [prod_const, card_univ, Fintype.card_fin, ← ENNReal.rpow_natCast,
          ← ENNReal.rpow_mul]
        norm_num

/-- **Finiteness of the gauge-fixed integral of the ten kernels**:
`∫ ∏_{a<b} I(V_a⁻¹ V_b) dV₀ ⋯ dV₃ < ∞`. -/
theorem lintegral_linkProd_kernelE_lt_top :
    ∫⁻ x, linkProd (fun a b => kernelE ((gauge x a)⁻¹ * gauge x b)) ∂haar4 < ∞ :=
  (lintegral_linkProd_le measurable_kernelE kernelE_inv).trans_lt
    (ENNReal.pow_lt_top lintegral_kernelE_rpow_lt_top)

end Lightlike.Lorentz
