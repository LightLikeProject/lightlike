import Lightlike.Spacetime.SpaceForms.AntiDeSitter
import Lightlike.Spacetime.SpaceForms.DeSitterKilling

/-!
# The Killing fields of anti-de Sitter space

The algebra `so(2, m)` of the ambient space `ℂ × ℝᵐ` with the form `B` of signature `(2, m)` acts on
anti-de Sitter space `S¹ × ℝᵐ`: for every `B`-skew endomorphism `A` the field `adsField A` with
`dι (adsField A) = A ∘ ι` (it exists because `A x` is `B`-orthogonal to `x` and the image of `dι` is the
orthogonal complement) is smooth (`contMDiff_adsField`, through `contMDiffAt_section_of_immersion`) and a
Killing field of the Levi-Civita connection (`isKillingAt_adsField`, through `isKillingAt_of_related`).

The generators are the maps `adsGen u v : x ↦ B(v, x) u - B(u, x) v`, skew for any symmetric form
(`adsGen_skew`), on the pairs `a < b` of the `B`-orthogonal basis `adsBasis`
(`(1, 0)`, `(i, 0)`, `(0, eₖ)`, with `B(bₐ, bₐ) = -1, -1, 1`).

* `eq_zero_of_vanish_adsIncl`: a linear map that vanishes on the quadric vanishes (the quadric spans);
* `exists_killing_antiDeSitterSpace`: **`n (n + 1)/2` linearly independent smooth Killing fields**,
  `n = m + 1` the dimension: since `B(bₐ, T b_k) = c_{ak} ε_a ε_k` for `T = Σ c_{ij} adsGen bᵢ bⱼ`.
-/

open Manifold Metric Bundle Set Module
open scoped ContDiff RealInnerProductSpace Manifold

set_option synthInstance.maxHeartbeats 400000
noncomputable section

namespace Lightlike

variable {m : ℕ}

/-! ## Skew maps and the induced fields -/

/-- The skew map `x ↦ B(v, x) u - B(u, x) v` of the ambient space. -/
def adsGen (u v : AdSAmb m) : AdSAmb m →L[ℝ] AdSAmb m :=
  (adsSpaceForm m v).smulRight u - (adsSpaceForm m u).smulRight v

theorem adsGen_apply (u v x : AdSAmb m) :
    adsGen u v x = adsSpaceForm m v x • u - adsSpaceForm m u x • v := rfl

/-- `adsGen u v` is skew for the form. -/
theorem adsGen_skew (u v : AdSAmb m) (x y : AdSAmb m) :
    adsSpaceForm m (adsGen u v x) y + adsSpaceForm m x (adsGen u v y) = 0 := by
  simp only [adsGen_apply, map_sub, map_smul, sub_apply, smul_apply, smul_eq_mul]
  rw [adsSpaceForm_symm x u, adsSpaceForm_symm x v]
  ring

/-- A skew map sends every point to a `B`-orthogonal vector. -/
theorem adsSpaceForm_self_skew {A : AdSAmb m →L[ℝ] AdSAmb m}
    (hA : ∀ u v, adsSpaceForm m (A u) v + adsSpaceForm m u (A v) = 0) (x : AdSAmb m) :
    adsSpaceForm m x (A x) = 0 := by
  have h := hA x x
  rw [adsSpaceForm_symm (A x) x] at h
  linarith

variable {L : ℝ}

/-- **The field of anti-de Sitter space induced by an ambient skew map** `A`: the tangent vector with
`dι = A ι`. -/
def adsField (hL : L ≠ 0) (A : AdSAmb m →L[ℝ] AdSAmb m)
    (hA : ∀ u v, adsSpaceForm m (A u) v + adsSpaceForm m u (A v) = 0) :
    Π p : antiDeSitterSpace m, TangentSpace (IAdS m) p :=
  fun p => Classical.choose (exists_dι_adsIncl_eq hL p (A (adsIncl L p)) (adsSpaceForm_self_skew hA _))

/-- The defining property of the induced field: `dι (adsField A) = A ∘ ι`. -/
theorem dι_adsField (hL : L ≠ 0) (A : AdSAmb m →L[ℝ] AdSAmb m)
    (hA : ∀ u v, adsSpaceForm m (A u) v + adsSpaceForm m u (A v) = 0) (p : antiDeSitterSpace m) :
    dι (I := IAdS m) (adsIncl L) p (adsField hL A hA p) = A (adsIncl L p) :=
  Classical.choose_spec (exists_dι_adsIncl_eq hL p (A (adsIncl L p)) (adsSpaceForm_self_skew hA _))

/-- The induced field is smooth. -/
theorem contMDiff_adsField (hL : L ≠ 0) (A : AdSAmb m →L[ℝ] AdSAmb m)
    (hA : ∀ u v, adsSpaceForm m (A u) v + adsSpaceForm m u (A v) = 0) :
    ContMDiff (IAdS m) ((IAdS m).prod 𝓘(ℝ, Fin (m + 1) → ℝ)) ∞
      (fun q : antiDeSitterSpace m =>
        (⟨q, adsField hL A hA q⟩ : TangentBundle (IAdS m) (antiDeSitterSpace m))) := by
  intro p
  refine contMDiffAt_section_of_immersion (contMDiff_adsIncl hL) (dι_adsIncl_injective hL p) ?_
  have : (fun q => dι (I := IAdS m) (adsIncl L) q (adsField hL A hA q)) = fun q => A (adsIncl L q) :=
    funext (dι_adsField hL A hA)
  rw [this]
  exact A.contMDiff.contMDiffAt.comp p ((contMDiff_adsIncl hL) p)

/-- **The induced field is a Killing field** of the Levi-Civita connection of anti-de Sitter space, at
every point. -/
theorem isKillingAt_adsField (hL : L ≠ 0) (A : AdSAmb m →L[ℝ] AdSAmb m)
    (hA : ∀ u v, adsSpaceForm m (A u) v + adsSpaceForm m u (A v) = 0) (p : antiDeSitterSpace m) :
    IsKillingAt (leviCivita (antiDeSitterSpaceMetric m L hL)) (antiDeSitterSpaceMetric m L hL)
      (adsField hL A hA) p :=
  isKillingAt_of_related ⟨leviCivita_torsion _, leviCivita_compat _⟩ (contMDiff_adsIncl hL)
    (antiDeSitterSpaceMetric_apply hL) A hA (dι_adsField hL A hA)
    ((contMDiff_adsField hL A hA p).mdifferentiableAt (by simp))

/-! ## The quadric spans -/

/-- The point `i` of the circle. -/
def circleI : Circle := ⟨Complex.I, by simp [Submonoid.unitSphere]⟩

/-- **The quadric spans the ambient space**: a linear map vanishing at every point `ι(θ, y)` is zero. -/
theorem eq_zero_of_vanish_adsIncl (hL : L ≠ 0) (T : AdSAmb m →L[ℝ] AdSAmb m)
    (hT : ∀ p, T (adsIncl L p) = 0) : T = 0 := by
  have ha : |L| ≠ 0 := abs_ne_zero.2 hL
  have hr0 : adsRad L (0 : EuclideanSpace ℝ (Fin m)) = |L| := by
    simp [adsRad, Real.sqrt_sq_eq_abs]
  have h1 : T (1, 0) = 0 := by
    have h := hT ((1 : Circle), 0)
    have e : adsIncl L ((1 : Circle), (0 : EuclideanSpace ℝ (Fin m))) = |L| • ((1 : ℂ), (0 : EuclideanSpace ℝ (Fin m))) := by
      simp [adsIncl, adsPhi, hr0]
    rw [e, map_smul] at h
    exact (smul_eq_zero.1 h).resolve_left ha
  have hI : T (Complex.I, 0) = 0 := by
    have h := hT (circleI, 0)
    have e : adsIncl L (circleI, (0 : EuclideanSpace ℝ (Fin m))) =
        |L| • (Complex.I, (0 : EuclideanSpace ℝ (Fin m))) := by
      simp [adsIncl, adsPhi, hr0, circleI]
    rw [e, map_smul] at h
    exact (smul_eq_zero.1 h).resolve_left ha
  have hk : ∀ k : Fin m, T (0, EuclideanSpace.single k 1) = 0 := by
    intro k
    have h := hT ((1 : Circle), EuclideanSpace.single k 1)
    have e : adsIncl L ((1 : Circle), EuclideanSpace.single k (1 : ℝ)) =
        adsRad L (EuclideanSpace.single k (1 : ℝ)) • ((1 : ℂ), (0 : EuclideanSpace ℝ (Fin m))) +
          ((0 : ℂ), EuclideanSpace.single k (1 : ℝ)) := by
      simp [adsIncl, adsPhi]
    rw [e, map_add, map_smul, h1, smul_zero, zero_add] at h
    exact h
  refine ContinuousLinearMap.ext fun u => ?_
  obtain ⟨z, x⟩ := u
  have hx : ((z, x) : AdSAmb m) = z.re • ((1 : ℂ), (0 : EuclideanSpace ℝ (Fin m))) +
      z.im • (Complex.I, (0 : EuclideanSpace ℝ (Fin m))) +
      ∑ k, x k • ((0 : ℂ), EuclideanSpace.single k (1 : ℝ)) := by
    refine Prod.ext ?_ ?_
    · simp only [Prod.fst_add, Prod.smul_fst, Prod.fst_sum, smul_zero, Finset.sum_const_zero, add_zero]
      apply Complex.ext <;> simp
    · simp only [Prod.snd_add, Prod.smul_snd, smul_zero, zero_add, Prod.snd_sum]
      conv_lhs => rw [← (EuclideanSpace.basisFun (Fin m) ℝ).sum_repr x]
      simp
  rw [hx, map_add, map_add, map_smul, map_smul, h1, hI, smul_zero, smul_zero, zero_add, zero_add,
    map_sum]
  exact Finset.sum_eq_zero fun k _ => by rw [map_smul, hk, smul_zero]

/-! ## The orthogonal basis and the independence of the generators -/

/-- The signs `ε = (-1, -1, 1, …, 1)` of the form in the basis `adsBasis`. -/
def adsEps : Fin (m + 2) → ℝ := Fin.cons (-1) (Fin.cons (-1) fun _ => 1)

/-- The `B`-orthogonal basis `(1, 0)`, `(i, 0)`, `(0, eₖ)` of `ℂ × ℝᵐ`. -/
def adsBasis : Fin (m + 2) → AdSAmb m :=
  Fin.cons (1, 0) (Fin.cons (Complex.I, 0) fun k => (0, EuclideanSpace.single k 1))

/-- The basis is `B`-orthogonal with `B(bₐ, bₐ) = εₐ`. -/
theorem adsSpaceForm_adsBasis (i j : Fin (m + 2)) :
    adsSpaceForm m (adsBasis i) (adsBasis j) = if i = j then adsEps i else 0 := by
  refine Fin.cases ?_ (fun i => Fin.cases ?_ (fun i => ?_) i) i <;>
    refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => ?_) j) j <;>
    simp [adsBasis, adsEps, adsSpaceForm_apply, Complex.inner, EuclideanSpace.inner_single_left,
      Fin.succ_ne_zero, (Fin.succ_ne_zero _).symm, Fin.succ_inj, eq_comm] <;>
    exact fun h => absurd (Fin.succ_injective _ h) (Fin.succ_ne_zero _)

/-- The generator of the pair `a < b`. -/
def adsPairGen (q : {q : Fin (m + 2) × Fin (m + 2) // q.1 < q.2}) : AdSAmb m →L[ℝ] AdSAmb m :=
  adsGen (adsBasis q.1.1) (adsBasis q.1.2)

/-- **The coefficient of a pair**: `B(bₐ, adsPairGen q b_k) = εₐ ε_k` if `q = (a, k)`, and `0` for
the other pairs, when `a < k`. -/
theorem adsSpaceForm_adsPairGen {a k : Fin (m + 2)} (hak : a < k)
    (q : {q : Fin (m + 2) × Fin (m + 2) // q.1 < q.2}) :
    adsSpaceForm m (adsBasis a) (adsPairGen q (adsBasis k)) =
      if q.1 = (a, k) then adsEps a * adsEps k else 0 := by
  obtain ⟨⟨i, j⟩, hij⟩ := q
  simp only [adsPairGen, adsGen_apply, map_sub, map_smul, smul_eq_mul, adsSpaceForm_adsBasis]
  by_cases h1 : i = a
  · subst h1
    by_cases h2 : j = k
    · subst h2
      simp [hak.ne, mul_comm]
    · simp [h2, hak.ne]
  · have : ¬ (i = a ∧ j = k) := fun h => h1 h.1
    simp only [Prod.mk.injEq, this, ite_false]
    by_cases h3 : i = k
    · subst h3
      have hja : j ≠ a := fun h => by subst h; exact lt_asymm hij hak
      simp [Ne.symm h1, Ne.symm hja]
    · simp [Ne.symm h1, h3]

theorem adsEps_ne_zero (a : Fin (m + 2)) : adsEps a ≠ 0 := by
  refine Fin.cases ?_ (fun a => Fin.cases ?_ (fun a => ?_) a) a <;> simp [adsEps]

/-- **The generators are independent**: if `Σ c_q adsPairGen q = 0` then every `c_q` is `0`. -/
theorem adsPairGen_independent (c : {q : Fin (m + 2) × Fin (m + 2) // q.1 < q.2} → ℝ)
    (h : ∑ q, c q • adsPairGen (m := m) q = 0) (q : {q : Fin (m + 2) × Fin (m + 2) // q.1 < q.2}) :
    c q = 0 := by
  obtain ⟨⟨a, k⟩, hak⟩ := q
  have h1 := congrArg (fun T : AdSAmb m →L[ℝ] AdSAmb m => adsSpaceForm m (adsBasis a) (T (adsBasis k))) h
  simp only [FunLike.coe_sum, FunLike.coe_smul, Finset.sum_apply,
    Pi.smul_apply, map_sum, map_smul, smul_eq_mul, zero_apply, map_zero] at h1
  simp_rw [adsSpaceForm_adsPairGen hak] at h1
  rw [Finset.sum_eq_single ⟨(a, k), hak⟩ (fun q _ hq => by
    rw [ite_eq_right (fun h => hq (Subtype.ext h)), mul_zero]) (by simp), ite_eq_left rfl] at h1
  exact (mul_eq_zero.1 h1).resolve_right (mul_ne_zero (adsEps_ne_zero a) (adsEps_ne_zero k))

/-- **Anti-de Sitter space has `n (n + 1)/2` independent Killing fields**, `n = m + 1`: smooth fields,
Killing for the Levi-Civita connection at every point, and linearly independent. -/
theorem exists_killing_antiDeSitterSpace (hL : L ≠ 0) :
    ∃ Y : Fin ((m + 1) * (m + 1 + 1) / 2) → Π p : antiDeSitterSpace m, TangentSpace (IAdS m) p,
      (∀ i, ContMDiff (IAdS m) ((IAdS m).prod 𝓘(ℝ, Fin (m + 1) → ℝ)) ∞
          (fun q : antiDeSitterSpace m =>
            (⟨q, Y i q⟩ : TangentBundle (IAdS m) (antiDeSitterSpace m))) ∧
        ∀ p, IsKillingAt (leviCivita (antiDeSitterSpaceMetric m L hL)) (antiDeSitterSpaceMetric m L hL)
          (Y i) p) ∧
      LinearIndependent ℝ Y := by
  have hcard : Fintype.card {q : Fin (m + 2) × Fin (m + 2) // q.1 < q.2} = (m + 1) * (m + 1 + 1) / 2 := by
    rw [card_pairs_lt, show m + 2 - 1 = m + 1 by omega, mul_comm]
  set P := {q : Fin (m + 2) × Fin (m + 2) // q.1 < q.2}
  obtain ⟨σ⟩ : Nonempty (Fin ((m + 1) * (m + 1 + 1) / 2) ≃ P) :=
    ⟨(Fintype.equivOfCardEq (by rw [hcard, Fintype.card_fin])).symm⟩
  have hB : ∀ q : P, ∀ u v, adsSpaceForm m (adsPairGen q u) v + adsSpaceForm m u (adsPairGen q v) = 0 :=
    fun q => adsGen_skew _ _
  let Z : P → Π p : antiDeSitterSpace m, TangentSpace (IAdS m) p :=
    fun q => adsField hL (adsPairGen q) (hB q)
  refine ⟨fun i => Z (σ i), fun i => ⟨contMDiff_adsField hL _ (hB _), isKillingAt_adsField hL _ (hB _)⟩, ?_⟩
  have hZ : LinearIndependent ℝ Z := by
    rw [Fintype.linearIndependent_iff]
    intro c hc
    set T : AdSAmb m →L[ℝ] AdSAmb m := ∑ q, c q • adsPairGen q with hTdef
    have hT : ∀ p, T (adsIncl L p) = 0 := by
      intro p
      have h2 : (∑ q, c q • Z q) p = 0 := congrFun hc p
      rw [Finset.sum_apply] at h2
      simp only [Pi.smul_apply] at h2
      have h3 := congrArg (dι (I := IAdS m) (adsIncl L) p) h2
      erw [map_sum, map_zero] at h3
      rw [hTdef, sum_apply, ← h3]
      refine Finset.sum_congr rfl fun x _ => ?_
      erw [map_smul, dι_adsField]
      rfl
    exact adsPairGen_independent c (eq_zero_of_vanish_adsIncl hL T hT)
  exact hZ.comp σ σ.injective

/-- Non-vacuity: four-dimensional anti-de Sitter space `S¹ × ℝ³` has `10 = 4 · 5/2` independent
smooth Killing fields. -/
example : ∃ Y : Fin 10 → Π p : antiDeSitterSpace 3, TangentSpace (IAdS 3) p,
    (∀ i, ContMDiff (IAdS 3) ((IAdS 3).prod 𝓘(ℝ, Fin (3 + 1) → ℝ)) ∞
        (fun q : antiDeSitterSpace 3 => (⟨q, Y i q⟩ : TangentBundle (IAdS 3) (antiDeSitterSpace 3))) ∧
      ∀ p, IsKillingAt (leviCivita (antiDeSitterSpaceMetric 3 1 one_ne_zero))
        (antiDeSitterSpaceMetric 3 1 one_ne_zero) (Y i) p) ∧
    LinearIndependent ℝ Y :=
  exists_killing_antiDeSitterSpace (m := 3) one_ne_zero

/-- Trust check: the generator of the two timelike directions (the rotation of the circle) is not
zero: `B(b₀, M₀₁ b₁) = ε₀ ε₁ = 1`. -/
example : adsPairGen (m := 1) ⟨(0, 1), by decide⟩ (adsBasis 1) ≠ 0 := by
  intro h
  have := adsSpaceForm_adsPairGen (m := 1) (a := 0) (k := 1) (by decide) ⟨(0, 1), by decide⟩
  rw [h, map_zero, ite_eq_left rfl] at this
  simp [adsEps] at this

end Lightlike
