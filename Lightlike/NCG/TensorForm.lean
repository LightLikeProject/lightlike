import Lightlike.NCG.Bimodule
import Mathlib.Data.Matrix.Basis

/-!
# The tensor form of the vertices `Hᵢⱼ` (Paschke-Sitarz, Lemma 2)

M. Paschke, A. Sitarz, arXiv:q-alg/9612029, Lemma 2, pp. 2-3 (read): for `A = ⊕ᵢ Mₙᵢ(ℂ)` acting complex-linearly,
`Hᵢⱼ = ℂⁿⁱ ⊗ ℂʳⁱʲ ⊗ ℂⁿʲ`, with `a` acting from the left as `aᵢ ⊗ 1 ⊗ 1` and from the right as `1 ⊗ 1 ⊗ aⱼᵀ`
(Krajewski, arXiv:hep-th/9701081, Section 3.1, p. 10: `Hᵢⱼ` is `mᵢⱼ` copies of `Mₙᵢ×ₙⱼ(ℂ)` with left and right matrix
multiplication). The proof uses the matrix units `Eᵢ,αβ` of the summands: `x ↦ (π(Eᵢ,0α) J π(Eⱼ,0β) J x)_{αβ}` is an
isomorphism `Hᵢⱼ ≃ (Fin nᵢ → Fin nⱼ → Vᵢⱼ)` with `Vᵢⱼ = π(Eᵢ,00) J π(Eⱼ,00) J H`, under which `π(a)` is the left
multiplication by `aᵢ` and `ξ ↦ J π(b*) J ξ` the right multiplication by `bⱼ`; `rᵢⱼ = dim Vᵢⱼ`.

* `MatSum n`, `stdPartition n`, `unit i α β`;
* `tensorEquiv`: `Hᵢⱼ ≃ₗ[ℂ] (Fin nᵢ → Fin nⱼ → Vᵢⱼ)`;
* `IsComplexLinear`, `tensorEquiv_pi`, `tensorEquiv_rightOp_star`: the two actions;
* `finrank_Hsub_eq`: `dim Hᵢⱼ = nᵢ nⱼ rᵢⱼ`.
-/

open scoped InnerProductSpace

namespace Lightlike.NCG

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (n : ι → ℕ)

/-- `A = ⊕ᵢ Mₙᵢ(ℂ)`. -/
abbrev MatSum := ∀ i, Matrix (Fin (n i)) (Fin (n i)) ℂ

/-- **The units of the summands**, a central partition of `⊕ᵢ Mₙᵢ(ℂ)`. -/
def stdPartition : CentralPartition (MatSum n) ι where
  P i := Pi.single i 1
  star_P i := by
    ext j : 1
    by_cases h : j = i
    · subst h; simp
    · simp [Pi.single_eq_of_ne h]
  mul_P i j := by
    ext k : 1
    by_cases hij : i = j
    · subst hij; by_cases hk : k = i
      · subst hk; simp
      · simp [Pi.single_eq_of_ne hk]
    · rw [if_neg hij]
      by_cases hk : k = i
      · subst hk; simp [Pi.single_eq_of_ne hij]
      · simp [Pi.single_eq_of_ne hk]
  sum_P := by
    ext k : 1
    simp [Finset.sum_apply, Pi.single_apply]
  central i a := by
    ext k : 1
    by_cases hk : k = i
    · subst hk; simp
    · simp [Pi.single_eq_of_ne hk]

/-- **The matrix unit** `Eᵢ,αβ` of the `i`-th summand. -/
def unit (i : ι) (α β : Fin (n i)) : MatSum n := Pi.single i (Matrix.single α β 1)

variable {n}

lemma unit_mul_unit (i : ι) (α β γ δ : Fin (n i)) :
    unit n i α β * unit n i γ δ = if β = γ then unit n i α δ else 0 := by
  simp only [unit]
  rw [← Pi.single_mul]
  split_ifs with h
  · subst h; rw [Matrix.single_mul_single_same, mul_one]
  · rw [Matrix.single_mul_single_of_ne (h := h), Pi.single_zero]

lemma sum_unit (i : ι) : ∑ α, unit n i α α = (stdPartition n).P i := by
  ext k : 1
  simp only [Finset.sum_apply, unit, stdPartition]
  by_cases hk : k = i
  · subst hk; simp only [Pi.single_eq_same]; exact Matrix.sum_single_one
  · simp [Pi.single_eq_of_ne hk]

lemma unit_mul_single (i : ι) (α β : Fin (n i)) (M : Matrix (Fin (n i)) (Fin (n i)) ℂ) :
    unit n i α β * Pi.single i M = ∑ γ, M β γ • unit n i α γ := by
  have hM : Matrix.single α β (1 : ℂ) * M = ∑ γ, M β γ • Matrix.single α γ 1 := by
    ext r c
    simp [Matrix.mul_apply, Matrix.single_apply, Matrix.sum_apply, ite_and]
  ext k : 1
  by_cases hk : k = i
  · subst hk
    simp only [unit, Pi.mul_apply, Finset.sum_apply, Pi.smul_apply, Pi.single_eq_same]
    exact hM
  · simp [unit, Pi.single_eq_of_ne hk]

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H] [CompleteSpace H]
variable {T : FiniteSpectralTriple (MatSum n) H} (R : RealStructure T)

variable (T) in
/-- `π(Eᵢ,αβ)`. -/
def lU (i : ι) (α β : Fin (n i)) : H →ₗ[ℂ] H := (T.π (unit n i α β) : H →L[ℂ] H)

/-- `J π(Eⱼ,γδ) J`. -/
def rU (j : ι) (γ δ : Fin (n j)) : H →ₗ[ℂ] H := rightOp R (unit n j γ δ)

lemma lU_lU (i : ι) (α β γ δ : Fin (n i)) (x : H) :
    lU T i α β (lU T i γ δ x) = if β = γ then lU T i α δ x else 0 := by
  simp only [lU, ContinuousLinearMap.coe_coe]
  rw [← ContinuousLinearMap.mul_apply, ← map_mul, unit_mul_unit]
  split_ifs <;> simp

lemma rU_rU (j : ι) (α β γ δ : Fin (n j)) (x : H) :
    rU R j α β (rU R j γ δ x) = if β = γ then rU R j α δ x else 0 := by
  have := congrArg (fun f : H →ₗ[ℂ] H => f x) (rightOp_mul R (unit n j α β) (unit n j γ δ))
  simp only [Module.End.mul_apply] at this
  simp only [rU, ← this, unit_mul_unit]
  split_ifs
  · rfl
  · simp [rightOp_apply]

lemma lU_rU (i j : ι) (α β : Fin (n i)) (γ δ : Fin (n j)) (x : H) :
    lU T i α β (rU R j γ δ x) = rU R j γ δ (lU T i α β x) :=
  R.order_zero _ _ x

lemma unit_mul (i : ι) (α β : Fin (n i)) (a : MatSum n) : unit n i α β * a = unit n i α β * Pi.single i (a i) := by
  ext k : 1
  by_cases hk : k = i
  · subst hk; simp [unit]
  · simp [unit, Pi.single_eq_of_ne hk]

lemma single_mul_unit (i : ι) (α β : Fin (n i)) : (stdPartition n).P i * unit n i α β = unit n i α β := by
  show Pi.single i 1 * Pi.single i _ = _
  rw [← Pi.single_mul, one_mul]; rfl

lemma leftP_lU (i : ι) (α β : Fin (n i)) (x : H) :
    leftP T (stdPartition n) i (lU T i α β x) = lU T i α β x := by
  simp only [leftP, lU, ContinuousLinearMap.coe_coe]
  rw [← ContinuousLinearMap.mul_apply, ← map_mul, single_mul_unit]

lemma rightP_rU (j : ι) (γ δ : Fin (n j)) (x : H) :
    rightP R (stdPartition n) j (rU R j γ δ x) = rU R j γ δ x := by
  have := congrArg (fun f : H →ₗ[ℂ] H => f x) (rightOp_mul R ((stdPartition n).P j) (unit n j γ δ))
  simp only [Module.End.mul_apply, single_mul_unit] at this
  exact this.symm

lemma sum_lU (i : ι) (x : H) : ∑ α, lU T i α α x = leftP T (stdPartition n) i x := by
  simp only [lU, leftP, ContinuousLinearMap.coe_coe, ← sum_unit, map_sum, ContinuousLinearMap.sum_apply]

lemma sum_rU (j : ι) (x : H) : ∑ β, rU R j β β x = rightP R (stdPartition n) j x := by
  simp only [rU, rightP, ← sum_unit, rightOp_sum, LinearMap.sum_apply, Finset.sum_apply]

/-- On `Hᵢⱼ`, `π(Pᵢ)` and `J π(Pⱼ) J` are the identity. -/
lemma leftP_rightP_of_mem {i j : ι} {x : H} (hx : x ∈ Hsub R (stdPartition n) i j) :
    leftP T (stdPartition n) i x = x ∧ rightP R (stdPartition n) j x = x := by
  obtain ⟨y, rfl⟩ := hx
  refine ⟨?_, ?_⟩
  · rw [proj_apply, leftP_leftP, if_pos rfl]
  · rw [proj_apply, rightP_leftP, rightP_rightP, if_pos rfl]

variable [∀ i, NeZero (n i)]

/-- **The multiplicity space** `Vᵢⱼ = π(Eᵢ,00) J π(Eⱼ,00) J H`. -/
def Vsub (i j : ι) : Submodule ℂ H := LinearMap.range (lU T i 0 0 ∘ₗ rU R j 0 0)

lemma mem_Vsub (i j : ι) (α : Fin (n i)) (β : Fin (n j)) (x : H) :
    lU T i 0 α (rU R j 0 β x) ∈ Vsub R i j := by
  refine ⟨lU T i 0 α (rU R j 0 β x), ?_⟩
  simp only [LinearMap.comp_apply]
  rw [← lU_rU, lU_lU, if_pos rfl, rU_rU, if_pos rfl]

lemma lU_rU_of_mem_Vsub {i j : ι} {v : H} (hv : v ∈ Vsub R i j) : lU T i 0 0 (rU R j 0 0 v) = v := by
  obtain ⟨w, rfl⟩ := hv
  simp only [LinearMap.comp_apply]
  rw [← lU_rU, lU_lU, if_pos rfl, rU_rU, if_pos rfl, lU_rU]

lemma mem_Hsub_of_sum (i j : ι) (v : Fin (n i) → Fin (n j) → H) :
    ∑ α, ∑ β, lU T i α 0 (rU R j β 0 (v α β)) ∈ Hsub R (stdPartition n) i j := by
  refine ⟨∑ α, ∑ β, lU T i α 0 (rU R j β 0 (v α β)), ?_⟩
  simp only [proj_apply, map_sum]
  refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun β _ => ?_
  rw [show rightP R (stdPartition n) j (lU T i α 0 (rU R j β 0 (v α β))) =
      lU T i α 0 (rightP R (stdPartition n) j (rU R j β 0 (v α β))) from (R.order_zero _ _ _).symm,
    rightP_rU, leftP_lU]

/-- **The tensor form** (Paschke-Sitarz, Lemma 2): `Hᵢⱼ ≃ (Fin nᵢ → Fin nⱼ → Vᵢⱼ)`,
`x ↦ (π(Eᵢ,0α) J π(Eⱼ,0β) J x)_{αβ}`. -/
def tensorEquiv (i j : ι) : Hsub R (stdPartition n) i j ≃ₗ[ℂ] (Fin (n i) → Fin (n j) → Vsub R i j) where
  toFun x α β := ⟨lU T i 0 α (rU R j 0 β x), mem_Vsub R i j α β x⟩
  map_add' x y := by ext α β; simp
  map_smul' c x := by ext α β; simp
  invFun v := ⟨∑ α, ∑ β, lU T i α 0 (rU R j β 0 (v α β)), mem_Hsub_of_sum R i j fun α β => v α β⟩
  left_inv x := by
    apply Subtype.ext
    obtain ⟨hL, hR⟩ := leftP_rightP_of_mem R x.2
    show ∑ α, ∑ β, lU T i α 0 (rU R j β 0 (lU T i 0 α (rU R j 0 β (x : H)))) = x
    calc ∑ α, ∑ β, lU T i α 0 (rU R j β 0 (lU T i 0 α (rU R j 0 β (x : H))))
        = ∑ α, ∑ β, lU T i α α (rU R j β β (x : H)) := by
          refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun β _ => ?_
          rw [← lU_rU R i j 0 α β 0, lU_lU, if_pos rfl, rU_rU, if_pos rfl]
      _ = ∑ α, lU T i α α (∑ β, rU R j β β (x : H)) := by simp only [map_sum]
      _ = x := by rw [sum_rU, hR, sum_lU, hL]
  right_inv v := by
    funext γ δ
    apply Subtype.ext
    show lU T i 0 γ (rU R j 0 δ (∑ α, ∑ β, lU T i α 0 (rU R j β 0 (v α β : H)))) = v γ δ
    have key : ∀ α β, lU T i 0 γ (rU R j 0 δ (lU T i α 0 (rU R j β 0 (v α β : H)))) =
        if γ = α then (if δ = β then (v α β : H) else 0) else 0 := by
      intro α β
      rw [← lU_rU R i j α 0 0 δ, lU_lU, rU_rU]
      by_cases h1 : γ = α
      · by_cases h2 : δ = β
        · subst h1; subst h2
          simp only [if_true]
          exact lU_rU_of_mem_Vsub R (v γ δ).2
        · simp [h1, h2]
      · simp [h1]
    simp only [map_sum, key]
    rw [Finset.sum_eq_single γ (fun α _ hα => by simp [Ne.symm hα]) (by simp)]
    rw [Finset.sum_eq_single δ (fun β _ hβ => by simp [Ne.symm hβ]) (by simp)]
    simp

/-- `π(a)` maps `Hᵢⱼ` into itself. -/
lemma pi_mem_Hsub (a : MatSum n) {i j : ι} {x : H} (hx : x ∈ Hsub R (stdPartition n) i j) :
    T.π a x ∈ Hsub R (stdPartition n) i j := by
  obtain ⟨y, rfl⟩ := hx
  refine ⟨T.π a y, ?_⟩
  have h1 : rightP R (stdPartition n) j (T.π a y) = T.π a (rightP R (stdPartition n) j y) :=
    (R.order_zero a _ y).symm
  have h2 : ∀ z, leftP T (stdPartition n) i (T.π a z) = T.π a (leftP T (stdPartition n) i z) := by
    intro z
    simp only [leftP_apply]
    rw [← ContinuousLinearMap.mul_apply, ← map_mul, (stdPartition n).central, map_mul,
      ContinuousLinearMap.mul_apply]
  rw [proj_apply, h1, h2, ← proj_apply]

/-- `ξ ↦ J π(b) J ξ` maps `Hᵢⱼ` into itself. -/
lemma rightOp_mem_Hsub (b : MatSum n) {i j : ι} {x : H} (hx : x ∈ Hsub R (stdPartition n) i j) :
    rightOp R b x ∈ Hsub R (stdPartition n) i j := by
  obtain ⟨y, rfl⟩ := hx
  refine ⟨rightOp R b y, ?_⟩
  have h1 : rightP R (stdPartition n) j (rightOp R b y) = rightOp R b (rightP R (stdPartition n) j y) := by
    have e1 := congrArg (fun f : H →ₗ[ℂ] H => f y) (rightOp_mul R ((stdPartition n).P j) b)
    have e2 := congrArg (fun f : H →ₗ[ℂ] H => f y) (rightOp_mul R b ((stdPartition n).P j))
    simp only [Module.End.mul_apply] at e1 e2
    rw [rightP, ← e1, (stdPartition n).central, e2]
  have h2 : ∀ z, leftP T (stdPartition n) i (rightOp R b z) = rightOp R b (leftP T (stdPartition n) i z) :=
    fun z => R.order_zero _ b z
  rw [proj_apply, h1, h2, ← proj_apply]

/-- `π` is complex-linear: the representation of a complex algebra in Paschke-Sitarz, Section 2, p. 2. -/
def IsComplexLinear (T : FiniteSpectralTriple (MatSum n) H) : Prop := ∀ (c : ℂ) (a : MatSum n), T.π (c • a) = c • T.π a

/-- For a complex-linear `π`, `J π(c b) J = c̄ J π(b) J`. -/
lemma rightOp_smul (hℂ : IsComplexLinear T) (c : ℂ) (b : MatSum n) :
    rightOp R (c • b) = (starRingEnd ℂ c) • rightOp R b := by
  ext x
  simp only [rightOp_apply, hℂ c b, ContinuousLinearMap.smul_apply, LinearMap.map_smulₛₗ, LinearMap.smul_apply]

/-- **The left action in the tensor form** (Paschke-Sitarz, Lemma 2): `π(a)` acts as the left multiplication by
`aᵢ`, `(π(a) x)_{αβ} = ∑_γ (aᵢ)_{αγ} x_{γβ}`. -/
theorem tensorEquiv_pi (hℂ : IsComplexLinear T) (a : MatSum n) {i j : ι} (x : Hsub R (stdPartition n) i j)
    (α : Fin (n i)) (β : Fin (n j)) :
    (tensorEquiv R i j ⟨T.π a x, pi_mem_Hsub R a x.2⟩ α β : H) = ∑ γ, a i α γ • (tensorEquiv R i j x γ β : H) := by
  show lU T i 0 α (rU R j 0 β (T.π a x)) = ∑ γ, a i α γ • lU T i 0 γ (rU R j 0 β (x : H))
  rw [show rU R j 0 β (T.π a x) = T.π a (rU R j 0 β (x : H)) from (R.order_zero a _ _).symm]
  simp only [lU, ContinuousLinearMap.coe_coe]
  rw [← ContinuousLinearMap.mul_apply, ← map_mul, unit_mul, unit_mul_single, map_sum,
    ContinuousLinearMap.sum_apply]
  refine Finset.sum_congr rfl fun γ _ => ?_
  rw [hℂ (a i α γ) (unit n i 0 γ), ContinuousLinearMap.smul_apply]

/-- **The right action in the tensor form** (Paschke-Sitarz, Lemma 2): `ξ ↦ J π(b*) J ξ` acts as the right
multiplication by `bⱼ`, `(x b)_{αβ} = ∑_δ x_{αδ} (bⱼ)_{δβ}`. -/
theorem tensorEquiv_rightOp_star (hℂ : IsComplexLinear T) (b : MatSum n) {i j : ι}
    (x : Hsub R (stdPartition n) i j) (α : Fin (n i)) (β : Fin (n j)) :
    (tensorEquiv R i j ⟨rightOp R (star b) x, rightOp_mem_Hsub R (star b) x.2⟩ α β : H) =
      ∑ δ, b j δ β • (tensorEquiv R i j x α δ : H) := by
  show lU T i 0 α (rU R j 0 β (rightOp R (star b) x)) = ∑ δ, b j δ β • lU T i 0 α (rU R j 0 δ (x : H))
  have e := congrArg (fun f : H →ₗ[ℂ] H => f x) (rightOp_mul R (unit n j 0 β) (star b))
  simp only [Module.End.mul_apply] at e
  rw [rU, ← e, unit_mul, unit_mul_single, rightOp_sum, LinearMap.sum_apply, map_sum]
  refine Finset.sum_congr rfl fun δ _ => ?_
  rw [rightOp_smul R hℂ, LinearMap.smul_apply, map_smul]
  simp only [Pi.star_apply, Matrix.star_apply, starRingEnd_apply, star_star]
  rfl

/-- **`dim Hᵢⱼ = nᵢ nⱼ rᵢⱼ`** with `rᵢⱼ = dim Vᵢⱼ`. -/
theorem finrank_Hsub_eq (i j : ι) :
    Module.finrank ℂ (Hsub R (stdPartition n) i j) = n i * n j * Module.finrank ℂ (Vsub R i j) := by
  rw [(tensorEquiv R i j).finrank_eq, Module.finrank_pi_fintype]
  simp only [Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  ring

end

end Lightlike.NCG
