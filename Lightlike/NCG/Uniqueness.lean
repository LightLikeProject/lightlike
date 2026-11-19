import Lightlike.NCG.KrajewskiModel
import Lightlike.NCG.RealForm

/-!
# Uniqueness of the real structure up to unitary equivalence

T. Krajewski, arXiv:hep-th/9701081, Section 3.2, p. 13 (read): "a `(A, A)`-bimodule with matrix of multiplicities `m`
is endowed with a real structure if only if `m` is symmetric. Moreover, if so, the charge conjugation is unique up to
unitary equivalence, and it acts as above on tensor products."

* `inner_lU_left`, `inner_rU_left`: `π(Eᵢ,αβ)* = π(Eᵢ,βα)` and `(J π(Eⱼ,γδ) J)* = J π(Eⱼ,δγ) J`;
* `inner_coord`, `sum_inner_coord`: the tensor coordinates are isometric.
-/

open scoped InnerProductSpace

namespace Lightlike.NCG

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H] [CompleteSpace H]
variable {T : FiniteSpectralTriple (MatSum n) H} (R : RealStructure T)

lemma star_unit (i : ι) (α β : Fin (n i)) : star (unit n i α β) = unit n i β α := by
  ext k : 1
  by_cases hk : k = i
  · subst hk
    simp [unit, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_single]
  · simp [unit, Pi.single_eq_of_ne hk]

/-- **`π(Eᵢ,αβ)* = π(Eᵢ,βα)`.** -/
lemma inner_lU_left (i : ι) (α β : Fin (n i)) (x y : H) : ⟪lU T i α β x, y⟫_ℂ = ⟪x, lU T i β α y⟫_ℂ := by
  simp only [lU, ContinuousLinearMap.coe_coe]
  rw [← star_unit, map_star, ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_left]

/-- `⟪J z, y⟫ = ⟪J y, z⟫`. -/
lemma inner_J_left (z y : H) : ⟪R.J z, y⟫_ℂ = ⟪R.J y, z⟫_ℂ := by
  conv_lhs => rw [← R.J_J y]
  exact R.inner_J z (R.J y)

/-- **`(J π(Eⱼ,γδ) J)* = J π(Eⱼ,δγ) J`.** -/
lemma inner_rU_left (j : ι) (γ δ : Fin (n j)) (x y : H) : ⟪rU R j γ δ x, y⟫_ℂ = ⟪x, rU R j δ γ y⟫_ℂ := by
  show ⟪R.J (T.π (unit n j γ δ) (R.J x)), y⟫_ℂ = ⟪x, R.J (T.π (unit n j δ γ) (R.J y))⟫_ℂ
  rw [inner_J_left, ← ContinuousLinearMap.adjoint_inner_left, ← ContinuousLinearMap.star_eq_adjoint, ← map_star,
    star_unit, ← inner_conj_symm, inner_J_left, inner_conj_symm]

variable [∀ i, NeZero (n i)]

/-- `⟪π(Eᵢ,0α) J π(Eⱼ,0β) J x, π(Eᵢ,0α) J π(Eⱼ,0β) J y⟫ = ⟪x, π(Eᵢ,αα) J π(Eⱼ,ββ) J y⟫`. -/
lemma inner_coord (i j : ι) (α : Fin (n i)) (β : Fin (n j)) (x y : H) :
    ⟪lU T i 0 α (rU R j 0 β x), lU T i 0 α (rU R j 0 β y)⟫_ℂ = ⟪x, lU T i α α (rU R j β β y)⟫_ℂ := by
  rw [inner_lU_left, lU_lU, if_pos rfl, lU_rU, inner_rU_left, rU_rU, if_pos rfl, ← lU_rU]

/-- **The coordinates are isometric**: `∑ᵢⱼ ∑_{αβ} ⟪(x)ᵢⱼ,αβ, (y)ᵢⱼ,αβ⟫ = ⟪x, y⟫`. -/
lemma sum_inner_coord (x y : H) :
    ∑ i, ∑ j, ∑ α : Fin (n i), ∑ β : Fin (n j),
      ⟪lU T i 0 α (rU R j 0 β x), lU T i 0 α (rU R j 0 β y)⟫_ℂ = ⟪x, y⟫_ℂ := by
  calc ∑ i, ∑ j, ∑ α : Fin (n i), ∑ β : Fin (n j),
        ⟪lU T i 0 α (rU R j 0 β x), lU T i 0 α (rU R j 0 β y)⟫_ℂ
      = ∑ i, ∑ j, ⟪x, leftP T (stdPartition n) i (rightP R (stdPartition n) j y)⟫_ℂ := by
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        simp only [inner_coord]
        rw [← sum_rU R j y, ← sum_lU]
        simp only [map_sum, inner_sum]
    _ = ⟪x, y⟫_ℂ := by
        simp only [← inner_sum, ← map_sum, sum_rightP, sum_leftP]

/-- `J π(u) = (J π(u) J) J`. -/
lemma J_lU (i : ι) (α β : Fin (n i)) (z : H) : R.J (lU T i α β z) = rU R i α β (R.J z) := by
  show R.J (T.π (unit n i α β) z) = R.J (T.π (unit n i α β) (R.J (R.J z)))
  rw [R.J_J]

/-- `J (J π(u) J) = π(u) J`. -/
lemma J_rU (j : ι) (γ δ : Fin (n j)) (z : H) : R.J (rU R j γ δ z) = lU T j γ δ (R.J z) := by
  show R.J (R.J (T.π (unit n j γ δ) (R.J z))) = T.π (unit n j γ δ) (R.J z)
  rw [R.J_J]

/-- **`J` maps `Vᵢⱼ` into `Vⱼᵢ`.** -/
lemma J_mem_Vsub {i j : ι} {v : H} (hv : v ∈ Vsub R i j) : R.J v ∈ Vsub R j i := by
  obtain ⟨y, rfl⟩ := hv
  refine ⟨R.J y, ?_⟩
  simp only [LinearMap.comp_apply]
  rw [J_lU, J_rU, lU_rU]

lemma unit_mul_unit_ne {i i' : ι} (h : i ≠ i') (α β : Fin (n i)) (γ δ : Fin (n i')) :
    unit n i α β * unit n i' γ δ = 0 := by
  ext k : 1
  by_cases hk : k = i
  · subst hk; simp [unit, Pi.single_eq_of_ne h]
  · simp [unit, Pi.single_eq_of_ne hk]

/-- Matrix units of different summands compose to zero on the left. -/
lemma lU_lU_ne {i i' : ι} (h : i ≠ i') (α β : Fin (n i)) (γ δ : Fin (n i')) (x : H) :
    lU T i α β (lU T i' γ δ x) = 0 := by
  simp only [lU, ContinuousLinearMap.coe_coe]
  rw [← ContinuousLinearMap.mul_apply, ← map_mul, unit_mul_unit_ne h, map_zero, ContinuousLinearMap.zero_apply]

/-- Matrix units of different summands compose to zero on the right. -/
lemma rU_rU_ne {j j' : ι} (h : j ≠ j') (α β : Fin (n j)) (γ δ : Fin (n j')) (x : H) :
    rU R j α β (rU R j' γ δ x) = 0 := by
  have := congrArg (fun f : H →ₗ[ℂ] H => f x) (rightOp_mul R (unit n j α β) (unit n j' γ δ))
  simp only [Module.End.mul_apply] at this
  simp only [rU, ← this, unit_mul_unit_ne h]
  simp [rightOp_apply]

/-- **The coordinates of `x`** in orthonormal bases `bᵢⱼ` of the multiplicity spaces:
`(i, j, ρ, α, β) ↦ ⟪bᵢⱼ ρ, π(Eᵢ,0α) J π(Eⱼ,0β) J x⟫`. -/
def coordU (b : ∀ i j, OrthonormalBasis (Fin (multiplicity R i j)) ℂ (Vsub R i j)) (x : H) :
    KIdx n (fun i j => multiplicity R i j) → ℂ
  | ⟨(i, j), (ρ, (α, β))⟩ => ⟪(b i j ρ : H), lU T i 0 α (rU R j 0 β x)⟫_ℂ

lemma coordU_apply (b : ∀ i j, OrthonormalBasis (Fin (multiplicity R i j)) ℂ (Vsub R i j)) (x : H) (i j : ι)
    (ρ : Fin (multiplicity R i j)) (α : Fin (n i)) (β : Fin (n j)) :
    coordU R b x ⟨(i, j), (ρ, (α, β))⟩ = ⟪(b i j ρ : H), lU T i 0 α (rU R j 0 β x)⟫_ℂ := rfl

/-- Parseval in `Vᵢⱼ`: `∑_ρ conj ⟪b ρ, u⟫ ⟪b ρ, v⟫ = ⟪u, v⟫`. -/
lemma parseval_Vsub {i j : ι} {m : ℕ} (b : OrthonormalBasis (Fin m) ℂ (Vsub R i j)) {u v : H}
    (hu : u ∈ Vsub R i j) (hv : v ∈ Vsub R i j) :
    ∑ ρ, star ⟪(b ρ : H), u⟫_ℂ * ⟪(b ρ : H), v⟫_ℂ = ⟪u, v⟫_ℂ := by
  have h := b.sum_inner_mul_inner ⟨u, hu⟩ ⟨v, hv⟩
  simp only [Submodule.coe_inner] at h
  rw [← h]
  refine Finset.sum_congr rfl fun ρ _ => ?_
  rw [← inner_conj_symm (b ρ : H) u, Complex.star_def, Complex.conj_conj]

/-- **The coordinates preserve the inner product**: `∑ₖ conj (x)ₖ (y)ₖ = ⟪x, y⟫`. -/
lemma sum_coordU (b : ∀ i j, OrthonormalBasis (Fin (multiplicity R i j)) ℂ (Vsub R i j)) (x y : H) :
    ∑ k, star (coordU R b x k) * coordU R b y k = ⟪x, y⟫_ℂ := by
  rw [← sum_inner_coord R x y]
  simp only [Fintype.sum_sigma, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun β _ => ?_
  exact parseval_Vsub R (b i j) (mem_Vsub R i j α β x) (mem_Vsub R i j α β y)

/-- The coordinates as a linear map `H → ⊕ᵢⱼ ℂʳⁱʲ ⊗ ℂⁿⁱ ⊗ ℂⁿʲ`. -/
def coordLin (b : ∀ i j, OrthonormalBasis (Fin (multiplicity R i j)) ℂ (Vsub R i j)) :
    H →ₗ[ℂ] HK n (fun i j => multiplicity R i j) where
  toFun x := WithLp.toLp 2 (coordU R b x)
  map_add' x y := by
    ext ⟨⟨i, j⟩, ρ, α, β⟩
    show ⟪(b i j ρ : H), lU T i 0 α (rU R j 0 β (x + y))⟫_ℂ =
      ⟪(b i j ρ : H), lU T i 0 α (rU R j 0 β x)⟫_ℂ + ⟪(b i j ρ : H), lU T i 0 α (rU R j 0 β y)⟫_ℂ
    rw [map_add, map_add, inner_add_right]
  map_smul' c x := by
    ext ⟨⟨i, j⟩, ρ, α, β⟩
    show ⟪(b i j ρ : H), lU T i 0 α (rU R j 0 β (c • x))⟫_ℂ = c * ⟪(b i j ρ : H), lU T i 0 α (rU R j 0 β x)⟫_ℂ
    rw [map_smul, map_smul, inner_smul_right]

/-- **The coordinate isometry** `H → ⊕ᵢⱼ ℂʳⁱʲ ⊗ ℂⁿⁱ ⊗ ℂⁿʲ`. -/
def coordIso (b : ∀ i j, OrthonormalBasis (Fin (multiplicity R i j)) ℂ (Vsub R i j)) :
    H →ₗᵢ[ℂ] HK n (fun i j => multiplicity R i j) :=
  (coordLin R b).isometryOfInner fun x y => by
    rw [PiLp.inner_apply]
    simp only [coordLin, LinearMap.coe_mk, AddHom.coe_mk, PiLp.toLp_apply, RCLike.inner_apply, starRingEnd_apply]
    rw [← sum_coordU R b x y]
    exact Finset.sum_congr rfl fun k _ => mul_comm _ _

/-- For a complex-linear `π`: `π(Eᵢ,0α) π(a) = ∑_γ (aᵢ)_{αγ} π(Eᵢ,0γ)`. -/
lemma lU_pi (hℂ : IsComplexLinear T) (i : ι) (α : Fin (n i)) (a : MatSum n) (y : H) :
    lU T i 0 α (T.π a y) = ∑ γ, a i α γ • lU T i 0 γ y := by
  simp only [lU, ContinuousLinearMap.coe_coe]
  rw [← ContinuousLinearMap.mul_apply, ← map_mul, unit_mul, unit_mul_single, map_sum, ContinuousLinearMap.sum_apply]
  refine Finset.sum_congr rfl fun γ _ => ?_
  rw [hℂ (a i α γ) (unit n i 0 γ), ContinuousLinearMap.smul_apply]

/-- **The coordinates intertwine `π` with the model**: `U π(a) = π_model(a) U`. -/
lemma coordU_pi (hℂ : IsComplexLinear T) (b : ∀ i j, OrthonormalBasis (Fin (multiplicity R i j)) ℂ (Vsub R i j))
    (a : MatSum n) (x : H) (i j : ι) (ρ : Fin (multiplicity R i j)) (α : Fin (n i)) (β : Fin (n j)) :
    coordU R b (T.π a x) ⟨(i, j), (ρ, (α, β))⟩ = ∑ γ, a i α γ * coordU R b x ⟨(i, j), (ρ, (γ, β))⟩ := by
  rw [coordU_apply, show rU R j 0 β (T.π a x) = T.π a (rU R j 0 β x) from (R.order_zero a _ _).symm,
    lU_pi hℂ, inner_sum]
  refine Finset.sum_congr rfl fun γ _ => ?_
  rw [inner_smul_right]
  rfl

/-- `⟪u, J w⟫ = ⟪w, J u⟫`. -/
lemma inner_J_right (u w : H) : ⟪u, R.J w⟫_ℂ = ⟪w, R.J u⟫_ℂ := by
  rw [← inner_conj_symm, inner_J_left, inner_conj_symm]

/-- **The coordinates intertwine `J` with the model** for `J`-compatible bases, `J bᵢⱼ ρ = bⱼᵢ ρ`. -/
lemma coordU_J (b : ∀ i j, OrthonormalBasis (Fin (multiplicity R i j)) ℂ (Vsub R i j))
    (hb : ∀ i j ρ, R.J (b i j ρ : H) = b j i (Fin.cast (multiplicity_symm R i j) ρ)) (x : H) (i j : ι)
    (ρ : Fin (multiplicity R i j)) (α : Fin (n i)) (β : Fin (n j)) :
    coordU R b (R.J x) ⟨(i, j), (ρ, (α, β))⟩ =
      star (coordU R b x ⟨(j, i), (Fin.cast (multiplicity_symm R i j) ρ, (β, α))⟩) := by
  rw [coordU_apply, coordU_apply, ← J_lU, ← J_rU, ← lU_rU, inner_J_right, hb, ← inner_conj_symm,
    Complex.star_def]

/-- `J` restricted to `Vᵢⱼ → Vⱼᵢ`, an antilinear map. -/
def JV (i j : ι) : Vsub R i j →ₗ⋆[ℂ] Vsub R j i where
  toFun v := ⟨R.J v, J_mem_Vsub R v.2⟩
  map_add' u v := Subtype.ext (map_add R.J (u : H) v)
  map_smul' c v := Subtype.ext (LinearMap.map_smulₛₗ R.J c (v : H))

lemma JV_coe (i j : ι) (v : Vsub R i j) : (JV R i j v : H) = R.J v := rfl

lemma inner_JV (i j : ι) (u v : Vsub R i j) : ⟪JV R i j u, JV R i j v⟫_ℂ = ⟪v, u⟫_ℂ := by
  simp only [Submodule.coe_inner, JV_coe, R.inner_J]

/-- **The `J`-transport of an orthonormal basis** of `Vᵢⱼ` to one of `Vⱼᵢ`. -/
def transportONB {i j : ι} (c : OrthonormalBasis (Fin (multiplicity R i j)) ℂ (Vsub R i j)) :
    OrthonormalBasis (Fin (multiplicity R j i)) ℂ (Vsub R j i) :=
  have hon : Orthonormal ℂ fun ρ => JV R i j (c (Fin.cast (multiplicity_symm R j i) ρ)) := by
    rw [orthonormal_iff_ite]
    intro ρ ρ'
    rw [inner_JV, orthonormal_iff_ite.1 c.orthonormal]
    by_cases h : ρ = ρ'
    · subst h; simp
    · rw [if_neg (fun h' => h (Fin.cast_injective _ h'.symm)), if_neg h]
  OrthonormalBasis.mk hon (hon.linearIndependent.span_eq_top_of_card_eq_finrank' (Fintype.card_fin _)).ge

lemma transportONB_apply {i j : ι} (c : OrthonormalBasis (Fin (multiplicity R i j)) ℂ (Vsub R i j))
    (ρ : Fin (multiplicity R j i)) :
    (transportONB R c ρ : H) = R.J (c (Fin.cast (multiplicity_symm R j i) ρ)) := by
  rw [transportONB, OrthonormalBasis.coe_mk]
  rfl

/-- **Orthonormal bases `bᵢⱼ` of the multiplicity spaces with `J bᵢⱼ ρ = bⱼᵢ ρ`** (Krajewski, Section 3.2, p. 13). -/
theorem exists_compatible_bases :
    ∃ b : ∀ i j, OrthonormalBasis (Fin (multiplicity R i j)) ℂ (Vsub R i j),
      ∀ i j ρ, R.J (b i j ρ : H) = b j i (Fin.cast (multiplicity_symm R i j) ρ) := by
  classical
  have hfix : ∀ i, ∃ c : OrthonormalBasis (Fin (multiplicity R i i)) ℂ (Vsub R i i), ∀ ρ, JV R i i (c ρ) = c ρ :=
    fun i => exists_orthonormalBasis_fixed (J := JV R i i) (inner_JV R i i) (fun x => Subtype.ext (R.J_J x))
  choose fx hfx using hfix
  let e := Fintype.equivFin ι
  let std : ∀ i j, OrthonormalBasis (Fin (multiplicity R i j)) ℂ (Vsub R i j) := fun i j =>
    stdOrthonormalBasis ℂ (Vsub R i j)
  let b : ∀ i j, OrthonormalBasis (Fin (multiplicity R i j)) ℂ (Vsub R i j) := fun i j =>
    if h : i = j then (by subst h; exact fx i) else if e i < e j then std i j else transportONB R (std j i)
  refine ⟨b, fun i j ρ => ?_⟩
  by_cases hij : i = j
  · subst hij
    have hb : b i i = fx i := dif_pos rfl
    rw [hb, Fin.cast_refl, id_eq]
    exact congrArg Subtype.val (hfx i ρ)
  · by_cases hlt : e i < e j
    · have hb1 : b i j = std i j := by simp only [b, dif_neg hij, if_pos hlt]
      have hb2 : b j i = transportONB R (std i j) := by
        simp only [b, dif_neg (Ne.symm hij), if_neg (lt_asymm hlt)]
      rw [hb1, hb2, transportONB_apply, Fin.cast_cast, Fin.cast_refl, id_eq]
    · have hb1 : b i j = transportONB R (std j i) := by simp only [b, dif_neg hij, if_neg hlt]
      have hgt : e j < e i := lt_of_le_of_ne (not_lt.1 hlt) (fun h => hij (e.injective h.symm))
      have hb2 : b j i = std j i := by simp only [b, dif_neg (Ne.symm hij), if_pos hgt]
      rw [hb1, hb2, transportONB_apply, R.J_J]

/-- **The preimage of a basis vector**: `U (π(Eᵢ,α0) J π(Eⱼ,β0) J bᵢⱼ ρ) = e_{(i, j, ρ, α, β)}`. -/
lemma coordIso_preimage (b : ∀ i j, OrthonormalBasis (Fin (multiplicity R i j)) ℂ (Vsub R i j)) (i j : ι)
    (ρ : Fin (multiplicity R i j)) (α : Fin (n i)) (β : Fin (n j)) :
    coordIso R b (lU T i α 0 (rU R j β 0 (b i j ρ))) =
      EuclideanSpace.single (⟨(i, j), (ρ, (α, β))⟩ : KIdx n (fun i j => multiplicity R i j)) 1 := by
  ext ⟨⟨i', j'⟩, ρ', α', β'⟩
  rw [PiLp.single_apply]
  show ⟪(b i' j' ρ' : H), lU T i' 0 α' (rU R j' 0 β' (lU T i α 0 (rU R j β 0 (b i j ρ))))⟫_ℂ = _
  by_cases hi : i' = i
  · subst hi
    by_cases hj : j' = j
    · subst hj
      rw [← lU_rU, lU_lU, rU_rU]
      by_cases hα : α' = α
      · by_cases hβ : β' = β
        · subst hα; subst hβ
          rw [if_pos rfl, if_pos rfl, lU_rU_of_mem_Vsub R (b i' j' ρ).2]
          have h := orthonormal_iff_ite.1 (b i' j').orthonormal ρ' ρ
          rw [Submodule.coe_inner] at h
          rw [h]
          by_cases hρ : ρ' = ρ
          · subst hρ; simp
          · rw [if_neg hρ, if_neg]
            intro hx
            simp only [Sigma.mk.inj_iff, heq_eq_eq, Prod.mk.injEq, true_and] at hx
            exact hρ hx.1
        · rw [if_pos hα, if_neg hβ, map_zero, inner_zero_right, if_neg]
          intro hx
          simp only [Sigma.mk.inj_iff, heq_eq_eq, Prod.mk.injEq, true_and] at hx
          exact hβ hx.2.2
      · rw [if_neg hα, inner_zero_right, if_neg]
        intro hx
        simp only [Sigma.mk.inj_iff, heq_eq_eq, Prod.mk.injEq, true_and] at hx
        exact hα hx.2.1
    · rw [← lU_rU, rU_rU_ne R hj, map_zero, map_zero, inner_zero_right, if_neg]
      intro hx
      simp only [Sigma.mk.inj_iff, Prod.mk.injEq] at hx
      exact hj hx.1.2
  · rw [← lU_rU R i j' α 0 0 β', lU_lU_ne hi, inner_zero_right, if_neg]
    intro hx
    simp only [Sigma.mk.inj_iff, Prod.mk.injEq] at hx
    exact hi hx.1.1

/-- **The coordinate isometry is onto**: every basis vector of the model has a preimage. -/
lemma coordIso_surjective (b : ∀ i j, OrthonormalBasis (Fin (multiplicity R i j)) ℂ (Vsub R i j)) :
    Function.Surjective (coordIso R b) := by
  have hrange : LinearMap.range (coordIso R b).toLinearMap = ⊤ := by
    rw [eq_top_iff, ← (EuclideanSpace.basisFun (KIdx n (fun i j => multiplicity R i j)) ℂ).toBasis.span_eq,
      Submodule.span_le]
    rintro _ ⟨⟨⟨i, j⟩, ρ, α, β⟩, rfl⟩
    refine ⟨lU T i α 0 (rU R j β 0 (b i j ρ)), ?_⟩
    rw [OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply]
    exact coordIso_preimage R b i j ρ α β
  exact LinearMap.range_eq_top.1 hrange

/-- **Uniqueness of the real structure up to unitary equivalence** (Krajewski, Section 3.2, p. 13: "the charge
conjugation is unique up to unitary equivalence, and it acts as above on tensor products"): for `A = ⊕ Mₙᵢ(ℂ)`
represented complex-linearly, every real structure is unitarily equivalent to the model `krajewskiReal` of its
multiplicity matrix, by a unitary intertwining `π` and `J`. -/
theorem exists_unitary_krajewski (hℂ : IsComplexLinear T) :
    ∃ U : H ≃ₗᵢ[ℂ] HK n (fun i j => multiplicity R i j),
      (∀ a x, U (T.π a x) = piK a (U x)) ∧ ∀ x, U (R.J x) = JK (multiplicity_symm R) (U x) := by
  obtain ⟨b, hb⟩ := exists_compatible_bases R
  refine ⟨LinearIsometryEquiv.ofSurjective (coordIso R b) (coordIso_surjective R b), fun a x => ?_, fun x => ?_⟩
  · ext ⟨⟨i, j⟩, ρ, α, β⟩
    show coordU R b (T.π a x) ⟨(i, j), (ρ, (α, β))⟩ = _
    rw [coordU_pi R hℂ, piK_apply]
    rfl
  · ext ⟨⟨i, j⟩, ρ, α, β⟩
    show coordU R b (R.J x) ⟨(i, j), (ρ, (α, β))⟩ = _
    rw [coordU_J R b hb, JK_apply]
    rfl

end

end Lightlike.NCG
