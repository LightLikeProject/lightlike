import Lightlike.NCG.Bimodule

/-!
# The Dirac operator of a real finite spectral triple: `D = Δ + J Δ J`

T. Krajewski, arXiv:hep-th/9701081, Section 3.4, p. 15 (read): `D = D_L + D_R` with `[D_L, π(A)] = [D_R, J π(A) J⁻¹] = 0`,
the decomposition is unique since `D` anticommutes with `χ`, `D_L = J D_R J⁻¹`, and "the Dirac operator of a finite
spectral triple is given by `D = Δ + J Δ J⁻¹`, where `Δ` is a hermitian operator on `H`, which commutes with `J π(A) J⁻¹`
and anticommutes with `χ`". M. Paschke, A. Sitarz, arXiv:q-alg/9612029, Lemma 6, p. 5 (read): `Dᵢⱼ,ₖₗ` vanishes unless
`i = k` or `j = l`, "in either of these cases `D` must commute with the corresponding action".

The chirality is assumed to be a scalar on each vertex `Hᵢⱼ` (Paschke-Sitarz, Lemma 3, p. 3: `γ = ±1` on `Hᵢⱼ`, a
consequence of the axiom that `γ` is the image of a Hochschild cycle; Krajewski, Section 3.3: `χ = ⊕ ±1`).

* `rightOp_proj`, `pi_proj`: the actions commute with the projections `Eᵢⱼ`;
* `proj_D_proj_rightOp` (`i ≠ k`), `proj_D_proj_pi` (`j ≠ l`): Lemma 6, second half;
* `proj_D_proj_diag`: `Eᵢⱼ D Eᵢⱼ = 0` for a scalar chirality;
* `D_eq_sum`, `Delta`, `J_Delta_J`, `D_eq_Delta_add`: `D = Δ + J Δ J`;
* `Delta_rightOp`, `Delta_gamma`, `Delta_symm`, `Delta_unique`: `Δ` commutes with `J π(A) J`, anticommutes with `γ`,
  is hermitian, and is unique.
-/

open scoped InnerProductSpace

namespace Lightlike.NCG

noncomputable section

variable {A H : Type*} [Ring A] [StarRing A] [Algebra ℝ A] [FiniteDimensional ℝ A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H] [CompleteSpace H]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {T : FiniteSpectralTriple A H} (R : RealStructure T) (C : CentralPartition A ι)

/-- `J π(b) J` commutes with `π(Pᵢ)`. -/
lemma rightOp_leftP (b : A) (i : ι) (x : H) : rightOp R b (leftP T C i x) = leftP T C i (rightOp R b x) :=
  (R.order_zero _ b x).symm

/-- `J π(b) J` commutes with `J π(Pⱼ) J`. -/
lemma rightOp_rightP (b : A) (j : ι) (x : H) : rightOp R b (rightP R C j x) = rightP R C j (rightOp R b x) := by
  have e1 := congrArg (fun f : H →ₗ[ℂ] H => f x) (rightOp_mul R b (C.P j))
  have e2 := congrArg (fun f : H →ₗ[ℂ] H => f x) (rightOp_mul R (C.P j) b)
  simp only [Module.End.mul_apply] at e1 e2
  rw [rightP, ← e1, ← C.central j b, e2]

/-- `J π(b) J` commutes with `Eᵢⱼ`. -/
lemma rightOp_proj (b : A) (i j : ι) (x : H) :
    rightOp R b (proj R C (i, j) x) = proj R C (i, j) (rightOp R b x) := by
  rw [proj_apply, proj_apply, rightOp_leftP, rightOp_rightP]

/-- `π(a)` commutes with `π(Pᵢ)`. -/
lemma pi_leftP (a : A) (i : ι) (x : H) : T.π a (leftP T C i x) = leftP T C i (T.π a x) := by
  simp only [leftP_apply]
  rw [← ContinuousLinearMap.mul_apply, ← map_mul, ← C.central i a, map_mul, ContinuousLinearMap.mul_apply]

/-- `π(a)` commutes with `Eᵢⱼ`. -/
lemma pi_proj (a : A) (i j : ι) (x : H) : T.π a (proj R C (i, j) x) = proj R C (i, j) (T.π a x) := by
  rw [proj_apply, proj_apply, pi_leftP, show T.π a (rightP R C j x) = rightP R C j (T.π a x) from R.order_zero a _ x]

lemma leftP_proj_ne {i k : ι} (h : i ≠ k) (j : ι) (x : H) : proj R C (i, j) (leftP T C k x) = 0 := by
  rw [proj_apply, rightP_leftP, leftP_leftP, if_neg h]

lemma proj_rightP_ne {j l : ι} (h : j ≠ l) (i : ι) (x : H) : proj R C (i, j) (rightP R C l x) = 0 := by
  rw [proj_apply, rightP_rightP, if_neg h, map_zero]

lemma proj_D_rightOp_of_leftP {i k : ι} (hik : i ≠ k) (j : ι) (b : A) {y : H} (hLy : leftP T C k y = y) :
    proj R C (i, j) (T.D (rightOp R b y)) = rightOp R b (proj R C (i, j) (T.D y)) := by
  have hLRy : leftP T C k (rightOp R b y) = rightOp R b y := by rw [← rightOp_leftP, hLy]
  have hfo := R.first_order (C.P k) b y
  simp only [FiniteSpectralTriple.comm, ContinuousLinearMap.sub_apply, ContinuousLinearMap.mul_apply] at hfo
  have h1 : T.π (C.P k) (R.J (T.π b (R.J y))) = rightOp R b y := hLRy
  have h2 : T.π (C.P k) y = y := hLy
  rw [h1, h2] at hfo
  have key : T.D (rightOp R b y) - leftP T C k (T.D (rightOp R b y)) =
      rightOp R b (T.D y) - rightOp R b (leftP T C k (T.D y)) := by
    rw [← map_sub]
    exact hfo
  have := congrArg (fun z => proj R C (i, j) z) key
  simp only [map_sub] at this
  rw [leftP_proj_ne R C hik, ← rightOp_proj R C b i j (leftP T C k (T.D y)), leftP_proj_ne R C hik, map_zero,
    sub_zero, sub_zero] at this
  rw [this, ← rightOp_proj]

/-- **Paschke-Sitarz, Lemma 6, second half (right action)**: for `i ≠ k`, `Eᵢⱼ D Eₖₗ` commutes with `J π(b) J`. -/
theorem proj_D_proj_rightOp {i k : ι} (hik : i ≠ k) (j l : ι) (b : A) (x : H) :
    proj R C (i, j) (T.D (proj R C (k, l) (rightOp R b x))) = rightOp R b (proj R C (i, j) (T.D (proj R C (k, l) x))) := by
  rw [← rightOp_proj R C b k l x]
  exact proj_D_rightOp_of_leftP R C hik j b (by rw [proj_apply, leftP_leftP, if_pos rfl])

lemma proj_D_pi_of_rightP {j l : ι} (hjl : j ≠ l) (i : ι) (a : A) {y : H} (hRy : rightP R C l y = y) :
    proj R C (i, j) (T.D (T.π a y)) = T.π a (proj R C (i, j) (T.D y)) := by
  have hfo := R.first_order a (C.P l) y
  simp only [FiniteSpectralTriple.comm, ContinuousLinearMap.sub_apply, ContinuousLinearMap.mul_apply] at hfo
  have h1 : R.J (T.π (C.P l) (R.J y)) = y := hRy
  rw [h1] at hfo
  have key : T.D (T.π a y) - T.π a (T.D y) = rightP R C l (T.D (T.π a y) - T.π a (T.D y)) := hfo
  have := congrArg (fun z => proj R C (i, j) z) key
  simp only [map_sub, proj_rightP_ne R C hjl, sub_self, sub_eq_zero] at this
  rw [this, ← pi_proj]

/-- **Paschke-Sitarz, Lemma 6, second half (left action)**: for `j ≠ l`, `Eᵢⱼ D Eₖₗ` commutes with `π(a)`. -/
theorem proj_D_proj_pi {j l : ι} (hjl : j ≠ l) (i k : ι) (a : A) (x : H) :
    proj R C (i, j) (T.D (proj R C (k, l) (T.π a x))) = T.π a (proj R C (i, j) (T.D (proj R C (k, l) x))) := by
  rw [← pi_proj R C a k l x]
  exact proj_D_pi_of_rightP R C hjl i a (by rw [proj_apply, rightP_leftP, rightP_rightP, if_pos rfl])

/-- **The diagonal blocks of `D` vanish** when the chirality is a scalar on `Hᵢⱼ`: `γ (Eᵢⱼ D Eᵢⱼ x) = s Eᵢⱼ D Eᵢⱼ x`
and `= -s Eᵢⱼ D Eᵢⱼ x`, with `s² = 1` unless `Hᵢⱼ = 0`. -/
theorem proj_D_proj_diag (G : Grading T R) {i j : ι} (s : ℂ) (hs : ∀ x ∈ Hsub R C i j, G.γ x = s • x) (x : H) :
    proj R C (i, j) (T.D (proj R C (i, j) x)) = 0 := by
  set y := proj R C (i, j) x with hy
  have hymem : y ∈ Hsub R C i j := ⟨x, rfl⟩
  set z := proj R C (i, j) (T.D y) with hz
  have hzmem : z ∈ Hsub R C i j := ⟨T.D y, rfl⟩
  have hπ : ∀ a w, G.γ (T.π a w) = T.π a (G.γ w) := fun a w => by
    have := congrArg (fun f : H →L[ℂ] H => f w) (G.γ_π a)
    simpa only [ContinuousLinearMap.mul_apply] using this
  have hγproj : ∀ w, G.γ (proj R C (i, j) w) = proj R C (i, j) (G.γ w) := fun w => by
    simp only [proj_apply, leftP_apply, rightP_apply, hπ, G.γ_J]
  have hγD : ∀ w, G.γ (T.D w) = -T.D (G.γ w) := fun w => by
    have := congrArg (fun f : H →L[ℂ] H => f w) G.D_γ
    simp only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.neg_apply] at this
    rw [this, neg_neg]
  have h1 : G.γ z = s • z := hs z hzmem
  have h2 : G.γ z = -(s • z) := by
    rw [hz, hγproj, hγD, hs y hymem, map_smul, map_neg, map_smul]
  have h3 : s • s • y = y := by
    have := congrArg (fun f : H →L[ℂ] H => f y) G.γ_γ
    simp only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.one_apply, hs y hymem, map_smul] at this
    exact this
  by_cases hs0 : s = 0
  · rw [hs0, zero_smul] at h3
    rw [hz, ← h3, map_zero, map_zero]
  · have h4 : (2 * s) • z = 0 := by
      rw [← smul_smul, two_smul]
      exact eq_neg_iff_add_eq_zero.1 (h1.symm.trans h2)
    exact (smul_eq_zero.1 h4).resolve_left (mul_ne_zero two_ne_zero hs0)

/-- `D = ∑ₚ ∑_q Eₚ D E_q`. -/
lemma D_eq_sum (x : H) : T.D x = ∑ p : ι × ι, ∑ q : ι × ι, proj R C p (T.D (proj R C q x)) := by
  have hc := (completeOrthogonalIdempotents_proj R C).complete
  have h1 : ∀ z : H, ∑ p : ι × ι, proj R C p z = z := fun z => by
    have := congrArg (fun f : H →ₗ[ℂ] H => f z) hc
    simpa only [LinearMap.sum_apply, Module.End.one_apply] using this
  conv_lhs => rw [← h1 x, map_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun q _ => (h1 _).symm

/-- **`Δ = ∑_{i ≠ k} Eᵢⱼ D Eₖₗ`**: the part of `D` between vertices in different rows. -/
def Delta : H →ₗ[ℂ] H where
  toFun x := ∑ p : ι × ι, ∑ q : ι × ι, if p.1 ≠ q.1 then proj R C p (T.D (proj R C q x)) else 0
  map_add' x y := by
    simp only [map_add, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
    split_ifs <;> simp
  map_smul' c x := by
    simp only [map_smul, Finset.smul_sum, RingHom.id_apply]
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
    split_ifs <;> simp

lemma Delta_apply (x : H) :
    Delta R C x = ∑ p : ι × ι, ∑ q : ι × ι, if p.1 ≠ q.1 then proj R C p (T.D (proj R C q x)) else 0 := rfl

lemma J_proj (p : ι × ι) (w : H) : R.J (proj R C p w) = proj R C p.swap (R.J w) := by
  obtain ⟨i, j⟩ := p
  show R.J (proj R C (i, j) w) = proj R C (j, i) (R.J w)
  rw [← J_proj_J R C i j (R.J w), R.J_J]

/-- **`J Δ J = ∑_{j ≠ l} Eᵢⱼ D Eₖₗ`**. -/
lemma J_Delta_J (x : H) :
    R.J (Delta R C (R.J x)) =
      ∑ p : ι × ι, ∑ q : ι × ι, if p.2 ≠ q.2 then proj R C p (T.D (proj R C q x)) else 0 := by
  simp only [Delta_apply, map_sum, apply_ite R.J, map_zero, J_proj, ← R.D_J, R.J_J]
  rw [← (Equiv.prodComm ι ι).sum_comp]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [← (Equiv.prodComm ι ι).sum_comp]
  rfl

/-- **`D = Δ + J Δ J`** (Krajewski, Section 3.4, p. 15) for a chirality that is a scalar on each vertex. -/
theorem D_eq_Delta_add (G : Grading T R) (hγ : ∀ i j, ∃ s : ℂ, ∀ x ∈ Hsub R C i j, G.γ x = s • x) (x : H) :
    T.D x = Delta R C x + R.J (Delta R C (R.J x)) := by
  rw [J_Delta_J, Delta_apply, ← Finset.sum_add_distrib, D_eq_sum R C x]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun q _ => ?_
  obtain ⟨i, j⟩ := p
  obtain ⟨k, l⟩ := q
  by_cases hik : i = k <;> by_cases hjl : j = l
  · subst hik; subst hjl
    obtain ⟨s, hs⟩ := hγ i j
    simp only [ne_eq, not_true_eq_false, if_false, add_zero, proj_D_proj_diag R C G s hs]
  · simp [hik, hjl]
  · simp [hik, hjl]
  · simp only [ne_eq, hik, hjl, not_false_eq_true, if_true, proj_D_proj_eq_zero R C hik hjl, add_zero]

/-- **`Δ` commutes with the right action** `J π(b) J` (Krajewski, Section 3.4, p. 15). -/
theorem Delta_rightOp (b : A) (x : H) : Delta R C (rightOp R b x) = rightOp R b (Delta R C x) := by
  simp only [Delta_apply, map_sum, apply_ite (rightOp R b), map_zero]
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
  obtain ⟨i, j⟩ := p
  obtain ⟨k, l⟩ := q
  split_ifs with h
  · exact proj_D_proj_rightOp R C h j l b x
  · rfl

lemma gamma_proj (G : Grading T R) (p : ι × ι) (w : H) : G.γ (proj R C p w) = proj R C p (G.γ w) := by
  have hπ : ∀ a z, G.γ (T.π a z) = T.π a (G.γ z) := fun a z => by
    have := congrArg (fun f : H →L[ℂ] H => f z) (G.γ_π a)
    simpa only [ContinuousLinearMap.mul_apply] using this
  obtain ⟨i, j⟩ := p
  simp only [proj_apply, leftP_apply, rightP_apply, hπ, G.γ_J]

lemma gamma_D (G : Grading T R) (w : H) : G.γ (T.D w) = -T.D (G.γ w) := by
  have := congrArg (fun f : H →L[ℂ] H => f w) G.D_γ
  simp only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.neg_apply] at this
  rw [this, neg_neg]

/-- **`Δ` anticommutes with the chirality** (Krajewski, Section 3.4, p. 15). -/
theorem Delta_gamma (G : Grading T R) (x : H) : Delta R C (G.γ x) = -G.γ (Delta R C x) := by
  simp only [Delta_apply, map_sum, apply_ite G.γ, map_zero, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
  split_ifs
  · rw [← gamma_proj, gamma_proj R C G p, gamma_D, map_neg, neg_neg]
  · rw [neg_zero]

/-- **The decomposition is unique** (Krajewski, Section 3.4, p. 15): two right-linear `Δ₁`, `Δ₂` anticommuting with a
chirality that is scalar on each vertex, with `D = Δₖ + J Δₖ J`, are equal. -/
theorem Delta_unique (G : Grading T R) (hγ : ∀ i j, ∃ s : ℂ, ∀ x ∈ Hsub R C i j, G.γ x = s • x)
    (Δ₁ Δ₂ : H →ₗ[ℂ] H) (hR₁ : ∀ b x, Δ₁ (rightOp R b x) = rightOp R b (Δ₁ x))
    (hR₂ : ∀ b x, Δ₂ (rightOp R b x) = rightOp R b (Δ₂ x)) (hγ₁ : ∀ x, Δ₁ (G.γ x) = -G.γ (Δ₁ x))
    (hγ₂ : ∀ x, Δ₂ (G.γ x) = -G.γ (Δ₂ x)) (hD₁ : ∀ x, T.D x = Δ₁ x + R.J (Δ₁ (R.J x)))
    (hD₂ : ∀ x, T.D x = Δ₂ x + R.J (Δ₂ (R.J x))) : Δ₁ = Δ₂ := by
  set X := Δ₁ - Δ₂ with hX
  have hXJ : ∀ x, X x = -R.J (X (R.J x)) := fun x => by
    have h := (hD₁ x).symm.trans (hD₂ x)
    simp only [hX, LinearMap.sub_apply, map_sub]
    rw [neg_sub, sub_eq_sub_iff_add_eq_add, h, add_comm]
  have hXR : ∀ b x, X (rightOp R b x) = rightOp R b (X x) := fun b x => by
    simp only [hX, LinearMap.sub_apply, hR₁, hR₂, map_sub]
  have hXL : ∀ a x, X (T.π a x) = T.π a (X x) := fun a x => by
    have e1 : R.J (T.π a x) = rightOp R a (R.J x) := by rw [rightOp_apply, R.J_J]
    have e2 : ∀ w, R.J (rightOp R a w) = T.π a (R.J w) := fun w => by rw [rightOp_apply, R.J_J]
    rw [hXJ (T.π a x), e1, hXR, e2, hXJ x, map_neg]
  have hXproj : ∀ p x, X (proj R C p x) = proj R C p (X x) := fun p x => by
    obtain ⟨i, j⟩ := p
    rw [proj_apply, proj_apply, leftP_apply, hXL, rightP, hXR]
    rfl
  have hc : ∀ z : H, ∑ p : ι × ι, proj R C p z = z := fun z => by
    have := congrArg (fun f : H →ₗ[ℂ] H => f z) (completeOrthogonalIdempotents_proj R C).complete
    simpa only [LinearMap.sum_apply, Module.End.one_apply] using this
  have hX0 : ∀ x, X x = 0 := fun x => by
    rw [← hc x, map_sum]
    refine Finset.sum_eq_zero fun p _ => ?_
    obtain ⟨i, j⟩ := p
    obtain ⟨s, hs⟩ := hγ i j
    have hy : proj R C (i, j) x ∈ Hsub R C i j := ⟨x, rfl⟩
    have hXy : X (proj R C (i, j) x) ∈ Hsub R C i j := ⟨X x, (hXproj (i, j) x).symm⟩
    have hXγ : ∀ y, X (G.γ y) = -G.γ (X y) := fun y => by
      simp only [hX, LinearMap.sub_apply, hγ₁, hγ₂, map_sub]
      abel
    have h3 : s • X (proj R C (i, j) x) = -(s • X (proj R C (i, j) x)) := by
      calc s • X (proj R C (i, j) x) = X (s • proj R C (i, j) x) := (map_smul X s _).symm
        _ = X (G.γ (proj R C (i, j) x)) := by rw [hs _ hy]
        _ = -G.γ (X (proj R C (i, j) x)) := hXγ _
        _ = -(s • X (proj R C (i, j) x)) := by rw [hs _ hXy]
    have h4 : s • s • proj R C (i, j) x = proj R C (i, j) x := by
      have := congrArg (fun f : H →L[ℂ] H => f (proj R C (i, j) x)) G.γ_γ
      simp only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.one_apply, hs _ hy, map_smul] at this
      exact this
    by_cases hs0 : s = 0
    · rw [hs0, zero_smul] at h4
      rw [← h4, map_zero]
    · have h5 : (2 * s) • X (proj R C (i, j) x) = 0 := by
        rw [← smul_smul, two_smul]
        exact eq_neg_iff_add_eq_zero.1 h3
      exact (smul_eq_zero.1 h5).resolve_left (mul_ne_zero two_ne_zero hs0)
  ext x
  have := hX0 x
  simp only [hX, LinearMap.sub_apply, sub_eq_zero] at this
  exact this

lemma inner_J_left' (z y : H) : ⟪R.J z, y⟫_ℂ = ⟪R.J y, z⟫_ℂ := by
  conv_lhs => rw [← R.J_J y]
  exact R.inner_J z (R.J y)

lemma inner_leftP (i : ι) (u v : H) : ⟪leftP T C i u, v⟫_ℂ = ⟪u, leftP T C i v⟫_ℂ := by
  simp only [leftP_apply]
  rw [← ContinuousLinearMap.adjoint_inner_right, ← ContinuousLinearMap.star_eq_adjoint, ← map_star, C.star_P]

lemma inner_rightP (j : ι) (u v : H) : ⟪rightP R C j u, v⟫_ℂ = ⟪u, rightP R C j v⟫_ℂ := by
  simp only [rightP_apply]
  rw [inner_J_left', ← ContinuousLinearMap.adjoint_inner_left, ← ContinuousLinearMap.star_eq_adjoint, ← map_star,
    C.star_P, ← inner_conj_symm, inner_J_left', inner_conj_symm]

/-- `Eᵢⱼ` is self-adjoint. -/
lemma inner_proj (p : ι × ι) (u v : H) : ⟪proj R C p u, v⟫_ℂ = ⟪u, proj R C p v⟫_ℂ := by
  obtain ⟨i, j⟩ := p
  rw [proj_apply, proj_apply, inner_leftP, inner_rightP, rightP_leftP]

/-- **`Δ` is hermitian** (Krajewski, Section 3.4, p. 15). -/
theorem Delta_symm (x y : H) : ⟪Delta R C x, y⟫_ℂ = ⟪x, Delta R C y⟫_ℂ := by
  have hD : ∀ u v, ⟪T.D u, v⟫_ℂ = ⟪u, T.D v⟫_ℂ := fun u v => T.isSelfAdjoint_D.isSymmetric u v
  simp only [Delta_apply, sum_inner, inner_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun p _ => ?_
  split_ifs with h1 h2 h2
  · rw [inner_proj, hD, inner_proj]
  · exact absurd (Ne.symm h1) h2
  · exact absurd (Ne.symm h2) h1
  · simp

end

end Lightlike.NCG
