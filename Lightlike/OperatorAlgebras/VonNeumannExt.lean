import Lightlike.OperatorAlgebras.VonNeumannBoundary

/-!
# The self-adjoint extensions `A_U` of a closed symmetric operator

Von Neumann's theorem, case `n₊ = n₋` (Bonneau, Faraut and Valent, arXiv:quant-ph/0103153, Section 4, Theorem 1, second case: the self-adjoint
extensions are parametrised by unitaries): for a closed symmetric densely defined `A` and a unitary `U : N_i → N_{-i}` between its deficiency
spaces, the restriction `A_U` of `A†` to `D(A) + {p + U p}` is a self-adjoint extension of `A` (`extU_isSelfAdjoint`, `le_extU`). The domain
formula `D(A_U) = D(A) + (1 + U) N_i` is the library's own (not in the source read); the source states the parametrisation, not the formula.
-/

open scoped InnerProductSpace LinearPMap

namespace Lightlike.OperatorAlgebras

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {A : H →ₗ.[ℂ] H}

/-- A densely defined symmetric partial map is contained in its adjoint. -/
lemma le_adjoint_of_symm {T : H →ₗ.[ℂ] H} (hd : Dense (T.domain : Set H))
    (hs : ∀ x y : T.domain, ⟪T x, (y : H)⟫_ℂ = ⟪(x : H), T y⟫_ℂ) : T ≤ T† := by
  refine ⟨fun x hx => LinearPMap.mem_adjoint_domain_of_exists x ⟨T ⟨x, hx⟩, fun y => hs ⟨x, hx⟩ y⟩, ?_⟩
  intro x y hxy
  refine (LinearPMap.adjoint_apply_eq hd y (x₀ := (T x : H)) fun w => ?_).symm
  rw [← hxy]
  exact hs x w

variable (A) in
/-- The vectors `p + U p`, `p ∈ N_i`. -/
noncomputable def graphU (U : deficiencySpace A Complex.I ≃ₗᵢ[ℂ] deficiencySpace A (-Complex.I)) : Submodule ℂ H :=
  LinearMap.range ((deficiencySpace A Complex.I).subtype +
    (deficiencySpace A (-Complex.I)).subtype ∘ₗ U.toLinearEquiv.toLinearMap)

variable (A) in
/-- The domain `D(A) + {p + U p}` of the extension `A_U`. -/
noncomputable def domU (U : deficiencySpace A Complex.I ≃ₗᵢ[ℂ] deficiencySpace A (-Complex.I)) : Submodule ℂ H :=
  A.domain ⊔ graphU A U

lemma mem_graphU {U : deficiencySpace A Complex.I ≃ₗᵢ[ℂ] deficiencySpace A (-Complex.I)} (p : deficiencySpace A Complex.I) :
    (p : H) + (U p : H) ∈ graphU A U := ⟨p, rfl⟩

lemma mem_domU_iff {U : deficiencySpace A Complex.I ≃ₗᵢ[ℂ] deficiencySpace A (-Complex.I)} {v : H} :
    v ∈ domU A U ↔ ∃ x ∈ A.domain, ∃ p : deficiencySpace A Complex.I, v = x + p + U p := by
  rw [domU, Submodule.mem_sup]
  constructor
  · rintro ⟨x, hx, w, ⟨p, rfl⟩, rfl⟩
    exact ⟨x, hx, p, by simp [add_assoc]⟩
  · rintro ⟨x, hx, p, rfl⟩
    exact ⟨x, hx, _, mem_graphU p, by simp [add_assoc]⟩

lemma domU_le (hA : ClosedSymm A) (U : deficiencySpace A Complex.I ≃ₗᵢ[ℂ] deficiencySpace A (-Complex.I)) :
    domU A U ≤ (A†).domain := by
  refine sup_le hA.le_adjoint.1 ?_
  rintro _ ⟨p, rfl⟩
  obtain ⟨h1, -⟩ := p.2
  obtain ⟨h2, -⟩ := (U p).2
  exact (A†).domain.add_mem h1 h2

variable (A) in
/-- **The extension `A_U`**: the restriction of `A†` to `D(A) + {p + U p}`. -/
noncomputable def extU (U : deficiencySpace A Complex.I ≃ₗᵢ[ℂ] deficiencySpace A (-Complex.I)) : H →ₗ.[ℂ] H :=
  (A†).domRestrict (domU A U)

variable {U : deficiencySpace A Complex.I ≃ₗᵢ[ℂ] deficiencySpace A (-Complex.I)}

lemma extU_domain (hA : ClosedSymm A) : (extU A U).domain = domU A U := by
  rw [extU, LinearPMap.domRestrict_domain]; exact inf_eq_left.mpr (domU_le hA U)

lemma mem_extU_domain (hA : ClosedSymm A) {v : H} : v ∈ (extU A U).domain ↔ v ∈ domU A U := by
  rw [extU_domain hA]

/-- `A_U` acts as `A†`. -/
lemma extU_apply (x : (extU A U).domain) : (extU A U x : H) = A† ⟨(x : H), (Submodule.mem_inf.mp x.2).2⟩ :=
  LinearPMap.domRestrict_apply rfl

/-- **`A_U` extends `A`**. -/
theorem le_extU (hA : ClosedSymm A) : A ≤ extU A U := by
  refine ⟨fun x hx => (mem_extU_domain hA).mpr (Submodule.mem_sup_left hx), fun x y hxy => ?_⟩
  rw [extU_apply]
  exact hA.le_adjoint.2 hxy

/-- **`A_U` is symmetric**: the boundary form vanishes on `D(A) + {p + U p}` because `U` is isometric. -/
theorem extU_symm (hA : ClosedSymm A) (u v : (extU A U).domain) :
    ⟪(extU A U u : H), (v : H)⟫_ℂ = ⟪(u : H), (extU A U v : H)⟫_ℂ := by
  obtain ⟨x, hx, p, hu⟩ := mem_domU_iff.mp ((mem_extU_domain hA).mp u.2)
  obtain ⟨x', hx', p', hv⟩ := mem_domU_iff.mp ((mem_extU_domain hA).mp v.2)
  rw [extU_apply, extU_apply]
  have hb := boundary_form hA ⟨(u : H), (Submodule.mem_inf.mp u.2).2⟩ ⟨(v : H), (Submodule.mem_inf.mp v.2).2⟩
    ⟨x, hx⟩ ⟨x', hx'⟩ p.2 (U p).2 p'.2 (U p').2 hu hv
  have hiso : ⟪((U p : deficiencySpace A (-Complex.I)) : H), ((U p' : deficiencySpace A (-Complex.I)) : H)⟫_ℂ =
      ⟪(p : H), (p' : H)⟫_ℂ := by
    rw [← Submodule.coe_inner, ← Submodule.coe_inner, U.inner_map_map]
  rw [hiso, sub_self, mul_zero, sub_eq_zero] at hb
  exact hb

lemma dense_extU_domain (hA : ClosedSymm A) : Dense ((extU A U).domain : Set H) :=
  hA.dense.mono fun x hx => (mem_extU_domain hA).mpr (Submodule.mem_sup_left hx)

/-- A vector in the domain of `A_U†` lies in the domain of `A†`, and the two adjoints agree on it. -/
lemma adjoint_extU_mem (hA : ClosedSymm A) (y : ((extU A U)†).domain) :
    ∃ h : (y : H) ∈ (A†).domain, (A† ⟨(y : H), h⟩ : H) = ((extU A U)† y : H) := by
  have hfa := LinearPMap.adjoint_isFormalAdjoint (dense_extU_domain hA (U := U)) y
  have key : ∀ x : A.domain, ⟪((extU A U)† y : H), (x : H)⟫_ℂ = ⟪(y : H), (A x : H)⟫_ℂ := by
    intro x
    have hxe : (x : H) ∈ (extU A U).domain := (le_extU hA (U := U)).1 x.2
    rw [hfa ⟨(x : H), hxe⟩, ((le_extU hA (U := U)).2 (x := x) (y := ⟨(x : H), hxe⟩) rfl).symm]
  have h := LinearPMap.mem_adjoint_domain_of_exists (y : H) ⟨_, key⟩
  exact ⟨h, LinearPMap.adjoint_apply_eq hA.dense ⟨(y : H), h⟩ key⟩

/-- **`A_U†` is contained in `A_U`**: a vector of `D(A_U†)` is `x + p + q` with `q = U p`, by the boundary form against all `p' + U p'`. -/
theorem adjoint_extU_le (hA : ClosedSymm A) : (extU A U)† ≤ extU A U := by
  have hmem : ∀ y : ((extU A U)†).domain, (y : H) ∈ domU A U := by
    intro y
    obtain ⟨h, hAy⟩ := adjoint_extU_mem hA y
    obtain ⟨x0, p, q, hp, hq, hy⟩ := exists_decomp hA ⟨(y : H), h⟩
    have hfa := LinearPMap.adjoint_isFormalAdjoint (dense_extU_domain hA (U := U)) y
    have horth : ∀ p' : deficiencySpace A Complex.I,
        ⟪q, ((U p' : deficiencySpace A (-Complex.I)) : H)⟫_ℂ = ⟪p, (p' : H)⟫_ℂ := by
      intro p'
      have hv : (p' : H) + (U p' : H) ∈ (extU A U).domain :=
        (mem_extU_domain hA).mpr (Submodule.mem_sup_right (mem_graphU p'))
      have hvd : (p' : H) + (U p' : H) ∈ (A†).domain := (Submodule.mem_inf.mp hv).2
      have hb := boundary_form hA ⟨(y : H), h⟩ ⟨(p' : H) + (U p' : H), hvd⟩ x0 0 hp hq p'.2 (U p').2 hy
        (by simp)
      have h0 : ⟪(A† ⟨(y : H), h⟩ : H), (p' : H) + (U p' : H)⟫_ℂ -
          ⟪(y : H), (A† ⟨(p' : H) + (U p' : H), hvd⟩ : H)⟫_ℂ = 0 := by
        rw [hAy, hfa ⟨_, hv⟩, extU_apply, sub_self]
      rw [h0] at hb
      have h2 : (2 * Complex.I) ≠ 0 := by simp
      have := (mul_eq_zero.mp hb.symm).resolve_left h2
      exact sub_eq_zero.mp this
    set Up : deficiencySpace A (-Complex.I) := U ⟨p, hp⟩ with hUp
    have hr : q - (Up : H) ∈ deficiencySpace A (-Complex.I) := Submodule.sub_mem _ hq Up.2
    have h1 := horth (U.symm ⟨q - (Up : H), hr⟩)
    rw [LinearIsometryEquiv.apply_symm_apply] at h1
    have hiso : ⟪(Up : H), q - (Up : H)⟫_ℂ = ⟪p, ((U.symm ⟨q - (Up : H), hr⟩ : deficiencySpace A Complex.I) : H)⟫_ℂ := by
      have := U.inner_map_map ⟨p, hp⟩ (U.symm ⟨q - (Up : H), hr⟩)
      rw [LinearIsometryEquiv.apply_symm_apply, Submodule.coe_inner, Submodule.coe_inner] at this
      exact this
    have hz : ⟪q - (Up : H), q - (Up : H)⟫_ℂ = 0 := by
      rw [inner_sub_left]
      simp only at h1
      rw [h1, hiso, sub_self]
    have hqU : q = (Up : H) := sub_eq_zero.mp (inner_self_eq_zero.mp hz)
    exact mem_domU_iff.mpr ⟨x0, x0.2, ⟨p, hp⟩, by rw [hy, hqU]⟩
  refine ⟨fun y hy => (mem_extU_domain hA).mpr (hmem ⟨y, hy⟩), fun y z hyz => ?_⟩
  obtain ⟨h, hAy⟩ := adjoint_extU_mem hA y
  rw [← hAy, extU_apply]
  congr 1
  exact Subtype.ext hyz

/-- **Von Neumann's theorem, case `n₊ = n₋`**: for a closed symmetric densely defined `A` and a unitary `U : N_i → N_{-i}`, the extension `A_U`
is self-adjoint. -/
theorem extU_isSelfAdjoint (hA : ClosedSymm A) : IsSelfAdjoint (extU A U) :=
  le_antisymm (adjoint_extU_le hA) (le_adjoint_of_symm (dense_extU_domain hA) (extU_symm hA))

end Lightlike.OperatorAlgebras
