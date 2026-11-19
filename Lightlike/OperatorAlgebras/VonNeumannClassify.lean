import Lightlike.OperatorAlgebras.VonNeumannExt

/-!
# Every self-adjoint extension is an `A_U`

For a closed symmetric densely defined `A` and a self-adjoint `B ⊇ A`: for each `p ∈ N_i` there is a unique `q ∈ N_{-i}` with `p + q ∈ D(B)`,
`p ↦ q` is a unitary `U_B : N_i → N_{-i}` and `B = A_{U_B}` (`eq_extU_of_selfAdjoint`). Hence a self-adjoint extension exists only if the
deficiency spaces are unitarily equivalent, in particular `n₊ = n₋` (`deficiencyDim_eq_of_selfAdjoint_ext`): von Neumann's theorem,
cases (ii) and (iii) (Bonneau, Faraut and Valent, arXiv:quant-ph/0103153, Section 4, Theorem 1).
-/

open scoped InnerProductSpace LinearPMap

namespace Lightlike.OperatorAlgebras

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {A : H →ₗ.[ℂ] H}

/-- **The adjoint reverses inclusions**: `S ≤ T` (`S` densely defined) gives `T† ≤ S†`. -/
lemma adjoint_antitone {S T : H →ₗ.[ℂ] H} (hS : Dense (S.domain : Set H)) (hST : S ≤ T) : T† ≤ S† := by
  have hT : Dense (T.domain : Set H) := hS.mono hST.1
  have key : ∀ y : (T†).domain, ∀ x : S.domain, ⟪(T† y : H), (x : H)⟫_ℂ = ⟪(y : H), (S x : H)⟫_ℂ := by
    intro y x
    rw [LinearPMap.adjoint_isFormalAdjoint hT y ⟨(x : H), hST.1 x.2⟩, (hST.2 (x := x) (y := ⟨(x : H), hST.1 x.2⟩) rfl).symm]
  refine ⟨fun y hy => LinearPMap.mem_adjoint_domain_of_exists y ⟨_, key ⟨y, hy⟩⟩, fun y z hyz => ?_⟩
  refine (LinearPMap.adjoint_apply_eq hS z (x₀ := (T† y : H)) fun x => ?_).symm
  rw [← hyz]; exact key y x

variable {B : H →ₗ.[ℂ] H}

lemma le_adjoint_of_selfAdjoint_ext (hA : ClosedSymm A) (hAB : A ≤ B) (hB : IsSelfAdjoint B) : B ≤ A† := by
  have h := adjoint_antitone hA.dense hAB
  have hBB : B† = B := hB
  rwa [hBB] at h

/-- `‖s‖ = 0` when `⟪φ, s⟫ = 0` and `φ = s`: the orthogonality step used twice below. -/
private lemma eq_zero_of_inner_self {s : H} (h : ⟪s, s⟫_ℂ = 0) : s = 0 := inner_self_eq_zero.mp h

/-- **A partner in `N_{-i}`**: for a self-adjoint `B ⊇ A` and `p ∈ N_i` there is `q ∈ N_{-i}` with `p + q ∈ D(B)`. -/
lemma exists_partner (hA : ClosedSymm A) (hAB : A ≤ B) (hB : IsSelfAdjoint B) {p : H}
    (hp : p ∈ deficiencySpace A Complex.I) : ∃ q ∈ deficiencySpace A (-Complex.I), p + q ∈ B.domain := by
  have hBA := le_adjoint_of_selfAdjoint_ext hA hAB hB
  obtain ⟨w, hw⟩ := sa_shiftMap_surjective hB (z := -Complex.I) (by simp) ((2 * Complex.I) • p)
  let w' : (A†).domain := ⟨(w : H), hBA.1 w.2⟩
  have hAw : (A† w' : H) = B w := (hBA.2 (x := w) (y := w') rfl).symm
  obtain ⟨x, p1, q1, hp1, hq1, hwd⟩ := exists_decomp hA w'
  have hdec := adjoint_decomp hA w' x hp1 hq1 hwd
  rw [hAw] at hdec
  rw [shiftMap_apply, hdec] at hw
  have hwd' : (w : H) = x + p1 + q1 := hwd
  rw [hwd'] at hw
  have hs : shiftMap A (-Complex.I) x = (2 * Complex.I) • (p - p1) := by
    rw [shiftMap_apply, smul_sub, ← hw]; module
  have hmem : (2 * Complex.I) • (p - p1) ∈ deficiencySpace A ((starRingEnd ℂ) (-Complex.I)) := by
    simpa using Submodule.smul_mem _ (2 * Complex.I) (Submodule.sub_mem _ hp hp1)
  have h0 := inner_deficiency_shift hA hmem x
  rw [hs] at h0
  have hpp : p = p1 := by
    have h1 := eq_zero_of_inner_self h0
    have h2 : p - p1 = 0 := (smul_eq_zero.mp h1).resolve_left (by simp)
    exact sub_eq_zero.mp h2
  refine ⟨q1, hq1, ?_⟩
  have hxB : (x : H) ∈ B.domain := hAB.1 x.2
  have : p + q1 = (w : H) - x := by rw [hwd', hpp]; abel
  rw [this]
  exact B.domain.sub_mem w.2 hxB

/-- **A partner in `N_i`**: for `q ∈ N_{-i}` there is `p ∈ N_i` with `p + q ∈ D(B)`. -/
lemma exists_partner' (hA : ClosedSymm A) (hAB : A ≤ B) (hB : IsSelfAdjoint B) {q : H}
    (hq : q ∈ deficiencySpace A (-Complex.I)) : ∃ p ∈ deficiencySpace A Complex.I, p + q ∈ B.domain := by
  have hBA := le_adjoint_of_selfAdjoint_ext hA hAB hB
  obtain ⟨w, hw⟩ := sa_shiftMap_surjective hB (z := Complex.I) (by simp) ((-(2 * Complex.I)) • q)
  let w' : (A†).domain := ⟨(w : H), hBA.1 w.2⟩
  have hAw : (A† w' : H) = B w := (hBA.2 (x := w) (y := w') rfl).symm
  obtain ⟨x, p1, q1, hp1, hq1, hwd⟩ := exists_decomp hA w'
  have hdec := adjoint_decomp hA w' x hp1 hq1 hwd
  rw [hAw] at hdec
  rw [shiftMap_apply, hdec] at hw
  have hwd' : (w : H) = x + p1 + q1 := hwd
  rw [hwd'] at hw
  have hs : shiftMap A Complex.I x = (-(2 * Complex.I)) • (q - q1) := by
    rw [shiftMap_apply, smul_sub, ← hw]; module
  have hmem : (-(2 * Complex.I)) • (q - q1) ∈ deficiencySpace A ((starRingEnd ℂ) Complex.I) := by
    simpa using Submodule.smul_mem _ (-(2 * Complex.I)) (Submodule.sub_mem _ hq hq1)
  have h0 := inner_deficiency_shift hA hmem x
  rw [hs] at h0
  have hqq : q = q1 := by
    have h1 := eq_zero_of_inner_self h0
    have h2 : q - q1 = 0 := (smul_eq_zero.mp h1).resolve_left (by simp)
    exact sub_eq_zero.mp h2
  refine ⟨p1, hp1, ?_⟩
  have hxB : (x : H) ∈ B.domain := hAB.1 x.2
  have : p1 + q = (w : H) - x := by rw [hwd', hqq]; abel
  rw [this]
  exact B.domain.sub_mem w.2 hxB

/-- A self-adjoint `B ⊇ A` has no vector of `N_{-i}` (or `N_i`) in its domain besides `0`. -/
lemma eq_zero_of_mem_deficiency_domain (hA : ClosedSymm A) (hAB : A ≤ B) (hB : IsSelfAdjoint B) {z : ℂ}
    (hz : z.im ≠ 0) {r : H} (hr : r ∈ deficiencySpace A z) (hrB : r ∈ B.domain) : r = 0 := by
  have hBA := le_adjoint_of_selfAdjoint_ext hA hAB hB
  obtain ⟨hrd, hre⟩ := hr
  have hBr : (B ⟨r, hrB⟩ : H) = z • r := by
    rw [← hre]; exact hBA.2 (x := ⟨r, hrB⟩) (y := ⟨r, hrd⟩) rfl
  have hmem : r ∈ deficiencySpace B z := by
    refine mem_deficiencySpace_of_forall hB.dense_domain z r fun x => ?_
    rw [← hBr, sa_symm_apply hB ⟨r, hrB⟩ x]
  rw [deficiencySpace_of_isSelfAdjoint hB hz] at hmem
  simpa using hmem

/-- **Uniqueness of the partner**. -/
lemma partner_unique (hA : ClosedSymm A) (hAB : A ≤ B) (hB : IsSelfAdjoint B) {p q q' : H}
    (hq : q ∈ deficiencySpace A (-Complex.I)) (hq' : q' ∈ deficiencySpace A (-Complex.I))
    (h1 : p + q ∈ B.domain) (h2 : p + q' ∈ B.domain) : q = q' := by
  have hr : q - q' ∈ deficiencySpace A (-Complex.I) := Submodule.sub_mem _ hq hq'
  have hrB : q - q' ∈ B.domain := by
    have := B.domain.sub_mem h1 h2
    rwa [add_sub_add_left_eq_sub] at this
  exact sub_eq_zero.mp (eq_zero_of_mem_deficiency_domain hA hAB hB (by simp) hr hrB)

section Partner

variable (hA : ClosedSymm A) (hAB : A ≤ B) (hB : IsSelfAdjoint B)
include hA hAB hB

/-- The partner map `p ↦ q` of a self-adjoint extension `B`. -/
noncomputable def partnerFun (p : deficiencySpace A Complex.I) : deficiencySpace A (-Complex.I) :=
  ⟨Classical.choose (exists_partner hA hAB hB p.2), (Classical.choose_spec (exists_partner hA hAB hB p.2)).1⟩

lemma partnerFun_spec (p : deficiencySpace A Complex.I) : (p : H) + (partnerFun hA hAB hB p : H) ∈ B.domain :=
  (Classical.choose_spec (exists_partner hA hAB hB p.2)).2

lemma partnerFun_eq {p : deficiencySpace A Complex.I} {q : deficiencySpace A (-Complex.I)}
    (h : (p : H) + (q : H) ∈ B.domain) : partnerFun hA hAB hB p = q :=
  Subtype.ext (partner_unique hA hAB hB (partnerFun hA hAB hB p).2 q.2 (partnerFun_spec hA hAB hB p) h)

/-- The partner map is linear. -/
noncomputable def partnerLin : deficiencySpace A Complex.I →ₗ[ℂ] deficiencySpace A (-Complex.I) where
  toFun := partnerFun hA hAB hB
  map_add' p p' := by
    refine partnerFun_eq hA hAB hB ?_
    have := B.domain.add_mem (partnerFun_spec hA hAB hB p) (partnerFun_spec hA hAB hB p')
    convert this using 1
    simp only [Submodule.coe_add]; abel
  map_smul' c p := by
    refine partnerFun_eq hA hAB hB ?_
    have := B.domain.smul_mem c (partnerFun_spec hA hAB hB p)
    convert this using 1
    simp [smul_add]

/-- The partner map preserves the norm: the boundary form of the symmetric `B` vanishes on `p + q`. -/
lemma norm_partnerFun (p : deficiencySpace A Complex.I) : ‖partnerFun hA hAB hB p‖ = ‖p‖ := by
  have hBA := le_adjoint_of_selfAdjoint_ext hA hAB hB
  set q := partnerFun hA hAB hB p
  have hv := partnerFun_spec hA hAB hB p
  let yB : B.domain := ⟨(p : H) + (q : H), hv⟩
  let y : (A†).domain := ⟨(p : H) + (q : H), hBA.1 hv⟩
  have hAy : (A† y : H) = B yB := (hBA.2 (x := yB) (y := y) rfl).symm
  have hb := boundary_form hA y y 0 0 p.2 q.2 p.2 q.2 (by simp [y]) (by simp [y])
  rw [hAy, sa_symm_apply hB yB yB, sub_self] at hb
  have h2 : (2 * Complex.I) ≠ 0 := by simp
  have h3 := sub_eq_zero.mp ((mul_eq_zero.mp hb.symm).resolve_left h2)
  rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h3
  have h4 : ‖(q : H)‖ ^ 2 = ‖(p : H)‖ ^ 2 := by exact_mod_cast h3
  have h5 := (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h4
  simpa using h5

lemma partnerFun_surjective : Function.Surjective (partnerFun hA hAB hB) := by
  intro q
  obtain ⟨p, hp, h⟩ := exists_partner' hA hAB hB q.2
  exact ⟨⟨p, hp⟩, partnerFun_eq hA hAB hB h⟩

/-- **The unitary of a self-adjoint extension**: `U_B : N_i → N_{-i}`, `p ↦` the `q` with `p + q ∈ D(B)`. -/
noncomputable def unitaryOfExt : deficiencySpace A Complex.I ≃ₗᵢ[ℂ] deficiencySpace A (-Complex.I) :=
  LinearIsometryEquiv.ofSurjective ⟨partnerLin hA hAB hB, norm_partnerFun hA hAB hB⟩
    (partnerFun_surjective hA hAB hB)

lemma unitaryOfExt_apply (p : deficiencySpace A Complex.I) :
    unitaryOfExt hA hAB hB p = partnerFun hA hAB hB p := rfl

end Partner

/-- **Every self-adjoint extension of `A` is an `A_U`**: `B = A_{U_B}`. -/
theorem eq_extU_of_selfAdjoint (hA : ClosedSymm A) (hAB : A ≤ B) (hB : IsSelfAdjoint B) :
    B = extU A (unitaryOfExt hA hAB hB) := by
  set U := unitaryOfExt hA hAB hB
  have hBA := le_adjoint_of_selfAdjoint_ext hA hAB hB
  have hle : extU A U ≤ B := by
    refine ⟨fun v hv => ?_, fun v w hvw => ?_⟩
    · obtain ⟨x, hx, p, rfl⟩ := mem_domU_iff.mp ((mem_extU_domain hA).mp hv)
      rw [add_assoc]
      exact B.domain.add_mem (hAB.1 hx) (partnerFun_spec hA hAB hB p)
    · rw [extU_apply]
      exact (hBA.2 (x := w) (y := ⟨(v : H), (Submodule.mem_inf.mp v.2).2⟩) hvw.symm).symm
  have hge : B ≤ extU A U := by
    have h := adjoint_antitone (dense_extU_domain hA) hle
    have h1 : B† = B := hB
    have h2 : (extU A U)† = extU A U := extU_isSelfAdjoint hA
    rwa [h1, h2] at h
  exact le_antisymm hge hle

/-- **Von Neumann's theorem, case `n₊ ≠ n₋`**: if `A` has a self-adjoint extension, its deficiency indices agree. -/
theorem deficiencyDim_eq_of_selfAdjoint_ext (hA : ClosedSymm A) (hAB : A ≤ B) (hB : IsSelfAdjoint B) :
    deficiencyDim A Complex.I = deficiencyDim A (-Complex.I) :=
  (unitaryOfExt hA hAB hB).toLinearEquiv.rank_eq

end Lightlike.OperatorAlgebras
