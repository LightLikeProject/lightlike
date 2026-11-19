import Lightlike.Canonical.HolonomyALGraph
import Lightlike.Canonical.HolonomyAnalytic

/-!
# The refinement order of graphs of Ashtekar–Lewandowski

Along a path that is only piecewise `C¹`, the parallel transport is characterised by right derivatives: `U(a) = 1`,
`U` continuous on `[a, b]` and `d⁺U/dt = −A_a(p(t)) ṗ⁺^a(t) U` on `[a, b)` (`IsRightTransport`); it is unique
(`IsRightTransport.unique`). Along an edge of Ashtekar–Lewandowski (arXiv:gr-qc/0404018, footnote 17, p. 33) the
transport exists and ends at the holonomy, the product along the analytic pieces (`ALEdge.exists_isRightTransport`).
Hence the holonomy along an edge does not depend on the subdivision into pieces (`ALEdge.hol_eq_of_eqOn`), it is
unchanged under orientation-preserving reparametrisation (`ALEdge.isRightTransport_comp`, with the right derivatives of
the reparametrisation from `ALEdge.rightDeriv_of_comp`), and the reversed edge has the inverse holonomy
(`ALEdge.hol_rev`, (4.37)).

The order (`ALGraph.Le`, p. 27): `α ≤ α'` when every edge of `α` is a composite `e'₁ ∘ ⋯ ∘ e'_K` of edges of `α'`, up to
orientation-preserving reparametrisation and in either orientation. It is reflexive (`ALGraph.le_refl`), and the
holonomy along each edge of `α` is the ordered product of the holonomies along the edges of `α'` that compose it or of
their inverses (`ALGraph.hol_of_le`).
-/

open Matrix Set Filter
open scoped ContDiff Topology NNReal

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

noncomputable section

namespace Lightlike.Canonical

variable {n : ℕ}

/-- The **right transport coefficient** `A_a(p(t)) ṗ⁺^a(t)` of a path, with the right derivative `ṗ⁺`. -/
def rCoeff (A : MatConn n) (p : ℝ → Fin 3 → ℝ) (t : ℝ) : Matrix (Fin n) (Fin n) ℂ :=
  ∑ a, ((derivWithin p (Ici t) t a : ℝ) : ℂ) • A (p t) a

/-- `U` is the **parallel transport along `p` on `[a, b]`**, in the sense of right derivatives. -/
def IsRightTransport (A : MatConn n) (p : ℝ → Fin 3 → ℝ) (a b : ℝ) (U : ℝ → Matrix (Fin n) (Fin n) ℂ) : Prop :=
  U a = 1 ∧ ContinuousOn U (Icc a b) ∧ ∀ τ ∈ Ico a b, HasDerivWithinAt U (-(rCoeff A p τ * U τ)) (Ici τ) τ

/-- **Uniqueness** for right derivatives: two continuous solutions of `d⁺U/dt = −M(t) U` on `[a, b]` with the same value
at `a` agree, for `M` bounded on `[a, b)`. -/
lemma eqOn_of_right_deriv {M : ℝ → Matrix (Fin n) (Fin n) ℂ} {a b C : ℝ} (hC : ∀ τ ∈ Ico a b, ‖M τ‖ ≤ C)
    {U V : ℝ → Matrix (Fin n) (Fin n) ℂ} (hU : ContinuousOn U (Icc a b))
    (hU' : ∀ τ ∈ Ico a b, HasDerivWithinAt U (-(M τ * U τ)) (Ici τ) τ) (hV : ContinuousOn V (Icc a b))
    (hV' : ∀ τ ∈ Ico a b, HasDerivWithinAt V (-(M τ * V τ)) (Ici τ) τ) (h0 : U a = V a) : EqOn U V (Icc a b) :=
  ODE_solution_unique_of_mem_Icc_right (v := fun τ U => -(M τ * U)) (s := fun _ => univ) (K := C.toNNReal)
    (fun τ hτ => by
      refine ((lipschitzWith_neg_mul (M τ)).weaken ?_).lipschitzOnWith
      rw [← NNReal.coe_le_coe, coe_nnnorm]
      exact (hC τ hτ).trans (Real.le_coe_toNNReal C))
    hU hU' (fun _ _ => mem_univ _) hV hV' (fun _ _ => mem_univ _) h0

/-- **Uniqueness of the transport along a path**, for a right coefficient bounded on `[a, b)`. -/
lemma IsRightTransport.unique {A : MatConn n} {p : ℝ → Fin 3 → ℝ} {a b C : ℝ}
    (hC : ∀ τ ∈ Ico a b, ‖rCoeff A p τ‖ ≤ C) {U V : ℝ → Matrix (Fin n) (Fin n) ℂ}
    (hU : IsRightTransport A p a b U) (hV : IsRightTransport A p a b V) : EqOn U V (Icc a b) :=
  eqOn_of_right_deriv hC hU.2.1 hU.2.2 hV.2.1 hV.2.2 (hU.1.trans hV.1.symm)

/-- The right coefficient depends only on the path to the right: on `[τ, b]`. -/
lemma rCoeff_congr {A : MatConn n} {p q : ℝ → Fin 3 → ℝ} {τ b : ℝ} (hτ : τ < b) (h : EqOn p q (Icc τ b)) :
    rCoeff A p τ = rCoeff A q τ := by
  have hmem : Icc τ b ∈ 𝓝[Ici τ] τ := Icc_mem_nhdsGE hτ
  have hev : p =ᶠ[𝓝[Ici τ] τ] q := Filter.mem_of_superset hmem fun x hx => h hx
  have hd : derivWithin p (Ici τ) τ = derivWithin q (Ici τ) τ :=
    hev.derivWithin_eq (h ⟨le_rfl, hτ.le⟩)
  simp only [rCoeff, hd, h ⟨le_rfl, hτ.le⟩]

/-- On an interval where a path agrees with a `C¹` arc, its right coefficient is the transport coefficient of the arc. -/
lemma rCoeff_eq_transportCoeff {A : MatConn n} {p g : ℝ → Fin 3 → ℝ} (hg : ContDiff ℝ 1 g) {τ b : ℝ} (hτ : τ < b)
    (h : EqOn p g (Icc τ b)) : rCoeff A p τ = transportCoeff A g τ := by
  rw [rCoeff_congr hτ h]
  have hd : derivWithin g (Ici τ) τ = deriv g τ :=
    ((hg.differentiable one_ne_zero) τ).derivWithin (uniqueDiffWithinAt_Ici τ)
  simp only [rCoeff, transportCoeff, hd]


namespace ALEdge

variable (E : ALEdge)

/-- The holonomy of the first `σ` pieces. -/
def partialHol (A : MatConn n) (σ : ℕ) : Matrix (Fin n) (Fin n) ℂ :=
  ((List.ofFn fun j => (E.piece j).hol A).take σ).reverse.prod

/-- One more piece. -/
lemma partialHol_succ (A : MatConn n) (j : Fin E.k) :
    E.partialHol A (j.val + 1) = (E.piece j).hol A * E.partialHol A j.val := by
  simp only [partialHol]
  rw [List.take_add_one, List.getElem?_ofFn]
  simp [List.reverse_append, List.prod_cons, j.2]

/-- All pieces. -/
lemma partialHol_k (A : MatConn n) : E.partialHol A E.k = E.hol A := by
  rw [partialHol, List.take_of_length_le (by simp)]
  rfl

/-- The subdivision point with a natural-number index `σ ≤ k`. -/
def τn (σ : ℕ) (hσ : σ ≤ E.k) : ℝ := E.τ ⟨σ, Nat.lt_succ_of_le hσ⟩

/-- **The transport along an edge, up to the `σ`-th subdivision point**, in the sense of right derivatives, ends at the
holonomy of the first `σ` pieces. -/
theorem exists_isRightTransport_partial {A : MatConn n} (hA : ∀ a, Continuous fun x => A x a) :
    ∀ σ (hσ : σ ≤ E.k), ∃ W, IsRightTransport A E.path E.t₀ (E.τn σ hσ) W ∧ W (E.τn σ hσ) = E.partialHol A σ
  | 0, _ => ⟨fun _ => 1, ⟨rfl, continuousOn_const, fun τ hτ => by
      exfalso; exact (lt_irrefl _ (hτ.1.trans_lt hτ.2))⟩, by simp [partialHol]⟩
  | σ + 1, hσ => by
    obtain ⟨W, ⟨hW0, hWc, hWd⟩, hWe⟩ := exists_isRightTransport_partial hA σ (Nat.le_of_succ_le hσ)
    set j : Fin E.k := ⟨σ, hσ⟩ with hj
    have hjc : E.τ j.castSucc = E.τn σ (Nat.le_of_succ_le hσ) := rfl
    have hjs : E.τ j.succ = E.τn (σ + 1) hσ := rfl
    set T := E.τn σ (Nat.le_of_succ_le hσ) with hT
    set T' := E.τn (σ + 1) hσ with hT'
    have hTT' : T < T' := E.τ_mono (Fin.lt_def.2 (by simp))
    have ht₀T : E.t₀ ≤ T := E.τ_mono.monotone (Fin.le_def.2 (by simp))
    obtain ⟨h1, h2⟩ := hasDerivWithinAt_transport hA (E.arc_smooth j) hTT'.le
    set V : ℝ → Matrix (Fin n) (Fin n) ℂ := fun t => transport A (E.arc j) T t * W T with hV
    have hVd : ∀ τ ∈ Ico T T', HasDerivWithinAt V (-(rCoeff A E.path τ * V τ)) (Ici τ) τ := fun τ hτ => by
      have hd := ((h2 τ (Ico_subset_Icc_self hτ)).mul_const (W T)).mono_of_mem_nhdsWithin
        (Filter.mem_of_superset (Icc_mem_nhdsGE hτ.2) (Icc_subset_Icc_left hτ.1))
      have hr : rCoeff A E.path τ = transportCoeff A (E.arc j) τ :=
        rCoeff_eq_transportCoeff (E.arc_smooth j) hτ.2 fun x hx =>
          E.arc_eq j ⟨hjc ▸ hτ.1.trans hx.1, hjs ▸ hx.2⟩
      refine hd.congr_deriv ?_
      rw [hr, Matrix.neg_mul, Matrix.mul_assoc]
    have hVc : ContinuousOn V (Icc T T') := fun τ hτ => ((h2 τ hτ).mul_const (W T)).continuousWithinAt
    have hVT : V T = W T := by simp [hV, h1]
    set Z : ℝ → Matrix (Fin n) (Fin n) ℂ := fun t => if t ≤ T then W t else V t with hZ
    have hZW : ∀ t, t ≤ T → Z t = W t := fun t ht => by simp [hZ, ht]
    have hZV : ∀ t, T ≤ t → Z t = V t := fun t ht => by
      rcases eq_or_lt_of_le ht with h | h
      · subst h; simp [hZ, hVT]
      · simp [hZ, not_le.2 h]
    refine ⟨Z, ⟨by rw [hZW _ ht₀T, hW0], ?_, ?_⟩, ?_⟩
    · rw [← Icc_union_Icc_eq_Icc ht₀T hTT'.le]
      exact ContinuousOn.union_of_isClosed (hWc.congr fun t ht => hZW t ht.2)
        (hVc.congr fun t ht => hZV t ht.1) isClosed_Icc isClosed_Icc
    · intro τ hτ
      rcases lt_or_ge τ T with h | h
      · have hev : Z =ᶠ[𝓝[Ici τ] τ] W :=
          Filter.mem_of_superset (Icc_mem_nhdsGE h) fun t ht => hZW t ht.2
        rw [hZW τ h.le]
        exact (hWd τ ⟨hτ.1, h⟩).congr_of_eventuallyEq hev (hZW τ h.le)
      · have hev : Z =ᶠ[𝓝[Ici τ] τ] V :=
          Filter.mem_of_superset (Icc_mem_nhdsGE hτ.2) fun t ht => hZV t (h.trans ht.1)
        rw [hZV τ h]
        exact (hVd τ ⟨h, hτ.2⟩).congr_of_eventuallyEq hev (hZV τ h)
    · rw [hZV T' hTT'.le, hV, hWe]
      exact (E.partialHol_succ A j).symm

end ALEdge


namespace ALEdge

variable (E : ALEdge)

/-- **The transport along an edge**, in the sense of right derivatives, ends at the holonomy along the edge. -/
theorem exists_isRightTransport {A : MatConn n} (hA : ∀ a, Continuous fun x => A x a) :
    ∃ W, IsRightTransport A E.path E.t₀ E.t₁ W ∧ W E.t₁ = E.hol A := by
  obtain ⟨W, hW, hWe⟩ := E.exists_isRightTransport_partial hA E.k le_rfl
  exact ⟨W, hW, by rw [← E.partialHol_k A]; exact hWe⟩

/-- Every parameter of `[t₀, t₁)` lies in a piece `[τ_{j−1}, τ_j)`. -/
lemma exists_piece {τ : ℝ} (hτ : τ ∈ Ico E.t₀ E.t₁) : ∃ j : Fin E.k, τ ∈ Ico (E.τ j.castSucc) (E.τ j.succ) := by
  classical
  set P : ℕ → Prop := fun σ => ∃ h : σ ≤ E.k, E.τn σ h ≤ τ with hP
  set σ₀ := Nat.findGreatest P E.k with hσ₀
  have hP0 : P 0 := ⟨Nat.zero_le _, hτ.1⟩
  have hspec : P σ₀ := Nat.findGreatest_spec (P := P) (Nat.zero_le _) hP0
  obtain ⟨hle, hτσ⟩ := hspec
  have hlt : σ₀ < E.k := by
    rcases eq_or_lt_of_le hle with h | h
    · exfalso
      have : E.τn σ₀ hle = E.t₁ := by simp only [τn, h]; rfl
      rw [this] at hτσ
      exact lt_irrefl _ (hτσ.trans_lt hτ.2)
    · exact h
  refine ⟨⟨σ₀, hlt⟩, hτσ, ?_⟩
  by_contra hcon
  push Not at hcon
  have : P (σ₀ + 1) := ⟨hlt, hcon⟩
  exact Nat.findGreatest_is_greatest (Nat.lt_succ_self σ₀) hlt this

/-- **The right coefficient along an edge is bounded.** -/
theorem exists_bound_rCoeff {A : MatConn n} (hA : ∀ a, Continuous fun x => A x a) :
    ∃ C, ∀ τ ∈ Ico E.t₀ E.t₁, ‖rCoeff A E.path τ‖ ≤ C := by
  have hb : ∀ j : Fin E.k, ∃ C, ∀ τ ∈ Icc (E.τ j.castSucc) (E.τ j.succ), ‖transportCoeff A (E.arc j) τ‖ ≤ C :=
    fun j => isCompact_Icc.exists_bound_of_continuousOn (continuous_transportCoeff hA (E.arc_smooth j)).continuousOn
  choose C hC using hb
  refine ⟨∑ j, |C j|, fun τ hτ => ?_⟩
  obtain ⟨j, hj⟩ := E.exists_piece hτ
  rw [rCoeff_eq_transportCoeff (E.arc_smooth j) hj.2 fun x hx => E.arc_eq j ⟨hj.1.trans hx.1, hx.2⟩]
  calc _ ≤ C j := hC j τ (Ico_subset_Icc_self hj)
    _ ≤ |C j| := le_abs_self _
    _ ≤ ∑ j, |C j| := Finset.single_le_sum (f := fun j => |C j|) (fun _ _ => abs_nonneg _) (Finset.mem_univ j)

/-- **The holonomy along an edge does not depend on the subdivision**: two edges with the same path on the same parameter
interval have the same holonomy. -/
theorem hol_eq_of_eqOn {A : MatConn n} (hA : ∀ a, Continuous fun x => A x a) {E' : ALEdge} (h₀ : E.t₀ = E'.t₀)
    (h₁ : E.t₁ = E'.t₁) (h : EqOn E.path E'.path (Icc E.t₀ E.t₁)) : E.hol A = E'.hol A := by
  obtain ⟨W, hW, hWe⟩ := E.exists_isRightTransport hA
  obtain ⟨W', hW', hW'e⟩ := E'.exists_isRightTransport hA
  obtain ⟨C, hC⟩ := E.exists_bound_rCoeff hA
  rw [← h₀, ← h₁] at hW'
  have hW'' : IsRightTransport A E.path E.t₀ E.t₁ W' := by
    refine ⟨hW'.1, hW'.2.1, fun τ hτ => ?_⟩
    rw [rCoeff_congr (q := E'.path) hτ.2 fun x hx => h ⟨hτ.1.trans hx.1, hx.2⟩]
    exact hW'.2.2 τ hτ
  rw [← hWe, ← hW'e, ← h₁]
  exact IsRightTransport.unique hC hW hW'' ⟨E.t₀_lt_t₁.le, le_rfl⟩

end ALEdge


namespace ALEdge

variable (E : ALEdge)

/-- The path of an edge has a right derivative at every parameter of `[t₀, t₁)`. -/
lemma hasDerivWithinAt_path_Ici {τ : ℝ} (hτ : τ ∈ Ico E.t₀ E.t₁) :
    HasDerivWithinAt E.path (derivWithin E.path (Ici τ) τ) (Ici τ) τ := by
  obtain ⟨j, hj⟩ := E.exists_piece hτ
  have hev : E.path =ᶠ[𝓝[Ici τ] τ] E.arc j :=
    Filter.mem_of_superset (Icc_mem_nhdsGE hj.2) fun x hx => E.arc_eq j ⟨hj.1.trans hx.1, hx.2⟩
  have hd : HasDerivWithinAt E.path (deriv (E.arc j) τ) (Ici τ) τ :=
    (((E.arc_smooth j).differentiable one_ne_zero) τ).hasDerivAt.hasDerivWithinAt.congr_of_eventuallyEq hev
      (E.arc_eq j (Ico_subset_Icc_self hj))
  rwa [hd.derivWithin (uniqueDiffWithinAt_Ici τ)]

/-- **Invariance under orientation-preserving reparametrisation**: if `p = E' ∘ φ` on `[a, b]`, for a continuous map `φ`,
monotone on `[a, b]` with right derivatives `φ'⁺` there, taking `[a, b]` onto the parameter interval of `E'`, the
transport along `p` on `[a, b]` ends at the holonomy along `E'`. -/
theorem isRightTransport_comp {A : MatConn n} (hA : ∀ a, Continuous fun x => A x a) {E' : ALEdge}
    {p : ℝ → Fin 3 → ℝ} {φ φ' : ℝ → ℝ} {a b : ℝ} (hab : a < b) (hφc : ContinuousOn φ (Icc a b))
    (hφr : ∀ s ∈ Ico a b, HasDerivWithinAt φ (φ' s) (Ici s) s) (hmono : MonotoneOn φ (Icc a b))
    (ha : φ a = E'.t₀) (hb : φ b = E'.t₁) (hp : EqOn p (E'.path ∘ φ) (Icc a b)) :
    ∃ U, IsRightTransport A p a b U ∧ U b = E'.hol A := by
  obtain ⟨W, ⟨hW0, hWc, hWd⟩, hWe⟩ := E'.exists_isRightTransport hA
  have hmaps : MapsTo φ (Icc a b) (Icc E'.t₀ E'.t₁) := fun x hx =>
    ⟨ha ▸ hmono ⟨le_rfl, hab.le⟩ hx hx.1, hb ▸ hmono hx ⟨hab.le, le_rfl⟩ hx.2⟩
  refine ⟨W ∘ φ, ⟨by simp [ha, hW0], hWc.comp hφc hmaps, fun s hs => ?_⟩, by simp [hb, hWe]⟩
  have hsI : s ∈ Icc a b := Ico_subset_Icc_self hs
  have hmaps' : MapsTo φ (Icc s b) (Ici (φ s)) := fun x hx =>
    hmono hsI ⟨hsI.1.trans hx.1, hx.2⟩ hx.1
  have hnhds : Icc s b ∈ 𝓝[Ici s] s := Icc_mem_nhdsGE hs.2
  have hφd : HasDerivWithinAt φ (φ' s) (Icc s b) s := (hφr s hs).mono Icc_subset_Ici_self
  have hpev : p =ᶠ[𝓝[Ici s] s] E'.path ∘ φ :=
    Filter.mem_of_superset hnhds fun x hx => hp ⟨hsI.1.trans hx.1, hx.2⟩
  rcases lt_or_eq_of_le (hmaps hsI).2 with hlt | heq
  · have hφs : φ s ∈ Ico E'.t₀ E'.t₁ := ⟨(hmaps hsI).1, hlt⟩
    -- the right derivative of `p`
    have hpd : HasDerivWithinAt p (φ' s • derivWithin E'.path (Ici (φ s)) (φ s)) (Ici s) s :=
      (((E'.hasDerivWithinAt_path_Ici hφs).scomp s hφd hmaps').mono_of_mem_nhdsWithin hnhds).congr_of_eventuallyEq
        hpev (hp hsI)
    have hr : rCoeff A p s = ((φ' s : ℝ) : ℂ) • rCoeff A E'.path (φ s) := by
      simp only [rCoeff, hpd.derivWithin (uniqueDiffWithinAt_Ici s), hp hsI, Function.comp_apply, Pi.smul_apply,
        smul_eq_mul, Complex.ofReal_mul, Finset.smul_sum, smul_smul]
    refine (((hWd (φ s) hφs).scomp s hφd hmaps').mono_of_mem_nhdsWithin hnhds).congr_deriv ?_
    rw [hr, Function.comp_apply, real_smul_neg_mul]
  · -- `φ` has reached the end: `φ` and `p` are constant on `[s, b]`
    have hconst : ∀ x ∈ Icc s b, φ x = E'.t₁ := fun x hx =>
      le_antisymm (hmaps ⟨hsI.1.trans hx.1, hx.2⟩).2 (heq ▸ hmono hsI ⟨hsI.1.trans hx.1, hx.2⟩ hx.1)
    have hUev : W ∘ φ =ᶠ[𝓝[Ici s] s] fun _ => W E'.t₁ :=
      Filter.mem_of_superset hnhds fun x hx => by simp [hconst x hx]
    have hpev' : p =ᶠ[𝓝[Ici s] s] fun _ => E'.path E'.t₁ :=
      hpev.trans (Filter.mem_of_superset hnhds fun x hx => by simp [hconst x hx])
    have hpd : HasDerivWithinAt p 0 (Ici s) s :=
      (hasDerivWithinAt_const s _ _).congr_of_eventuallyEq hpev' (by rw [hp hsI]; simp [heq])
    have hr : rCoeff A p s = 0 := by
      simp [rCoeff, hpd.derivWithin (uniqueDiffWithinAt_Ici s)]
    refine ((hasDerivWithinAt_const s _ (W E'.t₁)).congr_of_eventuallyEq hUev (by simp [heq])).congr_deriv ?_
    rw [hr, Matrix.zero_mul, neg_zero]

end ALEdge


/-- Reindexing a list by `Fin.rev` reverses it. -/
lemma ofFn_rev {β : Type*} : ∀ {k : ℕ} (f : Fin k → β), List.ofFn (fun j => f j.rev) = (List.ofFn f).reverse
  | 0, _ => rfl
  | k + 1, f => by
    rw [List.ofFn_succ, List.ofFn_succ', List.concat_eq_append, List.reverse_append]
    simp only [Fin.rev_zero, Fin.rev_succ, List.reverse_cons, List.reverse_nil, List.nil_append,
      List.singleton_append]
    rw [ofFn_rev (fun j => f j.castSucc)]

namespace ALEdge

variable (E : ALEdge)

/-- The **reversed edge** `e⁻¹`: the path run backwards on the same parameter interval. -/
def rev : ALEdge where
  path t := E.path (E.t₀ + E.t₁ - t)
  k := E.k
  k_pos := E.k_pos
  τ σ := E.t₀ + E.t₁ - E.τ σ.rev
  τ_mono a b hab := by
    have : E.τ b.rev < E.τ a.rev := E.τ_mono (Fin.rev_lt_rev.2 hab)
    linarith
  arc j t := E.arc j.rev (E.t₀ + E.t₁ - t)
  arc_smooth j := (E.arc_smooth j.rev).comp (contDiff_const.sub contDiff_id)
  arc_analytic j t ht := by
    have ht' : E.t₀ + E.t₁ - t ∈ Icc (E.τ j.rev.castSucc) (E.τ j.rev.succ) := by
      have h1 : E.t₀ + E.t₁ - E.τ j.castSucc.rev ≤ t := ht.1
      have h2 : t ≤ E.t₀ + E.t₁ - E.τ j.succ.rev := ht.2
      rw [Fin.rev_castSucc] at h1
      rw [Fin.rev_succ] at h2
      constructor <;> linarith
    obtain ⟨ha, hd⟩ := E.arc_analytic j.rev _ ht'
    refine ⟨ha.comp_of_eq (analyticAt_const.sub analyticAt_id) rfl, ?_⟩
    have : deriv (fun t => E.arc j.rev (E.t₀ + E.t₁ - t)) t = -deriv (E.arc j.rev) (E.t₀ + E.t₁ - t) :=
      deriv_comp_const_sub (f := E.arc j.rev) _ _
    rw [this, neg_ne_zero]
    exact hd
  arc_eq j t ht := by
    have ht' : E.t₀ + E.t₁ - t ∈ Icc (E.τ j.rev.castSucc) (E.τ j.rev.succ) := by
      have h1 : E.t₀ + E.t₁ - E.τ j.castSucc.rev ≤ t := ht.1
      have h2 : t ≤ E.t₀ + E.t₁ - E.τ j.succ.rev := ht.2
      rw [Fin.rev_castSucc] at h1
      rw [Fin.rev_succ] at h2
      constructor <;> linarith
    exact E.arc_eq j.rev ht'

/-- The reversed edge has the same parameter interval. -/
lemma rev_t₀ : E.rev.t₀ = E.t₀ := by
  show E.τ 0 + E.τ (Fin.last E.k) - E.τ (Fin.rev 0) = E.τ 0
  rw [Fin.rev_zero]; ring

/-- The reversed edge has the same parameter interval. -/
lemma rev_t₁ : E.rev.t₁ = E.t₁ := by
  show E.τ 0 + E.τ (Fin.last E.k) - E.τ (Fin.rev (Fin.last E.k)) = E.τ (Fin.last E.k)
  rw [Fin.rev_last]; ring

/-- **The holonomy of the reversed edge is the inverse** (Ashtekar–Lewandowski (4.37): `A(e⁻¹) = A(e)⁻¹`). -/
theorem hol_rev {A : MatConn n} (hA : ∀ a, Continuous fun x => A x a) : E.rev.hol A = (E.hol A)⁻¹ := by
  set c := E.t₀ + E.t₁ with hc
  have hpiece : ∀ j : Fin E.k, (E.rev.piece j).hol A = ((E.piece j.rev).hol A)⁻¹ := fun j => by
    set a := E.τ j.rev.castSucc
    set b := E.τ j.rev.succ
    have hab : a ≤ b := (E.piece_lt j.rev).le
    set ψ : ℝ → ℝ := fun t => t + (a + b - c) with hψ
    have hψc : ContDiff ℝ 1 ψ := contDiff_id.add contDiff_const
    have hpath : (E.rev.piece j).path = revPath (E.arc j.rev) a b ∘ ψ := funext fun t => by
      simp only [piece, rev, revPath, Function.comp_apply, hψ]; congr 1; ring
    have h0 : (E.rev.piece j).t₀ = c - b := by
      show E.t₀ + E.t₁ - E.τ j.castSucc.rev = c - b
      rw [Fin.rev_castSucc]
    have h1 : (E.rev.piece j).t₁ = c - a := by
      show E.t₀ + E.t₁ - E.τ j.succ.rev = c - a
      rw [Fin.rev_succ]
    have hψ0 : ψ (c - b) = a := by simp only [hψ]; ring
    have hψ1 : ψ (c - a) = b := by simp only [hψ]; ring
    have he : ContDiff ℝ 1 (revPath (E.arc j.rev) a b) :=
      (E.arc_smooth j.rev).comp (contDiff_const.sub contDiff_id)
    rw [Edge.hol, hpath, h0, h1, holonomy_comp_reparam (e := revPath (E.arc j.rev) a b) hA he hψc (by linarith)
      (fun x _ y _ hxy => by simp only [hψ]; linarith), hψ0, hψ1, holonomy_revPath hA (E.arc_smooth _) hab]
    rfl
  rw [hol, hol]
  show (List.ofFn fun j : Fin E.k => (E.rev.piece j).hol A).reverse.prod = _
  simp only [hpiece]
  rw [ofFn_rev (fun j => ((E.piece j).hol A)⁻¹), List.reverse_reverse, PwPath.inv_reverse_prod, List.map_ofFn]
  rfl

end ALEdge


namespace ALEdge

/-- An edge with a chosen orientation: the edge itself (`true`) or its reverse (`false`). -/
def orient (E : ALEdge) : Bool → ALEdge
  | true => E
  | false => E.rev

/-- The holonomy of an oriented edge: `A(e)` or `A(e)⁻¹`. -/
lemma hol_orient {A : MatConn n} (hA : ∀ a, Continuous fun x => A x a) (E : ALEdge) (b : Bool) :
    (E.orient b).hol A = if b then E.hol A else (E.hol A)⁻¹ := by
  cases b
  · exact E.hol_rev hA
  · rfl

end ALEdge


namespace ALEdge

/-- **Reparametrisations between edges have right derivatives.** If `p = E' ∘ φ` on `[a, b]` for a continuous map `φ`,
monotone on `[a, b]`, into the parameter interval of `E'`, and `p` has right derivatives, then so has `φ`: near each point
`φ` is the analytic local inverse of a coordinate of an analytic arc of `E'`, composed with that coordinate of `p`. -/
lemma rightDeriv_of_comp {E' : ALEdge} {p : ℝ → Fin 3 → ℝ} {φ : ℝ → ℝ} {a b : ℝ}
    (hφc : ContinuousOn φ (Icc a b)) (hmono : MonotoneOn φ (Icc a b)) (hmaps : MapsTo φ (Icc a b) (Icc E'.t₀ E'.t₁))
    (hp : EqOn p (E'.path ∘ φ) (Icc a b)) (hpr : ∀ s ∈ Ico a b, ∃ d, HasDerivWithinAt p d (Ici s) s) :
    ∀ s ∈ Ico a b, ∃ d, HasDerivWithinAt φ d (Ici s) s := by
  intro s hs
  have hsI : s ∈ Icc a b := Ico_subset_Icc_self hs
  have hnhds : Icc s b ∈ 𝓝[Ici s] s := Icc_mem_nhdsGE hs.2
  have hφt : Tendsto φ (𝓝[Ici s] s) (𝓝 (φ s)) := by
    have h1 : ContinuousWithinAt φ (Icc s b) s := (hφc s hsI).mono (Icc_subset_Icc_left hs.1)
    have h2 : 𝓝[Ici s] s ≤ 𝓝[Icc s b] s := by
      rw [nhdsWithin_le_iff]; exact Filter.mem_of_superset hnhds fun x hx => hx
    exact h1.tendsto.mono_left h2
  rcases lt_or_eq_of_le (hmaps hsI).2 with hlt | heq
  · obtain ⟨j, hj⟩ := E'.exists_piece ⟨(hmaps hsI).1, hlt⟩
    obtain ⟨ha, hd⟩ := E'.arc_analytic j (φ s) (Ico_subset_Icc_self hj)
    have hfd : ∀ k, DifferentiableAt ℝ (fun t => E'.arc j t k) (φ s) := fun k =>
      (analyticAt_pi_iff.1 ha k).differentiableAt
    obtain ⟨k, hk⟩ : ∃ k, deriv (fun t => E'.arc j t k) (φ s) ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hd (by rw [deriv_pi hfd]; exact funext hcon)
    have hstrict := (analyticAt_pi_iff.1 ha k).hasStrictDerivAt
    set g := hstrict.localInverse _ _ _ hk
    have hleft : ∀ᶠ t in 𝓝 (φ s), g (E'.arc j t k) = t := hstrict.eventually_left_inverse hk
    have hgd : HasDerivAt g (deriv (fun t => E'.arc j t k) (φ s))⁻¹ (E'.arc j (φ s) k) :=
      (hstrict.to_localInverse hk).hasDerivAt
    obtain ⟨d, hpd⟩ := hpr s hs
    have hpk : HasDerivWithinAt (fun x => p x k) (d k) (Ici s) s := hasDerivWithinAt_pi.1 hpd k
    have hps : p s k = E'.arc j (φ s) k := by
      rw [hp hsI, Function.comp_apply, E'.arc_eq j (Ico_subset_Icc_self hj)]
    -- `φ = g ∘ p_k` to the right of `s`
    have hev : φ =ᶠ[𝓝[Ici s] s] fun x => g (p x k) := by
      have h1 : ∀ᶠ x in 𝓝[Ici s] s, φ x < E'.τ j.succ := hφt.eventually (Iio_mem_nhds hj.2)
      have h2 : ∀ᶠ x in 𝓝[Ici s] s, g (E'.arc j (φ x) k) = φ x := hφt.eventually hleft
      filter_upwards [h1, h2, hnhds] with x hx1 hx2 hx3
      have hxI : x ∈ Icc a b := ⟨hsI.1.trans hx3.1, hx3.2⟩
      have hφx : φ x ∈ Icc (E'.τ j.castSucc) (E'.τ j.succ) :=
        ⟨hj.1.trans (hmono hsI hxI hx3.1), hx1.le⟩
      rw [hp hxI, Function.comp_apply, E'.arc_eq j hφx]
      exact hx2.symm
    refine ⟨_, (hps ▸ hgd).comp_hasDerivWithinAt s hpk |>.congr_of_eventuallyEq hev ?_⟩
    show φ s = g (p s k)
    rw [hps]; exact hleft.self_of_nhds.symm
  · refine ⟨0, (hasDerivWithinAt_const s _ (φ s)).congr_of_eventuallyEq ?_ rfl⟩
    refine Filter.mem_of_superset hnhds fun x hx => ?_
    have hxI : x ∈ Icc a b := ⟨hsI.1.trans hx.1, hx.2⟩
    have h1 := (hmaps hxI).2
    have h2 := hmono hsI hxI hx.1
    show φ x = φ s
    exact le_antisymm (by linarith) h2

end ALEdge

namespace ALGraph

/-- **The refinement order** (Ashtekar–Lewandowski, p. 27): `α ≤ α'` when every edge `e` of `α` can be written as
`e = e'₁ ∘ ⋯ ∘ e'_K` with edges `e'_l` of `α'` (in either orientation): the parameter interval of `e` splits at
`s₀ < s₁ < ⋯ < s_K` and on `[s_{l−1}, s_l]` the edge is `e'_l ∘ φ_l` for a continuous map `φ_l`, monotone there, onto
the parameter interval of `e'_l` (an orientation-preserving reparametrisation; the edges are sub-manifolds, footnote 13,
whose orientation is an arbitrary choice, p. 28). -/
def Le (α α' : ALGraph) : Prop :=
  ∀ i, ∃ (K : ℕ) (s : Fin (K + 1) → ℝ) (c : Fin K → Fin α'.m × Bool), StrictMono s ∧ s 0 = (α.edge i).t₀ ∧
    s (Fin.last K) = (α.edge i).t₁ ∧ ∀ l : Fin K, ∃ φ : ℝ → ℝ, ContinuousOn φ (Icc (s l.castSucc) (s l.succ)) ∧
      MonotoneOn φ (Icc (s l.castSucc) (s l.succ)) ∧ φ (s l.castSucc) = ((α'.edge (c l).1).orient (c l).2).t₀ ∧
      φ (s l.succ) = ((α'.edge (c l).1).orient (c l).2).t₁ ∧
      EqOn (α.edge i).path (((α'.edge (c l).1).orient (c l).2).path ∘ φ) (Icc (s l.castSucc) (s l.succ))

/-- **The order is reflexive.** -/
theorem le_refl (α : ALGraph) : α.Le α := fun i => by
  refine ⟨1, ![(α.edge i).t₀, (α.edge i).t₁], fun _ => (i, true), ?_, rfl, rfl, fun l => ?_⟩
  · intro a b hab
    fin_cases a <;> fin_cases b <;> simp_all [(α.edge i).t₀_lt_t₁]
  · fin_cases l
    exact ⟨id, continuousOn_id, monotoneOn_id, rfl, rfl, fun _ _ => rfl⟩

/-- **Holonomies under refinement**: if `α ≤ α'`, the holonomy along each edge of `α` is the ordered product of the
holonomies along the edges of `α'` that compose it, or of their inverses (so a function cylindrical over `α` is
cylindrical over `α'`, p. 35). -/
theorem hol_of_le {A : MatConn n} (hA : ∀ a, Continuous fun x => A x a) {α α' : ALGraph} (h : α.Le α')
    (i : Fin α.m) : ∃ (K : ℕ) (c : Fin K → Fin α'.m × Bool), (α.edge i).hol A =
      (List.ofFn fun l => if (c l).2 then (α'.edge (c l).1).hol A else ((α'.edge (c l).1).hol A)⁻¹).reverse.prod := by
  obtain ⟨K, s, c, hs, hs0, hsK, hφ⟩ := h i
  refine ⟨K, c, ?_⟩
  set e := α.edge i
  set f : Fin K → Matrix (Fin n) (Fin n) ℂ := fun l =>
    if (c l).2 then (α'.edge (c l).1).hol A else ((α'.edge (c l).1).hol A)⁻¹ with hf
  obtain ⟨W, ⟨hW0, hWc, hWd⟩, hWe⟩ := e.exists_isRightTransport hA
  obtain ⟨C, hC⟩ := e.exists_bound_rCoeff hA
  have hsub : ∀ l : Fin K, Icc (s l.castSucc) (s l.succ) ⊆ Icc e.t₀ e.t₁ := fun l =>
    Icc_subset_Icc (hs0 ▸ hs.monotone (Fin.zero_le _)) (hsK ▸ hs.monotone (Fin.le_last _))
  -- the transport across the `l`-th part
  have hstep : ∀ l : Fin K, W (s l.succ) = f l * W (s l.castSucc) := fun l => by
    obtain ⟨φ, hφc, hφm, hφ0, hφ1, hφe⟩ := hφ l
    have hlt : s l.castSucc < s l.succ := hs (Fin.castSucc_lt_succ)
    have hmaps : MapsTo φ (Icc (s l.castSucc) (s l.succ))
        (Icc ((α'.edge (c l).1).orient (c l).2).t₀ ((α'.edge (c l).1).orient (c l).2).t₁) := fun x hx =>
      ⟨hφ0 ▸ hφm ⟨le_rfl, hlt.le⟩ hx hx.1, hφ1 ▸ hφm hx ⟨hlt.le, le_rfl⟩ hx.2⟩
    have hφr := ALEdge.rightDeriv_of_comp hφc hφm hmaps hφe fun x hx =>
      ⟨_, e.hasDerivWithinAt_path_Ici ⟨(hsub l (Ico_subset_Icc_self hx)).1,
        lt_of_lt_of_le hx.2 (hsub l ⟨hlt.le, le_rfl⟩).2⟩⟩
    choose! φ' hφ' using hφr
    obtain ⟨U, ⟨hU0, hUc, hUd⟩, hUe⟩ := ALEdge.isRightTransport_comp hA hlt hφc hφ' hφm hφ0 hφ1 hφe
    have hV : ∀ τ ∈ Ico (s l.castSucc) (s l.succ),
        HasDerivWithinAt (fun σ => U σ * W (s l.castSucc)) (-(rCoeff A e.path τ * (U τ * W (s l.castSucc))))
          (Ici τ) τ := fun τ hτ => by
      have := (hUd τ hτ).mul_const (W (s l.castSucc))
      rwa [Matrix.neg_mul, Matrix.mul_assoc] at this
    have heq := eqOn_of_right_deriv (M := rCoeff A e.path) (C := C)
      (fun τ hτ => hC τ ⟨(hsub l (Ico_subset_Icc_self hτ)).1,
        lt_of_lt_of_le hτ.2 (hsub l ⟨hlt.le, le_rfl⟩).2⟩)
      (hWc.mono (hsub l))
      (fun τ hτ => hWd τ ⟨(hsub l (Ico_subset_Icc_self hτ)).1, lt_of_lt_of_le hτ.2 (hsub l ⟨hlt.le, le_rfl⟩).2⟩)
      (hUc.mul continuousOn_const) hV (by simp [hU0]) ⟨hlt.le, le_rfl⟩
    rw [heq, Pi.mul_apply, hUe, ALEdge.hol_orient hA]
  -- by induction on the parts
  have hind : ∀ l (hl : l ≤ K), W (s ⟨l, Nat.lt_succ_of_le hl⟩) = ((List.ofFn f).take l).reverse.prod := by
    intro l
    induction l with
    | zero => intro _; simp [show (⟨0, _⟩ : Fin (K + 1)) = 0 from rfl, hs0, hW0]
    | succ l ih =>
      intro hl
      have := hstep ⟨l, hl⟩
      simp only [Fin.succ_mk, Fin.castSucc_mk] at this
      rw [this, ih (Nat.le_of_succ_le hl), List.take_add_one, List.getElem?_ofFn,
        dite_eq_left (Nat.lt_of_succ_le hl)]
      simp only [Option.toList_some, List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
        List.singleton_append, List.prod_cons]
  have := hind K le_rfl
  rw [show (⟨K, Nat.lt_succ_self K⟩ : Fin (K + 1)) = Fin.last K from rfl, hsK, hWe,
    List.take_of_length_le (by simp)] at this
  exact this

end ALGraph

end Lightlike.Canonical
