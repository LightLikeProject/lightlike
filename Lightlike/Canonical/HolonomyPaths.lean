import Lightlike.Canonical.Holonomy

/-!
# Reparametrisation, invertibility and reversal of the holonomy

The holonomy along a path is unchanged under orientation-preserving reparametrisation (`holonomy_comp_reparam`); the
parallel transport is invertible (`transport_isUnit`); and the holonomy along the reversed path `e⁻¹` is the inverse
`A(e)⁻¹` (`holonomy_revPath`) (Ashtekar–Lewandowski, arXiv:gr-qc/0404018, p. 33, eq. (4.37) and the sentence before it).
-/

open Matrix Set
open scoped ContDiff NNReal

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

noncomputable section

namespace Lightlike.Canonical

variable {n : ℕ}

/-- The transport coefficient of a reparametrised path: `M_{e ∘ φ}(σ) = φ'(σ) M_e(φ(σ))`. -/
lemma transportCoeff_comp (A : MatConn n) {e : ℝ → Fin 3 → ℝ} (he : ContDiff ℝ 1 e) {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 1 φ) (σ : ℝ) :
    transportCoeff A (e ∘ φ) σ = ((deriv φ σ : ℝ) : ℂ) • transportCoeff A e (φ σ) := by
  have hd : deriv (e ∘ φ) σ = deriv φ σ • deriv e (φ σ) :=
    deriv.scomp σ ((he.differentiable one_ne_zero) (φ σ)) ((hφ.differentiable one_ne_zero) σ)
  simp only [transportCoeff, hd, Function.comp_apply, Finset.smul_sum, smul_smul, Pi.smul_apply, smul_eq_mul,
    Complex.ofReal_mul]

/-- `r • (−(M U)) = −((r : ℂ) • M * U)` for a real `r`. -/
lemma real_smul_neg_mul (r : ℝ) (M U : Matrix (Fin n) (Fin n) ℂ) :
    r • (-(M * U)) = -(((r : ℂ) • M) * U) := by
  ext i j
  simp only [Matrix.smul_apply, Matrix.neg_apply, Matrix.mul_apply, Complex.real_smul, smul_eq_mul]
  rw [mul_neg, Finset.mul_sum]
  exact congrArg Neg.neg (Finset.sum_congr rfl fun k _ => by ring)

/-- **Invariance under orientation-preserving reparametrisation** (Ashtekar–Lewandowski, p. 33: `A(e)` "is unchanged
under orientation-preserving re-parameterizations of `e`"): for a `C¹` map `φ` that is monotone on `[s₁, s₂]`, the
holonomy along `e ∘ φ` over `[s₁, s₂]` is the holonomy along `e` over `[φ s₁, φ s₂]`. -/
theorem holonomy_comp_reparam {A : MatConn n} (hA : ∀ a, Continuous fun x => A x a) {e : ℝ → Fin 3 → ℝ}
    (he : ContDiff ℝ 1 e) {φ : ℝ → ℝ} (hφ : ContDiff ℝ 1 φ) {s₁ s₂ : ℝ} (hs : s₁ ≤ s₂)
    (hmono : MonotoneOn φ (Icc s₁ s₂)) :
    holonomy A (e ∘ φ) s₁ s₂ = holonomy A e (φ s₁) (φ s₂) := by
  have ht : φ s₁ ≤ φ s₂ := hmono ⟨le_rfl, hs⟩ ⟨hs, le_rfl⟩ hs
  have hmaps : MapsTo φ (Icc s₁ s₂) (Icc (φ s₁) (φ s₂)) := fun σ hσ =>
    ⟨hmono ⟨le_rfl, hs⟩ hσ hσ.1, hmono hσ ⟨hs, le_rfl⟩ hσ.2⟩
  obtain ⟨h1, h2⟩ := hasDerivWithinAt_transport hA he ht
  have hsol : ∀ σ ∈ Icc s₁ s₂, HasDerivWithinAt (transport A e (φ s₁) ∘ φ)
      (-(transportCoeff A (e ∘ φ) σ * (transport A e (φ s₁) ∘ φ) σ)) (Icc s₁ s₂) σ := by
    intro σ hσ
    have hφd : HasDerivWithinAt φ (deriv φ σ) (Icc s₁ s₂) σ :=
      ((hφ.differentiable one_ne_zero) σ).hasDerivAt.hasDerivWithinAt
    refine ((h2 (φ σ) (hmaps hσ)).scomp σ hφd hmaps).congr_deriv ?_
    rw [transportCoeff_comp A he hφ, Function.comp_apply, real_smul_neg_mul]
  rw [holonomy, holonomy, transport_eq hA (he.comp hφ) hsol (by simpa using h1) s₂ ⟨hs, le_rfl⟩]
  rfl

/-- The right-hand side `Y ↦ Y M` is Lipschitz with constant `‖M‖`. -/
lemma lipschitzWith_mul_right (M : Matrix (Fin n) (Fin n) ℂ) :
    LipschitzWith ‖M‖₊ (fun Y : Matrix (Fin n) (Fin n) ℂ => Y * M) := by
  refine LipschitzWith.of_dist_le_mul fun Y Z => ?_
  rw [dist_eq_norm, dist_eq_norm, ← Matrix.sub_mul, coe_nnnorm, mul_comm]
  exact norm_mul_le (Y - Z) M

/-- **The parallel transport is invertible**: the solution of `Y' = Y A_a(e) ė^a`, `Y(s) = 1` is a left inverse. -/
theorem transport_isUnit {A : MatConn n} (hA : ∀ a, Continuous fun x => A x a) {e : ℝ → Fin 3 → ℝ}
    (he : ContDiff ℝ 1 e) {s t : ℝ} (hst : s ≤ t) : IsUnit (transport A e s t) := by
  have hM := continuous_transportCoeff hA he
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn (s := Icc s t) hM.continuousOn
  have hc : ∀ Y : Matrix (Fin n) (Fin n) ℂ, ContinuousOn (fun τ => Y * transportCoeff A e τ) (Icc s t) :=
    fun Y => (continuous_const.mul hM).continuousOn
  obtain ⟨Y, hY0, hY⟩ := Lightlike.ODE.exists_solution_Icc_of_lipschitz
    (f := fun τ Y => Y * transportCoeff A e τ) (K := C.toNNReal) hst (fun τ hτ => by
      refine (lipschitzWith_mul_right _).weaken ?_
      rw [← NNReal.coe_le_coe, coe_nnnorm]
      exact (hC τ hτ).trans (Real.le_coe_toNNReal C)) hc 1
  obtain ⟨h1, h2⟩ := hasDerivWithinAt_transport hA he hst
  have hD : ∀ τ ∈ Icc s t, HasDerivWithinAt (fun σ => Y σ * transport A e s σ) 0 (Icc s t) τ := fun τ hτ =>
    ((hY τ hτ).fun_mul (h2 τ hτ)).congr_deriv (by noncomm_ring)
  have h := eq_of_hasDerivWithinAt_zero hD t ⟨hst, le_rfl⟩
  rw [hY0, h1, Matrix.one_mul] at h
  rw [Matrix.isUnit_iff_isUnit_det]
  refine IsUnit.of_mul_eq_one (Y t).det ?_
  rw [mul_comm, ← Matrix.det_mul, h, Matrix.det_one]

/-- The **reversed path** `e⁻¹(t) = e(t₁ + t₂ − t)` of `e|[t₁, t₂]`. -/
def revPath (e : ℝ → Fin 3 → ℝ) (t₁ t₂ : ℝ) : ℝ → Fin 3 → ℝ := fun t => e (t₁ + t₂ - t)

/-- **The holonomy of the reversed path is the inverse** (Ashtekar–Lewandowski (4.37): `A(e⁻¹) = A(e)⁻¹`). -/
theorem holonomy_revPath {A : MatConn n} (hA : ∀ a, Continuous fun x => A x a) {e : ℝ → Fin 3 → ℝ}
    (he : ContDiff ℝ 1 e) {t₁ t₂ : ℝ} (h : t₁ ≤ t₂) :
    holonomy A (revPath e t₁ t₂) t₁ t₂ = (holonomy A e t₁ t₂)⁻¹ := by
  set r : ℝ → ℝ := fun σ => t₁ + t₂ - σ with hr
  have hrc : ContDiff ℝ 1 r := contDiff_const.sub contDiff_id
  have hrd : ∀ σ, HasDerivAt r (-1) σ := fun σ => by
    simpa using (hasDerivAt_id σ).const_sub (t₁ + t₂)
  have hrev : revPath e t₁ t₂ = e ∘ r := rfl
  have hmaps : MapsTo r (Icc t₁ t₂) (Icc t₁ t₂) := fun σ hσ => ⟨by simp [hr]; linarith [hσ.2],
    by simp [hr]; linarith [hσ.1]⟩
  obtain ⟨h1, h2⟩ := hasDerivWithinAt_transport hA he h
  have hu := transport_isUnit hA he h
  set U := transport A e t₁ with hU
  have hsol : ∀ σ ∈ Icc t₁ t₂, HasDerivWithinAt (fun σ => U (r σ) * (U t₂)⁻¹)
      (-(transportCoeff A (e ∘ r) σ * (U (r σ) * (U t₂)⁻¹))) (Icc t₁ t₂) σ := by
    intro σ hσ
    have hc := ((h2 (r σ) (hmaps hσ)).scomp σ (hrd σ).hasDerivWithinAt hmaps).mul_const (U t₂)⁻¹
    refine hc.congr_deriv ?_
    rw [transportCoeff_comp A he hrc, (hrd σ).deriv, real_smul_neg_mul, Matrix.neg_mul, Matrix.mul_assoc]
  have h0 : U (r t₁) * (U t₂)⁻¹ = 1 := by
    simp only [hr, add_sub_cancel_left]
    exact Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hu)
  rw [holonomy, holonomy, hrev, transport_eq hA (he.comp hrc) hsol h0 t₂ ⟨h, le_rfl⟩]
  simp only [hr, add_sub_cancel_right, ← hU, h1, Matrix.one_mul]

/-! ### Piecewise `C¹` paths and the composition law -/

/-- An **edge**: a `C¹` path on `ℝ` with a parameter interval `[t₀, t₁]`. -/
structure Edge where
  /-- The path. -/
  path : ℝ → Fin 3 → ℝ
  /-- The initial parameter. -/
  t₀ : ℝ
  /-- The final parameter. -/
  t₁ : ℝ
  /-- The parameter interval is not empty. -/
  le : t₀ ≤ t₁
  /-- The path is `C¹`. -/
  smooth : ContDiff ℝ 1 path

namespace Edge

/-- The source `e(t₀)` of an edge. -/
def source (e : Edge) : Fin 3 → ℝ := e.path e.t₀

/-- The target `e(t₁)` of an edge. -/
def target (e : Edge) : Fin 3 → ℝ := e.path e.t₁

/-- The **reversed edge** `e⁻¹`, on the same parameter interval. -/
def rev (e : Edge) : Edge where
  path := revPath e.path e.t₀ e.t₁
  t₀ := e.t₀
  t₁ := e.t₁
  le := e.le
  smooth := e.smooth.comp (contDiff_const.sub contDiff_id)

/-- The source of the reversed edge is the target. -/
lemma rev_source (e : Edge) : e.rev.source = e.target := by
  simp [rev, source, target, revPath]

/-- The target of the reversed edge is the source. -/
lemma rev_target (e : Edge) : e.rev.target = e.source := by
  simp [rev, source, target, revPath]

/-- The holonomy `A(e)` along an edge. -/
def hol (A : MatConn n) (e : Edge) : Matrix (Fin n) (Fin n) ℂ := holonomy A e.path e.t₀ e.t₁

/-- `A(e⁻¹) = A(e)⁻¹` for an edge. -/
lemma hol_rev {A : MatConn n} (hA : ∀ a, Continuous fun x => A x a) (e : Edge) : e.rev.hol A = (e.hol A)⁻¹ :=
  holonomy_revPath hA e.smooth e.le

/-- `A(e)` is invertible. -/
lemma isUnit_hol {A : MatConn n} (hA : ∀ a, Continuous fun x => A x a) (e : Edge) : IsUnit (e.hol A) :=
  transport_isUnit hA e.smooth e.le

/-- The first part `e|[t₀, m]` of an edge split at `m`. -/
def splitLeft (e : Edge) (m : ℝ) (hm : m ∈ Icc e.t₀ e.t₁) : Edge := ⟨e.path, e.t₀, m, hm.1, e.smooth⟩

/-- The second part `e|[m, t₁]` of an edge split at `m`. -/
def splitRight (e : Edge) (m : ℝ) (hm : m ∈ Icc e.t₀ e.t₁) : Edge := ⟨e.path, m, e.t₁, hm.2, e.smooth⟩

/-- **Subdivision**: splitting an edge at an interior parameter does not change the holonomy,
`A(e) = A(e|[m, t₁]) A(e|[t₀, m])`. -/
lemma hol_split {A : MatConn n} (hA : ∀ a, Continuous fun x => A x a) (e : Edge) (m : ℝ)
    (hm : m ∈ Icc e.t₀ e.t₁) : e.hol A = (e.splitRight m hm).hol A * (e.splitLeft m hm).hol A :=
  transport_trans hA e.smooth hm.1 hm.2

end Edge

/-- A **piecewise `C¹` path**: a list of edges, each starting where the previous one ends. -/
structure PwPath where
  /-- The pieces. -/
  pieces : List Edge
  /-- Each piece starts at the end of the previous one. -/
  chain : pieces.IsChain fun e f => e.target = f.source

namespace PwPath

/-- The **holonomy of a piecewise `C¹` path** `e_k ∘ ⋯ ∘ e_1`: the product `A(e_k) ⋯ A(e_1)`. -/
def hol (A : MatConn n) (p : PwPath) : Matrix (Fin n) (Fin n) ℂ := (p.pieces.map (Edge.hol A)).reverse.prod

/-- The **composite** `q ∘ p` of two piecewise paths, `q` starting where `p` ends. -/
def trans (p q : PwPath) (h : ∀ e ∈ p.pieces.getLast?, ∀ f ∈ q.pieces.head?, e.target = f.source) : PwPath :=
  ⟨p.pieces ++ q.pieces, p.chain.append q.chain h⟩

/-- **The composition law** (Ashtekar–Lewandowski (4.37)): `A(q ∘ p) = A(q) A(p)`. -/
theorem hol_trans (A : MatConn n) (p q : PwPath)
    (h : ∀ e ∈ p.pieces.getLast?, ∀ f ∈ q.pieces.head?, e.target = f.source) :
    (p.trans q h).hol A = q.hol A * p.hol A := by
  simp [hol, trans, List.map_append, List.reverse_append, List.prod_append]

/-- The piecewise path of one edge. -/
def ofEdge (e : Edge) : PwPath := ⟨[e], List.isChain_singleton e⟩

/-- The holonomy of a one-edge path is the holonomy of the edge. -/
lemma hol_ofEdge (A : MatConn n) (e : Edge) : (ofEdge e).hol A = e.hol A := by
  simp [hol, ofEdge]

/-- The composite `e₂ ∘ e₁` of two edges with `e₁(t₁) = e₂(t₀)`, a piecewise `C¹` path. -/
def comp₂ (e₁ e₂ : Edge) (h : e₁.target = e₂.source) : PwPath := ⟨[e₁, e₂], List.isChain_pair.2 h⟩

/-- **The composition law for two edges**: `A(e₂ ∘ e₁) = A(e₂) A(e₁)` (Ashtekar–Lewandowski (4.37)). -/
theorem hol_comp₂ (A : MatConn n) (e₁ e₂ : Edge) (h : e₁.target = e₂.source) :
    (comp₂ e₁ e₂ h).hol A = e₂.hol A * e₁.hol A := by
  simp [hol, comp₂]

/-- The **reversed path** `p⁻¹`: the reversed pieces in the opposite order. -/
def rev (p : PwPath) : PwPath where
  pieces := (p.pieces.map Edge.rev).reverse
  chain := by
    rw [List.isChain_reverse, List.isChain_map]
    refine p.chain.imp fun e f hef => ?_
    rw [Edge.rev_target, Edge.rev_source, hef]

/-- The inverse of a reversed product of matrices is the product of the inverses. -/
lemma inv_reverse_prod (l : List (Matrix (Fin n) (Fin n) ℂ)) : (l.reverse.prod)⁻¹ = (l.map (·⁻¹)).prod := by
  induction l with
  | nil => simp
  | cons x l ih => simp [List.reverse_cons, List.prod_append, Matrix.mul_inv_rev, ih]

/-- **The reversal law** (Ashtekar–Lewandowski (4.37)): `A(p⁻¹) = A(p)⁻¹`. -/
theorem hol_rev {A : MatConn n} (hA : ∀ a, Continuous fun x => A x a) (p : PwPath) :
    p.rev.hol A = (p.hol A)⁻¹ := by
  rw [hol, hol, inv_reverse_prod, rev, List.map_reverse, List.reverse_reverse, List.map_map, List.map_map]
  congr 1
  exact List.map_congr_left fun e _ => Edge.hol_rev hA e

end PwPath

end Lightlike.Canonical
