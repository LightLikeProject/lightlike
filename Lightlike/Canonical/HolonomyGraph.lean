import Lightlike.Canonical.HolonomyGauge
import Mathlib.LinearAlgebra.Matrix.DotProduct

/-!
# Connections and gauge transformations on a graph

A graph (`Graph`, Ashtekar–Lewandowski, arXiv:gr-qc/0404018, p. 27, footnote 13) is a finite family of embedded edges
that meet only at their end points. As on p. 28, a connection on the graph (`Graph.Conn`, `A_α`) is an `su(2)`-valued
1-form along each edge and a gauge transformation (`Graph.Gauge`, `G_α`) an `SU(2)`-valued map along the edges that
agrees at common end points; `G⁰_α` are those that are the identity at the vertices. The maps `I_E` (holonomies along the
edges, (4.16)) and `I_V` (values at the vertices, (4.17)) are one-to-one on the quotients and onto:

* `I_E(M^γ)_e = I_V(γ)(t(e))⁻¹ I_E(M)_e I_V(γ)(s(e))` (`Graph.IE_actCoeff`), so `I_E` is constant on the `G⁰_α`-orbits
  (`Graph.transportM_actCoeff_of_trivial`);
* two connections with the same `I_E` differ by an element of `G⁰_α` (`Graph.IE_injective_mod`);
* `I_E` is onto `SU(2)ⁿ` (`Graph.IE_surjective`), by the exponential form `h = cos θ · 1 + sin θ · K` of `SU(2)`
  (`su2_exp_form`) and the transport of a constant coefficient (`transportM_const_exp`);
* `I_V γ = I_V γ'` iff `γ'⁻¹ γ ∈ G⁰_α` (`Graph.IV_eq_iff`), and `I_V` is onto `SU(2)^m` (`Graph.IV_surjective`).
-/

open Matrix Set
open scoped ContDiff ComplexOrder

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

noncomputable section

namespace Lightlike.Canonical

/-! ### The exponential form of `SU(2)` -/

/-- For `h ∈ SU(2)`, `hᴴ` is the adjugate of `h`. -/
lemma su2_conjTranspose_eq_adjugate {h : Matrix (Fin 2) (Fin 2) ℂ} (hh : h ∈ specialUnitaryGroup (Fin 2) ℂ) :
    hᴴ = adjugate h := by
  obtain ⟨hu, hd⟩ := mem_specialUnitaryGroup_iff.1 hh
  have hu' : hᴴ * h = 1 := by rw [← star_eq_conjTranspose]; exact mem_unitaryGroup_iff'.1 hu
  calc hᴴ = hᴴ * (h * adjugate h) := by rw [mul_adjugate, hd, one_smul, Matrix.mul_one]
    _ = hᴴ * h * adjugate h := (Matrix.mul_assoc _ _ _).symm
    _ = adjugate h := by rw [hu', Matrix.one_mul]

/-- **The exponential form of `SU(2)`**: every `h ∈ SU(2)` is `cos θ · 1 + sin θ · K` with `K` anti-Hermitian,
traceless and `K² = −1`. -/
theorem su2_exp_form {h : Matrix (Fin 2) (Fin 2) ℂ} (hh : h ∈ specialUnitaryGroup (Fin 2) ℂ) :
    ∃ (θ : ℝ) (K : Matrix (Fin 2) (Fin 2) ℂ), Kᴴ = -K ∧ K.trace = 0 ∧ K * K = -1 ∧
      h = ((Real.cos θ : ℝ) : ℂ) • 1 + ((Real.sin θ : ℝ) : ℂ) • K := by
  have hadj := su2_conjTranspose_eq_adjugate hh
  have hd : h.det = 1 := (mem_specialUnitaryGroup_iff.1 hh).2
  have hu : hᴴ * h = 1 := by
    rw [← star_eq_conjTranspose]; exact mem_unitaryGroup_iff'.1 (mem_specialUnitaryGroup_iff.1 hh).1
  have h11 : h 1 1 = star (h 0 0) := by
    have := congrFun (congrFun hadj 1) 1
    simp [adjugate_fin_two, conjTranspose_apply] at this
    rw [← this]; simp
  set c : ℝ := (h 0 0).re with hc
  have htr : h.trace = ((2 * c : ℝ) : ℂ) := by
    rw [trace_fin_two, h11]
    apply Complex.ext <;> simp [hc] ; ring
  have hsum : h + hᴴ = ((2 * c : ℝ) : ℂ) • 1 := by
    rw [hadj, ← htr, adjugate_fin_two]
    ext i j; fin_cases i <;> fin_cases j
    all_goals simp [trace_fin_two]
    ring
  have hCH : h * h = ((2 * c : ℝ) : ℂ) • h - 1 := by
    rw [← htr, ← one_smul ℂ (1 : Matrix (Fin 2) (Fin 2) ℂ), ← hd]
    ext i j; fin_cases i <;> fin_cases j <;> simp [trace_fin_two, det_fin_two, Matrix.mul_apply, Fin.sum_univ_two]
      <;> ring
  have hc2 : c ^ 2 ≤ 1 := by
    have h00 := congrFun (congrFun hu 0) 0
    simp only [Matrix.mul_apply, Fin.sum_univ_two, conjTranspose_apply, Matrix.one_apply_eq] at h00
    have hre := congrArg Complex.re h00
    simp [Complex.mul_re, Complex.conj_re, Complex.conj_im] at hre
    nlinarith [sq_nonneg (h 0 0).im, sq_nonneg (h 1 0).re, sq_nonneg (h 1 0).im]
  have hc1 : -1 ≤ c := by nlinarith
  have hc1' : c ≤ 1 := by nlinarith
  set X : Matrix (Fin 2) (Fin 2) ℂ := h - ((c : ℝ) : ℂ) • 1 with hX
  have hXH : Xᴴ = -X := by
    have : hᴴ = ((2 * c : ℝ) : ℂ) • 1 - h := by rw [← hsum]; abel
    rw [hX, conjTranspose_sub, conjTranspose_smul, conjTranspose_one, this]
    simp only [Complex.star_def, Complex.conj_ofReal]
    push_cast
    module
  have hXtr : X.trace = 0 := by
    rw [hX, trace_sub, trace_smul, trace_one, htr]; simp; ring
  have hXX : X * X = (((c ^ 2 - 1 : ℝ)) : ℂ) • 1 := by
    have e1 : X * X = h * h - ((2 * c : ℝ) : ℂ) • h + (((c : ℝ) : ℂ) ^ 2) • 1 := by
      rw [hX]
      simp only [sub_mul, mul_sub, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one, smul_smul]
      push_cast
      module
    rw [e1, hCH]
    push_cast
    module
  refine ⟨Real.arccos c, ?_⟩
  rw [Real.cos_arccos hc1 hc1', Real.sin_arccos]
  set s : ℝ := √(1 - c ^ 2) with hs
  by_cases hs0 : s = 0
  · -- `h = ±1`
    have hc2' : c ^ 2 = 1 := by
      have : 1 - c ^ 2 = 0 := by
        have h0 : 0 ≤ 1 - c ^ 2 := by linarith
        rw [hs, Real.sqrt_eq_zero h0] at hs0; exact hs0
      linarith
    have hX0 : X = 0 := by
      have hXX0 : Xᴴ * X = 0 := by rw [hXH, Matrix.neg_mul, hXX, hc2', sub_self]; simp
      exact Matrix.conjTranspose_mul_self_eq_zero.1 hXX0
    refine ⟨!![Complex.I, 0; 0, -Complex.I], ?_, ?_, ?_, ?_⟩
    · ext i j; fin_cases i <;> fin_cases j <;> simp
    · simp [trace_fin_two]
    · ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
    · rw [hs0]
      have : h = ((c : ℝ) : ℂ) • 1 := by rw [← sub_eq_zero]; exact hX0
      rw [this]; simp
  · have hs2 : s ^ 2 = 1 - c ^ 2 := Real.sq_sqrt (by linarith)
    refine ⟨((1 / s : ℝ) : ℂ) • X, ?_, ?_, ?_, ?_⟩
    · rw [conjTranspose_smul, hXH]; simp [Complex.conj_ofReal]
    · rw [trace_smul, hXtr, smul_zero]
    · rw [Matrix.smul_mul, Matrix.mul_smul, hXX, smul_smul, smul_smul]
      have : ((1 / s : ℝ) : ℂ) * ((1 / s : ℝ) : ℂ) * ((c ^ 2 - 1 : ℝ) : ℂ) = -1 := by
        rw [← Complex.ofReal_mul, ← Complex.ofReal_mul]
        have : 1 / s * (1 / s) * (c ^ 2 - 1) = -1 := by field_simp; linarith
        rw [this]; simp
      rw [this, neg_one_smul]
    · rw [smul_smul, ← Complex.ofReal_mul, mul_one_div_cancel hs0, Complex.ofReal_one, one_smul, hX]
      abel


/-! ### Every element of `SU(2)` is a holonomy -/

/-- The constant `su(2)` coefficient `−(θ / (t − s)) K` of `transportM_const_exp`. -/
def expCoeff (K : Matrix (Fin 2) (Fin 2) ℂ) (θ s t : ℝ) : ℝ → Matrix (Fin 2) (Fin 2) ℂ :=
  fun _ => -(((θ / (t - s) : ℝ) : ℂ) • K)

/-- **The transport of a constant coefficient**: for `K² = −1` and `s < t`, the transport of `−(θ / (t − s)) K` from
`s` to `t` is `cos θ · 1 + sin θ · K`. -/
theorem transportM_const_exp {K : Matrix (Fin 2) (Fin 2) ℂ} (hKK : K * K = -1) {s t : ℝ} (hst : s < t) (θ : ℝ) :
    transportM (expCoeff K θ s t) s t = ((Real.cos θ : ℝ) : ℂ) • 1 + ((Real.sin θ : ℝ) : ℂ) • K := by
  set w : ℝ := θ / (t - s) with hw
  set U : ℝ → Matrix (Fin 2) (Fin 2) ℂ := fun τ =>
    ((Real.cos (w * (τ - s)) : ℝ) : ℂ) • 1 + ((Real.sin (w * (τ - s)) : ℝ) : ℂ) • K with hU
  have hφ : ∀ τ, HasDerivAt (fun τ : ℝ => w * (τ - s)) w τ := fun τ => by
    simpa using ((hasDerivAt_id τ).sub_const s).const_mul w
  have hsol : ∀ τ ∈ Icc s t, HasDerivWithinAt U (-(expCoeff K θ s t τ * U τ)) (Icc s t) τ := by
    intro τ _
    have hc := ((Real.hasDerivAt_cos (w * (τ - s))).comp τ (hφ τ)).ofReal_comp
    have hs := ((Real.hasDerivAt_sin (w * (τ - s))).comp τ (hφ τ)).ofReal_comp
    refine ((hc.smul_const (1 : Matrix (Fin 2) (Fin 2) ℂ)).add (hs.smul_const K)).hasDerivWithinAt.congr_deriv ?_
    simp only [expCoeff, hU, ← hw, Matrix.neg_mul, Matrix.smul_mul, Matrix.mul_add, Matrix.mul_smul,
      Matrix.mul_one, hKK, Complex.ofReal_mul, Complex.ofReal_neg]
    module
  have h0 : U s = 1 := by simp [hU]
  rw [transportM_eq (M := expCoeff K θ s t) continuousOn_const hsol h0 t ⟨hst.le, le_rfl⟩, hU]
  have : w * (t - s) = θ := by rw [hw]; field_simp [(sub_pos.2 hst).ne']
  simp only [this]

/-- The constant coefficient `−(θ / (t − s)) K` is in `su(2)` when `K` is. -/
lemma expCoeff_su2 {K : Matrix (Fin 2) (Fin 2) ℂ} (hKH : Kᴴ = -K) (hKtr : K.trace = 0) (θ s t τ : ℝ) :
    (expCoeff K θ s t τ)ᴴ = -expCoeff K θ s t τ ∧ (expCoeff K θ s t τ).trace = 0 := by
  refine ⟨?_, ?_⟩
  · simp [expCoeff, conjTranspose_smul, hKH, Complex.conj_ofReal]
  · simp [expCoeff, trace_smul, hKtr]

/-- **Every element of `SU(2)` is the transport of a constant `su(2)` coefficient** on any interval `[s, t]`,
`s < t`. -/
theorem exists_su2_coeff {h : Matrix (Fin 2) (Fin 2) ℂ} (hh : h ∈ specialUnitaryGroup (Fin 2) ℂ) {s t : ℝ}
    (hst : s < t) : ∃ K : Matrix (Fin 2) (Fin 2) ℂ, ∃ θ : ℝ, Kᴴ = -K ∧ K.trace = 0 ∧
      transportM (expCoeff K θ s t) s t = h := by
  obtain ⟨θ, K, hKH, hKtr, hKK, rfl⟩ := su2_exp_form hh
  exact ⟨K, θ, hKH, hKtr, transportM_const_exp hKK hst θ⟩


/-! ### The gauge action along an edge -/

/-- The gauge transform `γ⁻¹ M γ + γ⁻¹ γ'` of a coefficient along an edge, for unitary `γ` (Ashtekar–Lewandowski (4.14)
along the edges, `γ⁻¹ = γᴴ`). -/
def gaugeCoeff (γ γ' M : ℝ → Matrix (Fin 2) (Fin 2) ℂ) : ℝ → Matrix (Fin 2) (Fin 2) ℂ :=
  fun τ => (γ τ)ᴴ * M τ * γ τ + (γ τ)ᴴ * γ' τ

/-- **Gauge covariance along an edge**: for `γ` unitary and `C¹` on `[s, t]` (derivative `γ'`),
`U_{M^γ}(t, s) = γ(t)⁻¹ U_M(t, s) γ(s)`. -/
theorem transportM_gaugeCoeff {M γ γ' : ℝ → Matrix (Fin 2) (Fin 2) ℂ} {s t : ℝ} (hst : s < t)
    (hM : ContinuousOn M (Icc s t)) (hγ : ∀ τ ∈ Icc s t, HasDerivWithinAt γ (γ' τ) (Icc s t) τ)
    (hγ' : ContinuousOn γ' (Icc s t)) (hu : ∀ τ ∈ Icc s t, (γ τ)ᴴ * γ τ = 1) :
    transportM (gaugeCoeff γ γ' M) s t = (γ t)ᴴ * transportM M s t * γ s := by
  have hu' : ∀ τ ∈ Icc s t, γ τ * (γ τ)ᴴ = 1 := fun τ hτ => mul_eq_one_comm.1 (hu τ hτ)
  have hγc : ContinuousOn γ (Icc s t) := fun τ hτ => (hγ τ hτ).continuousWithinAt
  have hγH : ∀ τ ∈ Icc s t, HasDerivWithinAt (fun σ => (γ σ)ᴴ) ((γ' τ)ᴴ) (Icc s t) τ := fun τ hτ =>
    (conjTransposeCLM (n := 2)).hasFDerivAt.comp_hasDerivWithinAt τ (hγ τ hτ)
  have hkey : ∀ τ ∈ Icc s t, (γ' τ)ᴴ * γ τ + (γ τ)ᴴ * γ' τ = 0 := fun τ hτ => by
    have h1 := (hγH τ hτ).fun_mul (hγ τ hτ)
    have h2 : HasDerivWithinAt (fun σ => (γ σ)ᴴ * γ σ) 0 (Icc s t) τ :=
      (hasDerivWithinAt_const τ (Icc s t) (1 : Matrix (Fin 2) (Fin 2) ℂ)).congr (fun σ hσ => hu σ hσ) (hu τ hτ)
    exact (uniqueDiffOn_Icc hst τ hτ).eq_deriv _ h1 h2
  have hγ'H : ∀ τ ∈ Icc s t, (γ' τ)ᴴ = -((γ τ)ᴴ * γ' τ * (γ τ)ᴴ) := fun τ hτ => by
    have : (γ' τ)ᴴ = ((γ' τ)ᴴ * γ τ) * (γ τ)ᴴ := by rw [Matrix.mul_assoc, hu' τ hτ, Matrix.mul_one]
    rw [this, eq_neg_of_add_eq_zero_left (hkey τ hτ), Matrix.neg_mul]
  have hMg : ContinuousOn (gaugeCoeff γ γ' M) (Icc s t) := by
    have hγHc : ContinuousOn (fun σ => (γ σ)ᴴ) (Icc s t) := fun τ hτ => (hγH τ hτ).continuousWithinAt
    exact ((hγHc.mul hM).mul hγc).add (hγHc.mul hγ')
  obtain ⟨h1, h2⟩ := hasDerivWithinAt_transportM hM hst.le
  have hsol : ∀ τ ∈ Icc s t, HasDerivWithinAt (fun σ => (γ σ)ᴴ * transportM M s σ * γ s)
      (-(gaugeCoeff γ γ' M τ * ((γ τ)ᴴ * transportM M s τ * γ s))) (Icc s t) τ := by
    intro τ hτ
    refine (((hγH τ hτ).fun_mul (h2 τ hτ)).mul_const (γ s)).congr_deriv ?_
    rw [gaugeCoeff, hγ'H τ hτ]
    calc (-((γ τ)ᴴ * γ' τ * (γ τ)ᴴ) * transportM M s τ + (γ τ)ᴴ * -(M τ * transportM M s τ)) * γ s
        = -((γ τ)ᴴ * M τ * (γ τ * (γ τ)ᴴ) * transportM M s τ * γ s +
            (γ τ)ᴴ * γ' τ * (γ τ)ᴴ * transportM M s τ * γ s) := by
          rw [hu' τ hτ]; noncomm_ring
      _ = _ := by noncomm_ring
  have h0 : (γ s)ᴴ * transportM M s s * γ s = 1 := by rw [h1, Matrix.mul_one, hu s ⟨le_rfl, hst.le⟩]
  exact transportM_eq hMg hsol h0 t ⟨hst.le, le_rfl⟩

/-! ### Graphs, their connections and gauge transformations -/

/-- A **graph with `C¹` edges**: finitely many `C¹` edges, each injective on `[t₀, t₁)` and on `(t₀, t₁]`, two edges
meeting only at end points. This is the tool for the analytic pieces of the edges of a graph of Ashtekar–Lewandowski
(`ALGraph.pieceGraph` in `Lightlike/Canonical/HolonomyALGraph.lean`), whose edges are closed-piecewise analytic. -/
structure Graph where
  /-- The number of edges. -/
  m : ℕ
  /-- The edges. -/
  edge : Fin m → Edge
  /-- Each edge has a nonempty interior. -/
  nondeg : ∀ i, (edge i).t₀ < (edge i).t₁
  /-- Each edge is embedded on `[t₀, t₁)`. -/
  injOn_Ico : ∀ i, InjOn (edge i).path (Ico (edge i).t₀ (edge i).t₁)
  /-- Each edge is embedded on `(t₀, t₁]`. -/
  injOn_Ioc : ∀ i, InjOn (edge i).path (Ioc (edge i).t₀ (edge i).t₁)
  /-- Two edges meet only at end points. -/
  meet : ∀ i j, i ≠ j → ∀ s ∈ Icc (edge i).t₀ (edge i).t₁, ∀ t ∈ Icc (edge j).t₀ (edge j).t₁,
    (edge i).path s = (edge j).path t → (s = (edge i).t₀ ∨ s = (edge i).t₁) ∧ (t = (edge j).t₀ ∨ t = (edge j).t₁)

namespace Graph

variable (α : Graph)

/-- The parameter interval of the edge `i`. -/
abbrev I (i : Fin α.m) : Set ℝ := Icc (α.edge i).t₀ (α.edge i).t₁

/-- The **vertices**: the end points of the edges. -/
def vertices : Set (Fin 3 → ℝ) := {v | ∃ i, v = (α.edge i).source ∨ v = (α.edge i).target}

/-- The source of an edge is a vertex. -/
lemma source_mem (i : Fin α.m) : (α.edge i).source ∈ α.vertices := ⟨i, Or.inl rfl⟩

/-- The target of an edge is a vertex. -/
lemma target_mem (i : Fin α.m) : (α.edge i).target ∈ α.vertices := ⟨i, Or.inr rfl⟩

/-- A **connection on the graph** (`A_α`, Ashtekar–Lewandowski p. 28): an `su(2)`-valued 1-form along each edge, given
by its component `M_i(t)` in the edge parameter, continuous on the edge. -/
structure Conn where
  /-- The component along each edge. -/
  coeff : Fin α.m → ℝ → Matrix (Fin 2) (Fin 2) ℂ
  /-- It is continuous on the edge. -/
  cont : ∀ i, ContinuousOn (coeff i) (α.I i)
  /-- It is anti-Hermitian. -/
  antiHerm : ∀ i, ∀ τ ∈ α.I i, (coeff i τ)ᴴ = -coeff i τ
  /-- It is traceless. -/
  traceless : ∀ i, ∀ τ ∈ α.I i, (coeff i τ).trace = 0

/-- The **restriction to the graph** of an `su(2)` connection on the chart: its pull-back `A_a(e(t)) ė^a(t)` to each
edge. -/
def restrict {A : MatConn 2} (hA : ∀ a, Continuous fun x => A x a) (hAH : ∀ x a, (A x a)ᴴ = -A x a)
    (htr : ∀ x a, (A x a).trace = 0) : α.Conn where
  coeff i := transportCoeff A (α.edge i).path
  cont i := (continuous_transportCoeff hA (α.edge i).smooth).continuousOn
  antiHerm _ τ _ := transportCoeff_conjTranspose hAH _ τ
  traceless _ τ _ := trace_transportCoeff htr _ τ

/-- **The map `I_E`** (Ashtekar–Lewandowski (4.16)): the holonomies along the edges. -/
def IE (M : α.Conn) : Fin α.m → Matrix (Fin 2) (Fin 2) ℂ :=
  fun i => transportM (M.coeff i) (α.edge i).t₀ (α.edge i).t₁

/-- `I_E` takes values in `SU(2)ⁿ`. -/
lemma IE_mem (M : α.Conn) (i : Fin α.m) : α.IE M i ∈ specialUnitaryGroup (Fin 2) ℂ :=
  transportM_mem_specialUnitaryGroup (M.cont i) (M.antiHerm i) (M.traceless i) (α.nondeg i).le

/-- On the restriction of a connection of the chart, `I_E` is the holonomy along the edges. -/
lemma IE_restrict {A : MatConn 2} (hA : ∀ a, Continuous fun x => A x a) (hAH : ∀ x a, (A x a)ᴴ = -A x a)
    (htr : ∀ x a, (A x a).trace = 0) (i : Fin α.m) : α.IE (α.restrict hA hAH htr) i = (α.edge i).hol A := rfl

/-- A **gauge transformation on the graph** (`G_α`, Ashtekar–Lewandowski p. 28): an `SU(2)`-valued `C¹` map along each
edge (derivative `der`), the maps of two edges agreeing at the end points where they meet. -/
structure Gauge where
  /-- The value along each edge. -/
  val : Fin α.m → ℝ → Matrix (Fin 2) (Fin 2) ℂ
  /-- Its derivative along the edge. -/
  der : Fin α.m → ℝ → Matrix (Fin 2) (Fin 2) ℂ
  /-- `der` is the derivative of `val` on the edge. -/
  hasDeriv : ∀ i, ∀ τ ∈ α.I i, HasDerivWithinAt (val i) (der i τ) (α.I i) τ
  /-- The derivative is continuous on the edge. -/
  cont : ∀ i, ContinuousOn (der i) (α.I i)
  /-- The values are in `SU(2)`. -/
  mem : ∀ i, ∀ τ ∈ α.I i, val i τ ∈ specialUnitaryGroup (Fin 2) ℂ
  /-- The values agree at common end points. -/
  consistent : ∀ i j, ∀ s ∈ ({(α.edge i).t₀, (α.edge i).t₁} : Set ℝ), ∀ t ∈ ({(α.edge j).t₀, (α.edge j).t₁} : Set ℝ),
    (α.edge i).path s = (α.edge j).path t → val i s = val j t

/-- `G⁰_α`: the gauge transformations that are the identity at the vertices. -/
def Gauge.TrivialAtVertices {α : Graph} (γ : α.Gauge) : Prop :=
  ∀ i, γ.val i (α.edge i).t₀ = 1 ∧ γ.val i (α.edge i).t₁ = 1

/-- The **gauge action** (4.14) on the components of a graph connection along the edges. -/
def actCoeff (γ : α.Gauge) (M : α.Conn) (i : Fin α.m) : ℝ → Matrix (Fin 2) (Fin 2) ℂ :=
  gaugeCoeff (γ.val i) (γ.der i) (M.coeff i)

/-- A unitary of `SU(2)` -/
lemma conjTranspose_mul_self_of_mem {g : Matrix (Fin 2) (Fin 2) ℂ} (hg : g ∈ specialUnitaryGroup (Fin 2) ℂ) :
    gᴴ * g = 1 := by
  rw [← star_eq_conjTranspose]; exact mem_unitaryGroup_iff'.1 (mem_specialUnitaryGroup_iff.1 hg).1

/-- **Gauge covariance of `I_E`**: `I_E(M^γ)_e = γ(t(e))⁻¹ I_E(M)_e γ(s(e))`. -/
theorem transportM_actCoeff (γ : α.Gauge) (M : α.Conn) (i : Fin α.m) :
    transportM (α.actCoeff γ M i) (α.edge i).t₀ (α.edge i).t₁ =
      (γ.val i (α.edge i).t₁)ᴴ * α.IE M i * γ.val i (α.edge i).t₀ :=
  transportM_gaugeCoeff (α.nondeg i) (M.cont i) (γ.hasDeriv i) (γ.cont i)
    (fun τ hτ => conjTranspose_mul_self_of_mem (γ.mem i τ hτ))

/-- **`I_E` descends to `A_α / G⁰_α`**: a gauge transformation that is the identity at the vertices does not change
`I_E`. -/
theorem transportM_actCoeff_of_trivial (γ : α.Gauge) (hγ : γ.TrivialAtVertices) (M : α.Conn) (i : Fin α.m) :
    transportM (α.actCoeff γ M i) (α.edge i).t₀ (α.edge i).t₁ = α.IE M i := by
  rw [transportM_actCoeff, (hγ i).1, (hγ i).2, conjTranspose_one, Matrix.one_mul, Matrix.mul_one]

end Graph


namespace Graph

variable (α : Graph)

/-- The conjugate transpose of an element of `SU(2)` is in `SU(2)`. -/
lemma conjTranspose_mem {g : Matrix (Fin 2) (Fin 2) ℂ} (hg : g ∈ specialUnitaryGroup (Fin 2) ℂ) :
    gᴴ ∈ specialUnitaryGroup (Fin 2) ℂ := by
  rw [mem_specialUnitaryGroup_iff]
  refine ⟨mem_unitaryGroup_iff'.2 ?_, ?_⟩
  · rw [star_eq_conjTranspose, conjTranspose_conjTranspose]
    exact mul_eq_one_comm.1 (conjTranspose_mul_self_of_mem hg)
  · rw [det_conjTranspose, (mem_specialUnitaryGroup_iff.1 hg).2, star_one]

open Classical in
/-- **The map `I_V`** (Ashtekar–Lewandowski (4.17)): the values of a gauge transformation at the vertices. -/
def IV (γ : α.Gauge) (v : α.vertices) : Matrix (Fin 2) (Fin 2) ℂ :=
  if (α.edge (Classical.choose v.2)).source = v.1 then γ.val (Classical.choose v.2) (α.edge (Classical.choose v.2)).t₀
  else γ.val (Classical.choose v.2) (α.edge (Classical.choose v.2)).t₁

/-- `I_V γ v` is the value of `γ` at any end point of an edge at `v`. -/
lemma IV_eq (γ : α.Gauge) {v : α.vertices} {j : Fin α.m} {t : ℝ}
    (ht : t ∈ ({(α.edge j).t₀, (α.edge j).t₁} : Set ℝ)) (hv : (α.edge j).path t = v.1) : α.IV γ v = γ.val j t := by
  have hspec := Classical.choose_spec v.2
  set i := Classical.choose v.2 with hi
  unfold IV
  rw [← hi]
  split_ifs with hs
  · exact γ.consistent i j _ (Or.inl rfl) t ht (hs.trans hv.symm)
  · have hti : (α.edge i).target = v.1 := by
      rcases hspec with h | h
      · exact absurd h.symm hs
      · exact h.symm
    exact γ.consistent i j _ (Or.inr rfl) t ht (hti.trans hv.symm)

/-- `I_V` at the source of an edge. -/
lemma IV_source (γ : α.Gauge) (i : Fin α.m) : α.IV γ ⟨_, α.source_mem i⟩ = γ.val i (α.edge i).t₀ :=
  α.IV_eq γ (Or.inl rfl) rfl

/-- `I_V` at the target of an edge. -/
lemma IV_target (γ : α.Gauge) (i : Fin α.m) : α.IV γ ⟨_, α.target_mem i⟩ = γ.val i (α.edge i).t₁ :=
  α.IV_eq γ (Or.inr rfl) rfl

/-- **Equivariance of `I_E`** (Ashtekar–Lewandowski (4.14)-(4.17)): `I_E(M^γ)_e = I_V(γ)(t(e))⁻¹ I_E(M)_e I_V(γ)(s(e))`. -/
theorem IE_actCoeff (γ : α.Gauge) (M : α.Conn) (i : Fin α.m) :
    transportM (α.actCoeff γ M i) (α.edge i).t₀ (α.edge i).t₁ =
      (α.IV γ ⟨_, α.target_mem i⟩)ᴴ * α.IE M i * α.IV γ ⟨_, α.source_mem i⟩ := by
  rw [IV_source, IV_target]
  exact α.transportM_actCoeff γ M i

/-- **`I_E` is one-to-one on `A_α / G⁰_α`**: two connections on the graph with the same holonomies along every edge
are related by a gauge transformation that is the identity at the vertices. -/
theorem IE_injective_mod (M M' : α.Conn) (h : α.IE M = α.IE M') :
    ∃ γ : α.Gauge, γ.TrivialAtVertices ∧ ∀ i, ∀ τ ∈ α.I i, M'.coeff i τ = α.actCoeff γ M i τ := by
  have hU := fun i => hasDerivWithinAt_transportM (M.cont i) (α.nondeg i).le
  have hU' := fun i => hasDerivWithinAt_transportM (M'.cont i) (α.nondeg i).le
  have hmem : ∀ (N : α.Conn) i, ∀ τ ∈ α.I i,
      transportM (N.coeff i) (α.edge i).t₀ τ ∈ specialUnitaryGroup (Fin 2) ℂ := fun N i τ hτ => by
    have hsub : Icc (α.edge i).t₀ τ ⊆ α.I i := Icc_subset_Icc_right hτ.2
    exact transportM_mem_specialUnitaryGroup ((N.cont i).mono hsub) (fun σ hσ => N.antiHerm i σ (hsub hσ))
      (fun σ hσ => N.traceless i σ (hsub hσ)) hτ.1
  set U := fun i => transportM (M.coeff i) (α.edge i).t₀ with hUdef
  set U' := fun i => transportM (M'.coeff i) (α.edge i).t₀ with hU'def
  have hU'H : ∀ i, ∀ τ ∈ α.I i, HasDerivWithinAt (fun σ => (U' i σ)ᴴ) ((-(M'.coeff i τ * U' i τ))ᴴ) (α.I i) τ :=
    fun i τ hτ => (conjTransposeCLM (n := 2)).hasFDerivAt.comp_hasDerivWithinAt τ ((hU' i).2 τ hτ)
  have hval1 : ∀ i, U i (α.edge i).t₁ * (U' i (α.edge i).t₁)ᴴ = 1 := fun i => by
    have : U i (α.edge i).t₁ = U' i (α.edge i).t₁ := congrFun h i
    rw [this]
    exact mul_eq_one_comm.1 (conjTranspose_mul_self_of_mem (hmem M' i _ ⟨(α.nondeg i).le, le_rfl⟩))
  have hval0 : ∀ i, U i (α.edge i).t₀ * (U' i (α.edge i).t₀)ᴴ = 1 := fun i => by
    simp only [hUdef, hU'def]
    rw [(hU i).1, (hU' i).1, conjTranspose_one, Matrix.mul_one]
  have hends : ∀ i, ∀ s ∈ ({(α.edge i).t₀, (α.edge i).t₁} : Set ℝ), U i s * (U' i s)ᴴ = 1 := fun i s hs => by
    rcases hs with rfl | rfl
    · exact hval0 i
    · exact hval1 i
  let γ : α.Gauge :=
    { val := fun i τ => U i τ * (U' i τ)ᴴ
      der := fun i τ => -(M.coeff i τ * U i τ) * (U' i τ)ᴴ + U i τ * (-(M'.coeff i τ * U' i τ))ᴴ
      hasDeriv := fun i τ hτ => ((hU i).2 τ hτ).fun_mul (hU'H i τ hτ)
      cont := fun i => by
        have hUc : ContinuousOn (U i) (α.I i) := fun τ hτ => ((hU i).2 τ hτ).continuousWithinAt
        have hU'c : ContinuousOn (U' i) (α.I i) := fun τ hτ => ((hU' i).2 τ hτ).continuousWithinAt
        have hU'Hc : ContinuousOn (fun τ => (U' i τ)ᴴ) (α.I i) := fun τ hτ => (hU'H i τ hτ).continuousWithinAt
        have hc1 : ContinuousOn (fun τ => (-(M'.coeff i τ * U' i τ))ᴴ) (α.I i) :=
          (conjTransposeCLM (n := 2)).continuous.comp_continuousOn (((M'.cont i).mul hU'c).neg)
        exact (((M.cont i).mul hUc).neg.mul hU'Hc).add (hUc.mul hc1)
      mem := fun i τ hτ => Submonoid.mul_mem _ (hmem M i τ hτ) (conjTranspose_mem (hmem M' i τ hτ))
      consistent := fun i j s hs t ht _ => by rw [hends i s hs, hends j t ht] }
  refine ⟨γ, fun i => ⟨hval0 i, hval1 i⟩, fun i τ hτ => ?_⟩
  have hUU : (U i τ)ᴴ * U i τ = 1 := conjTranspose_mul_self_of_mem (hmem M i τ hτ)
  have hU'U' : U' i τ * (U' i τ)ᴴ = 1 := mul_eq_one_comm.1 (conjTranspose_mul_self_of_mem (hmem M' i τ hτ))
  have e : α.actCoeff γ M i τ = U' i τ * ((U i τ)ᴴ * U i τ) * (U' i τ)ᴴ * M'.coeff i τ := by
    simp only [actCoeff, gaugeCoeff, γ]
    rw [conjTranspose_mul, conjTranspose_conjTranspose, conjTranspose_neg, conjTranspose_mul,
      M'.antiHerm i τ hτ]
    noncomm_ring
  rw [e, hUU, Matrix.mul_one, hU'U', Matrix.one_mul]

/-- **`I_E` is onto `SU(2)ⁿ`**: every family of elements of `SU(2)` is the family of holonomies of a connection on the
graph (constant `su(2)` components along the edges). -/
theorem IE_surjective (h : Fin α.m → Matrix (Fin 2) (Fin 2) ℂ) (hh : ∀ i, h i ∈ specialUnitaryGroup (Fin 2) ℂ) :
    ∃ M : α.Conn, α.IE M = h := by
  choose K θ hKH hKtr hK using fun i => exists_su2_coeff (hh i) (α.nondeg i)
  exact ⟨⟨fun i => expCoeff (K i) (θ i) (α.edge i).t₀ (α.edge i).t₁, fun i => continuousOn_const,
    fun i τ _ => (expCoeff_su2 (hKH i) (hKtr i) _ _ _ τ).1, fun i τ _ => (expCoeff_su2 (hKH i) (hKtr i) _ _ _ τ).2⟩,
    funext fun i => hK i⟩

/-- **`I_V` is onto `SU(2)^m`**: every assignment of elements of `SU(2)` to the vertices is the family of values of a
gauge transformation on the graph. -/
theorem IV_surjective (f : α.vertices → Matrix (Fin 2) (Fin 2) ℂ) (hf : ∀ v, f v ∈ specialUnitaryGroup (Fin 2) ℂ) :
    ∃ γ : α.Gauge, α.IV γ = f := by
  choose K θ hKH hKtr hK using fun i =>
    exists_su2_coeff (Submonoid.mul_mem _ (conjTranspose_mem (hf ⟨_, α.source_mem i⟩)) (hf ⟨_, α.target_mem i⟩))
      (α.nondeg i)
  have hPd := fun i => hasDerivWithinAt_transportM (M := expCoeff (K i) (θ i) (α.edge i).t₀ (α.edge i).t₁)
    continuousOn_const (α.nondeg i).le
  have hPmem : ∀ i, ∀ τ ∈ α.I i, transportM (expCoeff (K i) (θ i) (α.edge i).t₀ (α.edge i).t₁) (α.edge i).t₀ τ ∈
      specialUnitaryGroup (Fin 2) ℂ := fun i τ hτ =>
    transportM_mem_specialUnitaryGroup continuousOn_const
      (fun σ _ => (expCoeff_su2 (hKH i) (hKtr i) _ _ _ σ).1) (fun σ _ => (expCoeff_su2 (hKH i) (hKtr i) _ _ _ σ).2) hτ.1
  have hval : ∀ i, ∀ s (hs : s ∈ ({(α.edge i).t₀, (α.edge i).t₁} : Set ℝ)),
      f ⟨_, α.source_mem i⟩ * transportM (expCoeff (K i) (θ i) (α.edge i).t₀ (α.edge i).t₁) (α.edge i).t₀ s =
        f ⟨(α.edge i).path s, by rcases hs with rfl | rfl; exacts [α.source_mem i, α.target_mem i]⟩ := by
    intro i s hs
    rcases hs with rfl | rfl
    · rw [(hPd i).1, Matrix.mul_one]; rfl
    · rw [hK i, ← Matrix.mul_assoc, mul_eq_one_comm.1 (conjTranspose_mul_self_of_mem (hf ⟨_, α.source_mem i⟩)),
        Matrix.one_mul]
      rfl
  let γ : α.Gauge :=
    { val := fun i τ => f ⟨_, α.source_mem i⟩ *
        transportM (expCoeff (K i) (θ i) (α.edge i).t₀ (α.edge i).t₁) (α.edge i).t₀ τ
      der := fun i τ => f ⟨_, α.source_mem i⟩ * -(expCoeff (K i) (θ i) (α.edge i).t₀ (α.edge i).t₁ τ *
        transportM (expCoeff (K i) (θ i) (α.edge i).t₀ (α.edge i).t₁) (α.edge i).t₀ τ)
      hasDeriv := fun i τ hτ => ((hPd i).2 τ hτ).const_mul _
      cont := fun i => by
        have hPc : ContinuousOn (transportM (expCoeff (K i) (θ i) (α.edge i).t₀ (α.edge i).t₁) (α.edge i).t₀)
            (α.I i) := fun τ hτ => ((hPd i).2 τ hτ).continuousWithinAt
        exact continuousOn_const.mul ((continuousOn_const.mul hPc).neg)
      mem := fun i τ hτ => Submonoid.mul_mem _ (hf _) (hPmem i τ hτ)
      consistent := fun i j s hs t ht hst => by
        rw [hval i s hs, hval j t ht]
        exact congrArg f (Subtype.ext hst) }
  refine ⟨γ, funext fun v => ?_⟩
  obtain ⟨i, hi⟩ := v.2
  rcases hi with hi | hi
  · rw [α.IV_eq γ (Or.inl rfl) hi.symm]
    exact (hval i _ (Or.inl rfl)).trans (congrArg f (Subtype.ext hi.symm))
  · rw [α.IV_eq γ (Or.inr rfl) hi.symm]
    exact (hval i _ (Or.inr rfl)).trans (congrArg f (Subtype.ext hi.symm))

end Graph


/-- The edge-wise quotient `γ'⁻¹ γ` of two gauge transformations on a graph. -/
def Graph.Gauge.quot {α : Graph} (γ' γ : α.Gauge) : α.Gauge where
  val i τ := (γ'.val i τ)ᴴ * γ.val i τ
  der i τ := (γ'.der i τ)ᴴ * γ.val i τ + (γ'.val i τ)ᴴ * γ.der i τ
  hasDeriv i τ hτ := ((conjTransposeCLM (n := 2)).hasFDerivAt.comp_hasDerivWithinAt τ
    (γ'.hasDeriv i τ hτ)).fun_mul (γ.hasDeriv i τ hτ)
  cont i := by
    have hγc : ContinuousOn (γ.val i) (α.I i) := fun τ hτ => (γ.hasDeriv i τ hτ).continuousWithinAt
    have hγ'c : ContinuousOn (fun τ => (γ'.val i τ)ᴴ) (α.I i) := fun τ hτ =>
      ((conjTransposeCLM (n := 2)).hasFDerivAt.comp_hasDerivWithinAt τ (γ'.hasDeriv i τ hτ)).continuousWithinAt
    have hd : ContinuousOn (fun τ => (γ'.der i τ)ᴴ) (α.I i) :=
      (conjTransposeCLM (n := 2)).continuous.comp_continuousOn (γ'.cont i)
    exact (hd.mul hγc).add (hγ'c.mul (γ.cont i))
  mem i τ hτ := Submonoid.mul_mem _ (Graph.conjTranspose_mem (γ'.mem i τ hτ)) (γ.mem i τ hτ)
  consistent i j s hs t ht h := by
    show (γ'.val i s)ᴴ * γ.val i s = (γ'.val j t)ᴴ * γ.val j t
    rw [γ'.consistent i j s hs t ht h, γ.consistent i j s hs t ht h]

namespace Graph

variable (α : Graph)

/-- **`I_V` is one-to-one on `G_α / G⁰_α`** (Ashtekar–Lewandowski (4.17)): two gauge transformations on a graph have the
same values at the vertices if and only if `γ'⁻¹ γ` is the identity at the vertices. -/
theorem IV_eq_iff (γ γ' : α.Gauge) : α.IV γ = α.IV γ' ↔ (γ'.quot γ).TrivialAtVertices := by
  have hend : ∀ i, ∀ s ∈ ({(α.edge i).t₀, (α.edge i).t₁} : Set ℝ), s ∈ α.I i := fun i s hs => by
    rcases hs with rfl | rfl
    exacts [⟨le_rfl, (α.nondeg i).le⟩, ⟨(α.nondeg i).le, le_rfl⟩]
  constructor
  · intro h i
    have key : ∀ s ∈ ({(α.edge i).t₀, (α.edge i).t₁} : Set ℝ), (γ'.val i s)ᴴ * γ.val i s = 1 := by
      intro s hs
      have hv : (α.edge i).path s ∈ α.vertices := by
        rcases hs with rfl | rfl; exacts [α.source_mem i, α.target_mem i]
      have := congrFun h ⟨_, hv⟩
      rw [α.IV_eq γ hs rfl, α.IV_eq γ' hs rfl] at this
      rw [this]
      exact conjTranspose_mul_self_of_mem (γ'.mem i s (hend i s hs))
    exact ⟨key _ (Or.inl rfl), key _ (Or.inr rfl)⟩
  · intro h
    funext v
    obtain ⟨i, hi⟩ := v.2
    have key : ∀ s ∈ ({(α.edge i).t₀, (α.edge i).t₁} : Set ℝ), (γ'.val i s)ᴴ * γ.val i s = 1 →
        γ.val i s = γ'.val i s := fun s hs h1 => by
      have hu : γ'.val i s * (γ'.val i s)ᴴ = 1 :=
        mul_eq_one_comm.1 (conjTranspose_mul_self_of_mem (γ'.mem i s (hend i s hs)))
      calc γ.val i s = γ'.val i s * (γ'.val i s)ᴴ * γ.val i s := by rw [hu, Matrix.one_mul]
        _ = γ'.val i s := by rw [Matrix.mul_assoc, h1, Matrix.mul_one]
    rcases hi with hi | hi
    · rw [α.IV_eq γ (Or.inl rfl) hi.symm, α.IV_eq γ' (Or.inl rfl) hi.symm]
      exact key _ (Or.inl rfl) (h i).1
    · rw [α.IV_eq γ (Or.inr rfl) hi.symm, α.IV_eq γ' (Or.inr rfl) hi.symm]
      exact key _ (Or.inr rfl) (h i).2

end Graph


/-- The one-edge graph: the segment `t e₀`, `t ∈ [0, 1]`. -/
def segmentGraph : Graph where
  m := 1
  edge _ := ⟨fun t => t • (Pi.single 0 1 : Fin 3 → ℝ), 0, 1, zero_le_one, contDiff_id.smul contDiff_const⟩
  nondeg _ := zero_lt_one
  injOn_Ico _ := fun s _ t _ h => by simpa using congrFun h 0
  injOn_Ioc _ := fun s _ t _ h => by simpa using congrFun h 0
  meet i j hij := absurd (Subsingleton.elim i j) hij

/-- **Trust check: the hypotheses of a graph are satisfiable**, and on the one-edge graph every element of `SU(2)` is
the holonomy of a connection. -/
theorem segmentGraph_IE_surjective {h : Matrix (Fin 2) (Fin 2) ℂ} (hh : h ∈ specialUnitaryGroup (Fin 2) ℂ) :
    ∃ M : segmentGraph.Conn, segmentGraph.IE M ⟨0, Nat.one_pos⟩ = h := by
  obtain ⟨M, hM⟩ := segmentGraph.IE_surjective (fun _ => h) fun _ => hh
  exact ⟨M, congrFun hM _⟩

end Lightlike.Canonical
