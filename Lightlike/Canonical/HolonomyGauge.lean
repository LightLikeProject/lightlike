import Lightlike.Canonical.HolonomyPaths

/-!
# Gauge covariance of the holonomy

A gauge transformation is a `C¹` map `g` with unitary values (`g⁻¹ = gᴴ`); it acts on connections by
`A ↦ g⁻¹ A g + g⁻¹ dg` (Ashtekar–Lewandowski, arXiv:gr-qc/0404018, eq. (4.14), p. 28) (`gaugeConn`). The holonomy
transforms at the end points only: `A^g(e) = g(e(t₂))⁻¹ A(e) g(e(t₁))` (`holonomy_gaugeConn`). In particular a gauge
transformation that is the identity at the end points does not change the holonomy, the reason why the holonomies of a
graph's edges are the coordinates of the connections on the graph modulo such gauge transformations ((4.15)–(4.16)).
-/

open Matrix Set
open scoped ContDiff

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

noncomputable section

namespace Lightlike.Canonical

variable {n : ℕ}

/-- The **gauge transform** `A^g_a = g⁻¹ A_a g + g⁻¹ ∂_a g` of a connection by a unitary-valued `g`, with `g⁻¹ = gᴴ`
(Ashtekar–Lewandowski (4.14)). -/
def gaugeConn (g : (Fin 3 → ℝ) → Matrix (Fin n) (Fin n) ℂ) (A : MatConn n) : MatConn n :=
  fun x a => (g x)ᴴ * A x a * g x + (g x)ᴴ * fderiv ℝ g x (Pi.single a 1)

/-- A complex scalar from a real one acts as the real one. -/
lemma ofReal_smul_matrix (r : ℝ) (X : Matrix (Fin n) (Fin n) ℂ) : ((r : ℂ)) • X = r • X := by
  ext i j
  simp [Complex.real_smul]

/-- The transport coefficient of the gauge transform: `M^g = g⁻¹ M g + g⁻¹ ġ` with `ġ = d/dt g(e(t))`. -/
lemma transportCoeff_gaugeConn (g : (Fin 3 → ℝ) → Matrix (Fin n) (Fin n) ℂ) (A : MatConn n)
    (e : ℝ → Fin 3 → ℝ) (t : ℝ) :
    transportCoeff (gaugeConn g A) e t = (g (e t))ᴴ * transportCoeff A e t * g (e t) +
      (g (e t))ᴴ * fderiv ℝ g (e t) (deriv e t) := by
  have hv : fderiv ℝ g (e t) (deriv e t) = ∑ a, (deriv e t a) • fderiv ℝ g (e t) (Pi.single a 1) := by
    conv_lhs => rw [pi_eq_sum_univ' (deriv e t)]
    rw [map_sum]
    exact Finset.sum_congr rfl fun a _ => map_smul _ _ _
  rw [hv]
  simp only [transportCoeff, gaugeConn, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib, smul_add,
    Matrix.mul_smul, Matrix.smul_mul, ofReal_smul_matrix]

/-- The gauge transform of a continuous connection by a `C¹` gauge transformation is continuous. -/
lemma continuous_gaugeConn {A : MatConn n} (hA : ∀ a, Continuous fun x => A x a)
    {g : (Fin 3 → ℝ) → Matrix (Fin n) (Fin n) ℂ} (hg : ContDiff ℝ 1 g) (a : Fin 3) :
    Continuous fun x => gaugeConn g A x a := by
  have hgH : Continuous fun x => (g x)ᴴ := (conjTransposeCLM (n := n)).continuous.comp hg.continuous
  have hdg : Continuous fun x => fderiv ℝ g x (Pi.single a 1) :=
    (hg.continuous_fderiv one_ne_zero).clm_apply continuous_const
  exact ((hgH.mul (hA a)).mul hg.continuous).add (hgH.mul hdg)

/-- **Gauge covariance of the holonomy** (Ashtekar–Lewandowski (4.14)): for a `C¹` gauge transformation with unitary
values, `A^g(e) = g(e(t₂))ᴴ A(e) g(e(t₁))`. -/
theorem holonomy_gaugeConn {A : MatConn n} (hA : ∀ a, Continuous fun x => A x a)
    {g : (Fin 3 → ℝ) → Matrix (Fin n) (Fin n) ℂ} (hg : ContDiff ℝ 1 g) (hgu : ∀ x, (g x)ᴴ * g x = 1)
    {e : ℝ → Fin 3 → ℝ} (he : ContDiff ℝ 1 e) {t₁ t₂ : ℝ} (h : t₁ ≤ t₂) :
    holonomy (gaugeConn g A) e t₁ t₂ = (g (e t₂))ᴴ * holonomy A e t₁ t₂ * g (e t₁) := by
  have hgu' : ∀ x, g x * (g x)ᴴ = 1 := fun x => mul_eq_one_comm.1 (hgu x)
  set G : ℝ → Matrix (Fin n) (Fin n) ℂ := fun t => g (e t) with hG
  set dG : ℝ → Matrix (Fin n) (Fin n) ℂ := fun t => fderiv ℝ g (e t) (deriv e t) with hdG
  have hGd : ∀ t, HasDerivAt G (dG t) t := fun t =>
    ((hg.differentiable one_ne_zero) (e t)).hasFDerivAt.comp_hasDerivAt t
      ((he.differentiable one_ne_zero) t).hasDerivAt
  have hGHd : ∀ t, HasDerivAt (fun s => (G s)ᴴ) ((dG t)ᴴ) t := fun t =>
    (conjTransposeCLM (n := n)).hasFDerivAt.comp_hasDerivAt t (hGd t)
  -- differentiating `gᴴ g = 1` along the path: `ġᴴ g + gᴴ ġ = 0`
  have hkey : ∀ t, (dG t)ᴴ * G t + (G t)ᴴ * dG t = 0 := fun t => by
    have h1 : HasDerivAt (fun s => (G s)ᴴ * G s) ((dG t)ᴴ * G t + (G t)ᴴ * dG t) t := (hGHd t).fun_mul (hGd t)
    have h2 : (fun s => (G s)ᴴ * G s) = fun _ => (1 : Matrix (Fin n) (Fin n) ℂ) := funext fun s => hgu (e s)
    rw [h2] at h1
    exact h1.unique (hasDerivAt_const t 1)
  have hdGH : ∀ t, (dG t)ᴴ = -((G t)ᴴ * dG t * (G t)ᴴ) := fun t => by
    have : (dG t)ᴴ = ((dG t)ᴴ * G t) * (G t)ᴴ := by rw [Matrix.mul_assoc, hgu', Matrix.mul_one]
    rw [this, eq_neg_of_add_eq_zero_left (hkey t), Matrix.neg_mul]
  obtain ⟨h1, h2⟩ := hasDerivWithinAt_transport hA he h
  have hsol : ∀ τ ∈ Icc t₁ t₂, HasDerivWithinAt (fun s => (G s)ᴴ * transport A e t₁ s * G t₁)
      (-(transportCoeff (gaugeConn g A) e τ * ((G τ)ᴴ * transport A e t₁ τ * G t₁))) (Icc t₁ t₂) τ := by
    intro τ hτ
    refine (((hGHd τ).hasDerivWithinAt.fun_mul (h2 τ hτ)).mul_const (G t₁)).congr_deriv ?_
    rw [transportCoeff_gaugeConn, hdGH τ]
    calc (-((G τ)ᴴ * dG τ * (G τ)ᴴ) * transport A e t₁ τ +
          (G τ)ᴴ * -(transportCoeff A e τ * transport A e t₁ τ)) * G t₁
        = -((G τ)ᴴ * transportCoeff A e τ * (G τ * (G τ)ᴴ) * transport A e t₁ τ * G t₁ +
            (G τ)ᴴ * dG τ * (G τ)ᴴ * transport A e t₁ τ * G t₁) := by
          rw [hgu' (e τ)]; noncomm_ring
      _ = _ := by noncomm_ring
  have h0 : (G t₁)ᴴ * transport A e t₁ t₁ * G t₁ = 1 := by rw [h1, Matrix.mul_one, hgu]
  rw [holonomy, transport_eq (fun a => continuous_gaugeConn hA hg a) he hsol h0 t₂ ⟨h, le_rfl⟩]
  rfl

/-- A gauge transformation that is the identity at the end points of an edge does not change its holonomy. -/
theorem holonomy_gaugeConn_of_endpoints {A : MatConn n} (hA : ∀ a, Continuous fun x => A x a)
    {g : (Fin 3 → ℝ) → Matrix (Fin n) (Fin n) ℂ} (hg : ContDiff ℝ 1 g) (hgu : ∀ x, (g x)ᴴ * g x = 1)
    {e : ℝ → Fin 3 → ℝ} (he : ContDiff ℝ 1 e) {t₁ t₂ : ℝ} (h : t₁ ≤ t₂) (h₁ : g (e t₁) = 1) (h₂ : g (e t₂) = 1) :
    holonomy (gaugeConn g A) e t₁ t₂ = holonomy A e t₁ t₂ := by
  rw [holonomy_gaugeConn hA hg hgu he h, h₁, h₂, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one]


/-- The holonomy of the zero connection is `1`. -/
theorem holonomy_zero {e : ℝ → Fin 3 → ℝ} (he : ContDiff ℝ 1 e) {t₁ t₂ : ℝ} (h : t₁ ≤ t₂) :
    holonomy (fun _ _ => (0 : Matrix (Fin n) (Fin n) ℂ)) e t₁ t₂ = 1 := by
  have hsol : ∀ τ ∈ Icc t₁ t₂, HasDerivWithinAt (fun _ => (1 : Matrix (Fin n) (Fin n) ℂ))
      (-(transportCoeff (fun _ _ => (0 : Matrix (Fin n) (Fin n) ℂ)) e τ * 1)) (Icc t₁ t₂) τ := fun τ _ =>
    (hasDerivWithinAt_const τ (Icc t₁ t₂) (1 : Matrix (Fin n) (Fin n) ℂ)).congr_deriv
      (by simp [transportCoeff])
  exact transport_eq (fun _ => continuous_const) he hsol rfl t₂ ⟨h, le_rfl⟩

/-- **Trust check: pure gauge connections.** The holonomy of `A = g⁻¹ dg` (the gauge transform of the zero connection)
along any edge is `g(e(t₂))⁻¹ g(e(t₁))`: it depends only on the end points. -/
theorem holonomy_pureGauge {g : (Fin 3 → ℝ) → Matrix (Fin n) (Fin n) ℂ} (hg : ContDiff ℝ 1 g)
    (hgu : ∀ x, (g x)ᴴ * g x = 1) {e : ℝ → Fin 3 → ℝ} (he : ContDiff ℝ 1 e) {t₁ t₂ : ℝ} (h : t₁ ≤ t₂) :
    holonomy (gaugeConn g fun _ _ => 0) e t₁ t₂ = (g (e t₂))ᴴ * g (e t₁) := by
  rw [holonomy_gaugeConn (fun _ => continuous_const) hg hgu he h, holonomy_zero he h, Matrix.mul_one]

end Lightlike.Canonical
