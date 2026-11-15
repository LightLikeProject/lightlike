import Mathlib

/-!
# Normal coordinates to fourth order, in two dimensions (RC6b, step 5)

Jet-level algebra behind the expansion of a vertex deficit. A metric jet at a point is a matrix
`g`, its first derivatives `A k i j = ∂_k g_ij` and second derivatives `B k l i j = ∂_k ∂_l g_ij`.
From it we build the Christoffel symbols (`gam`), their derivatives (`dGam`), the scalar curvature
(`jetScalar`, the formula of `Lightlike.scalarCurvature` written on the jet), and the displacement
to normal coordinates `u(w) = w + ½ Γ(w,w) + cub w`.

## Main results

* `deg3`: the cubic terms of the squared distance between `v + w` and `v + w'` cancel against the
  quadratic displacement: `∂_s g(Δ,Δ) = g(Δ, Γ(w',w') - Γ(w,w))`, `s` the midpoint, `Δ = w' - w`.
* `deg4`: the quartic terms agree with those of the displaced Euclidean distance up to the
  curvature term `-(R/6)(|w|²|w'|² - (w·w')²)`.

Checked independently by `scripts/vertex_identity_check.py` (SymPy, numerical evidence).
-/

noncomputable section

namespace Lightlike.CMS
variable {n : ℕ}

/-- `Γ_{k,ij} = ½ (∂_i g_kj + ∂_j g_ki - ∂_k g_ij)` from the first jet `A k i j = ∂_k g_ij`. -/
def gamLow (A : Fin n → Fin n → Fin n → ℝ) (k i j : Fin n) : ℝ := (A i k j + A j k i - A k i j) / 2

/-- The Christoffel symbols `Γ^i_{jk} = g^{im} Γ_{m,jk}` of a jet. -/
def gam (g : Matrix (Fin n) (Fin n) ℝ) (A : Fin n → Fin n → Fin n → ℝ) (i j k : Fin n) : ℝ :=
  ∑ m, g⁻¹ i m * gamLow A m j k

/-- The contraction `Γ(u, v)^i = Γ^i_{jk} u^j v^k`. -/
def chrV (g : Matrix (Fin n) (Fin n) ℝ) (A : Fin n → Fin n → Fin n → ℝ) (u v : Fin n → ℝ) :
    Fin n → ℝ := fun i => ∑ j, ∑ k, gam g A i j k * u j * v k

/-- `∂_l Γ_{m,jk}` from the second jet `B l k i j = ∂_l ∂_k g_ij`. -/
def dGamLow (B : Fin n → Fin n → Fin n → Fin n → ℝ) (l m j k : Fin n) : ℝ :=
  (B l j m k + B l k m j - B l m j k) / 2

/-- The derivative `∂_l Γ^i_{jk}`, using `∂ g⁻¹ = -g⁻¹ (∂ g) g⁻¹`. -/
def dGam (g : Matrix (Fin n) (Fin n) ℝ) (A : Fin n → Fin n → Fin n → ℝ)
    (B : Fin n → Fin n → Fin n → Fin n → ℝ) (l i j k : Fin n) : ℝ :=
  ∑ m, (g⁻¹ i m * dGamLow B l m j k
    - (∑ a, ∑ b, g⁻¹ i a * A l a b * g⁻¹ b m) * gamLow A m j k)

/-- The Riemann tensor `R^ρ_{σμν}` of a jet, in the convention of `Lightlike.riemann`. -/
def jetRiem (g : Matrix (Fin n) (Fin n) ℝ) (A : Fin n → Fin n → Fin n → ℝ)
    (B : Fin n → Fin n → Fin n → Fin n → ℝ) (ρ σ μ ν : Fin n) : ℝ :=
  dGam g A B μ ρ ν σ - dGam g A B ν ρ μ σ +
    ∑ l, (gam g A ρ μ l * gam g A l ν σ - gam g A ρ ν l * gam g A l μ σ)

/-- The scalar curvature `g^{σν} R^ρ_{σρν}` of a jet. -/
def jetScalar (g : Matrix (Fin n) (Fin n) ℝ) (A : Fin n → Fin n → Fin n → ℝ)
    (B : Fin n → Fin n → Fin n → Fin n → ℝ) : ℝ :=
  ∑ σ, ∑ ν, g⁻¹ σ ν * ∑ ρ, jetRiem g A B ρ σ ρ ν

/-- The inner product `u · g v`. -/
def ip (g : Matrix (Fin n) (Fin n) ℝ) (u v : Fin n → ℝ) : ℝ := ∑ i, ∑ j, u i * g i j * v j

/-- The cubic part of the displacement to normal coordinates. -/
def cub (g : Matrix (Fin n) (Fin n) ℝ) (A : Fin n → Fin n → Fin n → ℝ)
    (B : Fin n → Fin n → Fin n → Fin n → ℝ) (w : Fin n → ℝ) (i : Fin n) : ℝ :=
  (1 / 6) * ((∑ j, ∑ k, ∑ l, dGam g A B l i j k * w j * w k * w l)
    + ∑ j, ∑ m, gam g A i j m * w j * chrV g A w w m)

/-- The quartic form `∂_k ∂_l g_ij s^k s^l Δ^i Δ^j`. -/
def quad4 (B : Fin n → Fin n → Fin n → Fin n → ℝ) (s Δ : Fin n → ℝ) : ℝ :=
  ∑ k, ∑ l, ∑ i, ∑ j, s k * s l * B k l i j * Δ i * Δ j

/-- **First-order cancellation** (two dimensions): the cubic part of the squared distance equals the cubic part of the displaced Euclidean distance. -/
theorem deg3 (g : Matrix (Fin 2) (Fin 2) ℝ) (A : Fin 2 → Fin 2 → Fin 2 → ℝ)
    (hg : g.det ≠ 0) (hs : ∀ i j, g i j = g j i) (hA : ∀ k i j, A k i j = A k j i)
    (w w' : Fin 2 → ℝ) :
    ∑ k, ∑ i, ∑ j, ((w k + w' k) / 2) * A k i j * (w' i - w i) * (w' j - w j) =
      ip g (w' - w) (fun i => chrV g A w' w' i - chrV g A w w i) := by
  have h1 : g.det = g 0 0 * g 1 1 - g 0 1 * g 1 0 := Matrix.det_fin_two g
  have h2 : g⁻¹ = (g 0 0 * g 1 1 - g 0 1 * g 1 0)⁻¹ • g.adjugate := by
    rw [Matrix.inv_def, Ring.inverse_eq_inv', h1]
  rw [h1] at hg
  have hA0 := hA 0 1 0; have hA1 := hA 1 1 0
  have hs0 := hs 0 1
  simp [ip, chrV, gam, gamLow, h2, Matrix.adjugate_fin_two, Fin.sum_univ_two]
  have hs1 : g 1 0 = g 0 1 := hs 1 0
  have hg' : g 0 0 * g 1 1 - g 0 1 ^ 2 ≠ 0 := by rw [sq]; nth_rewrite 2 [← hs1]; exact hg
  rw [hs1]
  rw [hA0, hA1]
  field_simp
  ring

set_option maxHeartbeats 8000000 in
/-- **Curvature identity.** The quartic part of the squared distance (midpoint form) equals the quartic part of the displaced Euclidean distance minus `(R/6)(|w|²|w'|² - (w·w')²)`. -/
theorem deg4 (g : Matrix (Fin 2) (Fin 2) ℝ) (A : Fin 2 → Fin 2 → Fin 2 → ℝ)
    (B : Fin 2 → Fin 2 → Fin 2 → Fin 2 → ℝ)
    (hg : g.det ≠ 0) (hs : ∀ i j, g i j = g j i) (hA : ∀ k i j, A k i j = A k j i)
    (hB1 : ∀ k l i j, B k l i j = B k l j i) (hB2 : ∀ k l i j, B k l i j = B l k i j)
    (w w' : Fin 2 → ℝ) :
    (1 / 2) * quad4 B (fun i => (w i + w' i) / 2) (w' - w) + (1 / 24) * quad4 B (w' - w) (w' - w)
        - (1 / 12) * ip g (chrV g A (w' - w) (w' - w)) (chrV g A (w' - w) (w' - w)) =
      (1 / 4) * ip g (fun i => chrV g A w' w' i - chrV g A w w i) (fun i => chrV g A w' w' i - chrV g A w w i)
      + 2 * ip g (w' - w) (fun i => cub g A B w' i - cub g A B w i)
      - (jetScalar g A B / 6) * (ip g w w * ip g w' w' - ip g w w' ^ 2) := by
  have h1 : g.det = g 0 0 * g 1 1 - g 0 1 * g 1 0 := Matrix.det_fin_two g
  have h2 : g⁻¹ = (g 0 0 * g 1 1 - g 0 1 * g 1 0)⁻¹ • g.adjugate := by
    rw [Matrix.inv_def, Ring.inverse_eq_inv', h1]
  rw [h1] at hg
  have hs1 : g 1 0 = g 0 1 := hs 1 0
  have hg' : g 0 0 * g 1 1 - g 0 1 ^ 2 ≠ 0 := by rw [sq]; nth_rewrite 2 [← hs1]; exact hg
  have hA0 := hA 0 1 0; have hA1 := hA 1 1 0
  simp [ip, quad4, cub, chrV, gam, gamLow, dGam, dGamLow, jetScalar, jetRiem, h2,
    Matrix.adjugate_fin_two, Fin.sum_univ_two]
  rw [hs1, hA0, hA1]
  simp only [hB2 1 0, hB1 _ _ 1 0]
  field_simp
  ring
end Lightlike.CMS
end
