import Lightlike.Canonical.Tetrad

/-!
# The Holst action density and the vanishing of the Holst term on the tetrad connection

On a chart `ℝ⁴`, for a tetrad `e` of a metric `g` (`g = eᵀ η e`, `IsTetrad`) and a matrix-valued (Lorentz) connection `ω`
with curvature `F = gaugeCurv ω`, with `f = e⁻¹` (`f^α_I = e^α_I`) and the internal metric `η = diag(−1, 1, 1, 1)`:

* `palatiniDensity e ω = det e · e^α_I e^β_J F_αβ^{IJ}` and `holstStarDensity e ω = det e · e^α_I e^β_J ε^{IJ}_{KL}
  F_αβ^{KL}` (internal indices raised with `η`);
* `holstDensity γ e ω = ½ (palatiniDensity − (1/γ) · ½ holstStarDensity)`: the integrand of Holst's action,
  `S = ½ ∫ e e^α_I e^β_J (F_αβ^{IJ} − α ⋆F_αβ^{IJ})`, `⋆F^{IJ} = ½ ε^{IJ}_{KL} F^{KL}`, with `α = 1/γ` (Holst,
  arXiv:gr-qc/9511026, eq. (1), p. 1, and p. 2: "`α = β⁻¹`" with Barbero's parameter `β = γ`); Ashtekar–Lewandowski,
  arXiv:gr-qc/0404018, eq. (2.6), p. 11, write the same term as `−(1/2kγ) ∫ e^I ∧ e^J ∧ Ω_IJ`.

Results: on the tetrad connection `ω(e)` (`tetradConn`), the Holst term vanishes, `holstStar_tetradConn` (Holst, eq. (4),
p. 2: it equals `ε^{αβγδ} R_{αβγδ}`, zero by `R_{[αβγ]δ} = 0`), here from the first Bianchi identity
`IsCoordMetric.bianchi_first` of `Lightlike/Spacetime/RiemannSymmetry.lean` (the core is `sum_antisymm_bianchi`); the
Palatini term is `det e · R(g)` for a tetrad of `g` (`palatini_tetradConn`); so the Holst density on `ω(e)` is the
Einstein–Hilbert density `½ det e R` for every `γ` (`holstDensity_tetradConn`). Trust check: the Holst term of a constant
rotation connection is `4`, not zero (`holstStar_rotation`).
-/

open Matrix
open scoped ContDiff

noncomputable section

namespace Lightlike.Canonical

/-- **A totally antisymmetric array contracted with an array satisfying the cyclic identity in its last three
indices vanishes**: `Σ D_{μνρτ} W_{ρτμν} = 0`. -/
theorem sum_antisymm_bianchi (D W : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ)
    (h12 : ∀ a b c d, D a b c d = -D b a c d) (h23 : ∀ a b c d, D a b c d = -D a c b d)
    (h34 : ∀ a b c d, D a b c d = -D a b d c)
    (hW : ∀ r t m n, W r t m n + W r m n t + W r n t m = 0) :
    ∑ μ, ∑ ν, ∑ ρ, ∑ τ, D μ ν ρ τ * W ρ τ μ ν = 0 := by
  -- pair exchange: `D_{μνρτ} = D_{ρτμν}` (an even permutation)
  have hpair : ∀ a b c d, D a b c d = D c d a b := fun a b c d => by
    rw [h23, h12, h34, h23, neg_neg, neg_neg]
  -- cyclic permutations of the last three indices are even
  have hcyc : ∀ a b c d, D a b c d = D a c d b := fun a b c d => by
    rw [h23, h34, neg_neg]
  set S := ∑ ρ, ∑ τ, ∑ μ, ∑ ν, D ρ τ μ ν * W ρ τ μ ν with hS
  have h0 : ∑ μ, ∑ ν, ∑ ρ, ∑ τ, D μ ν ρ τ * W ρ τ μ ν = S := by
    calc ∑ μ, ∑ ν, ∑ ρ, ∑ τ, D μ ν ρ τ * W ρ τ μ ν
        = ∑ μ, ∑ ρ, ∑ ν, ∑ τ, D μ ν ρ τ * W ρ τ μ ν := Finset.sum_congr rfl fun μ _ => Finset.sum_comm
      _ = ∑ ρ, ∑ μ, ∑ ν, ∑ τ, D μ ν ρ τ * W ρ τ μ ν := Finset.sum_comm
      _ = ∑ ρ, ∑ μ, ∑ τ, ∑ ν, D μ ν ρ τ * W ρ τ μ ν :=
          Finset.sum_congr rfl fun ρ _ => Finset.sum_congr rfl fun μ _ => Finset.sum_comm
      _ = ∑ ρ, ∑ τ, ∑ μ, ∑ ν, D μ ν ρ τ * W ρ τ μ ν := Finset.sum_congr rfl fun ρ _ => Finset.sum_comm
      _ = S := Finset.sum_congr rfl fun ρ _ => Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl
          fun μ _ => Finset.sum_congr rfl fun ν _ => by rw [hpair μ ν ρ τ]
  have h1 : ∑ ρ, ∑ τ, ∑ μ, ∑ ν, D ρ τ μ ν * W ρ μ ν τ = S := by
    refine Finset.sum_congr rfl fun ρ _ => ?_
    calc ∑ τ, ∑ μ, ∑ ν, D ρ τ μ ν * W ρ μ ν τ
        = ∑ μ, ∑ τ, ∑ ν, D ρ τ μ ν * W ρ μ ν τ := Finset.sum_comm
      _ = ∑ μ, ∑ ν, ∑ τ, D ρ τ μ ν * W ρ μ ν τ := Finset.sum_congr rfl fun μ _ => Finset.sum_comm
      _ = _ := Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun ν _ => Finset.sum_congr rfl
          fun τ _ => by rw [hcyc ρ τ μ ν]
  have h2 : ∑ ρ, ∑ τ, ∑ μ, ∑ ν, D ρ τ μ ν * W ρ ν τ μ = S := by
    refine Finset.sum_congr rfl fun ρ _ => ?_
    calc ∑ τ, ∑ μ, ∑ ν, D ρ τ μ ν * W ρ ν τ μ
        = ∑ τ, ∑ ν, ∑ μ, D ρ τ μ ν * W ρ ν τ μ := Finset.sum_congr rfl fun τ _ => Finset.sum_comm
      _ = ∑ ν, ∑ τ, ∑ μ, D ρ τ μ ν * W ρ ν τ μ := Finset.sum_comm
      _ = _ := Finset.sum_congr rfl fun ν _ => Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl
          fun μ _ => by rw [← hcyc ρ ν τ μ]
  have h3 : 3 * S = 0 := by
    have : ∑ ρ, ∑ τ, ∑ μ, ∑ ν, D ρ τ μ ν * (W ρ τ μ ν + W ρ μ ν τ + W ρ ν τ μ) = 0 := by simp [hW]
    simp only [mul_add, Finset.sum_add_distrib] at this
    rw [h1, h2, ← hS] at this
    linarith
  rw [h0]
  linarith

/-- The Levi-Civita symbol `ε_IJKL` of `ℝ⁴` (`ε_0123 = 1`), as the normalized Vandermonde product of the indices. -/
def eps4 (I J K L : Fin 4) : ℝ :=
  ((J : ℝ) - I) * ((K : ℝ) - I) * ((L : ℝ) - I) * ((K : ℝ) - J) * ((L : ℝ) - J) * ((L : ℝ) - K) / 12

lemma eps4_0123 : eps4 0 1 2 3 = 1 := by norm_num [eps4]

lemma eps4_swap12 (I J K L : Fin 4) : eps4 I J K L = -eps4 J I K L := by unfold eps4; ring
lemma eps4_swap23 (I J K L : Fin 4) : eps4 I J K L = -eps4 I K J L := by unfold eps4; ring
lemma eps4_swap34 (I J K L : Fin 4) : eps4 I J K L = -eps4 I J L K := by unfold eps4; ring

/-- The internal Minkowski metric `η = diag(−1, 1, 1, 1)` (`Lightlike.eta 4`). -/
abbrev etaI : Matrix (Fin 4) (Fin 4) ℝ := Lightlike.eta 4

/-- The Holst (dual) term `det e · e^α_I e^β_J ε^{IJ}_{KL} F_αβ^{KL}` of a Lorentz connection `ω` (internal indices
raised with `η`; `e^α_I` the inverse tetrad). -/
def holstStarDensity (e : (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ)
    (om : (Fin 4 → ℝ) → Fin 4 → Matrix (Fin 4) (Fin 4) ℝ) (x : Fin 4 → ℝ) : ℝ :=
  (e x).det * ∑ α, ∑ β, ∑ I, ∑ J, ∑ K, ∑ L,
    (e x)⁻¹ α I * (e x)⁻¹ β J * (etaI I I * etaI J J * eps4 I J K L) * (gaugeCurv om x α β * etaI) K L

/-- The Palatini term `det e · e^α_I e^β_J F_αβ^{IJ}`. -/
def palatiniDensity (e : (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ)
    (om : (Fin 4 → ℝ) → Fin 4 → Matrix (Fin 4) (Fin 4) ℝ) (x : Fin 4 → ℝ) : ℝ :=
  (e x).det * ∑ α, ∑ β, ∑ I, ∑ J, (e x)⁻¹ α I * (e x)⁻¹ β J * (gaugeCurv om x α β * etaI) I J

/-- **The Holst action density** `½ e e^α_I e^β_J (F_αβ^{IJ} − (1/γ) ⋆F_αβ^{IJ})`, `⋆F^{IJ} = ½ ε^{IJ}_{KL} F^{KL}`
(Holst (1) with `α = 1/γ`). -/
def holstDensity (γ : ℝ) (e : (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ)
    (om : (Fin 4 → ℝ) → Fin 4 → Matrix (Fin 4) (Fin 4) ℝ) (x : Fin 4 → ℝ) : ℝ :=
  (1 / 2) * (palatiniDensity e om x - (1 / γ) * ((1 / 2) * holstStarDensity e om x))

/-- Moving a pair of summations inside four others. -/
lemma sum_pair_inside (G : Fin 4 → Fin 4 → Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ) :
    ∑ α, ∑ β, ∑ I, ∑ J, ∑ K, ∑ L, G α β I J K L = ∑ I, ∑ J, ∑ K, ∑ L, ∑ α, ∑ β, G α β I J K L := by
  have h1 : ∀ α, ∑ β, ∑ I, ∑ J, ∑ K, ∑ L, G α β I J K L = ∑ I, ∑ J, ∑ K, ∑ L, ∑ β, G α β I J K L := by
    intro α
    rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun I _ => ?_
    rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun J _ => ?_
    rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun K _ => ?_
    rw [Finset.sum_comm]
  simp only [h1]
  rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun I _ => ?_
  rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun J _ => ?_
  rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun K _ => ?_
  rw [Finset.sum_comm]

/-- Exchanging two pairs of summations. -/
lemma sum_swap_pairs (G : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ) :
    ∑ α, ∑ β, ∑ ρ, ∑ σ, G α β ρ σ = ∑ ρ, ∑ σ, ∑ α, ∑ β, G α β ρ σ := by
  have h1 : ∀ α, ∑ β, ∑ ρ, ∑ σ, G α β ρ σ = ∑ ρ, ∑ σ, ∑ β, G α β ρ σ := by
    intro α
    rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun ρ _ => ?_
    rw [Finset.sum_comm]
  simp only [h1]
  rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun ρ _ => ?_
  rw [Finset.sum_comm]

variable {e g : (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ} {U : Set (Fin 4 → ℝ)} {x : Fin 4 → ℝ}

/-- **The Holst term vanishes on the tetrad connection** (Holst (4)): for a frame with smooth entries and nonzero
determinant on `U` and a coordinate metric `g` on `U`, `holstStarDensity e (tetradConn e g) = 0`, from the first Bianchi
identity of `g`. -/
theorem holstStar_tetradConn (hU : IsOpen U) (hx : x ∈ U) (he : ∀ i j, ContDiffOn ℝ ∞ (fun y => e y i j) U)
    (hdet : ∀ y ∈ U, (e y).det ≠ 0) (hg : IsCoordMetric g U) :
    holstStarDensity e (tetradConn e g) x = 0 := by
  set E := e x with hE
  set A := (e x)⁻¹ * etaI with hA
  -- `F_αβ η = E R_αβ A`
  have hF : ∀ α β, gaugeCurv (tetradConn e g) x α β * etaI =
      E * (Matrix.of fun ρ σ => Lightlike.riemann g ρ σ α β x) * A := fun α β => by
    rw [gaugeCurv_tetradConn hU hx he hdet hg, ← riemMat_eq_gaugeCurv, hA, hE]
    simp only [Matrix.mul_assoc]
  have hAe : ∀ α I, (e x)⁻¹ α I * etaI I I = A α I := fun α I => by
    rw [hA, Matrix.mul_apply, Finset.sum_eq_single I]
    · intro M _ hM; simp [Lightlike.eta_apply, hM]
    · simp
  -- the frame components `T_{Kpqr} = Σ E_Kρ A_σp A_αq A_βr R^ρ_{σαβ}`
  set T : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ := fun K p q r =>
    ∑ ρ, ∑ σ, ∑ α, ∑ β, E K ρ * A σ p * A α q * A β r * Lightlike.riemann g ρ σ α β x with hT
  have hsum : holstStarDensity e (tetradConn e g) x = E.det * ∑ I, ∑ J, ∑ K, ∑ L, eps4 I J K L * T K L I J := by
    unfold holstStarDensity
    congr 1
    have hpt : ∀ α β I J K L, (e x)⁻¹ α I * (e x)⁻¹ β J * (etaI I I * etaI J J * eps4 I J K L) *
        (gaugeCurv (tetradConn e g) x α β * etaI) K L =
        eps4 I J K L * (A α I * A β J * ∑ σ, ∑ ρ, E K ρ * Lightlike.riemann g ρ σ α β x * A σ L) := by
      intro α β I J K L
      rw [hF, ← hAe α I, ← hAe β J]
      simp only [Matrix.mul_apply, Matrix.of_apply, Finset.sum_mul]
      ring
    simp only [hpt]
    rw [sum_pair_inside]
    refine Finset.sum_congr rfl fun I _ => Finset.sum_congr rfl fun J _ => Finset.sum_congr rfl fun K _ =>
      Finset.sum_congr rfl fun L _ => ?_
    simp only [← Finset.mul_sum]
    congr 1
    rw [hT]
    simp only [Finset.mul_sum]
    rw [sum_swap_pairs, Finset.sum_comm]
    refine Finset.sum_congr rfl fun ρ _ => Finset.sum_congr rfl fun σ _ => Finset.sum_congr rfl fun α _ =>
      Finset.sum_congr rfl fun β _ => ?_
    ring
  -- the cyclic identity of `T` in its last three indices, from the first Bianchi identity
  have hTb : ∀ K p q r, T K p q r + T K q r p + T K r p q = 0 := by
    intro K p q r
    have r1 : ∀ ρ, ∑ σ, ∑ α, ∑ β, E K ρ * A σ q * A α r * A β p * Lightlike.riemann g ρ σ α β x =
        ∑ σ, ∑ α, ∑ β, E K ρ * A σ p * A α q * A β r * Lightlike.riemann g ρ α β σ x := by
      intro ρ
      calc ∑ a, ∑ b, ∑ c, E K ρ * A a q * A b r * A c p * Lightlike.riemann g ρ a b c x
          = ∑ a, ∑ c, ∑ b, E K ρ * A a q * A b r * A c p * Lightlike.riemann g ρ a b c x :=
            Finset.sum_congr rfl fun a _ => Finset.sum_comm
        _ = ∑ c, ∑ a, ∑ b, E K ρ * A a q * A b r * A c p * Lightlike.riemann g ρ a b c x := Finset.sum_comm
        _ = _ := Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl
            fun b _ => by ring
    have r2 : ∀ ρ, ∑ σ, ∑ α, ∑ β, E K ρ * A σ r * A α p * A β q * Lightlike.riemann g ρ σ α β x =
        ∑ σ, ∑ α, ∑ β, E K ρ * A σ p * A α q * A β r * Lightlike.riemann g ρ β σ α x := by
      intro ρ
      calc ∑ a, ∑ b, ∑ c, E K ρ * A a r * A b p * A c q * Lightlike.riemann g ρ a b c x
          = ∑ b, ∑ a, ∑ c, E K ρ * A a r * A b p * A c q * Lightlike.riemann g ρ a b c x := Finset.sum_comm
        _ = ∑ b, ∑ c, ∑ a, E K ρ * A a r * A b p * A c q * Lightlike.riemann g ρ a b c x :=
            Finset.sum_congr rfl fun b _ => Finset.sum_comm
        _ = _ := Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl
            fun a _ => by ring
    simp only [hT]
    rw [Finset.sum_congr rfl fun ρ _ => r1 ρ, Finset.sum_congr rfl fun ρ _ => r2 ρ, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun ρ _ => ?_
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun σ _ => ?_
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun α _ => ?_
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun β _ => ?_
    have hb := hg.bianchi_first hx ρ σ α β
    linear_combination (E K ρ * A σ p * A α q * A β r) * hb
  rw [hsum, sum_antisymm_bianchi eps4 T eps4_swap12 eps4_swap23 eps4_swap34 hTb, mul_zero]

/-- `e` is a **tetrad of `g` on `U`**: `g = eᵀ η e` there (`g_μν = η_IJ e^I_μ e^J_ν`, Ashtekar–Lewandowski, p. 10,
after eq. (2.1)). -/
def IsTetrad (e g : (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ) (U : Set (Fin 4 → ℝ)) : Prop :=
  ∀ y ∈ U, (e y)ᵀ * etaI * e y = g y

/-- The inverse metric of a tetrad: `g⁻¹ = e⁻¹ η e⁻ᵀ`. -/
lemma inv_metric_of_tetrad (hT : IsTetrad e g U) (hx : x ∈ U) (hdet : (e x).det ≠ 0) :
    (e x)⁻¹ * etaI * ((e x)⁻¹)ᵀ = (g x)⁻¹ := by
  have hu : IsUnit (e x).det := isUnit_iff_ne_zero.2 hdet
  have huT : IsUnit (e x)ᵀ.det := by rw [Matrix.det_transpose]; exact hu
  rw [← hT x hx, Matrix.mul_inv_rev, Matrix.mul_inv_rev, Lightlike.eta_inv, Matrix.transpose_nonsing_inv,
    Matrix.mul_assoc]

/-- **The Palatini term on the tetrad connection is the Einstein–Hilbert density**: `det e · R(g)`. -/
theorem palatini_tetradConn (hU : IsOpen U) (hx : x ∈ U) (he : ∀ i j, ContDiffOn ℝ ∞ (fun y => e y i j) U)
    (hdet : ∀ y ∈ U, (e y).det ≠ 0) (hg : IsCoordMetric g U) (hT : IsTetrad e g U) :
    palatiniDensity e (tetradConn e g) x = (e x).det * Lightlike.scalarCurvature g x := by
  have hu : IsUnit (e x).det := isUnit_iff_ne_zero.2 (hdet x hx)
  have hfe : (e x)⁻¹ * e x = 1 := nonsing_inv_mul _ hu
  have hgi := inv_metric_of_tetrad hT hx (hdet x hx)
  set Rm : Fin 4 → Fin 4 → Matrix (Fin 4) (Fin 4) ℝ := fun α β => Matrix.of fun ρ σ => Lightlike.riemann g ρ σ α β x
    with hRm
  have hF : ∀ α β, gaugeCurv (tetradConn e g) x α β * etaI = e x * Rm α β * ((e x)⁻¹ * etaI) := fun α β => by
    rw [gaugeCurv_tetradConn hU hx he hdet hg, ← riemMat_eq_gaugeCurv]
    simp only [hRm, Matrix.mul_assoc]
  -- `Σ_IJ f_αI f_βJ M_IJ = (f M fᵀ)_αβ`
  have hcontr : ∀ (M : Matrix (Fin 4) (Fin 4) ℝ) (α β : Fin 4),
      ∑ I, ∑ J, (e x)⁻¹ α I * (e x)⁻¹ β J * M I J = ((e x)⁻¹ * M * ((e x)⁻¹)ᵀ) α β := by
    intro M α β
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun J _ => Finset.sum_congr rfl fun I _ => by ring
  have hM : ∀ α β, (e x)⁻¹ * (e x * Rm α β * ((e x)⁻¹ * etaI)) * ((e x)⁻¹)ᵀ = Rm α β * (g x)⁻¹ := by
    intro α β
    rw [← hgi]
    simp only [← Matrix.mul_assoc, hfe, Matrix.one_mul]
  unfold palatiniDensity
  congr 1
  simp only [hF, hcontr, hM]
  unfold Lightlike.scalarCurvature Lightlike.ricci
  simp only [hRm, Matrix.mul_apply, Matrix.of_apply, Finset.mul_sum]
  -- `Σ_α Σ_β Σ_σ R^α_{σαβ} g^{σβ} = Σ_σ Σ_β g^{σβ} Σ_α R^α_{σαβ}`
  calc ∑ α, ∑ β, ∑ σ, Lightlike.riemann g α σ α β x * (g x)⁻¹ σ β
      = ∑ α, ∑ σ, ∑ β, Lightlike.riemann g α σ α β x * (g x)⁻¹ σ β :=
        Finset.sum_congr rfl fun α _ => Finset.sum_comm
    _ = ∑ σ, ∑ α, ∑ β, Lightlike.riemann g α σ α β x * (g x)⁻¹ σ β := Finset.sum_comm
    _ = ∑ σ, ∑ β, ∑ α, Lightlike.riemann g α σ α β x * (g x)⁻¹ σ β :=
        Finset.sum_congr rfl fun σ _ => Finset.sum_comm
    _ = _ := Finset.sum_congr rfl fun σ _ => Finset.sum_congr rfl fun β _ => Finset.sum_congr rfl
        fun α _ => by ring

/-- **On the tetrad connection the Holst action density is the Einstein–Hilbert density** `½ det e · R(g)`, for every
Barbero–Immirzi parameter `γ`: the Holst term does not change the action on the solutions of the connection equation
(Holst, the discussion of eq. (4), p. 2; Ashtekar–Lewandowski, p. 11). -/
theorem holstDensity_tetradConn (γ : ℝ) (hU : IsOpen U) (hx : x ∈ U)
    (he : ∀ i j, ContDiffOn ℝ ∞ (fun y => e y i j) U) (hdet : ∀ y ∈ U, (e y).det ≠ 0) (hg : IsCoordMetric g U)
    (hT : IsTetrad e g U) :
    holstDensity γ e (tetradConn e g) x = (1 / 2) * ((e x).det * Lightlike.scalarCurvature g x) := by
  unfold holstDensity
  rw [palatini_tetradConn hU hx he hdet hg hT, holstStar_tetradConn hU hx he hdet hg]
  ring

/-- The rotation generators `L₁₂ = E₁₂ − E₂₁` and `L₁₃ = E₁₃ − E₃₁` of `so(3) ⊂ so(1, 3)`. -/
def rotL12 : Matrix (Fin 4) (Fin 4) ℝ := Matrix.single 1 2 1 - Matrix.single 2 1 1
def rotL13 : Matrix (Fin 4) (Fin 4) ℝ := Matrix.single 1 3 1 - Matrix.single 3 1 1

/-- **Trust check: the Holst term is not identically zero.** For the flat frame and the constant connection
`ω_0 = L₁₂`, `ω_1 = L₁₃` (curvature `F_01 = [L₁₂, L₁₃] = E₃₂ − E₂₃`), the Holst term is `4`. -/
theorem holstStar_rotation (x : Fin 4 → ℝ) :
    holstStarDensity (fun _ => 1)
      (fun _ μ => if μ = 0 then rotL12 else if μ = 1 then rotL13 else 0) x = 4 := by
  have hpd : ∀ (μ ν : Fin 4), pdMat μ (fun _ : Fin 4 → ℝ =>
      (if ν = 0 then rotL12 else if ν = 1 then rotL13 else (0 : Matrix (Fin 4) (Fin 4) ℝ))) x = 0 := fun μ ν => by
    ext i j; simp [pdMat, Lightlike.pd_const]
  unfold holstStarDensity gaugeCurv
  simp only [hpd, sub_zero, Matrix.det_one, inv_one, one_mul]
  simp [Fin.sum_univ_four, Matrix.mul_apply, Lightlike.eta_apply, Lightlike.etaDiag, eps4, rotL12, rotL13,
    Matrix.single_apply, Matrix.one_apply]
  norm_num

end Lightlike.Canonical
