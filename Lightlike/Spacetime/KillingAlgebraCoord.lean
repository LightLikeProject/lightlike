import Lightlike.Spacetime.KillingRigidityCoord
import Lightlike.Spacetime.ConformalCoord

/-!
# Killing algebras in coordinates (G1-024)

The bridge between the two coordinate forms of Killing's equation used in the library:

* `lowerVec`: the covector `θ_b = g_{bc} Yᶜ` of a vector field;
* `covCo_lowerVec`: `∇_a θ_b = g_{bl} (∂_a Yˡ + Γˡ_{ac} Yᶜ)`, the lowered covariant derivative of `Y`;
* `covCo_lowerVec_add`: `∇_a θ_b + ∇_b θ_a = Yᶜ ∂_c g_{ab} + ∂_a Yˡ g_{lb} + g_{al} ∂_b Yˡ`, the Lie derivative
  `(L_Y g)_{ab}` in coordinates (the form of the Killing hypotheses of `isometric_spaceForm` and
  `flrw_of_killing_algebra` on coordinate vectors), so the rigidity of `KillingRigidityCoord.lean` applies to those fields;
* `lieCo`, `bracketCo`: the coordinate Lie derivative `(L_Y T)_{ab} = Yᶜ ∂_c T_{ab} + ∂_a Yˡ T_{lb} + T_{al} ∂_b Yˡ` of a
  field of bilinear forms and the bracket `[Y, Z]ᶜ = Yᵈ ∂_d Zᶜ - Zᵈ ∂_d Yᶜ` (`lieCo_lowerVec`: `L_Y g` is the covector
  form of Killing's equation);
* `lieCo_bracketCo`: `L_{[Y,Z]} T = L_Y (L_Z T) - L_Z (L_Y T)` for smooth fields;
* `lieCo_bracketCo_eq_zero`: the bracket of two Killing fields is Killing, so the Killing fields on an open set are
  closed under the bracket;
* `eq_sum_of_rigVec_eq_sum`: on a connected open set, a Killing covector whose value and first derivatives at a point
  are a combination of those of other Killing covectors is that combination (rigidity and linearity);
* `pd_eq_of_killing`, `rigVec_eq_sum_of_data`: at a point the first derivatives of a Killing covector are its
  antisymmetric part plus `Γᶜ_{ab} θ_c`, so the data `(θ, ½ (∂_a θ_b - ∂_b θ_a))` at the point determines `rigVec`;
* `lowerVec_bracketCo`: the lowered bracket `[Y, Z]_b = Yᵈ ∇_d Z_b - Zᵈ ∇_d Y_b`.
-/

open Matrix Filter Set
open scoped ContDiff Topology

noncomputable section

namespace Lightlike

variable {n : ℕ}

/-- The covector `θ_b = g_{bc} Yᶜ` of a vector field in coordinates. -/
def lowerVec (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (Y : (Fin n → ℝ) → Fin n → ℝ) (z : Fin n → ℝ)
    (b : Fin n) : ℝ :=
  ∑ c, g z b c * Y z c

section

variable {g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ} {Y : (Fin n → ℝ) → Fin n → ℝ} {y : Fin n → ℝ}

/-- **The covariant derivative of the lowered field** is the lowered covariant derivative:
`∇_a θ_b = g_{bl} (∂_a Yˡ + Γˡ_{ac} Yᶜ)`. -/
theorem covCo_lowerVec (hgs : ∀ z a b, g z a b = g z b a) (hdet : (g y).det ≠ 0)
    (hgd : ∀ a b, DifferentiableAt ℝ (fun z => g z a b) y) (hY : ∀ c, DifferentiableAt ℝ (fun z => Y z c) y)
    (a b : Fin n) :
    covCo g (lowerVec g Y) a b y =
      ∑ l, g y b l * (pd a (fun z => Y z l) y + ∑ c, christoffel g l a c y * Y y c) := by
  unfold covCo lowerVec
  rw [pd_sum Finset.univ (f := fun c z => g z b c * Y z c) (fun c _ => (hgd b c).mul (hY c)) a]
  simp only [fun c => pd_mul (hgd b c) (hY c) a, pd_metric_eq_christoffel hgs hdet a b]
  simp only [add_mul, Finset.sum_mul, Finset.sum_add_distrib, mul_add, Finset.mul_sum]
  have e1 : ∑ c, ∑ l, g y l c * christoffel g l a b y * Y y c = ∑ c, ∑ l, christoffel g c a b y * (g y c l * Y y l) := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by rw [hgs y]; ring
  have e2 : ∑ c, ∑ l, g y b l * christoffel g l a c y * Y y c = ∑ l, ∑ c, g y b l * (christoffel g l a c y * Y y c) := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  rw [e1, e2]
  ring

/-- **Killing's equation for the lowered field is the Lie-derivative form in coordinates**:
`∇_a θ_b + ∇_b θ_a = Yᶜ ∂_c g_{ab} + ∂_a Yˡ g_{lb} + g_{al} ∂_b Yˡ`. -/
theorem covCo_lowerVec_add (hgs : ∀ z a b, g z a b = g z b a) (hdet : (g y).det ≠ 0)
    (hgd : ∀ a b, DifferentiableAt ℝ (fun z => g z a b) y) (hY : ∀ c, DifferentiableAt ℝ (fun z => Y z c) y)
    (a b : Fin n) :
    covCo g (lowerVec g Y) a b y + covCo g (lowerVec g Y) b a y =
      ∑ c, Y y c * pd c (fun z => g z a b) y +
        ∑ l, (pd a (fun z => Y z l) y * g y l b + g y a l * pd b (fun z => Y z l) y) := by
  rw [covCo_lowerVec hgs hdet hgd hY, covCo_lowerVec hgs hdet hgd hY]
  simp only [pd_metric_eq_christoffel hgs hdet _ a b]
  have hΓ : ∀ l i j, christoffel g l i j y = christoffel g l j i y := fun l i j => christoffel_symm g hgs l i j y
  simp only [mul_add, Finset.mul_sum, Finset.sum_add_distrib]
  have e1 : ∑ l, ∑ c, g y b l * (christoffel g l a c y * Y y c) =
      ∑ c, ∑ l, Y y c * (g y l b * christoffel g l c a y) := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun l _ => by rw [hgs y b l, hΓ l a c]; ring
  have e2 : ∑ l, ∑ c, g y a l * (christoffel g l b c y * Y y c) =
      ∑ c, ∑ l, Y y c * (g y a l * christoffel g l c b y) := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun l _ => by rw [hΓ l b c]; ring
  rw [e1, e2]
  have e3 : ∀ l, g y b l * pd a (fun z => Y z l) y = pd a (fun z => Y z l) y * g y l b := fun l => by
    rw [hgs y b l]; ring
  simp only [e3]
  ring

/-- The Lie derivative `(L_Y T)_{ab} = Yᶜ ∂_c T_{ab} + ∂_a Yˡ T_{lb} + T_{al} ∂_b Yˡ` of a field of bilinear forms in
coordinates. -/
def lieCo (T : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (Y : (Fin n → ℝ) → Fin n → ℝ) (y : Fin n → ℝ) :
    Matrix (Fin n) (Fin n) ℝ := fun a b =>
  ∑ c, Y y c * pd c (fun z => T z a b) y +
    ∑ l, (pd a (fun z => Y z l) y * T y l b + T y a l * pd b (fun z => Y z l) y)

/-- The Lie bracket `[Y, Z]ᶜ = Yᵈ ∂_d Zᶜ - Zᵈ ∂_d Yᶜ` of vector fields in coordinates. -/
def bracketCo (Y Z : (Fin n → ℝ) → Fin n → ℝ) (y : Fin n → ℝ) : Fin n → ℝ := fun c =>
  ∑ d, (Y y d * pd d (fun z => Z z c) y - Z y d * pd d (fun z => Y z c) y)

theorem lieCo_lowerVec (hgs : ∀ z a b, g z a b = g z b a) (hdet : (g y).det ≠ 0)
    (hgd : ∀ a b, DifferentiableAt ℝ (fun z => g z a b) y) (hY : ∀ c, DifferentiableAt ℝ (fun z => Y z c) y)
    (a b : Fin n) :
    lieCo g Y y a b = covCo g (lowerVec g Y) a b y + covCo g (lowerVec g Y) b a y :=
  (covCo_lowerVec_add hgs hdet hgd hY a b).symm

end

section Bracket

variable {U : Set (Fin n → ℝ)} {T : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ} {Y Z : (Fin n → ℝ) → Fin n → ℝ}
  {y : Fin n → ℝ}

variable (hU : IsOpen U) (hT : ∀ a b, ContDiffOn ℝ ∞ (fun z => T z a b) U)
  (hY : ∀ c, ContDiffOn ℝ ∞ (fun z => Y z c) U) (hZ : ∀ c, ContDiffOn ℝ ∞ (fun z => Z z c) U) (hy : y ∈ U)

omit hT hZ in
include hU hY hy in
theorem differentiableAt_pd_field (k c : Fin n) : DifferentiableAt ℝ (fun z => pd k (fun w => Y w c) z) y :=
  differentiableAt_of_contDiffOn (contDiffOn_pd (hY c) hU k) hU hy

include hU hT hZ hy in
/-- `∂_c (L_Z T)_{ab}`, expanded. -/
theorem pd_lieCo (c a b : Fin n) :
    pd c (fun z => lieCo T Z z a b) y =
      ∑ d, (pd c (fun z => Z z d) y * pd d (fun z => T z a b) y + Z y d * pd c (fun z => pd d (fun w => T w a b) z) y) +
      ∑ m, (pd c (fun z => pd a (fun w => Z w m) z) y * T y m b + pd a (fun z => Z z m) y * pd c (fun z => T z m b) y +
        (pd c (fun z => T z a m) y * pd b (fun z => Z z m) y + T y a m * pd c (fun z => pd b (fun w => Z w m) z) y)) := by
  have dZ : ∀ m, DifferentiableAt ℝ (fun z => Z z m) y := fun m => differentiableAt_of_contDiffOn (hZ m) hU hy
  have dT : ∀ i j, DifferentiableAt ℝ (fun z => T z i j) y := fun i j => differentiableAt_of_contDiffOn (hT i j) hU hy
  have dpZ : ∀ k m, DifferentiableAt ℝ (fun z => pd k (fun w => Z w m) z) y := fun k m =>
    differentiableAt_of_contDiffOn (contDiffOn_pd (hZ m) hU k) hU hy
  have dpT : ∀ k i j, DifferentiableAt ℝ (fun z => pd k (fun w => T w i j) z) y := fun k i j =>
    differentiableAt_of_contDiffOn (contDiffOn_pd (hT i j) hU k) hU hy
  unfold lieCo
  rw [pd_add (f₁ := fun z => ∑ d, Z z d * pd d (fun w => T w a b) z)
      (f₂ := fun z => ∑ l, (pd a (fun w => Z w l) z * T z l b + T z a l * pd b (fun w => Z w l) z))
      (DifferentiableAt.fun_sum fun d _ => (dZ d).mul (dpT d a b))
      (DifferentiableAt.fun_sum fun l _ => ((dpZ a l).mul (dT l b)).add ((dT a l).mul (dpZ b l))) c,
    pd_sum Finset.univ (f := fun d z => Z z d * pd d (fun w => T w a b) z) (fun d _ => (dZ d).mul (dpT d a b)) c,
    pd_sum Finset.univ (f := fun l z => pd a (fun w => Z w l) z * T z l b + T z a l * pd b (fun w => Z w l) z)
      (fun l _ => ((dpZ a l).mul (dT l b)).add ((dT a l).mul (dpZ b l))) c]
  congr 1
  · exact Finset.sum_congr rfl fun d _ => pd_mul (dZ d) (dpT d a b) c
  · refine Finset.sum_congr rfl fun m _ => ?_
    rw [pd_add (f₁ := fun z => pd a (fun w => Z w m) z * T z m b) (f₂ := fun z => T z a m * pd b (fun w => Z w m) z)
      ((dpZ a m).mul (dT m b)) ((dT a m).mul (dpZ b m)) c,
      pd_mul (f₁ := fun z => pd a (fun w => Z w m) z) (f₂ := fun z => T z m b) (dpZ a m) (dT m b) c,
      pd_mul (f₁ := fun z => T z a m) (f₂ := fun z => pd b (fun w => Z w m) z) (dT a m) (dpZ b m) c]

include hU hY hZ hy in
/-- `∂_a [Y, Z]ˡ`, expanded. -/
theorem pd_bracketCo (a l : Fin n) :
    pd a (fun z => bracketCo Y Z z l) y =
      ∑ d, (pd a (fun z => Y z d) y * pd d (fun z => Z z l) y + Y y d * pd a (fun z => pd d (fun w => Z w l) z) y -
        (pd a (fun z => Z z d) y * pd d (fun z => Y z l) y + Z y d * pd a (fun z => pd d (fun w => Y w l) z) y)) := by
  have dY : ∀ m, DifferentiableAt ℝ (fun z => Y z m) y := fun m => differentiableAt_of_contDiffOn (hY m) hU hy
  have dZ : ∀ m, DifferentiableAt ℝ (fun z => Z z m) y := fun m => differentiableAt_of_contDiffOn (hZ m) hU hy
  have dpY := fun k m => differentiableAt_pd_field hU hY hy k m
  have dpZ := fun k m => differentiableAt_pd_field hU hZ hy k m
  unfold bracketCo
  rw [pd_sum Finset.univ (f := fun d z => Y z d * pd d (fun w => Z w l) z - Z z d * pd d (fun w => Y w l) z)
    (fun d _ => ((dY d).mul (dpZ d l)).sub ((dZ d).mul (dpY d l))) a]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [pd_sub (f₁ := fun z => Y z d * pd d (fun w => Z w l) z) (f₂ := fun z => Z z d * pd d (fun w => Y w l) z)
    ((dY d).mul (dpZ d l)) ((dZ d).mul (dpY d l)) a,
    pd_mul (f₁ := fun z => Y z d) (f₂ := fun z => pd d (fun w => Z w l) z) (dY d) (dpZ d l) a,
    pd_mul (f₁ := fun z => Z z d) (f₂ := fun z => pd d (fun w => Y w l) z) (dZ d) (dpY d l) a]

include hU hT hY hZ hy in
/-- **The Lie derivative of the bracket is the commutator of Lie derivatives**: `L_{[Y,Z]} T = L_Y (L_Z T) - L_Z (L_Y T)`
for a field of bilinear forms in coordinates. -/
theorem lieCo_bracketCo (a b : Fin n) :
    lieCo T (bracketCo Y Z) y a b = lieCo (lieCo T Z) Y y a b - lieCo (lieCo T Y) Z y a b := by
  have hcT : ∀ k m i j, pd k (fun z => pd m (fun w => T w i j) z) y = pd m (fun z => pd k (fun w => T w i j) z) y :=
    fun k m i j => pd_pd_comm (hT i j) hU hy k m
  have hcY : ∀ k m l, pd k (fun z => pd m (fun w => Y w l) z) y = pd m (fun z => pd k (fun w => Y w l) z) y :=
    fun k m l => pd_pd_comm (hY l) hU hy k m
  have hcZ : ∀ k m l, pd k (fun z => pd m (fun w => Z w l) z) y = pd m (fun z => pd k (fun w => Z w l) z) y :=
    fun k m l => pd_pd_comm (hZ l) hU hy k m
  have e1 : lieCo T (bracketCo Y Z) y a b = ∑ c, bracketCo Y Z y c * pd c (fun z => T z a b) y +
      ∑ l, (pd a (fun z => bracketCo Y Z z l) y * T y l b + T y a l * pd b (fun z => bracketCo Y Z z l) y) := rfl
  have e2 : lieCo (lieCo T Z) Y y a b = ∑ c, Y y c * pd c (fun z => lieCo T Z z a b) y +
      ∑ l, (pd a (fun z => Y z l) y * lieCo T Z y l b + lieCo T Z y a l * pd b (fun z => Y z l) y) := rfl
  have e3 : lieCo (lieCo T Y) Z y a b = ∑ c, Z y c * pd c (fun z => lieCo T Y z a b) y +
      ∑ l, (pd a (fun z => Z z l) y * lieCo T Y y l b + lieCo T Y y a l * pd b (fun z => Z z l) y) := rfl
  rw [e1, e2, e3]
  simp only [pd_lieCo hU hT hZ hy, pd_lieCo hU hT hY hy, pd_bracketCo hU hY hZ hy]
  simp only [lieCo, bracketCo]
  simp only [Finset.mul_sum, Finset.sum_mul, mul_add, add_mul, mul_sub, sub_mul, Finset.sum_add_distrib,
    Finset.sum_sub_distrib]
  have sw : ∀ (f g : Fin n → Fin n → ℝ), (∀ x i, f x i = g i x) → ∑ x, ∑ i, f x i = ∑ x, ∑ i, g x i :=
    fun f g h => by rw [Finset.sum_comm]; exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun x _ => h x i
  -- terms of `L_{[Y,Z]} T` against terms of `L_Y L_Z T` and `L_Z L_Y T`
  have hA1 : ∑ x, ∑ i, Y y x * (pd x (fun z ↦ Z z i) y * pd i (fun z ↦ T z a b) y) =
      ∑ x, ∑ i, Y y i * pd i (fun z ↦ Z z x) y * pd x (fun z ↦ T z a b) y := sw _ _ fun x i => by ring
  have hB1 : ∑ x, ∑ i, Z y x * (pd x (fun z ↦ Y z i) y * pd i (fun z ↦ T z a b) y) =
      ∑ x, ∑ i, Z y i * pd i (fun z ↦ Y z x) y * pd x (fun z ↦ T z a b) y := sw _ _ fun x i => by ring
  have hA2 : ∑ x, ∑ i, Y y x * (Z y i * pd x (fun z ↦ pd i (fun z ↦ T z a b) z) y) =
      ∑ x, ∑ i, Z y x * (Y y i * pd x (fun z ↦ pd i (fun z ↦ T z a b) z) y) :=
    sw _ _ fun x i => by rw [hcT x i a b]; ring
  have hA3 : ∑ x, ∑ i, Y y x * (pd x (fun z ↦ pd a (fun w ↦ Z w i) z) y * T y i b) =
      ∑ x, ∑ i, Y y i * pd a (fun z ↦ pd i (fun z ↦ Z z x) z) y * T y x b :=
    sw _ _ fun x i => by rw [hcZ x a i]; ring
  have hB3 : ∑ x, ∑ i, Z y x * (pd x (fun z ↦ pd a (fun w ↦ Y w i) z) y * T y i b) =
      ∑ x, ∑ i, Z y i * pd a (fun z ↦ pd i (fun z ↦ Y z x) z) y * T y x b :=
    sw _ _ fun x i => by rw [hcY x a i]; ring
  have hA4 : ∑ x, ∑ i, Y y x * (pd a (fun w ↦ Z w i) y * pd x (fun z ↦ T z i b) y) =
      ∑ x, ∑ i, pd a (fun z ↦ Z z x) y * (Y y i * pd i (fun z ↦ T z x b) y) := sw _ _ fun x i => by ring
  have hB4 : ∑ x, ∑ i, Z y x * (pd a (fun w ↦ Y w i) y * pd x (fun z ↦ T z i b) y) =
      ∑ x, ∑ i, pd a (fun z ↦ Y z x) y * (Z y i * pd i (fun z ↦ T z x b) y) := sw _ _ fun x i => by ring
  have hA5 : ∑ x, ∑ i, Y y x * (pd x (fun z ↦ T z a i) y * pd b (fun w ↦ Z w i) y) =
      ∑ x, ∑ i, Y y i * pd i (fun z ↦ T z a x) y * pd b (fun z ↦ Z z x) y := sw _ _ fun x i => by ring
  have hB5 : ∑ x, ∑ i, Z y x * (pd x (fun z ↦ T z a i) y * pd b (fun w ↦ Y w i) y) =
      ∑ x, ∑ i, Z y i * pd i (fun z ↦ T z a x) y * pd b (fun z ↦ Y z x) y := sw _ _ fun x i => by ring
  have hA6 : ∑ x, ∑ i, Y y x * (T y a i * pd x (fun z ↦ pd b (fun w ↦ Z w i) z) y) =
      ∑ x, ∑ i, T y a x * (Y y i * pd b (fun z ↦ pd i (fun z ↦ Z z x) z) y) :=
    sw _ _ fun x i => by rw [hcZ x b i]; ring
  have hB6 : ∑ x, ∑ i, Z y x * (T y a i * pd x (fun z ↦ pd b (fun w ↦ Y w i) z) y) =
      ∑ x, ∑ i, T y a x * (Z y i * pd b (fun z ↦ pd i (fun z ↦ Y z x) z) y) :=
    sw _ _ fun x i => by rw [hcY x b i]; ring
  have hA8 : ∑ x, ∑ i, pd a (fun z ↦ Y z x) y * (pd x (fun z ↦ Z z i) y * T y i b) =
      ∑ x, ∑ i, pd a (fun z ↦ Y z i) y * pd i (fun z ↦ Z z x) y * T y x b := sw _ _ fun x i => by ring
  have hB8 : ∑ x, ∑ i, pd a (fun z ↦ Z z x) y * (pd x (fun z ↦ Y z i) y * T y i b) =
      ∑ x, ∑ i, pd a (fun z ↦ Z z i) y * pd i (fun z ↦ Y z x) y * T y x b := sw _ _ fun x i => by ring
  have hA9 : ∑ x, ∑ i, pd a (fun z ↦ Y z x) y * (T y x i * pd b (fun z ↦ Z z i) y) =
      ∑ x, ∑ i, pd a (fun z ↦ Y z i) y * T y i x * pd b (fun z ↦ Z z x) y := sw _ _ fun x i => by ring
  have hB9 : ∑ x, ∑ i, pd a (fun z ↦ Z z x) y * (T y x i * pd b (fun z ↦ Y z i) y) =
      ∑ x, ∑ i, pd a (fun z ↦ Z z i) y * T y i x * pd b (fun z ↦ Y z x) y := sw _ _ fun x i => by ring
  have hA12 : ∑ x, ∑ i, T y a i * pd x (fun z ↦ Z z i) y * pd b (fun z ↦ Y z x) y =
      ∑ x, ∑ i, T y a x * (pd b (fun z ↦ Y z i) y * pd i (fun z ↦ Z z x) y) := sw _ _ fun x i => by ring
  have hB12 : ∑ x, ∑ i, T y a i * pd x (fun z ↦ Y z i) y * pd b (fun z ↦ Z z x) y =
      ∑ x, ∑ i, T y a x * (pd b (fun z ↦ Z z i) y * pd i (fun z ↦ Y z x) y) := sw _ _ fun x i => by ring
  linarith

include hU hT hY hZ hy in
/-- **The bracket of two Killing fields is Killing**, in coordinates: if `L_Y T = 0` and `L_Z T = 0` on `U`, then
`L_{[Y,Z]} T = 0` at every point of `U`. -/
theorem lieCo_bracketCo_eq_zero (hYk : ∀ z ∈ U, lieCo T Y z = 0) (hZk : ∀ z ∈ U, lieCo T Z z = 0) (a b : Fin n) :
    lieCo T (bracketCo Y Z) y a b = 0 := by
  rw [lieCo_bracketCo hU hT hY hZ hy]
  have h0 : ∀ (W : (Fin n → ℝ) → Fin n → ℝ), (∀ z ∈ U, lieCo T W z = 0) → ∀ V : (Fin n → ℝ) → Fin n → ℝ,
      lieCo (lieCo T W) V y a b = 0 := by
    intro W hW V
    have hev : ∀ i j, ∀ᶠ z in 𝓝 y, lieCo T W z i j = 0 := fun i j =>
      Filter.mem_of_superset (hU.mem_nhds hy) fun z hz => by
        show lieCo T W z i j = 0
        rw [hW z hz]; rfl
    simp only [lieCo]
    have hpd : ∀ c i j, pd c (fun z => lieCo T W z i j) y = 0 := fun c i j =>
      pd_eq_zero_of_eventually_eq_zero (hev i j) c
    have hpt : ∀ i j, lieCo T W y i j = 0 := fun i j => by rw [hW y hy]; rfl
    simp only [lieCo] at hpd hpt
    simp [hpd, hpt]
  rw [h0 Z hZk Y, h0 Y hYk Z, sub_zero]

end Bracket

section Combination

variable {g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ} {U : Set (Fin n → ℝ)} {ι : Type*} [Fintype ι]

/-- **A Killing covector whose data at a point is a combination of the data of others is that combination**: on a
connected open set, if `(θ, ∂θ)(z) = Σₑ cₑ (θₑ, ∂θₑ)(z)` for Killing covectors, then `θ = Σₑ cₑ θₑ`. -/
theorem eq_sum_of_rigVec_eq_sum (hg : IsCoordMetric g U) (hgs : ∀ z a b, g z a b = g z b a) (hU : IsPreconnected U)
    {θ : (Fin n → ℝ) → Fin n → ℝ} (θs : ι → (Fin n → ℝ) → Fin n → ℝ)
    (hθ : ∀ c, ContDiffOn ℝ ∞ (fun z => θ z c) U) (hθs : ∀ e c, ContDiffOn ℝ ∞ (fun z => θs e z c) U)
    (hK : ∀ z ∈ U, ∀ a b, covCo g θ a b z + covCo g θ b a z = 0)
    (hKs : ∀ e, ∀ z ∈ U, ∀ a b, covCo g (θs e) a b z + covCo g (θs e) b a z = 0) {z : Fin n → ℝ} (hz : z ∈ U)
    (c : ι → ℝ) (h : rigVec θ z = ∑ e, c e • rigVec (θs e) z) :
    ∀ w ∈ U, θ w = ∑ e, c e • θs e w := by
  set θ' : (Fin n → ℝ) → Fin n → ℝ := fun y k => ∑ e, c e * θs e y k with hθ'
  have hθ'd : ∀ k, ContDiffOn ℝ ∞ (fun z => θ' z k) U := fun k =>
    ContDiffOn.sum fun e _ => contDiffOn_const.mul (hθs e k)
  have hd : ∀ e, ∀ y ∈ U, ∀ k, DifferentiableAt ℝ (fun z => θs e z k) y := fun e y hy k =>
    differentiableAt_of_contDiffOn (hθs e k) hg.isOpen hy
  have hpd : ∀ y ∈ U, ∀ a k, pd a (fun w => θ' w k) y = ∑ e, c e * pd a (fun w => θs e w k) y := by
    intro y hy a k
    rw [hθ', pd_sum Finset.univ (f := fun e w => c e * θs e w k) (fun e _ => (hd e y hy k).const_mul _) a]
    exact Finset.sum_congr rfl fun e _ => pd_const_mul _ (hd e y hy k) a
  have hcov : ∀ y ∈ U, ∀ a b, covCo g θ' a b y = ∑ e, c e * covCo g (θs e) a b y := by
    intro y hy a b
    unfold covCo
    rw [hpd y hy a b]
    simp only [hθ', mul_sub, Finset.mul_sum, Finset.sum_sub_distrib]
    rw [Finset.sum_comm (s := Finset.univ) (t := Finset.univ)]
    congr 1
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  have hK' : ∀ y ∈ U, ∀ a b, covCo g θ' a b y + covCo g θ' b a y = 0 := by
    intro y hy a b
    rw [hcov y hy, hcov y hy, ← Finset.sum_add_distrib]
    exact Finset.sum_eq_zero fun e _ => by rw [← mul_add, hKs e y hy a b, mul_zero]
  have h' : rigVec θ z = rigVec θ' z := by
    rw [h]
    funext i
    rcases i with k | ⟨a, k⟩
    · simp [rigVec, hθ', Finset.sum_apply]
    · simp only [rigVec, Sum.elim_inr, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      rw [hpd z hz a k]
  have := eq_of_rigVec_eq hg hgs hθ hθ'd hU hK hK' hz h'
  intro w hw
  rw [this w hw]
  funext k
  simp [hθ', Finset.sum_apply]

end Combination

section Data

variable {g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ} {θ : (Fin n → ℝ) → Fin n → ℝ} {z : Fin n → ℝ}

/-- **The first derivatives of a Killing covector at a point are its antisymmetric part plus a value term**:
`∂_a θ_b = ½ (∂_a θ_b - ∂_b θ_a) + Γᶜ_{ab} θ_c` when `∇_a θ_b + ∇_b θ_a = 0` (and `Γ` is symmetric). -/
theorem pd_eq_of_killing (hgs : ∀ z a b, g z a b = g z b a)
    (hK : ∀ a b, covCo g θ a b z + covCo g θ b a z = 0) (a b : Fin n) :
    pd a (fun w => θ w b) z =
      (pd a (fun w => θ w b) z - pd b (fun w => θ w a) z) / 2 + ∑ c, christoffel g c a b z * θ z c := by
  have h := hK a b
  unfold covCo at h
  have hs : ∑ c, christoffel g c b a z * θ z c = ∑ c, christoffel g c a b z * θ z c :=
    Finset.sum_congr rfl fun c _ => by rw [christoffel_symm g hgs c b a z]
  rw [hs] at h
  linarith

/-- The data `(θ(z), ½ (∂_a θ_b - ∂_b θ_a)(z))` of a Killing covector determines `rigVec θ z`, linearly: if the data
of `θ` is the combination `Σₑ cₑ` of the data of Killing covectors `θₑ`, so is `rigVec`. -/
theorem rigVec_eq_sum_of_data {ι : Type*} [Fintype ι] (hgs : ∀ z a b, g z a b = g z b a)
    (θs : ι → (Fin n → ℝ) → Fin n → ℝ) (hK : ∀ a b, covCo g θ a b z + covCo g θ b a z = 0)
    (hKs : ∀ e a b, covCo g (θs e) a b z + covCo g (θs e) b a z = 0) (c : ι → ℝ)
    (h0 : ∀ k, θ z k = ∑ e, c e * θs e z k)
    (h1 : ∀ a b, pd a (fun w => θ w b) z - pd b (fun w => θ w a) z =
      ∑ e, c e * (pd a (fun w => θs e w b) z - pd b (fun w => θs e w a) z)) :
    rigVec θ z = ∑ e, c e • rigVec (θs e) z := by
  funext i
  rcases i with k | ⟨a, k⟩
  · simp [rigVec, Finset.sum_apply, h0]
  · simp only [rigVec, Sum.elim_inr, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [pd_eq_of_killing hgs hK a k, h1]
    have hr : ∀ e, c e * pd a (fun w => θs e w k) z = c e * ((pd a (fun w => θs e w k) z -
        pd k (fun w => θs e w a) z) / 2 + ∑ l, christoffel g l a k z * θs e z l) := fun e => by
      conv_lhs => rw [pd_eq_of_killing hgs (hKs e) a k]
    rw [Finset.sum_congr rfl fun e _ => hr e]
    simp only [h0, mul_add, Finset.sum_add_distrib, Finset.sum_div, Finset.mul_sum]
    rw [Finset.sum_comm (s := Finset.univ) (t := Finset.univ) (f := fun l e => christoffel g l a k z * (c e * θs e z l))]
    congr 1
    · exact Finset.sum_congr rfl fun e _ => by ring
    · exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

end Data

section LowerBracket

variable {g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ} {Y Z : (Fin n → ℝ) → Fin n → ℝ} {y : Fin n → ℝ}

/-- **The lowered bracket**: `[Y, Z]_b = Yᵈ ∇_d Z_b - Zᵈ ∇_d Y_b` (the connection is torsion free). -/
theorem lowerVec_bracketCo (hgs : ∀ z a b, g z a b = g z b a) (hdet : (g y).det ≠ 0)
    (hgd : ∀ a b, DifferentiableAt ℝ (fun z => g z a b) y) (hY : ∀ c, DifferentiableAt ℝ (fun z => Y z c) y)
    (hZ : ∀ c, DifferentiableAt ℝ (fun z => Z z c) y) (b : Fin n) :
    lowerVec g (bracketCo Y Z) y b =
      ∑ d, (Y y d * covCo g (lowerVec g Z) d b y - Z y d * covCo g (lowerVec g Y) d b y) := by
  simp only [covCo_lowerVec hgs hdet hgd hY, covCo_lowerVec hgs hdet hgd hZ]
  unfold lowerVec bracketCo
  have hΓ : ∀ l i j, christoffel g l i j y = christoffel g l j i y := fun l i j => christoffel_symm g hgs l i j y
  simp only [mul_add, Finset.mul_sum, mul_sub, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  have sw3 : ∀ f : Fin n → Fin n → Fin n → ℝ, ∑ x, ∑ w, ∑ v, f x w v = ∑ v, ∑ w, ∑ x, f x w v := fun f => by
    calc ∑ x, ∑ w, ∑ v, f x w v = ∑ w, ∑ x, ∑ v, f x w v := Finset.sum_comm
      _ = ∑ w, ∑ v, ∑ x, f x w v := Finset.sum_congr rfl fun w _ => Finset.sum_comm
      _ = ∑ v, ∑ w, ∑ x, f x w v := Finset.sum_comm
  have e1 : ∑ d, ∑ l, ∑ c, Y y d * (g y b l * (christoffel g l d c y * Z y c)) =
      ∑ d, ∑ l, ∑ c, Z y d * (g y b l * (christoffel g l d c y * Y y c)) := by
    rw [sw3]
    exact Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun d _ => by
      rw [hΓ l d c]; ring
  have e2 : ∑ c, ∑ d, g y b c * (Y y d * pd d (fun z => Z z c) y) = ∑ d, ∑ l, Y y d * (g y b l * pd d (fun z => Z z l) y) := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  have e3 : ∑ c, ∑ d, g y b c * (Z y d * pd d (fun z => Y z c) y) = ∑ d, ∑ l, Z y d * (g y b l * pd d (fun z => Y z l) y) := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  rw [e1, e2, e3]
  ring

end LowerBracket

end Lightlike
