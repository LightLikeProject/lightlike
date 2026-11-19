import Lightlike.Spacetime.PalatiniCoord
import Lightlike.Spacetime.RicciContinuous
import Lightlike.Spacetime.RiemannSymmetry
import Lightlike.Spacetime.EHManifold.DomainDivergence
import Lightlike.Spacetime.LinearODEZero

/-!
# Killing rigidity in coordinates (G1-024)

For a coordinate metric and a smooth covector field `θ` in coordinates:

* `covCo`, `covCo2`: the covariant derivatives `∇_a θ_b` and `∇_a ∇_b θ_c`;
* `covCo2_sub_covCo2`: the Ricci identity `∇_a ∇_b θ_c - ∇_b ∇_a θ_c = -Rᵈ_{cab} θ_d`;
* `covCo2_antisymm`: if `θ` satisfies Killing's equation `∇_a θ_b + ∇_b θ_a = 0` near a point, `∇_a ∇_b θ_c` is
  antisymmetric in `b, c` there;
* `covCo2_killing`: for such `θ`, `∇_a ∇_b θ_c = Rᵈ_{abc} θ_d` (from the Ricci identity at three orderings of the
  indices and the first Bianchi identity): the second derivatives of a Killing field are determined by its value;
  `pd_pd_killing`: the same for the partial derivatives `∂_a ∂_b θ_c`, linear in `θ` and `∂θ`;
* `rigVec`, `rigCoef`, `sum_rigCoef_mul`: `(θ, ∂θ)` as one vector, whose derivatives are linear in it;
* `rigVec_eq_zero_of_segment`: along a segment in the domain, `(θ, ∂θ)` solves a linear ODE with continuous
  coefficients, so it vanishes at the end if it vanishes at the start (`linear_ode_eq_zero`, Gronwall);
* `rigVec_eq_zero_of_isPreconnected`, `eq_of_rigVec_eq`: **Killing rigidity**: on a connected open set a Killing covector
  is determined by its value and first derivatives at one point.

## References

* M. Blau, *Lecture Notes on General Relativity* (version of 15 November 2026,
  http://www.blau.itp.unibe.ch/newlecturesGR.pdf), section 13.2, eqs. (13.5)–(13.8), p. 322, and section 14.1,
  eq. (14.2) and the statement after it, p. 337: `∇_α ∇_β K_γ = Rᵟ_{αβγ} K_δ`, so that "a Killing vector field is
  completely and uniquely determined everywhere by the values of `K_μ(x₀)` and `∇_μ K_ν(x₀)` at a single point".
-/

open Matrix Filter Set
open scoped ContDiff Topology

noncomputable section

namespace Lightlike

variable {n : ℕ}

/-- The covariant derivative `∇_a θ_b = ∂_a θ_b - Γᶜ_{ab} θ_c` of a covector field in coordinates. -/
def covCo (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (θ : (Fin n → ℝ) → Fin n → ℝ) (a b : Fin n)
    (y : Fin n → ℝ) : ℝ :=
  pd a (fun z => θ z b) y - ∑ c, christoffel g c a b y * θ y c

/-- The second covariant derivative `∇_a ∇_b θ_c = ∂_a (∇_b θ_c) - Γᵈ_{ab} ∇_d θ_c - Γᵈ_{ac} ∇_b θ_d`. -/
def covCo2 (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (θ : (Fin n → ℝ) → Fin n → ℝ) (a b c : Fin n)
    (y : Fin n → ℝ) : ℝ :=
  pd a (fun z => covCo g θ b c z) y - ∑ d, christoffel g d a b y * covCo g θ d c y -
    ∑ d, christoffel g d a c y * covCo g θ b d y

/-- The derivative of a differentiable function along `v` is `∑ₐ vₐ ∂ₐ f`. -/
theorem fderiv_eq_sum_pd {f : (Fin n → ℝ) → ℝ} {x : Fin n → ℝ} (v : Fin n → ℝ) :
    fderiv ℝ f x v = ∑ a, v a * pd a f x := by
  conv_lhs => rw [show v = ∑ a, v a • Pi.single a (1 : ℝ) by
    ext i; simp [Finset.sum_apply, Pi.single_apply]]
  rw [map_sum]
  exact Finset.sum_congr rfl fun a _ => by rw [map_smul, smul_eq_mul]; rfl


/-- The value and first partial derivatives of a covector field at `y`, as one vector indexed by
`Fin n ⊕ (Fin n × Fin n)`: `θ_c` and `∂_k θ_e`. -/
def rigVec (θ : (Fin n → ℝ) → Fin n → ℝ) (y : Fin n → ℝ) : Fin n ⊕ (Fin n × Fin n) → ℝ :=
  Sum.elim (fun c => θ y c) (fun p => pd p.1 (fun w => θ w p.2) y)

/-- The coefficients of `∂_a` of `rigVec` in terms of `rigVec`, for a Killing covector (`pd_pd_killing`). -/
def rigCoef (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (a : Fin n) (i j : Fin n ⊕ (Fin n × Fin n))
    (y : Fin n → ℝ) : ℝ :=
  Sum.elim
    (fun c => Sum.elim (fun _ => (0 : ℝ)) (fun p : Fin n × Fin n => if p.1 = a ∧ p.2 = c then (1 : ℝ) else 0) j)
    (fun bc : Fin n × Fin n => Sum.elim
      (fun e => riemann g e a bc.1 bc.2 y + pd a (christoffel g e bc.1 bc.2) y -
        ∑ d, christoffel g d a bc.1 y * christoffel g e d bc.2 y -
        ∑ d, christoffel g d a bc.2 y * christoffel g e bc.1 d y)
      (fun p : Fin n × Fin n => (if p.1 = a then christoffel g p.2 bc.1 bc.2 y else 0) +
        (if p.2 = bc.2 then christoffel g p.1 a bc.1 y else 0) +
        (if p.1 = bc.1 then christoffel g p.2 a bc.2 y else 0)) j) i

section

variable {g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ} {U : Set (Fin n → ℝ)} {θ : (Fin n → ℝ) → Fin n → ℝ}
  {y : Fin n → ℝ}

variable (hg : IsCoordMetric g U) (hgs : ∀ z a b, g z a b = g z b a) (hθ : ∀ c, ContDiffOn ℝ ∞ (fun z => θ z c) U)
  (hy : y ∈ U)
include hg hgs hθ hy

/-- **The Ricci identity for a covector field** in coordinates: `∇_a ∇_b θ_c - ∇_b ∇_a θ_c = -Rᵈ_{cab} θ_d`. -/
theorem covCo2_sub_covCo2 (a b c : Fin n) :
    covCo2 g θ a b c y - covCo2 g θ b a c y = -∑ d, riemann g d c a b y * θ y d := by
  have hdθ : ∀ c, DifferentiableAt ℝ (fun z => θ z c) y := fun c =>
    differentiableAt_of_contDiffOn (hθ c) hg.isOpen hy
  have hdpθ : ∀ k c, DifferentiableAt ℝ (fun z => pd k (fun w => θ w c) z) y := fun k c =>
    differentiableAt_of_contDiffOn (contDiffOn_pd (hθ c) hg.isOpen k) hg.isOpen hy
  have hdΓ : ∀ i j k, DifferentiableAt ℝ (christoffel g i j k) y := fun i j k =>
    differentiableAt_of_contDiffOn (contDiffOn_christoffel hg i j k) hg.isOpen hy
  have hΓ : ∀ l i j, christoffel g l i j y = christoffel g l j i y := fun l i j => christoffel_symm g hgs l i j y
  have hpd : ∀ k b c, pd k (fun z => covCo g θ b c z) y =
      pd k (fun z => pd b (fun w => θ w c) z) y -
        ∑ e, (pd k (christoffel g e b c) y * θ y e + christoffel g e b c y * pd k (fun z => θ z e) y) := by
    intro k b c
    unfold covCo
    rw [pd_sub (f₁ := fun z => pd b (fun w => θ w c) z) (f₂ := fun z => ∑ e, christoffel g e b c z * θ z e)
      (hdpθ b c) (DifferentiableAt.fun_sum fun e _ => (hdΓ e b c).mul (hdθ e)) k,
      pd_sum Finset.univ (f := fun e z => christoffel g e b c z * θ z e) (fun e _ => (hdΓ e b c).mul (hdθ e)) k]
    congr 1
    exact Finset.sum_congr rfl fun e _ => pd_mul (hdΓ e b c) (hdθ e) k
  have hcomm : pd a (fun z => pd b (fun w => θ w c) z) y = pd b (fun z => pd a (fun w => θ w c) z) y :=
    pd_pd_comm (hθ c) hg.isOpen hy a b
  unfold covCo2
  rw [hpd a b c, hpd b a c, hcomm]
  unfold covCo riemann
  simp only [hΓ _ b a, Finset.mul_sum, Finset.sum_mul, mul_sub, sub_mul, Finset.sum_sub_distrib,
    Finset.sum_add_distrib, add_mul]
  have h1 : ∑ x, ∑ i, christoffel g x a c y * (christoffel g i b x y * θ y i) =
      ∑ x, ∑ i, christoffel g x b i y * christoffel g i a c y * θ y x := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  have h2 : ∑ x, ∑ i, christoffel g x b c y * (christoffel g i a x y * θ y i) =
      ∑ x, ∑ i, christoffel g x a i y * christoffel g i b c y * θ y x := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  rw [h1, h2]
  ring

omit hgs in
/-- A covector field satisfying Killing's equation near `y` has a second covariant derivative antisymmetric in its last
two indices at `y`. -/
theorem covCo2_antisymm (hK : ∀ᶠ z in 𝓝 y, ∀ a b, covCo g θ a b z + covCo g θ b a z = 0) (a b c : Fin n) :
    covCo2 g θ a b c y + covCo2 g θ a c b y = 0 := by
  have hdθ : ∀ c, DifferentiableAt ℝ (fun z => θ z c) y := fun c =>
    differentiableAt_of_contDiffOn (hθ c) hg.isOpen hy
  have hdpθ : ∀ k c, DifferentiableAt ℝ (fun z => pd k (fun w => θ w c) z) y := fun k c =>
    differentiableAt_of_contDiffOn (contDiffOn_pd (hθ c) hg.isOpen k) hg.isOpen hy
  have hdΓ : ∀ i j k, DifferentiableAt ℝ (christoffel g i j k) y := fun i j k =>
    differentiableAt_of_contDiffOn (contDiffOn_christoffel hg i j k) hg.isOpen hy
  have hdcov : ∀ b c, DifferentiableAt ℝ (fun z => covCo g θ b c z) y := fun b c =>
    (hdpθ b c).sub (DifferentiableAt.fun_sum fun e _ => (hdΓ e b c).mul (hdθ e))
  have hK0 := hK.self_of_nhds
  have hpd : pd a (fun z => covCo g θ b c z) y + pd a (fun z => covCo g θ c b z) y = 0 := by
    rw [← pd_add (hdcov b c) (hdcov c b)]
    exact pd_eq_zero_of_eventually_eq_zero (hK.mono fun z hz => hz b c) a
  have e1 : ∑ d, christoffel g d a b y * covCo g θ d c y + ∑ d, christoffel g d a b y * covCo g θ c d y = 0 := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_eq_zero fun d _ => by rw [← mul_add, hK0 d c, mul_zero]
  have e2 : ∑ d, christoffel g d a c y * covCo g θ b d y + ∑ d, christoffel g d a c y * covCo g θ d b y = 0 := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_eq_zero fun d _ => by rw [← mul_add, hK0 b d, mul_zero]
  unfold covCo2
  linarith

/-- **The second covariant derivative of a Killing covector** (Blau (13.8)): if `∇_a θ_b + ∇_b θ_a = 0` near `y`, then
`∇_a ∇_b θ_c = Rᵈ_{abc} θ_d` at `y`. -/
theorem covCo2_killing (hK : ∀ᶠ z in 𝓝 y, ∀ a b, covCo g θ a b z + covCo g θ b a z = 0) (a b c : Fin n) :
    covCo2 g θ a b c y = ∑ d, riemann g d a b c y * θ y d := by
  have r1 := covCo2_sub_covCo2 hg hgs hθ hy a b c
  have r2 := covCo2_sub_covCo2 hg hgs hθ hy b c a
  have r3 := covCo2_sub_covCo2 hg hgs hθ hy c a b
  have i1 := covCo2_antisymm hg hθ hy hK a b c
  have i2 := covCo2_antisymm hg hθ hy hK b c a
  have i3 := covCo2_antisymm hg hθ hy hK c a b
  have hb : ∑ d, riemann g d c a b y * θ y d + ∑ d, riemann g d a b c y * θ y d +
      ∑ d, riemann g d b c a y * θ y d = 0 := by
    simp only [← Finset.sum_add_distrib, ← add_mul]
    exact Finset.sum_eq_zero fun d _ => by rw [hg.bianchi_first hy d c a b, zero_mul]
  linarith

omit hgs in
/-- `∂_k (∇_b θ_c) = ∂_k ∂_b θ_c - ∑ₑ (∂_k Γᵉ_{bc} θ_e + Γᵉ_{bc} ∂_k θ_e)`. -/
theorem pd_covCo (k b c : Fin n) :
    pd k (fun z => covCo g θ b c z) y =
      pd k (fun z => pd b (fun w => θ w c) z) y -
        ∑ e, (pd k (christoffel g e b c) y * θ y e + christoffel g e b c y * pd k (fun z => θ z e) y) := by
  have hdθ : ∀ c, DifferentiableAt ℝ (fun z => θ z c) y := fun c =>
    differentiableAt_of_contDiffOn (hθ c) hg.isOpen hy
  have hdpθ : ∀ k c, DifferentiableAt ℝ (fun z => pd k (fun w => θ w c) z) y := fun k c =>
    differentiableAt_of_contDiffOn (contDiffOn_pd (hθ c) hg.isOpen k) hg.isOpen hy
  have hdΓ : ∀ i j k, DifferentiableAt ℝ (christoffel g i j k) y := fun i j k =>
    differentiableAt_of_contDiffOn (contDiffOn_christoffel hg i j k) hg.isOpen hy
  unfold covCo
  rw [pd_sub (f₁ := fun z => pd b (fun w => θ w c) z) (f₂ := fun z => ∑ e, christoffel g e b c z * θ z e)
    (hdpθ b c) (DifferentiableAt.fun_sum fun e _ => (hdΓ e b c).mul (hdθ e)) k,
    pd_sum Finset.univ (f := fun e z => christoffel g e b c z * θ z e) (fun e _ => (hdΓ e b c).mul (hdθ e)) k]
  congr 1
  exact Finset.sum_congr rfl fun e _ => pd_mul (hdΓ e b c) (hdθ e) k

/-- **The second partial derivatives of a Killing covector** in terms of its value and first derivatives:
`∂_a ∂_b θ_c = ∑ₑ (Rᵉ_{abc} + ∂_a Γᵉ_{bc} - Γᵈ_{ab} Γᵉ_{dc} - Γᵈ_{ac} Γᵉ_{bd}) θ_e
+ Γᵉ_{bc} ∂_a θ_e + Γᵈ_{ab} ∂_d θ_c + Γᵈ_{ac} ∂_b θ_d`. -/
theorem pd_pd_killing (hK : ∀ᶠ z in 𝓝 y, ∀ a b, covCo g θ a b z + covCo g θ b a z = 0) (a b c : Fin n) :
    pd a (fun z => pd b (fun w => θ w c) z) y =
      ∑ e, (riemann g e a b c y + pd a (christoffel g e b c) y - ∑ d, christoffel g d a b y * christoffel g e d c y -
          ∑ d, christoffel g d a c y * christoffel g e b d y) * θ y e +
        ∑ e, christoffel g e b c y * pd a (fun z => θ z e) y + ∑ d, christoffel g d a b y * pd d (fun w => θ w c) y +
        ∑ d, christoffel g d a c y * pd b (fun z => θ z d) y := by
  have h := covCo2_killing hg hgs hθ hy hK a b c
  unfold covCo2 at h
  rw [pd_covCo hg hθ hy a b c] at h
  unfold covCo at h
  simp only [mul_sub, Finset.sum_sub_distrib, Finset.mul_sum, sub_mul, add_mul, Finset.sum_add_distrib,
    Finset.sum_mul] at h ⊢
  have s1 : ∑ x, ∑ i, christoffel g x a b y * (christoffel g i x c y * θ y i) =
      ∑ x, ∑ i, christoffel g i a b y * christoffel g x i c y * θ y x := by
    rw [Finset.sum_comm]; exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  have s2 : ∑ x, ∑ i, christoffel g x a c y * (christoffel g i b x y * θ y i) =
      ∑ x, ∑ i, christoffel g i a c y * christoffel g x b i y * θ y x := by
    rw [Finset.sum_comm]; exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  rw [s1, s2] at h
  linarith

/-- **The derivatives of `rigVec` are linear in `rigVec`** for a Killing covector. -/
theorem sum_rigCoef_mul (hK : ∀ᶠ z in 𝓝 y, ∀ a b, covCo g θ a b z + covCo g θ b a z = 0) (a : Fin n)
    (i : Fin n ⊕ (Fin n × Fin n)) :
    ∑ j, rigCoef g a i j y * rigVec θ y j = pd a (fun w => rigVec θ w i) y := by
  rcases i with c | ⟨b, c⟩
  · simp only [rigCoef, rigVec, Sum.elim_inl, Fintype.sum_sum_type, Sum.elim_inr, zero_mul, Finset.sum_const_zero,
      zero_add, Fintype.sum_prod_type, ite_mul, one_mul, zero_mul]
    simp [ite_and, Finset.sum_ite_eq']
  · simp only [rigCoef, rigVec, Sum.elim_inr, Sum.elim_inl, Fintype.sum_sum_type, Fintype.sum_prod_type]
    rw [pd_pd_killing hg hgs hθ hy hK a b c]
    simp only [add_mul, ite_mul, zero_mul, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    simp only [Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    ring

end

section Segment

variable {g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ} {U : Set (Fin n → ℝ)} {θ : (Fin n → ℝ) → Fin n → ℝ}

variable (hg : IsCoordMetric g U) (hgs : ∀ z a b, g z a b = g z b a) (hθ : ∀ c, ContDiffOn ℝ ∞ (fun z => θ z c) U)
include hg hθ

omit hθ in
theorem continuousOn_rigCoef (a : Fin n) (i j : Fin n ⊕ (Fin n × Fin n)) : ContinuousOn (rigCoef g a i j) U := by
  have hΓ : ∀ i j k, ContinuousOn (christoffel g i j k) U := fun i j k => (contDiffOn_christoffel hg i j k).continuousOn
  have hdΓ : ∀ k i j l, ContinuousOn (pd k (christoffel g i j l)) U := fun k i j l =>
    (contDiffOn_pd (contDiffOn_christoffel hg i j l) hg.isOpen k).continuousOn
  rcases i with c | ⟨b, c⟩ <;> rcases j with e | ⟨k, e⟩
  · exact continuousOn_const
  · exact continuousOn_const
  · exact ((((continuousOn_riemann hg e a b c).add (hdΓ a e b c)).sub
      (continuousOn_finsetSum _ fun d _ => (hΓ d a b).mul (hΓ e d c))).sub
      (continuousOn_finsetSum _ fun d _ => (hΓ d a c).mul (hΓ e b d)))
  · refine (((?_ : ContinuousOn (fun y => if k = a then christoffel g e b c y else 0) U).add
      (?_ : ContinuousOn (fun y => if e = c then christoffel g k a b y else 0) U)).add
      (?_ : ContinuousOn (fun y => if k = b then christoffel g e a c y else 0) U)) <;>
      split_ifs <;> first | exact continuousOn_const | exact hΓ _ _ _

theorem differentiableAt_rigVec {y : Fin n → ℝ} (hy : y ∈ U) (i : Fin n ⊕ (Fin n × Fin n)) :
    DifferentiableAt ℝ (fun w => rigVec θ w i) y := by
  rcases i with c | ⟨k, e⟩
  · exact differentiableAt_of_contDiffOn (hθ c) hg.isOpen hy
  · exact differentiableAt_of_contDiffOn (contDiffOn_pd (hθ e) hg.isOpen k) hg.isOpen hy

include hgs in
/-- **Rigidity along a segment**: a Killing covector on `U` whose value and first derivatives vanish at `z` has value
and first derivatives zero at `w`, if the segment from `z` to `w` lies in `U`. -/
theorem rigVec_eq_zero_of_segment (hKU : ∀ z ∈ U, ∀ a b, covCo g θ a b z + covCo g θ b a z = 0) {z w : Fin n → ℝ}
    (hseg : ∀ t ∈ Icc (0 : ℝ) 1, z + t • (w - z) ∈ U) (h0 : rigVec θ z = 0) : rigVec θ w = 0 := by
  set v := w - z with hv
  set γ : ℝ → Fin n → ℝ := fun t => z + t • v with hγdef
  have hγ : ∀ t, HasDerivAt γ v t := fun t =>
    (((hasDerivAt_id t).smul_const v).const_add z).congr_deriv (one_smul ℝ v)
  have hγc : Continuous γ := by fun_prop
  have hK : ∀ y ∈ U, ∀ᶠ z in 𝓝 y, ∀ a b, covCo g θ a b z + covCo g θ b a z = 0 := fun y hy =>
    Filter.mem_of_superset (hg.isOpen.mem_nhds hy) fun z hz => hKU z hz
  set A : Fin n ⊕ (Fin n × Fin n) → Fin n ⊕ (Fin n × Fin n) → ℝ → ℝ :=
    fun i j t => ∑ a, v a * rigCoef g a i j (γ t) with hAdef
  have hA : ∀ i j, ContinuousOn (A i j) (Icc 0 1) := fun i j =>
    continuousOn_finsetSum _ fun a _ => continuousOn_const.mul
      ((continuousOn_rigCoef hg a i j).comp hγc.continuousOn fun t ht => hseg t ht)
  have hF : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt (fun t => rigVec θ (γ t))
      (fun i => ∑ j, A i j t * rigVec θ (γ t) j) t := by
    intro t ht
    refine hasDerivAt_pi.2 fun i => ?_
    have h1 := (differentiableAt_rigVec hg hθ (hseg t ht) i).hasFDerivAt.comp_hasDerivAt t (hγ t)
    refine h1.congr_deriv ?_
    rw [fderiv_eq_sum_pd]
    have h2 : ∀ a, pd a (fun w => rigVec θ w i) (γ t) = ∑ j, rigCoef g a i j (γ t) * rigVec θ (γ t) j := fun a =>
      (sum_rigCoef_mul hg hgs hθ (hseg t ht) (hK _ (hseg t ht)) a i).symm
    simp only [hγdef] at h2 ⊢
    simp only [h2, hAdef, hγdef, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  have h00 : rigVec θ (γ 0) = 0 := by simpa [hγdef] using h0
  have := linear_ode_eq_zero hA hF h00 1 ⟨zero_le_one, le_refl 1⟩
  simpa [hγdef, hv] using this

include hgs in
/-- **Killing rigidity in coordinates** (Blau, after (14.2)): on a connected open set, a covector field satisfying
Killing's equation whose value and first derivatives vanish at one point vanishes, with its first derivatives,
everywhere. -/
theorem rigVec_eq_zero_of_isPreconnected (hU : IsPreconnected U)
    (hKU : ∀ z ∈ U, ∀ a b, covCo g θ a b z + covCo g θ b a z = 0) {z : Fin n → ℝ} (hz : z ∈ U)
    (h0 : rigVec θ z = 0) : ∀ w ∈ U, rigVec θ w = 0 := by
  set S := {w | w ∈ U ∧ rigVec θ w = 0} with hS
  have hSo : IsOpen S := by
    refine Metric.isOpen_iff.2 fun w ⟨hw, hw0⟩ => ?_
    obtain ⟨r, hr, hrU⟩ := Metric.isOpen_iff.1 hg.isOpen w hw
    refine ⟨r, hr, fun w' hw' => ⟨hrU hw', ?_⟩⟩
    refine rigVec_eq_zero_of_segment hg hgs hθ hKU (fun t ht => hrU ?_) hw0
    exact (convex_ball w r).add_smul_sub_mem (Metric.mem_ball_self hr) hw' ht
  have hcl : closure S ∩ U ⊆ S := by
    rintro w ⟨hwc, hw⟩
    refine ⟨hw, funext fun i => ?_⟩
    have hc : ContinuousAt (fun w => rigVec θ w i) w := (differentiableAt_rigVec hg hθ hw i).continuousAt
    have := mem_closure_image hc hwc
    have hsub : (fun w => rigVec θ w i) '' S ⊆ {0} := by
      rintro _ ⟨w', ⟨_, hw'⟩, rfl⟩; simp [hw']
    have := closure_mono hsub this
    simpa using this
  intro w hw
  exact (hU.subset_of_closure_inter_subset hSo ⟨z, hz, hz, h0⟩ hcl hw).2

end Segment

section Determined

variable {g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ} {U : Set (Fin n → ℝ)} {θ₁ θ₂ : (Fin n → ℝ) → Fin n → ℝ}

/-- **A Killing covector is determined by its value and first derivatives at one point** (Blau, after (14.2)): two
covector fields satisfying Killing's equation on a connected open set that agree with their first derivatives at a point
agree everywhere. -/
theorem eq_of_rigVec_eq (hg : IsCoordMetric g U) (hgs : ∀ z a b, g z a b = g z b a)
    (hθ₁ : ∀ c, ContDiffOn ℝ ∞ (fun z => θ₁ z c) U) (hθ₂ : ∀ c, ContDiffOn ℝ ∞ (fun z => θ₂ z c) U)
    (hU : IsPreconnected U) (hK₁ : ∀ z ∈ U, ∀ a b, covCo g θ₁ a b z + covCo g θ₁ b a z = 0)
    (hK₂ : ∀ z ∈ U, ∀ a b, covCo g θ₂ a b z + covCo g θ₂ b a z = 0) {z : Fin n → ℝ} (hz : z ∈ U)
    (h : rigVec θ₁ z = rigVec θ₂ z) : ∀ w ∈ U, θ₁ w = θ₂ w := by
  set θ : (Fin n → ℝ) → Fin n → ℝ := fun y c => θ₁ y c - θ₂ y c with hθdef
  have hθ : ∀ c, ContDiffOn ℝ ∞ (fun z => θ z c) U := fun c => (hθ₁ c).sub (hθ₂ c)
  have hd : ∀ (θ' : (Fin n → ℝ) → Fin n → ℝ), (∀ c, ContDiffOn ℝ ∞ (fun z => θ' z c) U) →
      ∀ y ∈ U, ∀ c, DifferentiableAt ℝ (fun z => θ' z c) y := fun θ' h y hy c =>
    differentiableAt_of_contDiffOn (h c) hg.isOpen hy
  have hpd : ∀ y ∈ U, ∀ k c, pd k (fun w => θ w c) y = pd k (fun w => θ₁ w c) y - pd k (fun w => θ₂ w c) y :=
    fun y hy k c => pd_sub (hd θ₁ hθ₁ y hy c) (hd θ₂ hθ₂ y hy c) k
  have hcov : ∀ y ∈ U, ∀ a b, covCo g θ a b y = covCo g θ₁ a b y - covCo g θ₂ a b y := fun y hy a b => by
    unfold covCo
    rw [hpd y hy a b]
    simp only [hθdef, mul_sub, Finset.sum_sub_distrib]
    ring
  have hK : ∀ z ∈ U, ∀ a b, covCo g θ a b z + covCo g θ b a z = 0 := fun z hz a b => by
    rw [hcov z hz, hcov z hz]; linarith [hK₁ z hz a b, hK₂ z hz a b]
  have h0 : rigVec θ z = 0 := funext fun i => by
    have hi := congrFun h i
    rcases i with c | ⟨k, c⟩
    · simp only [rigVec, Sum.elim_inl] at hi ⊢; simp [hθdef, hi]
    · simp only [rigVec, Sum.elim_inr] at hi ⊢; rw [hpd z hz k c, hi, sub_self]; rfl
  intro w hw
  funext c
  have := congrFun (rigVec_eq_zero_of_isPreconnected hg hgs hθ hU hK hz h0 w hw) (Sum.inl c)
  simp only [rigVec, Sum.elim_inl, hθdef] at this
  simpa [sub_eq_zero] using this

end Determined

end Lightlike
