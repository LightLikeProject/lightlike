import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.SpecialFunctions.Exponential

/-!
# Gibbs states in infinite dimension satisfy the KMS condition

J. Panangaden, *Energy Full Counting Statistics in Return-to-Equilibrium*, arXiv:2110.01678 (read): Proposition 5.4, p. 43
(the Gibbs state `ω(A) = tr(e^{-βH} A)/tr(e^{-βH})` satisfies `ω(A τ^{iβ}(B)) = ω(BA)` for `τᵗ(A) = e^{itH} A e^{-itH}`,
"as long as the Gibbs state exists, even if `H` is not finite-dimensional"), Remark 5.1 (the boundary form
`F_{A,B}(t + iβ) = ω(τᵗ(B) A)` of `F_{A,B}(z) = ω(A τᶻ(B))` on the strip `0 ≤ Im z ≤ β`), Definition 5.8, p. 46 and
Proposition 5.9, p. 47 (a `(τ, β)`-KMS state has, for all `A`, `B`, a function `F_{A,B}` bounded and continuous on the
closed strip, analytic inside, with `F_{A,B}(t) = ω(A τᵗ(B))` and `F_{A,B}(t + iβ) = ω(τᵗ(B) A)`).

Here `H` is the self-adjoint operator `H x = ∑ₙ λₙ ⟪bₙ, x⟫ bₙ` of a Hilbert basis `b` and real eigenvalues `λ` (on its
natural domain `{x | ∑ₙ λₙ² |⟪bₙ, x⟫|² < ∞}`), with `∑ₙ e^{-βλₙ} < ∞`: then `e^{-βH}` is trace class, so compact and
self-adjoint, and every such `H` has this form (G. Teschl, *Mathematical Methods in Quantum Mechanics*, Theorem 6.6,
p. 136). `e^{itH}` is the diagonal unitary `diag(e^{itλₙ})`.

* `evol b λ t`: `e^{itH}`; `dyn b λ t A = e^{itH} A e^{-itH}`;
* `gibbs b λ β A = (∑ₙ e^{-βλₙ} ⟪bₙ, A bₙ⟫) / Z`, the Gibbs state (the trace of `e^{-βH} A` in the eigenbasis), a state
  (`gibbs_one`, `gibbs_star_mul_self_nonneg`) invariant under the dynamics (`gibbs_dyn`);
* `kmsFun b λ β A B z`, and `continuousOn_kmsFun`, `differentiableOn_kmsFun`, `norm_kmsFun_le`, `kmsFun_ofReal`,
  `kmsFun_add_I_mul`: the KMS condition in the strip form of Proposition 5.9.
-/

open scoped InnerProductSpace ComplexConjugate

namespace Lightlike.OperatorAlgebras.GibbsKMS

variable {ι : Type*}

/-! ### Diagonal operators -/

lemma memℓp_mul {w : ι → ℂ} (hw : ∀ n, ‖w n‖ ≤ 1) (x : lp (fun _ : ι => ℂ) 2) :
    Memℓp (fun n => w n * x n) 2 := by
  have hx := lp.memℓp x
  rw [memℓp_gen_iff (by norm_num)] at hx ⊢
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) hx
  rw [norm_mul, Real.mul_rpow (norm_nonneg _) (norm_nonneg _)]
  exact mul_le_of_le_one_left (by positivity) (Real.rpow_le_one (norm_nonneg _) (hw n) (by norm_num))

/-- Multiplication by a sequence `w` with `‖wₙ‖ ≤ 1` on `ℓ²(ι)`. -/
noncomputable def mulOp (w : ι → ℂ) (hw : ∀ n, ‖w n‖ ≤ 1) : lp (fun _ : ι => ℂ) 2 →L[ℂ] lp (fun _ : ι => ℂ) 2 :=
  LinearMap.mkContinuous
    { toFun := fun x => ⟨fun n => w n * x n, memℓp_mul hw x⟩
      map_add' := fun x y => by ext n; simp [mul_add, Pi.add_apply]; rfl
      map_smul' := fun c x => by ext n; simp [mul_left_comm] } 1
    (fun x => by
      rw [one_mul]
      refine lp.norm_le_of_forall_sum_le (by norm_num : (0 : ℝ) < (2 : ENNReal).toReal) (norm_nonneg x) fun s => ?_
      refine le_trans (Finset.sum_le_sum fun n _ => ?_) (lp.sum_rpow_le_norm_rpow (by norm_num) x s)
      show ‖w n * x n‖ ^ (2 : ENNReal).toReal ≤ ‖x n‖ ^ (2 : ENNReal).toReal
      rw [norm_mul, Real.mul_rpow (norm_nonneg _) (norm_nonneg _)]
      exact mul_le_of_le_one_left (by positivity) (Real.rpow_le_one (norm_nonneg _) (hw n) (by norm_num)))

lemma mulOp_apply (w : ι → ℂ) (hw : ∀ n, ‖w n‖ ≤ 1) (x : lp (fun _ : ι => ℂ) 2) (n : ι) :
    mulOp w hw x n = w n * x n := rfl

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (b : HilbertBasis ι ℂ H)

/-- **The diagonal operator** `x ↦ ∑ₙ wₙ ⟪bₙ, x⟫ bₙ` of a Hilbert basis `b` and a sequence with `‖wₙ‖ ≤ 1`. -/
noncomputable def diag (w : ι → ℂ) (hw : ∀ n, ‖w n‖ ≤ 1) : H →L[ℂ] H :=
  (b.repr.symm.toContinuousLinearEquiv : lp (fun _ : ι => ℂ) 2 →L[ℂ] H) ∘L mulOp w hw ∘L
    (b.repr.toContinuousLinearEquiv : H →L[ℂ] lp (fun _ : ι => ℂ) 2)

lemma repr_diag (w : ι → ℂ) (hw : ∀ n, ‖w n‖ ≤ 1) (x : H) (n : ι) :
    b.repr (diag b w hw x) n = w n * b.repr x n := by
  simp [diag, mulOp_apply]

/-- `⟪bₘ, D x⟫ = wₘ ⟪bₘ, x⟫`. -/
lemma inner_basis_diag (w : ι → ℂ) (hw : ∀ n, ‖w n‖ ≤ 1) (m : ι) (x : H) :
    ⟪b m, diag b w hw x⟫_ℂ = w m * ⟪b m, x⟫_ℂ := by
  rw [← HilbertBasis.repr_apply_apply, ← HilbertBasis.repr_apply_apply, repr_diag]

/-- `D bₘ = wₘ bₘ`. -/
lemma diag_basis (w : ι → ℂ) (hw : ∀ n, ‖w n‖ ≤ 1) (m : ι) : diag b w hw (b m) = w m • b m := by
  classical
  refine b.repr.injective ?_
  ext n
  rw [repr_diag, map_smul, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, b.repr_self]
  by_cases h : n = m
  · subst h; simp
  · simp [lp.single_apply, h]

/-! ### The Hamiltonian on its natural domain, and the dynamics `τᵗ(A) = e^{itH} A e^{-itH}` -/

variable (ev : ι → ℝ)

/-- **The natural domain** `{x | ∑ₙ λₙ² |⟪bₙ, x⟫|² < ∞}` of `H x = ∑ₙ λₙ ⟪bₙ, x⟫ bₙ`. -/
def domain : Submodule ℂ H where
  carrier := {x | Memℓp (fun n => (ev n : ℂ) * b.repr x n) 2}
  add_mem' {x y} hx hy := by
    simp only [Set.mem_ofPred_eq, map_add, lp.coeFn_add, Pi.add_apply, mul_add] at hx hy ⊢
    exact hx.add hy
  zero_mem' := by
    show Memℓp (fun n => (ev n : ℂ) * b.repr (0 : H) n) 2
    simp only [map_zero, lp.coeFn_zero, Pi.zero_apply, mul_zero]
    exact zero_memℓp
  smul_mem' c x hx := by
    show Memℓp (fun n => (ev n : ℂ) * b.repr (c • x) n) 2
    have hx' : Memℓp (fun n => (ev n : ℂ) * b.repr x n) 2 := hx
    have h : (fun n => (ev n : ℂ) * b.repr (c • x) n) = c • fun n => (ev n : ℂ) * b.repr x n := by
      funext n
      rw [map_smul, lp.coeFn_smul, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul]
      ring
    rw [h]
    exact hx'.const_smul c

/-- **The Hamiltonian** `H x = ∑ₙ λₙ ⟪bₙ, x⟫ bₙ` on its natural domain: the self-adjoint operator of the Hilbert basis `b`
with eigenvalues `λ`. -/
noncomputable def hamiltonian : domain b ev →ₗ[ℂ] H where
  toFun x := b.repr.symm ⟨fun n => (ev n : ℂ) * b.repr x n, x.2⟩
  map_add' x y := by
    rw [← map_add]; congr 1; ext n
    show (ev n : ℂ) * b.repr ((x : H) + y) n = (ev n : ℂ) * b.repr x n + (ev n : ℂ) * b.repr y n
    rw [map_add, lp.coeFn_add, Pi.add_apply, mul_add]
  map_smul' c x := by
    rw [RingHom.id_apply, ← map_smul]; congr 1; ext n
    show (ev n : ℂ) * b.repr (c • (x : H)) n = c * ((ev n : ℂ) * b.repr x n)
    rw [map_smul, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
    ring

/-- `⟪bₘ, H x⟫ = λₘ ⟪bₘ, x⟫`. -/
lemma inner_basis_hamiltonian (x : domain b ev) (m : ι) :
    ⟪b m, hamiltonian b ev x⟫_ℂ = (ev m : ℂ) * ⟪b m, (x : H)⟫_ℂ := by
  rw [← HilbertBasis.repr_apply_apply, ← HilbertBasis.repr_apply_apply, hamiltonian]
  simp

/-- The eigenvectors: `bₘ` is in the domain and `H bₘ = λₘ bₘ`. -/
lemma basis_mem_domain (m : ι) : b m ∈ domain b ev := by
  classical
  show Memℓp (fun n => (ev n : ℂ) * b.repr (b m) n) 2
  have h : (fun n => (ev n : ℂ) * b.repr (b m) n) = (ev m : ℂ) • ⇑(b.repr (b m)) := by
    funext n
    rw [Pi.smul_apply, smul_eq_mul, b.repr_self]
    by_cases hn : n = m
    · subst hn; rfl
    · simp [lp.single_apply, hn]
  rw [h]
  exact (lp.memℓp _).const_smul _

lemma norm_exp_I_mul (t : ℝ) (n : ι) : ‖Complex.exp (Complex.I * t * ev n)‖ ≤ 1 := by
  rw [Complex.norm_exp]
  simp

/-- **`e^{itH}`**, the diagonal unitary `diag(e^{itλₙ})`. -/
noncomputable def evol (t : ℝ) : H →L[ℂ] H :=
  diag b (fun n => Complex.exp (Complex.I * t * ev n)) (norm_exp_I_mul ev t)

/-- **The dynamics** `τᵗ(A) = e^{itH} A e^{-itH}`. -/
noncomputable def dyn (t : ℝ) (A : H →L[ℂ] H) : H →L[ℂ] H := evol b ev t * A * evol b ev (-t)

lemma evol_basis (t : ℝ) (m : ι) : evol b ev t (b m) = Complex.exp (Complex.I * t * ev m) • b m :=
  diag_basis b _ _ m

lemma inner_basis_evol (t : ℝ) (m : ι) (x : H) :
    ⟪b m, evol b ev t x⟫_ℂ = Complex.exp (Complex.I * t * ev m) * ⟪b m, x⟫_ℂ :=
  inner_basis_diag b _ _ m x

/-- **The matrix elements of `τᵗ(B)`**: `⟪bₙ, τᵗ(B) bₘ⟫ = e^{it(λₙ - λₘ)} ⟪bₙ, B bₘ⟫`. -/
lemma inner_dyn (t : ℝ) (B : H →L[ℂ] H) (n m : ι) :
    ⟪b n, dyn b ev t B (b m)⟫_ℂ =
      Complex.exp (Complex.I * t * (ev n - ev m)) * ⟪b n, B (b m)⟫_ℂ := by
  simp only [dyn, ContinuousLinearMap.mul_apply, evol_basis, map_smul, inner_basis_evol, inner_smul_right]
  rw [← mul_assoc, ← Complex.exp_add]
  congr 2
  push_cast; ring

/-! ### The Gibbs state -/

variable {β : ℝ}

/-- The partition function `Z = ∑ₙ e^{-βλₙ}`. -/
noncomputable def partition (β : ℝ) : ℝ := ∑' n, Real.exp (-(β * ev n))

/-- **The Gibbs state** `ω(A) = (∑ₙ e^{-βλₙ} ⟪bₙ, A bₙ⟫) / Z`: the trace of `e^{-βH} A` in the eigenbasis, divided by
`Z = tr e^{-βH}`. -/
noncomputable def gibbs (β : ℝ) (A : H →L[ℂ] H) : ℂ :=
  (∑' n, (Real.exp (-(β * ev n)) : ℂ) * ⟪b n, A (b n)⟫_ℂ) / partition ev β

lemma partition_pos [Nonempty ι] (hZ : Summable fun n => Real.exp (-(β * ev n))) : 0 < partition ev β := by
  obtain ⟨n⟩ := ‹Nonempty ι›
  exact hZ.tsum_pos (fun _ => (Real.exp_pos _).le) n (Real.exp_pos _)

/-- **`ω(1) = 1`.** -/
theorem gibbs_one [Nonempty ι] (hZ : Summable fun n => Real.exp (-(β * ev n))) : gibbs b ev β 1 = 1 := by
  have h1 : ∀ n, (Real.exp (-(β * ev n)) : ℂ) * ⟪b n, (1 : H →L[ℂ] H) (b n)⟫_ℂ = (Real.exp (-(β * ev n)) : ℂ) := by
    intro n
    rw [ContinuousLinearMap.one_apply, inner_self_eq_norm_sq_to_K, b.orthonormal.1 n]
    simp
  rw [gibbs, tsum_congr h1, ← Complex.ofReal_tsum, partition]
  exact div_self (by exact_mod_cast (partition_pos ev hZ).ne')

/-- **`ω(A* A) ≥ 0`**: `ω` is positive. -/
theorem gibbs_star_mul_self_nonneg (A : H →L[ℂ] H) :
    0 ≤ (gibbs b ev β (ContinuousLinearMap.adjoint A * A)).re ∧
      (gibbs b ev β (ContinuousLinearMap.adjoint A * A)).im = 0 := by
  have h1 : ∀ n, (Real.exp (-(β * ev n)) : ℂ) * ⟪b n, (ContinuousLinearMap.adjoint A * A) (b n)⟫_ℂ =
      ((Real.exp (-(β * ev n)) * ‖A (b n)‖ ^ 2 : ℝ) : ℂ) := by
    intro n
    rw [ContinuousLinearMap.mul_apply, ContinuousLinearMap.adjoint_inner_right, inner_self_eq_norm_sq_to_K,
      Complex.ofReal_mul, Complex.ofReal_pow]
    rfl
  rw [gibbs, tsum_congr h1, ← Complex.ofReal_tsum, ← Complex.ofReal_div]
  refine ⟨?_, Complex.ofReal_im _⟩
  rw [Complex.ofReal_re]
  exact div_nonneg (tsum_nonneg fun n => by positivity) (tsum_nonneg fun n => (Real.exp_pos _).le)

/-- **The Gibbs state is invariant**: `ω(τᵗ(A)) = ω(A)`. -/
theorem gibbs_dyn (t : ℝ) (A : H →L[ℂ] H) : gibbs b ev β (dyn b ev t A) = gibbs b ev β A := by
  simp only [gibbs, inner_dyn, sub_self, mul_zero, Complex.exp_zero, one_mul]

/-! ### The KMS function -/

/-- The terms of the KMS function: `e^{-βλₘ} ⟪bₘ, A bₙ⟫ ⟪bₙ, B bₘ⟫ e^{iz(λₙ - λₘ)}`. -/
noncomputable def kmsTerm (β : ℝ) (A B : H →L[ℂ] H) (p : ι × ι) (z : ℂ) : ℂ :=
  (Real.exp (-(β * ev p.1)) : ℂ) * ⟪b p.1, A (b p.2)⟫_ℂ * ⟪b p.2, B (b p.1)⟫_ℂ *
    Complex.exp (Complex.I * z * (ev p.2 - ev p.1))

/-- **The KMS function** `F_{A,B}(z) = ω(A τᶻ(B))`, as the double series `∑ₘₙ kmsTerm / Z`. -/
noncomputable def kmsFun (β : ℝ) (A B : H →L[ℂ] H) (z : ℂ) : ℂ :=
  (∑' p, kmsTerm b ev β A B p z) / partition ev β

/-- The summable majorant `|⟪bₘ, A bₙ⟫| |⟪bₙ, B bₘ⟫| (e^{-βλₘ} + e^{-βλₙ})`. -/
noncomputable def kmsBound (β : ℝ) (A B : H →L[ℂ] H) (p : ι × ι) : ℝ :=
  ‖⟪b p.1, A (b p.2)⟫_ℂ‖ * ‖⟪b p.2, B (b p.1)⟫_ℂ‖ * (Real.exp (-(β * ev p.1)) + Real.exp (-(β * ev p.2)))

/-- The closed strip `0 ≤ Im z ≤ β`. -/
def strip (β : ℝ) : Set ℂ := {z | 0 ≤ z.im ∧ z.im ≤ β}

/-- The open strip `0 < Im z < β`. -/
def openStrip (β : ℝ) : Set ℂ := {z | 0 < z.im ∧ z.im < β}

lemma isOpen_openStrip : IsOpen (openStrip β) :=
  (isOpen_lt continuous_const Complex.continuous_im).inter (isOpen_lt Complex.continuous_im continuous_const)

/-- On the closed strip each term is bounded by the majorant: `e^{-(β - s)λₘ - sλₙ} ≤ e^{-βλₘ} + e^{-βλₙ}`. -/
lemma norm_kmsTerm_le (hβ : 0 < β) (A B : H →L[ℂ] H) (p : ι × ι) {z : ℂ} (hz : z ∈ strip β) :
    ‖kmsTerm b ev β A B p z‖ ≤ kmsBound b ev β A B p := by
  obtain ⟨hz0, hzβ⟩ := hz
  have hexp : ‖Complex.exp (Complex.I * z * (ev p.2 - ev p.1))‖ = Real.exp (-(z.im * (ev p.2 - ev p.1))) := by
    rw [Complex.norm_exp]
    congr 1
    simp [Complex.mul_re]
  rw [kmsTerm, kmsBound, norm_mul, norm_mul, norm_mul, hexp, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
  have key : Real.exp (-(β * ev p.1)) * Real.exp (-(z.im * (ev p.2 - ev p.1))) ≤
      Real.exp (-(β * ev p.1)) + Real.exp (-(β * ev p.2)) := by
    rw [← Real.exp_add]
    -- the exponent `-(β - s) λₘ - s λₙ` lies between `-βλₘ` and `-βλₙ`
    set θ := z.im / β
    have hθ0 : 0 ≤ θ := div_nonneg hz0 hβ.le
    have hθ1 : θ ≤ 1 := (div_le_one hβ).mpr hzβ
    have hs : z.im = θ * β := by simp [θ, div_mul_cancel₀ _ hβ.ne']
    have hx : -(β * ev p.1) + -(z.im * (ev p.2 - ev p.1)) =
        (1 - θ) * (-(β * ev p.1)) + θ * (-(β * ev p.2)) := by rw [hs]; ring
    rw [hx]
    rcases le_total (-(β * ev p.1)) (-(β * ev p.2)) with h | h
    · calc Real.exp ((1 - θ) * (-(β * ev p.1)) + θ * (-(β * ev p.2))) ≤ Real.exp (-(β * ev p.2)) :=
            Real.exp_le_exp.mpr (by nlinarith)
        _ ≤ _ := le_add_of_nonneg_left (Real.exp_pos _).le
    · calc Real.exp ((1 - θ) * (-(β * ev p.1)) + θ * (-(β * ev p.2))) ≤ Real.exp (-(β * ev p.1)) :=
            Real.exp_le_exp.mpr (by nlinarith)
        _ ≤ _ := le_add_of_nonneg_right (Real.exp_pos _).le
  calc Real.exp (-(β * ev p.1)) * ‖⟪b p.1, A (b p.2)⟫_ℂ‖ * ‖⟪b p.2, B (b p.1)⟫_ℂ‖ *
        Real.exp (-(z.im * (ev p.2 - ev p.1)))
      = ‖⟪b p.1, A (b p.2)⟫_ℂ‖ * ‖⟪b p.2, B (b p.1)⟫_ℂ‖ *
        (Real.exp (-(β * ev p.1)) * Real.exp (-(z.im * (ev p.2 - ev p.1)))) := by ring
    _ ≤ _ := by gcongr

/-- **Parseval**: `∑ₙ ‖⟪bₙ, x⟫‖² = ‖x‖²`. -/
lemma hasSum_norm_sq_inner (x : H) : HasSum (fun n => ‖⟪b n, x⟫_ℂ‖ ^ 2) (‖x‖ ^ 2) := by
  have h := b.hasSum_inner_mul_inner x x
  have h' : ∀ n, ⟪x, b n⟫_ℂ * ⟪b n, x⟫_ℂ = ((‖⟪b n, x⟫_ℂ‖ ^ 2 : ℝ) : ℂ) := fun n => by
    rw [← inner_conj_symm x (b n), RCLike.conj_mul]; push_cast; rfl
  simp_rw [h'] at h
  rw [inner_self_eq_norm_sq_to_K] at h
  have h'' : HasSum (fun n => ((‖⟪b n, x⟫_ℂ‖ ^ 2 : ℝ) : ℂ)) ((‖x‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.ofReal_pow]; exact h
  exact Complex.hasSum_ofReal.mp h''

/-- One half of the majorant is summable: `∑ₘₙ |⟪bₘ, A bₙ⟫| |⟪bₙ, B bₘ⟫| e^{-βλₘ} < ∞`, by
`|a| |c| ≤ |a|² + |c|²`, Parseval in `n`, and `∑ₘ e^{-βλₘ} < ∞`. -/
lemma summable_half (hZ : Summable fun n => Real.exp (-(β * ev n))) (A B : H →L[ℂ] H) :
    Summable fun p : ι × ι => ‖⟪b p.1, A (b p.2)⟫_ℂ‖ * ‖⟪b p.2, B (b p.1)⟫_ℂ‖ * Real.exp (-(β * ev p.1)) := by
  set A' := ContinuousLinearMap.adjoint A
  have hrow : ∀ m, HasSum (fun n => ‖⟪b m, A (b n)⟫_ℂ‖ ^ 2) (‖A' (b m)‖ ^ 2) := by
    intro m
    have h := hasSum_norm_sq_inner b (A' (b m))
    refine h.congr_fun fun n => ?_
    rw [← ContinuousLinearMap.adjoint_inner_left, norm_inner_symm]
  have hcol : ∀ m, HasSum (fun n => ‖⟪b n, B (b m)⟫_ℂ‖ ^ 2) (‖B (b m)‖ ^ 2) := fun m => hasSum_norm_sq_inner b _
  -- the dominating family `(|a|² + |c|²) e^{-βλₘ}`
  let g : ι × ι → ℝ := fun p => (‖⟪b p.1, A (b p.2)⟫_ℂ‖ ^ 2 + ‖⟪b p.2, B (b p.1)⟫_ℂ‖ ^ 2) * Real.exp (-(β * ev p.1))
  have hg0 : ∀ p, 0 ≤ g p := fun p => by positivity
  have hg : Summable g := by
    rw [summable_prod_of_nonneg hg0]
    have hrowm : ∀ m, Summable fun n =>
        (‖⟪b m, A (b n)⟫_ℂ‖ ^ 2 + ‖⟪b n, B (b m)⟫_ℂ‖ ^ 2) * Real.exp (-(β * ev m)) :=
      fun m => ((hrow m).summable.add (hcol m).summable).mul_right _
    refine ⟨fun m => hrowm m, ?_⟩
    have heq : (fun m => ∑' n, g (m, n)) = fun m => (‖A' (b m)‖ ^ 2 + ‖B (b m)‖ ^ 2) * Real.exp (-(β * ev m)) := by
      funext m
      simp only [g]
      rw [tsum_mul_right, ((hrow m).add (hcol m)).tsum_eq]
    rw [heq]
    refine Summable.of_nonneg_of_le (fun m => by positivity) (fun m => ?_) (hZ.mul_left (‖A'‖ ^ 2 + ‖B‖ ^ 2))
    have h1 : ‖A' (b m)‖ ≤ ‖A'‖ := by
      simpa [b.orthonormal.1 m] using A'.le_opNorm (b m)
    have h2 : ‖B (b m)‖ ≤ ‖B‖ := by
      simpa [b.orthonormal.1 m] using B.le_opNorm (b m)
    gcongr
  refine Summable.of_nonneg_of_le (fun p => by positivity) (fun p => ?_) hg
  simp only [g]
  have := two_mul_le_add_sq ‖⟪b p.1, A (b p.2)⟫_ℂ‖ ‖⟪b p.2, B (b p.1)⟫_ℂ‖
  have hab : ‖⟪b p.1, A (b p.2)⟫_ℂ‖ * ‖⟪b p.2, B (b p.1)⟫_ℂ‖ ≤
      ‖⟪b p.1, A (b p.2)⟫_ℂ‖ ^ 2 + ‖⟪b p.2, B (b p.1)⟫_ℂ‖ ^ 2 := by
    nlinarith [norm_nonneg ⟪b p.1, A (b p.2)⟫_ℂ, norm_nonneg ⟪b p.2, B (b p.1)⟫_ℂ]
  exact mul_le_mul_of_nonneg_right hab (Real.exp_pos _).le

/-- **The majorant is summable.** -/
lemma summable_kmsBound (hZ : Summable fun n => Real.exp (-(β * ev n))) (A B : H →L[ℂ] H) :
    Summable (kmsBound b ev β A B) := by
  -- the second half is the first half for `(B, A)` with the two indices exchanged
  have h1 := summable_half b ev hZ A B
  have h2 := summable_half b ev hZ B A
  have h2' : Summable fun p : ι × ι =>
      ‖⟪b p.1, A (b p.2)⟫_ℂ‖ * ‖⟪b p.2, B (b p.1)⟫_ℂ‖ * Real.exp (-(β * ev p.2)) := by
    have := (Equiv.prodComm ι ι).summable_iff.mpr h2
    refine this.congr fun p => ?_
    simp only [Function.comp_apply, Equiv.prodComm_apply, Prod.fst_swap, Prod.snd_swap]
    ring
  refine (h1.add h2').congr fun p => ?_
  simp only [kmsBound]
  ring

lemma continuous_kmsTerm (A B : H →L[ℂ] H) (p : ι × ι) : Continuous (kmsTerm b ev β A B p) := by
  unfold kmsTerm; fun_prop

lemma differentiable_kmsTerm (A B : H →L[ℂ] H) (p : ι × ι) : Differentiable ℂ (kmsTerm b ev β A B p) := by
  unfold kmsTerm; fun_prop

/-- **`F_{A,B}` is continuous on the closed strip** `0 ≤ Im z ≤ β` (Panangaden, Proposition 5.9, p. 47). -/
theorem continuousOn_kmsFun (hβ : 0 < β) (hZ : Summable fun n => Real.exp (-(β * ev n))) (A B : H →L[ℂ] H) :
    ContinuousOn (kmsFun b ev β A B) (strip β) := by
  have h := continuousOn_tsum (fun p => (continuous_kmsTerm b ev A B p).continuousOn) (summable_kmsBound b ev hZ A B)
    (fun p z hz => norm_kmsTerm_le b ev hβ A B p hz)
  exact h.div_const _

/-- **`F_{A,B}` is analytic on the open strip** `0 < Im z < β` (Panangaden, Proposition 5.9, p. 47). -/
theorem differentiableOn_kmsFun (hβ : 0 < β) (hZ : Summable fun n => Real.exp (-(β * ev n))) (A B : H →L[ℂ] H) :
    DifferentiableOn ℂ (kmsFun b ev β A B) (openStrip β) := by
  have h := Complex.differentiableOn_tsum_of_summable_norm (summable_kmsBound b ev hZ A B)
    (fun p => (differentiable_kmsTerm b ev A B p).differentiableOn) isOpen_openStrip
    (fun p z hz => norm_kmsTerm_le b ev hβ A B p ⟨hz.1.le, hz.2.le⟩)
  exact h.div_const _

/-- **`F_{A,B}` is bounded on the closed strip** (Panangaden, Proposition 5.9, p. 47). -/
theorem norm_kmsFun_le (hβ : 0 < β) (hZ : Summable fun n => Real.exp (-(β * ev n))) (A B : H →L[ℂ] H) {z : ℂ}
    (hz : z ∈ strip β) : ‖kmsFun b ev β A B z‖ ≤ (∑' p, kmsBound b ev β A B p) / partition ev β := by
  have hZ0 : 0 ≤ partition ev β := tsum_nonneg fun n => (Real.exp_pos _).le
  rw [kmsFun, norm_div, Complex.norm_real, Real.norm_of_nonneg hZ0]
  gcongr
  exact tsum_of_norm_bounded (summable_kmsBound b ev hZ A B).hasSum fun p => norm_kmsTerm_le b ev hβ A B p hz

/-- `⟪bₘ, (A X) bₘ⟫ = ∑ₙ ⟪bₘ, A bₙ⟫ ⟪bₙ, X bₘ⟫`. -/
lemma hasSum_inner_mul (A X : H →L[ℂ] H) (m : ι) :
    HasSum (fun n => ⟪b m, A (b n)⟫_ℂ * ⟪b n, X (b m)⟫_ℂ) ⟪b m, (A * X) (b m)⟫_ℂ := by
  have h := b.hasSum_inner_mul_inner (ContinuousLinearMap.adjoint A (b m)) (X (b m))
  rw [ContinuousLinearMap.adjoint_inner_left] at h
  refine h.congr_fun fun n => ?_
  rw [ContinuousLinearMap.adjoint_inner_left]

/-- **The lower boundary value** `F_{A,B}(t) = ω(A τᵗ(B))` (Panangaden, Proposition 5.9, p. 47). -/
theorem kmsFun_ofReal (hβ : 0 < β) (hZ : Summable fun n => Real.exp (-(β * ev n))) (A B : H →L[ℂ] H) (t : ℝ) :
    kmsFun b ev β A B t = gibbs b ev β (A * dyn b ev t B) := by
  have hs : Summable fun p => kmsTerm b ev β A B p t :=
    Summable.of_norm_bounded (summable_kmsBound b ev hZ A B)
      fun p => norm_kmsTerm_le b ev hβ A B p (by simp [strip, hβ.le])
  rw [kmsFun, gibbs, hs.tsum_prod' (fun m => hs.prod_factor m)]
  congr 1
  refine tsum_congr fun m => ?_
  rw [← (hasSum_inner_mul b A (dyn b ev t B) m).tsum_eq, ← tsum_mul_left]
  refine tsum_congr fun n => ?_
  rw [inner_dyn]
  simp only [kmsTerm]
  ring

/-- **The upper boundary value** `F_{A,B}(t + iβ) = ω(τᵗ(B) A)`, the KMS condition (Panangaden, Remark 5.1 and
Proposition 5.9, p. 47). -/
theorem kmsFun_add_I_mul (hβ : 0 < β) (hZ : Summable fun n => Real.exp (-(β * ev n))) (A B : H →L[ℂ] H) (t : ℝ) :
    kmsFun b ev β A B (t + Complex.I * β) = gibbs b ev β (dyn b ev t B * A) := by
  have hmem : (t + Complex.I * β : ℂ) ∈ strip β := by simp [strip, hβ.le]
  have hs : Summable fun p => kmsTerm b ev β A B p (t + Complex.I * β) :=
    Summable.of_norm_bounded (summable_kmsBound b ev hZ A B) fun p => norm_kmsTerm_le b ev hβ A B p hmem
  have hs' : Summable fun q : ι × ι => kmsTerm b ev β A B (q.2, q.1) (t + Complex.I * β) :=
    (Equiv.prodComm ι ι).summable_iff.mpr hs
  have hsw : ∑' p, kmsTerm b ev β A B p (t + Complex.I * β) =
      ∑' q : ι × ι, kmsTerm b ev β A B (q.2, q.1) (t + Complex.I * β) :=
    ((Equiv.prodComm ι ι).tsum_eq _).symm
  rw [kmsFun, gibbs, hsw, hs'.tsum_prod' (fun n => hs'.prod_factor n)]
  congr 1
  refine tsum_congr fun n => ?_
  rw [← (hasSum_inner_mul b (dyn b ev t B) A n).tsum_eq, ← tsum_mul_left]
  refine tsum_congr fun m => ?_
  rw [inner_dyn]
  have hexp : (Real.exp (-(β * ev m)) : ℂ) * Complex.exp (Complex.I * (t + Complex.I * β) * (ev n - ev m)) =
      (Real.exp (-(β * ev n)) : ℂ) * Complex.exp (Complex.I * t * (ev n - ev m)) := by
    rw [Complex.ofReal_exp, Complex.ofReal_exp, ← Complex.exp_add, ← Complex.exp_add]
    congr 1
    push_cast
    linear_combination ((β : ℂ) * ((ev n : ℂ) - ev m)) * Complex.I_sq
  simp only [kmsTerm]
  linear_combination (⟪b m, A (b n)⟫_ℂ * ⟪b n, B (b m)⟫_ℂ) * hexp

end Lightlike.OperatorAlgebras.GibbsKMS
