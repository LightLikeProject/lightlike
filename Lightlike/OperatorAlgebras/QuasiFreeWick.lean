import Lightlike.OperatorAlgebras.QuasiFree

/-!
# Wick's formula for a quasi-free vector, in generating-function form

For a representation `W` of the CCR and a vector `Ψ`, the *generating function* of `y₀, …, yₙ₋₁` is
`t ↦ (Ψ | W(t₀y₀) ⋯ W(tₙ₋₁yₙ₋₁) Ψ)` (`CCRRep.genFun`), and the *n-point function* is `(-i)ⁿ ∂₀ ⋯ ∂ₙ₋₁` of it at
`t = 0` (`CCRRep.npoint`, with `mixedDeriv`): formally `(Ψ | φ(y₀) ⋯ φ(yₙ₋₁) Ψ)` for `W(ty) = e^{itφ(y)}`.

For a quasi-free vector (`(Ψ|W(y)Ψ) = exp(-¼ η(y, y))`) the generating function is `exp` of a quadratic form
(`CCRRep.IsQuasiFree.genFun_eq`), and:

* `CCRRep.IsQuasiFree.npoint_two`: the two-point function is `½(η(a, b) + iσ(a, b))`;
* `CCRRep.IsQuasiFree.npoint_eq_haf` (**Wick's formula**): the n-point function is the sum over pairings of the
  two-point functions, `haf (fun j k => npoint ![y j, y k])`, where `haf` pairs the first index with each later one in
  turn (the pairings `σ(1) < σ(3) < ⋯`, `σ(2j - 1) < σ(2j)` of Dereziński, arXiv:math-ph/0511030, p. 38, read);
  in particular it vanishes for odd `n` (`CCRRep.IsQuasiFree.npoint_odd`).

The combinatorial core is `mixedDeriv_exp_quad` (Isserlis): `∂₀ ⋯ ∂ₙ₋₁ exp(∑_{j<k} c_{jk} t_j t_k + ∑ d_j t_j²)` at
`0` is `haf c`.

Limits: this is the generating-function form. Dereziński's Theorem 38 (p. 39) states Wick's formula for
`(Ψ|φ(y₁) ⋯ φ(yₙ)Ψ)` with `Ψ ∈ Dom(φ(y₁) ⋯ φ(yₙ))`; that domain statement, which identifies `npoint` with the
operator product, is not proved here.
-/

open scoped InnerProductSpace ContDiff

namespace Lightlike.OperatorAlgebras

/-! ### Mixed derivatives at the origin -/

/-- The derivative in the first variable at `0`, as a function of the others. -/
noncomputable def derivHead {n : ℕ} (f : (Fin (n + 1) → ℝ) → ℂ) (t : Fin n → ℝ) : ℂ :=
  deriv (fun s : ℝ => f (Fin.cons s t)) 0

/-- **The mixed derivative** `∂₀ ∂₁ ⋯ ∂ₙ₋₁ f` at the origin, the variables taken in order. -/
noncomputable def mixedDeriv : {n : ℕ} → ((Fin n → ℝ) → ℂ) → ℂ
  | 0, f => f Fin.elim0
  | _ + 1, f => mixedDeriv (derivHead f)

lemma mixedDeriv_zero (f : (Fin 0 → ℝ) → ℂ) : mixedDeriv f = f Fin.elim0 := rfl

lemma mixedDeriv_succ {n : ℕ} (f : (Fin (n + 1) → ℝ) → ℂ) : mixedDeriv f = mixedDeriv (derivHead f) := rfl

lemma contDiff_cons_right {n : ℕ} (s : ℝ) :
    ContDiff ℝ ∞ (fun t : Fin n → ℝ => (Fin.cons s t : Fin (n + 1) → ℝ)) := by
  refine contDiff_pi.2 fun i => ?_
  refine Fin.cases ?_ (fun j => ?_) i
  · simpa using (contDiff_const : ContDiff ℝ ∞ fun _ : Fin n → ℝ => s)
  · simpa using (contDiff_apply ℝ (fun _ : Fin n => ℝ) j : ContDiff ℝ ∞ fun t : Fin n → ℝ => t j)

lemma cons_eq_add {n : ℕ} (s : ℝ) (t : Fin n → ℝ) :
    (Fin.cons s t : Fin (n + 1) → ℝ) = Fin.cons 0 t + s • Pi.single 0 1 := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i <;> simp [Pi.single_apply, Fin.succ_ne_zero]

lemma hasDerivAt_cons {n : ℕ} (t : Fin n → ℝ) (s : ℝ) :
    HasDerivAt (fun s : ℝ => (Fin.cons s t : Fin (n + 1) → ℝ)) (Pi.single 0 1) s := by
  have h : (fun s : ℝ => (Fin.cons s t : Fin (n + 1) → ℝ)) = fun s => Fin.cons 0 t + s • Pi.single 0 1 :=
    funext fun s => cons_eq_add s t
  rw [h]
  simpa using ((hasDerivAt_id s).smul_const (Pi.single 0 1 : Fin (n + 1) → ℝ)).const_add (Fin.cons 0 t)

lemma derivHead_eq_fderiv {n : ℕ} {f : (Fin (n + 1) → ℝ) → ℂ} (hf : Differentiable ℝ f) (t : Fin n → ℝ) :
    derivHead f t = fderiv ℝ f (Fin.cons 0 t) (Pi.single 0 1) := by
  have := (hf (Fin.cons 0 t)).hasFDerivAt.comp_hasDerivAt (0 : ℝ) (hasDerivAt_cons t 0)
  exact this.deriv

lemma contDiff_derivHead {n : ℕ} {f : (Fin (n + 1) → ℝ) → ℂ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (derivHead f) := by
  obtain ⟨hd, hc⟩ := contDiff_infty_iff_fderiv.mp hf
  have : derivHead f = fun t => fderiv ℝ f (Fin.cons 0 t) (Pi.single 0 1) := funext (derivHead_eq_fderiv hd)
  rw [this]
  exact (hc.comp (contDiff_cons_right 0)).clm_apply contDiff_const

lemma differentiableAt_cons_comp {n : ℕ} {f : (Fin (n + 1) → ℝ) → ℂ} (hf : ContDiff ℝ ∞ f) (t : Fin n → ℝ) (s : ℝ) :
    DifferentiableAt ℝ (fun s : ℝ => f (Fin.cons s t)) s :=
  ((hf.differentiable (by simp)) _).comp s (hasDerivAt_cons t s).differentiableAt

lemma mixedDeriv_const : ∀ {n : ℕ} (a : ℂ), mixedDeriv (fun _ : Fin n → ℝ => a) = if n = 0 then a else 0
  | 0, a => rfl
  | n + 1, a => by
    rw [mixedDeriv_succ]
    have : derivHead (fun _ : Fin (n + 1) → ℝ => a) = fun _ => 0 := by
      funext t; simp [derivHead]
    rw [this, mixedDeriv_const (n := n) 0]
    simp

lemma mixedDeriv_add : ∀ {n : ℕ} {f g : (Fin n → ℝ) → ℂ}, ContDiff ℝ ∞ f → ContDiff ℝ ∞ g →
    mixedDeriv (fun t => f t + g t) = mixedDeriv f + mixedDeriv g
  | 0, _, _, _, _ => rfl
  | n + 1, f, g, hf, hg => by
    rw [mixedDeriv_succ, mixedDeriv_succ, mixedDeriv_succ]
    have : derivHead (fun t => f t + g t) = fun t => derivHead f t + derivHead g t := by
      funext t
      exact deriv_add (differentiableAt_cons_comp hf t 0) (differentiableAt_cons_comp hg t 0)
    rw [this]
    exact mixedDeriv_add (contDiff_derivHead hf) (contDiff_derivHead hg)

lemma mixedDeriv_const_mul : ∀ {n : ℕ} (a : ℂ) (f : (Fin n → ℝ) → ℂ),
    mixedDeriv (fun t => a * f t) = a * mixedDeriv f
  | 0, _, _ => rfl
  | n + 1, a, f => by
    rw [mixedDeriv_succ, mixedDeriv_succ]
    have : derivHead (fun t => a * f t) = fun t => a * derivHead f t := by
      funext t; exact deriv_const_mul_field a
    rw [this]
    exact mixedDeriv_const_mul a _

lemma mixedDeriv_sum {n : ℕ} {ι : Type*} (s : Finset ι) (f : ι → (Fin n → ℝ) → ℂ)
    (hf : ∀ i ∈ s, ContDiff ℝ ∞ (f i)) :
    mixedDeriv (fun t => ∑ i ∈ s, f i t) = ∑ i ∈ s, mixedDeriv (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    rw [mixedDeriv_const]
    split_ifs <;> rfl
  | insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    rw [mixedDeriv_add (hf i (Finset.mem_insert_self i s))
      (ContDiff.sum fun j hj => hf j (Finset.mem_insert_of_mem hj)),
      ih fun j hj => hf j (Finset.mem_insert_of_mem hj)]

lemma contDiff_coord {n : ℕ} (j : Fin n) : ContDiff ℝ ∞ (fun t : Fin n → ℝ => ((t j : ℝ) : ℂ)) :=
  Complex.ofRealCLM.contDiff.comp (contDiff_apply ℝ (fun _ : Fin n => ℝ) j)

lemma derivHead_coord_zero_mul {n : ℕ} {g : (Fin (n + 1) → ℝ) → ℂ} (hg : ContDiff ℝ ∞ g) :
    derivHead (fun t => ((t 0 : ℝ) : ℂ) * g t) = fun t => g (Fin.cons 0 t) := by
  funext t
  have h1 := (hasDerivAt_id (0 : ℝ)).ofReal_comp.mul (differentiableAt_cons_comp hg t 0).hasDerivAt
  simp only [id] at h1
  have e : derivHead (fun t : Fin (n + 1) → ℝ => ((t 0 : ℝ) : ℂ) * g t) t =
      deriv (fun s : ℝ => ((s : ℝ) : ℂ) * g (Fin.cons s t)) 0 := by
    simp only [derivHead, Fin.cons_zero]
  rw [e, show (fun s : ℝ => ((s : ℝ) : ℂ) * g (Fin.cons s t)) =
      ((fun y : ℝ => ((y : ℝ) : ℂ)) * fun s => g (Fin.cons s t)) from rfl, h1.deriv]
  simp

/-- **`∂ₖ (tₖ g)` at `tₖ = 0` is `g` there**: the mixed derivative of `tₖ g` is that of `g` restricted to `tₖ = 0`. -/
lemma mixedDeriv_coord_mul {n : ℕ} (k : Fin (n + 1)) {g : (Fin (n + 1) → ℝ) → ℂ} (hg : ContDiff ℝ ∞ g) :
    mixedDeriv (fun t => ((t k : ℝ) : ℂ) * g t) = mixedDeriv (fun t : Fin n → ℝ => g (Fin.insertNth k 0 t)) := by
  induction n with
  | zero =>
    refine Fin.cases ?_ (fun k' => k'.elim0) k
    conv_lhs => rw [mixedDeriv_succ]
    rw [derivHead_coord_zero_mul hg]
    simp only [Fin.insertNth_zero']
  | succ m ih =>
    refine Fin.cases ?_ (fun k' => ?_) k
    · conv_lhs => rw [mixedDeriv_succ]
      rw [derivHead_coord_zero_mul hg]
      simp only [Fin.insertNth_zero']
    · conv_lhs => rw [mixedDeriv_succ]
      conv_rhs => rw [mixedDeriv_succ]
      have e1 : derivHead (fun t : Fin (m + 2) → ℝ => ((t k'.succ : ℝ) : ℂ) * g t) =
          fun t => ((t k' : ℝ) : ℂ) * derivHead g t := by
        funext t
        simp only [derivHead, Fin.cons_succ]
        exact deriv_const_mul_field _
      have e2 : derivHead (fun t : Fin (m + 1) → ℝ => g (Fin.insertNth k'.succ 0 t)) =
          fun u => derivHead g (Fin.insertNth k' 0 u) := by
        funext u
        simp only [derivHead, Fin.insertNth_succ_cons]
      rw [e1, e2]
      exact ih k' (contDiff_derivHead hg)

/-! ### The sum over pairings -/

/-- **The sum over pairings** (the Hafnian) of `c`: the first index is paired with each later one in turn,
`haf c = ∑ₖ c 0 (k + 1) · haf c'` with `c'` the restriction of `c` to the remaining indices; these are the pairings
`σ(1) < σ(3) < ⋯ < σ(2m - 1)`, `σ(2j - 1) < σ(2j)`. It is `0` for an odd number of indices. -/
noncomputable def haf : {n : ℕ} → (Fin n → Fin n → ℂ) → ℂ
  | 0, _ => 1
  | 1, _ => 0
  | n + 2, c => ∑ k : Fin (n + 1), c 0 k.succ * haf fun i j => c (k.succAbove i).succ (k.succAbove j).succ

lemma haf_odd : ∀ {n : ℕ}, Odd n → ∀ c : Fin n → Fin n → ℂ, haf c = 0
  | 0, h, _ => by simp at h
  | 1, _, _ => rfl
  | n + 2, h, c => by
    have hn : Odd n := by
      obtain ⟨m, hm⟩ := h; exact ⟨m - 1, by omega⟩
    simp only [haf]
    exact Finset.sum_eq_zero fun k _ => by rw [haf_odd hn, mul_zero]

lemma haf_neg_I_pow : ∀ {n : ℕ} (c : Fin n → Fin n → ℂ), (-Complex.I) ^ n * haf c = haf fun j k => -c j k
  | 0, _ => by simp [haf]
  | 1, _ => by simp [haf]
  | n + 2, c => by
    simp only [haf]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← haf_neg_I_pow]
    have : (-Complex.I) ^ (n + 2) = -(-Complex.I) ^ n := by
      rw [pow_add]; simp [Complex.I_sq]
    rw [this]
    ring

/-! ### Isserlis' formula -/

/-- The quadratic form `∑_{j<k} c_{jk} t_j t_k + ∑_j d_j t_j²`. -/
noncomputable def quad {n : ℕ} (c : Fin n → Fin n → ℂ) (d : Fin n → ℂ) (t : Fin n → ℝ) : ℂ :=
  (∑ j, ∑ k, if j < k then c j k * (t j : ℂ) * (t k : ℂ) else 0) + ∑ j, d j * (t j : ℂ) ^ 2

lemma contDiff_quad {n : ℕ} (c : Fin n → Fin n → ℂ) (d : Fin n → ℂ) : ContDiff ℝ ∞ (quad c d) := by
  unfold quad
  refine ContDiff.add (ContDiff.sum fun j _ => ContDiff.sum fun k _ => ?_)
    (ContDiff.sum fun j _ => contDiff_const.mul ((contDiff_coord j).pow 2))
  split_ifs
  · exact (contDiff_const.mul (contDiff_coord j)).mul (contDiff_coord k)
  · exact contDiff_const

lemma quad_cons {n : ℕ} (c : Fin (n + 1) → Fin (n + 1) → ℂ) (d : Fin (n + 1) → ℂ) (s : ℝ) (t : Fin n → ℝ) :
    quad c d (Fin.cons s t) = (s : ℂ) * (∑ k, c 0 k.succ * (t k : ℂ)) + d 0 * (s : ℂ) ^ 2 +
      quad (fun i j => c i.succ j.succ) (fun i => d i.succ) t := by
  unfold quad
  simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, lt_self_iff_false, if_false, Fin.succ_pos, if_true,
    Fin.succ_lt_succ_iff, not_lt_zero', zero_add, Finset.mul_sum]
  try simp only [show ∀ i : Fin n, ¬ (i.succ < 0) from fun i => (Fin.succ_pos i).asymm, if_false, zero_add]
  rw [show ∑ x : Fin n, c 0 x.succ * (s : ℂ) * (t x : ℂ) = ∑ x : Fin n, (s : ℂ) * (c 0 x.succ * (t x : ℂ)) from
    Finset.sum_congr rfl fun x _ => by ring]
  ring

lemma quad_insertNth_zero {n : ℕ} (c : Fin (n + 1) → Fin (n + 1) → ℂ) (d : Fin (n + 1) → ℂ) (k : Fin (n + 1))
    (t : Fin n → ℝ) :
    quad c d (Fin.insertNth k 0 t) =
      quad (fun i j => c (k.succAbove i) (k.succAbove j)) (fun i => d (k.succAbove i)) t := by
  unfold quad
  simp only [Fin.sum_univ_succAbove _ k, Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove,
    Fin.succAbove_lt_succAbove_iff, Complex.ofReal_zero, mul_zero, zero_mul, ite_self, Finset.sum_const_zero,
    zero_add, add_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]

lemma derivHead_exp_quad {n : ℕ} (c : Fin (n + 1) → Fin (n + 1) → ℂ) (d : Fin (n + 1) → ℂ) (t : Fin n → ℝ) :
    derivHead (fun u => Complex.exp (quad c d u)) t =
      (∑ k, c 0 k.succ * (t k : ℂ)) * Complex.exp (quad (fun i j => c i.succ j.succ) (fun i => d i.succ) t) := by
  have h : HasDerivAt (fun z : ℂ => Complex.exp (z * (∑ k, c 0 k.succ * (t k : ℂ)) + d 0 * z ^ 2 +
      quad (fun i j => c i.succ j.succ) (fun i => d i.succ) t))
      (Complex.exp (quad (fun i j => c i.succ j.succ) (fun i => d i.succ) t) * (∑ k, c 0 k.succ * (t k : ℂ)))
      ((0 : ℝ) : ℂ) := by
    have := ((((hasDerivAt_id ((0 : ℝ) : ℂ)).mul_const (∑ k, c 0 k.succ * (t k : ℂ))).add
      ((hasDerivAt_pow 2 ((0 : ℝ) : ℂ)).const_mul (d 0))).add_const
      (quad (fun i j => c i.succ j.succ) (fun i => d i.succ) t)).cexp
    convert this using 1 <;> simp
  have hfun : (fun s : ℝ => Complex.exp (quad c d (Fin.cons s t))) = fun s : ℝ =>
      Complex.exp ((s : ℂ) * (∑ k, c 0 k.succ * (t k : ℂ)) + d 0 * (s : ℂ) ^ 2 +
        quad (fun i j => c i.succ j.succ) (fun i => d i.succ) t) := by
    funext s; rw [quad_cons]
  unfold derivHead
  rw [hfun, h.comp_ofReal.deriv]
  ring

/-- **Isserlis' formula**: the mixed derivative of `exp(∑_{j<k} c_{jk} t_j t_k + ∑ d_j t_j²)` at `0` is the sum over
pairings of the `c_{jk}`. -/
theorem mixedDeriv_exp_quad : ∀ {n : ℕ} (c : Fin n → Fin n → ℂ) (d : Fin n → ℂ),
    mixedDeriv (fun t => Complex.exp (quad c d t)) = haf c
  | 0, c, d => by simp [mixedDeriv_zero, quad, haf]
  | 1, c, d => by
    rw [mixedDeriv_succ]
    have : derivHead (fun t => Complex.exp (quad c d t)) = fun _ => 0 := by
      funext t; rw [derivHead_exp_quad]; simp
    rw [this, mixedDeriv_zero]
    simp [haf]
  | n + 2, c, d => by
    rw [mixedDeriv_succ]
    have e : derivHead (fun t => Complex.exp (quad c d t)) = fun t => ∑ k : Fin (n + 1),
        c 0 k.succ * (((t k : ℝ) : ℂ) * Complex.exp (quad (fun i j => c i.succ j.succ) (fun i => d i.succ) t)) := by
      funext t; rw [derivHead_exp_quad, Finset.sum_mul]
      exact Finset.sum_congr rfl fun k _ => by ring
    rw [e, mixedDeriv_sum _ _ fun k _ => contDiff_const.mul ((contDiff_coord k).mul (contDiff_quad _ _).cexp)]
    simp only [haf]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [mixedDeriv_const_mul, mixedDeriv_coord_mul k (contDiff_quad _ _).cexp]
    simp only [quad_insertNth_zero]
    rw [mixedDeriv_exp_quad]

/-! ### The n-point functions of a representation of the CCR -/

variable {h : Type*} [NormedAddCommGroup h] [InnerProductSpace ℂ h]
variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K]

/-- `W(t₀ y₀) W(t₁ y₁) ⋯ W(tₙ₋₁ yₙ₋₁) ψ`. -/
noncomputable def CCRRep.weylProd (R : CCRRep h K) : {n : ℕ} → (Fin n → h) → (Fin n → ℝ) → K → K
  | 0, _, _, ψ => ψ
  | _ + 1, y, t, ψ => R.W ((t 0 : ℂ) • y 0) (R.weylProd (Fin.tail y) (Fin.tail t) ψ)

/-- **The generating function** `t ↦ (Ψ | W(t₀ y₀) ⋯ W(tₙ₋₁ yₙ₋₁) Ψ)`. -/
noncomputable def CCRRep.genFun (R : CCRRep h K) (Ψ : K) {n : ℕ} (y : Fin n → h) (t : Fin n → ℝ) : ℂ :=
  ⟪Ψ, R.weylProd y t Ψ⟫_ℂ

/-- **The n-point function** of `Ψ`: `(-i)ⁿ ∂₀ ⋯ ∂ₙ₋₁` of the generating function at `0`, formally
`(Ψ | φ(y₀) ⋯ φ(yₙ₋₁) Ψ)` for `W(t y) = e^{itφ(y)}`. -/
noncomputable def CCRRep.npoint (R : CCRRep h K) (Ψ : K) {n : ℕ} (y : Fin n → h) : ℂ :=
  (-Complex.I) ^ n * mixedDeriv (R.genFun Ψ y)

/-- The phase `∑_{j<k} t_j t_k σ(y_j, y_k)` of a product of Weyl unitaries. -/
noncomputable def weylPhase {n : ℕ} (y : Fin n → h) (t : Fin n → ℝ) : ℝ :=
  ∑ j, ∑ k, if j < k then t j * t k * symp h (y j) (y k) else 0

lemma symp_sum_right {ι : Type*} (s : Finset ι) (f : h) (g : ι → h) :
    symp h f (∑ i ∈ s, g i) = ∑ i ∈ s, symp h f (g i) := by
  simp [symp, inner_sum, Complex.im_sum]

lemma weylPhase_succ {n : ℕ} (y : Fin (n + 1) → h) (t : Fin (n + 1) → ℝ) :
    weylPhase y t = symp h ((t 0 : ℂ) • y 0) (∑ k : Fin n, ((Fin.tail t k : ℝ) : ℂ) • Fin.tail y k) +
      weylPhase (Fin.tail y) (Fin.tail t) := by
  unfold weylPhase
  rw [symp_sum_right]
  simp only [Fin.sum_univ_succ, lt_self_iff_false, if_false, Fin.succ_pos, if_true, Fin.succ_lt_succ_iff,
    zero_add, Fin.tail, symp_real_smul_left, symp_real_smul_right]
  try simp only [show ∀ i : Fin n, ¬ (i.succ < 0) from fun i => (Fin.succ_pos i).asymm, if_false,
    Finset.sum_const_zero, zero_add]
  congr 1
  exact Finset.sum_congr rfl fun k _ => by ring

/-- **A product of Weyl unitaries** is a phase times the Weyl unitary of the sum:
`W(t₀y₀) ⋯ W(tₙ₋₁yₙ₋₁) = e^{-i ∑_{j<k} t_j t_k σ(y_j, y_k)/2} W(∑ t_j y_j)`. -/
lemma CCRRep.weylProd_eq (R : CCRRep h K) : ∀ {n : ℕ} (y : Fin n → h) (t : Fin n → ℝ) (ψ : K),
    R.weylProd y t ψ = Complex.exp (-(Complex.I * ((weylPhase y t / 2 : ℝ) : ℂ))) • R.W (∑ j, (t j : ℂ) • y j) ψ
  | 0, y, t, ψ => by simp [CCRRep.weylProd, weylPhase, R.W_zero_apply]
  | n + 1, y, t, ψ => by
    have hS : (∑ j, (t j : ℂ) • y j) = (t 0 : ℂ) • y 0 + ∑ k, ((Fin.tail t k : ℝ) : ℂ) • Fin.tail y k :=
      Fin.sum_univ_succ _
    rw [CCRRep.weylProd, R.weylProd_eq (Fin.tail y) (Fin.tail t) ψ, map_smul, R.weyl, smul_smul,
      ← Complex.exp_add, hS, weylPhase_succ]
    congr 2
    push_cast
    ring

lemma sum_sum_split {M : Type*} [AddCommMonoid M] {n : ℕ} (a : Fin n → Fin n → M) :
    ∑ j, ∑ k, a j k = (∑ j, ∑ k, if j < k then a j k + a k j else 0) + ∑ j, a j j := by
  have h1 : ∀ j k, a j k = (if j < k then a j k else 0) + (if k < j then a j k else 0) + (if j = k then a j k else 0) := by
    intro j k
    rcases lt_trichotomy j k with h | h | h
    · simp [h, h.ne, not_lt.mpr h.le]
    · subst h; simp
    · simp [h, h.ne', not_lt.mpr h.le]
  have h2 : ∑ j, ∑ k, (if k < j then a j k else 0) = ∑ j, ∑ k, if j < k then a k j else 0 := Finset.sum_comm
  have h3 : ∀ j k, ((if j < k then a j k + a k j else 0) : M) = (if j < k then a j k else 0) + if j < k then a k j else 0 := by
    intro j k; split_ifs <;> simp
  calc ∑ j, ∑ k, a j k
      = ∑ j, ∑ k, ((if j < k then a j k else 0) + (if k < j then a j k else 0) + (if j = k then a j k else 0)) :=
        Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => h1 j k
    _ = (∑ j, ∑ k, if j < k then a j k + a k j else 0) + ∑ j, a j j := by
        simp only [Finset.sum_add_distrib, h3, h2, Finset.sum_ite_eq, Finset.mem_univ, if_true]

lemma ss_mul {n : ℕ} (c : ℂ) (A : Fin n → Fin n → ℂ) :
    c * (∑ j, ∑ k, if j < k then A j k else 0) = ∑ j, ∑ k, if j < k then c * A j k else 0 := by
  simp only [Finset.mul_sum, mul_ite, mul_zero]

lemma ss_add {n : ℕ} (A B : Fin n → Fin n → ℂ) :
    ((∑ j, ∑ k, if j < k then A j k else 0) + ∑ j, ∑ k, if j < k then B j k else 0) =
      ∑ j, ∑ k, if j < k then A j k + B j k else 0 := by
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  split_ifs <;> simp

lemma ss_ofReal {n : ℕ} (A : Fin n → Fin n → ℝ) :
    (((∑ j, ∑ k, if j < k then A j k else 0 : ℝ)) : ℂ) = ∑ j, ∑ k, if j < k then ((A j k : ℝ) : ℂ) else 0 := by
  push_cast
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
  split_ifs <;> simp

variable {R : CCRRep h K} {Ψ : K} {η : LinearMap.BilinForm ℝ h}

/-- The coefficient `-(i σ(y_j, y_k) + η(y_j, y_k))/2` of `t_j t_k`, `j < k`, in the exponent of the generating function. -/
noncomputable def wickC (η : LinearMap.BilinForm ℝ h) {n : ℕ} (y : Fin n → h) (j k : Fin n) : ℂ :=
  -(Complex.I * ((symp h (y j) (y k) / 2 : ℝ) : ℂ)) - ((η (y j) (y k) / 2 : ℝ) : ℂ)

/-- The coefficient `-η(y_j, y_j)/4` of `t_j²`. -/
noncomputable def wickD (η : LinearMap.BilinForm ℝ h) {n : ℕ} (y : Fin n → h) (j : Fin n) : ℂ :=
  -((η (y j) (y j) / 4 : ℝ) : ℂ)

/-- **The generating function of a quasi-free vector** is `exp` of a quadratic form. -/
theorem CCRRep.IsQuasiFree.genFun_eq (hΨ : R.IsQuasiFree Ψ η) {n : ℕ} (y : Fin n → h) (t : Fin n → ℝ) :
    R.genFun Ψ y t = Complex.exp (quad (wickC η y) (wickD η y) t) := by
  rw [CCRRep.genFun, R.weylProd_eq, inner_smul_right, hΨ.expectation, ← Complex.exp_add]
  congr 1
  have hη : η (∑ j, (t j : ℂ) • y j) (∑ j, (t j : ℂ) • y j) = ∑ j, ∑ k, t j * t k * η (y j) (y k) := by
    simp only [map_sum, LinearMap.sum_apply, bilin_real_smul]
    first | rfl | exact Finset.sum_comm
  have hs := sum_sum_split (fun j k => t j * t k * η (y j) (y k))
  beta_reduce at hs
  rw [hη, hs]
  calc -(Complex.I * ((weylPhase y t / 2 : ℝ) : ℂ)) +
        -(((∑ j, ∑ k, if j < k then t j * t k * η (y j) (y k) + t k * t j * η (y k) (y j) else 0) +
          ∑ j, t j * t j * η (y j) (y j)) / 4 : ℝ)
      = (-Complex.I / 2) * ((weylPhase y t : ℝ) : ℂ) +
        (-1 / 4) * (((∑ j, ∑ k, if j < k then t j * t k * η (y j) (y k) + t k * t j * η (y k) (y j) else 0 : ℝ)) : ℂ) +
        (-1 / 4) * (((∑ j, t j * t j * η (y j) (y j) : ℝ)) : ℂ) := by
        simp only [Complex.ofReal_div, Complex.ofReal_add, Complex.ofReal_neg, Complex.ofReal_ofNat]
        ring
    _ = (∑ j, ∑ k, if j < k then (-Complex.I / 2) * ((t j * t k * symp h (y j) (y k) : ℝ) : ℂ) +
          (-1 / 4) * ((t j * t k * η (y j) (y k) + t k * t j * η (y k) (y j) : ℝ) : ℂ) else 0) +
        ∑ j, (-1 / 4) * ((t j * t j * η (y j) (y j) : ℝ) : ℂ) := by
        rw [weylPhase, ss_ofReal, ss_ofReal, Complex.ofReal_sum, ss_mul, ss_mul, ss_add, Finset.mul_sum]
    _ = quad (wickC η y) (wickD η y) t := by
        unfold quad wickC wickD
        congr 1
        · refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
          split_ifs
          · rw [hΨ.symm (y k) (y j)]
            push_cast
            ring
          · rfl
        · refine Finset.sum_congr rfl fun j _ => ?_
          push_cast
          ring

/-- **The n-point functions of a quasi-free vector** are the sums over pairings of `-(iσ + η)/2`, times `(-i)ⁿ`. -/
theorem CCRRep.IsQuasiFree.npoint_eq (hΨ : R.IsQuasiFree Ψ η) {n : ℕ} (y : Fin n → h) :
    R.npoint Ψ y = haf fun j k => -wickC η y j k := by
  rw [CCRRep.npoint, show R.genFun Ψ y = fun t => Complex.exp (quad (wickC η y) (wickD η y) t) from
    funext (hΨ.genFun_eq y), mixedDeriv_exp_quad, haf_neg_I_pow]

/-- **The two-point function of a quasi-free vector** is `½(η(a, b) + iσ(a, b))`. -/
theorem CCRRep.IsQuasiFree.npoint_two (hΨ : R.IsQuasiFree Ψ η) (a b : h) :
    R.npoint Ψ ![a, b] = ((η a b / 2 : ℝ) : ℂ) + Complex.I * ((symp h a b / 2 : ℝ) : ℂ) := by
  rw [hΨ.npoint_eq]
  simp [haf, wickC] <;> ring

/-- **Wick's formula** for a quasi-free vector, in generating-function form: the n-point function is the sum over
pairings of the two-point functions. -/
theorem CCRRep.IsQuasiFree.npoint_eq_haf (hΨ : R.IsQuasiFree Ψ η) {n : ℕ} (y : Fin n → h) :
    R.npoint Ψ y = haf fun j k => R.npoint Ψ ![y j, y k] := by
  rw [hΨ.npoint_eq]
  congr 1
  funext j k
  rw [hΨ.npoint_two, wickC]
  ring

/-- The odd n-point functions of a quasi-free vector vanish. -/
theorem CCRRep.IsQuasiFree.npoint_odd (hΨ : R.IsQuasiFree Ψ η) {n : ℕ} (hn : Odd n) (y : Fin n → h) :
    R.npoint Ψ y = 0 := by
  rw [hΨ.npoint_eq, haf_odd hn]

end Lightlike.OperatorAlgebras
