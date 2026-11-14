module

public import Lightlike.Oscillatory.QuadraticPhase

/-!
# Amplitudes vanishing at a critical point, and integration by parts

For the proof of stationary phase (Hörmander, *The Analysis of Linear Partial Differential
Operators I*, Theorem 7.7.5) an amplitude that vanishes to high order at the critical point
must give a small integral. This file supplies the two estimates that the proof uses.

`Vanish K p v` says that the family `v s x` (smooth in `(s, x) ∈ ℝ × ℝⁿ`, zero for `x ∉ K`)
vanishes to order `p` at the origin, in the explicit form `v = ∑ⱼ xⱼ wⱼ` iterated `p` times. The
class is closed under sums, products with smooth functions (`vanish_mul`), multiplication by
coordinates (`vanish_coord_mul`) and by cubic functions (`vanish_mul_cubic`, the order rises by
three), and differentiation lowers the order by one (`vanish_coordDeriv`).

* `integral_ibp_step`: if `∑ₗ cⱼₗ ∂ₗF = xⱼ` on `K` and the `wⱼ` vanish off `K`, then
  `∫ (∑ⱼ xⱼ wⱼ) e^{iτF} = -(iτ)⁻¹ ∑ⱼₗ ∫ ∂ₗ(cⱼₗ wⱼ) e^{iτF}`. This is the integration by parts
  behind Hörmander's estimate (7.7.1)', in the form used in his proof of Theorem 7.7.5.
* `exists_bound_vanish`: for a family of phases `F_s`, `s ∈ [0, 1]`, with `Im F_s ≥ 0` on `K` and
  such coefficients, `|∫ v e^{iτF_s}| ≤ C τ^{-⌊p/2⌋}` for `v` of order `p`, uniformly in `s`.
  Each integration by parts gains `τ⁻¹` and costs two orders of vanishing.
* `exists_bound_quad`: for the quadratic phase `⟨A x, x⟩/2` and `v` of order `2m + 1`, the
  integral is `O(τ^{-n/2-1-m})`: `m` integrations by parts with `c = A⁻¹`, then the
  quadratic-phase lemma `quadratic_phase` for an amplitude with `v(0) = 0`.
-/

@[expose] public section

namespace Lightlike.Oscillatory


open MeasureTheory Complex Matrix Finset Set Filter
open scoped Real ContDiff Topology

variable {n : ℕ}

/-- The partial derivative `∂ₗ f(x)` of `f : ℝⁿ → ℂ`. -/
noncomputable def coordDeriv (f : (Fin n → ℝ) → ℂ) (l : Fin n) (x : Fin n → ℝ) : ℂ :=
  fderiv ℝ f x (Pi.single l 1)

/-- Families `v s x` of amplitudes, smooth in `(s, x)`, zero for `x ∉ K`, that vanish to order
`p` at the origin: `v = ∑ⱼ xⱼ wⱼ` with each `wⱼ` of order `p - 1`. -/
def Vanish (K : Set (Fin n → ℝ)) : ℕ → (ℝ → (Fin n → ℝ) → ℂ) → Prop
  | 0, v => ContDiff ℝ ∞ (fun p : ℝ × (Fin n → ℝ) => v p.1 p.2) ∧ ∀ s, ∀ x ∉ K, v s x = 0
  | p + 1, v => ∃ w : Fin n → ℝ → (Fin n → ℝ) → ℂ, (∀ j, Vanish K p (w j)) ∧
      ∀ s x, v s x = ∑ j, (x j : ℂ) * w j s x

variable {K : Set (Fin n → ℝ)}

/-- The coordinate `xⱼ`, as a complex function of `(s, x)`, is smooth. -/
theorem contDiff_coord (j : Fin n) :
    ContDiff ℝ ∞ (fun p : ℝ × (Fin n → ℝ) => ((p.2 j : ℝ) : ℂ)) := by
  have h : ContDiff ℝ ∞ (fun p : ℝ × (Fin n → ℝ) => p.2 j) :=
    contDiff_pi.mp contDiff_snd j
  exact ofRealCLM.contDiff.comp h

/-- `Vanish` depends only on the values of the family. -/
theorem vanish_congr {p : ℕ} {v v' : ℝ → (Fin n → ℝ) → ℂ} (h : ∀ s x, v s x = v' s x)
    (hv : Vanish K p v) : Vanish K p v' := by
  have : v = v' := funext fun s => funext fun x => h s x
  exact this ▸ hv

/-- Vanishing to order `p + 1` implies vanishing to order `p`. -/
theorem vanish_mono : ∀ {p : ℕ} {v : ℝ → (Fin n → ℝ) → ℂ}, Vanish K (p + 1) v → Vanish K p v
  | 0, v, ⟨w, hw, hv⟩ => by
    refine ⟨?_, fun s x hx => ?_⟩
    · have : (fun p : ℝ × (Fin n → ℝ) => v p.1 p.2) =
          fun p => ∑ j, ((p.2 j : ℝ) : ℂ) * w j p.1 p.2 := funext fun p => hv p.1 p.2
      rw [this]
      exact ContDiff.sum fun j _ => (contDiff_coord j).mul (hw j).1
    · rw [hv s x]
      exact Finset.sum_eq_zero fun j _ => by rw [(hw j).2 s x hx, mul_zero]
  | p + 1, v, ⟨w, hw, hv⟩ => ⟨w, fun j => vanish_mono (hw j), hv⟩

/-- Vanishing to order `q` implies vanishing to every order `p ≤ q`. -/
theorem vanish_of_le {p q : ℕ} (hpq : p ≤ q) {v : ℝ → (Fin n → ℝ) → ℂ} (hv : Vanish K q v) :
    Vanish K p v := by
  induction q, hpq using Nat.le_induction with
  | base => exact hv
  | succ q _ ih => exact ih (vanish_mono hv)

/-- Order `0`: smooth in `(s, x)` and zero for `x ∉ K`. -/
theorem vanish_zero_iff {v : ℝ → (Fin n → ℝ) → ℂ} :
    Vanish K 0 v ↔ ContDiff ℝ ∞ (fun p : ℝ × (Fin n → ℝ) => v p.1 p.2) ∧
      ∀ s, ∀ x ∉ K, v s x = 0 := Iff.rfl

/-- A family of any order is smooth in `(s, x)`. -/
theorem Vanish.contDiff {p : ℕ} {v : ℝ → (Fin n → ℝ) → ℂ} (hv : Vanish K p v) :
    ContDiff ℝ ∞ (fun p : ℝ × (Fin n → ℝ) => v p.1 p.2) :=
  (vanish_of_le (Nat.zero_le p) hv).1

/-- A family of any order is zero for `x ∉ K`. -/
theorem Vanish.eq_zero {p : ℕ} {v : ℝ → (Fin n → ℝ) → ℂ} (hv : Vanish K p v) (s : ℝ)
    {x : Fin n → ℝ} (hx : x ∉ K) : v s x = 0 :=
  (vanish_of_le (Nat.zero_le p) hv).2 s x hx

/-- Each member `v s` of a family is smooth. -/
theorem Vanish.contDiff_slice {p : ℕ} {v : ℝ → (Fin n → ℝ) → ℂ} (hv : Vanish K p v) (s : ℝ) :
    ContDiff ℝ ∞ (v s) :=
  hv.contDiff.comp ((contDiff_const (c := s)).prodMk contDiff_id)

/-- A family of order at least one vanishes at the origin. -/
theorem Vanish.apply_zero {p : ℕ} {v : ℝ → (Fin n → ℝ) → ℂ} (hv : Vanish K (p + 1) v)
    (s : ℝ) : v s 0 = 0 := by
  obtain ⟨w, _, hv⟩ := hv
  simp [hv s 0]

/-- The zero family vanishes to every order. -/
theorem vanish_zero_fun : ∀ {p : ℕ}, Vanish K p (fun _ _ => 0)
  | 0 => ⟨contDiff_const, fun _ _ _ => rfl⟩
  | _ + 1 => ⟨fun _ _ _ => 0, fun _ => vanish_zero_fun, fun _ _ => by simp⟩

/-- Sums of families of order `p` have order `p`. -/
theorem vanish_add : ∀ {p : ℕ} {v v' : ℝ → (Fin n → ℝ) → ℂ}, Vanish K p v → Vanish K p v' →
    Vanish K p (fun s x => v s x + v' s x)
  | 0, _, _, ⟨h1, h2⟩, ⟨h1', h2'⟩ =>
    ⟨h1.add h1', fun s x hx => by dsimp only; rw [h2 s x hx, h2' s x hx, add_zero]⟩
  | _ + 1, _, _, ⟨w, hw, hv⟩, ⟨w', hw', hv'⟩ =>
    ⟨fun j s x => w j s x + w' j s x, fun j => vanish_add (hw j) (hw' j), fun s x => by
      dsimp only
      rw [hv s x, hv' s x, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun j _ => by ring⟩

/-- Finite sums of families of order `p` have order `p`. -/
theorem vanish_sum {p : ℕ} {ι : Type*} (S : Finset ι) {v : ι → ℝ → (Fin n → ℝ) → ℂ}
    (hv : ∀ i ∈ S, Vanish K p (v i)) : Vanish K p (fun s x => ∑ i ∈ S, v i s x) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using (vanish_zero_fun : Vanish K p fun _ _ => 0)
  | insert a S ha ih =>
    have h1 := hv a (Finset.mem_insert_self a S)
    have h2 := ih fun i hi => hv i (Finset.mem_insert_of_mem hi)
    refine vanish_congr (fun s x => ?_) (vanish_add h1 h2)
    rw [Finset.sum_insert ha]

/-- Multiplying by a function smooth in `(s, x)` keeps the order. -/
theorem vanish_mul : ∀ {p : ℕ} {c v : ℝ → (Fin n → ℝ) → ℂ},
    ContDiff ℝ ∞ (fun p : ℝ × (Fin n → ℝ) => c p.1 p.2) → Vanish K p v →
    Vanish K p (fun s x => c s x * v s x)
  | 0, _, _, hc, ⟨h1, h2⟩ => ⟨hc.mul h1, fun s x hx => by dsimp only; rw [h2 s x hx, mul_zero]⟩
  | _ + 1, c, _, hc, ⟨w, hw, hv⟩ =>
    ⟨fun j s x => c s x * w j s x, fun j => vanish_mul hc (hw j), fun s x => by
      dsimp only
      rw [hv s x, Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring⟩

/-- Multiplying by a coordinate `xⱼ` raises the order by one. -/
theorem vanish_coord_mul {p : ℕ} {v : ℝ → (Fin n → ℝ) → ℂ} (hv : Vanish K p v) (j : Fin n) :
    Vanish K (p + 1) (fun s x => (x j : ℂ) * v s x) := by
  classical
  refine ⟨fun i => if i = j then v else fun _ _ => 0, fun i => ?_, fun s x => ?_⟩
  · by_cases h : i = j
    · simp only [h, ite_true]; exact hv
    · simp only [h, ite_false]; exact vanish_zero_fun
  · simp [apply_ite (fun f : ℝ → (Fin n → ℝ) → ℂ => f s x)]

/-- Freezing the parameter at `s₀` keeps the order. -/
theorem vanish_freeze : ∀ {p : ℕ} {v : ℝ → (Fin n → ℝ) → ℂ} (s₀ : ℝ), Vanish K p v →
    Vanish K p (fun _ x => v s₀ x)
  | 0, _, s₀, ⟨h1, h2⟩ =>
    ⟨h1.comp ((contDiff_const (c := s₀)).prodMk contDiff_snd), fun _ x hx => h2 s₀ x hx⟩
  | _ + 1, _, s₀, ⟨w, hw, hv⟩ =>
    ⟨fun j _ x => w j s₀ x, fun j => vanish_freeze s₀ (hw j), fun _ x => hv s₀ x⟩

/-- The derivative of a product `∑ⱼ xⱼ wⱼ(x)` along `eₗ`. -/
theorem coordDeriv_sum_coord_mul {w : Fin n → (Fin n → ℝ) → ℂ}
    (hw : ∀ j, Differentiable ℝ (w j)) (l : Fin n) (x : Fin n → ℝ) :
    coordDeriv (fun y => ∑ j, (y j : ℂ) * w j y) l x =
      w l x + ∑ j, (x j : ℂ) * coordDeriv (w j) l x := by
  classical
  have hc : ∀ j, HasFDerivAt (fun y : Fin n → ℝ => ((y j : ℝ) : ℂ))
      (ofRealCLM.comp (ContinuousLinearMap.proj j)) x := fun j =>
    ofRealCLM.hasFDerivAt.comp x (hasFDerivAt_apply j x)
  have hs : HasFDerivAt (fun y => ∑ j, (y j : ℂ) * w j y)
      (∑ j, (((x j : ℝ) : ℂ) • fderiv ℝ (w j) x +
        w j x • ofRealCLM.comp (ContinuousLinearMap.proj j))) x := by
    refine HasFDerivAt.fun_sum fun j _ => ?_
    exact (hc j).mul ((hw j) x).hasFDerivAt
  unfold coordDeriv
  rw [hs.fderiv]
  simp only [FunLike.coe_sum, Finset.sum_apply, _root_.add_apply,
    _root_.smul_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply,
    smul_eq_mul, ofRealCLM_apply, Finset.sum_add_distrib]
  rw [add_comm]
  congr 1
  simp only [Pi.single_apply]
  rw [Finset.sum_eq_single l (fun b _ hb => by simp [hb]) (by simp)]
  simp

/-- Differentiating once lowers the order of vanishing by one. -/
theorem vanish_coordDeriv (hK : IsClosed K) (l : Fin n) : ∀ {p : ℕ} {v : ℝ → (Fin n → ℝ) → ℂ},
    Vanish K (p + 1) v → Vanish K p (fun s x => coordDeriv (v s) l x)
  | 0, v, hv => by
    have hv0 := vanish_mono hv
    refine ⟨?_, fun s x hx => ?_⟩
    · have h1 : ContDiff ℝ ∞ (Function.uncurry fun (q : ℝ × (Fin n → ℝ)) (y : Fin n → ℝ) =>
          v q.1 y) :=
        hv0.1.comp (contDiff_fst.fst.prodMk contDiff_snd)
      exact (h1.fderiv contDiff_snd (by simp)).clm_apply contDiff_const
    · have hev : v s =ᶠ[𝓝 x] fun _ => 0 :=
        Filter.mem_of_superset (hK.isOpen_compl.mem_nhds hx) fun y hy => hv0.2 s y hy
      show fderiv ℝ (v s) x (Pi.single l 1) = 0
      rw [hev.fderiv_eq]
      simp
  | p + 1, v, ⟨w, hw, hv⟩ => by
    have hd : ∀ s j, Differentiable ℝ (w j s) := fun s j =>
      ((hw j).contDiff_slice s).differentiable (by simp)
    have hrepr : ∀ s, v s = fun y => ∑ j, (y j : ℂ) * w j s y := fun s =>
      funext fun y => hv s y
    have hsum : Vanish K (p + 1) (fun s x => ∑ j, (x j : ℂ) * coordDeriv (w j s) l x) :=
      ⟨fun j s x => coordDeriv (w j s) l x, fun j => vanish_coordDeriv hK l (hw j),
        fun _ _ => rfl⟩
    refine vanish_congr (fun s x => ?_) (vanish_add (hw l) hsum)
    rw [hrepr s, coordDeriv_sum_coord_mul (hd s) l x]

/-! ### Products with a cubic remainder -/

/-- `∑ⱼ xⱼ wⱼ` with every `wⱼ` of order `p` has order `p + 1`. -/
theorem vanish_of_coord_sum {p : ℕ} {w : Fin n → ℝ → (Fin n → ℝ) → ℂ}
    (hw : ∀ j, Vanish K p (w j)) : Vanish K (p + 1) (fun s x => ∑ j, (x j : ℂ) * w j s x) :=
  ⟨w, hw, fun _ _ => rfl⟩

/-- Multiplying by `g = ∑ xᵢ xⱼ xₖ gᵢⱼₖ` raises the order of vanishing by three. -/
theorem vanish_mul_cubic {p : ℕ} {g : (Fin n → ℝ) → ℂ}
    {gc : Fin n → Fin n → Fin n → (Fin n → ℝ) → ℂ} (hgc : ∀ i j k, ContDiff ℝ ∞ (gc i j k))
    (hg : ∀ x, g x = ∑ i, (x i : ℂ) * ∑ j, (x j : ℂ) * ∑ k, (x k : ℂ) * gc i j k x)
    {v : ℝ → (Fin n → ℝ) → ℂ} (hv : Vanish K p v) :
    Vanish K (p + 3) (fun s x => g x * v s x) := by
  have h1 : ∀ i j k, Vanish K p (fun s x => gc i j k x * v s x) := fun i j k =>
    vanish_mul (c := fun _ x => gc i j k x) ((hgc i j k).comp contDiff_snd) hv
  have h3 : Vanish K (p + 3) (fun s x => ∑ i, (x i : ℂ) * ∑ j, (x j : ℂ) *
      ∑ k, (x k : ℂ) * (gc i j k x * v s x)) :=
    vanish_of_coord_sum fun i => vanish_of_coord_sum fun j => vanish_of_coord_sum fun k => h1 i j k
  refine vanish_congr (fun s x => ?_) h3
  simp only [hg, Finset.sum_mul, mul_assoc]

/-! ### Integration by parts -/

/-- The quadratic form `⟨A x, x⟩` is smooth. -/
theorem contDiff_qform (A : Matrix (Fin n) (Fin n) ℂ) : ContDiff ℝ ∞ (qform A) := by
  have hc : ∀ i, ContDiff ℝ ∞ (fun x : Fin n → ℝ => ((x i : ℝ) : ℂ)) := fun i =>
    ofRealCLM.contDiff.comp (contDiff_apply ℝ (fun _ : Fin n => ℝ) i)
  have : qform A = fun x => ∑ i, ∑ j, A i j * (x i : ℂ) * (x j : ℂ) := funext fun x => rfl
  rw [this]
  exact ContDiff.sum fun i _ => ContDiff.sum fun j _ => (contDiff_const.mul (hc i)).mul (hc j)

/-- For symmetric `A`, `∂ₗ(⟨A x, x⟩/2) = (A x)ₗ`. -/
theorem coordDeriv_qform_half {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsSymm) (l : Fin n)
    (x : Fin n → ℝ) : coordDeriv (fun y => qform A y / 2) l x = (A *ᵥ cvec x) l := by
  have hd : DifferentiableAt ℝ (fun y => qform A y / 2) x :=
    ((contDiff_qform A).div_const 2).differentiable (by simp) x
  have hl : HasDerivAt (fun t : ℝ => x + t • (Pi.single l 1 : Fin n → ℝ)) (Pi.single l 1) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (Pi.single l 1 : Fin n → ℝ)).const_add x
  have h1 : HasDerivAt (fun t : ℝ => qform A (x + t • (Pi.single l 1 : Fin n → ℝ)) / 2)
      (fderiv ℝ (fun y => qform A y / 2) x (Pi.single l 1)) 0 :=
    hd.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hl (by simp)
  have h2 := (hasDerivAt_qform_line A x (Pi.single l 1)).div_const 2
  rw [coordDeriv, h1.unique h2, sum_qform_line_single hA x l]
  ring

/-- The derivative of `e^{iτF}` is `e^{iτF} iτ dF`. -/
theorem hasFDerivAt_cexp_phase {F : (Fin n → ℝ) → ℂ} (hF : Differentiable ℝ F) (τ : ℝ)
    (x : Fin n → ℝ) :
    HasFDerivAt (fun y => cexp (I * τ * F y)) (cexp (I * τ * F x) • ((I * τ) • fderiv ℝ F x)) x :=
  ((hF x).hasFDerivAt.const_mul (I * τ)).cexp

/-- One integration by parts: if `∑ₗ cⱼₗ ∂ₗF = xⱼ` on `K` and every `wⱼ` vanishes off `K`, then
`∫ (∑ⱼ xⱼ wⱼ) e^{iτF} = -(iτ)⁻¹ ∑ⱼₗ ∫ ∂ₗ(cⱼₗ wⱼ) e^{iτF}`. -/
theorem integral_ibp_step {F : (Fin n → ℝ) → ℂ} (hF : ContDiff ℝ ∞ F) (hK : IsCompact K)
    {w : Fin n → (Fin n → ℝ) → ℂ} (hw : ∀ j, ContDiff ℝ ∞ (w j))
    (hwK : ∀ j, ∀ x ∉ K, w j x = 0)
    {c : Fin n → Fin n → (Fin n → ℝ) → ℂ} (hc : ∀ j l, ContDiff ℝ ∞ (c j l))
    (hid : ∀ x ∈ K, ∀ j, ∑ l, c j l x * coordDeriv F l x = x j) {τ : ℝ} (hτ : τ ≠ 0) :
    ∫ x, (∑ j, (x j : ℂ) * w j x) * cexp (I * τ * F x) =
      -(1 / (I * τ)) * ∑ j, ∑ l,
        ∫ x, coordDeriv (fun y => c j l y * w j y) l x * cexp (I * τ * F x) := by
  have hFd : Differentiable ℝ F := hF.differentiable (by simp)
  have hEc : ContDiff ℝ ∞ (fun y => cexp (I * τ * F y)) := (contDiff_const.mul hF).cexp
  have hEd := hasFDerivAt_cexp_phase hFd τ
  have hIτ : I * (τ : ℂ) ≠ 0 := mul_ne_zero I_ne_zero (ofReal_ne_zero.mpr hτ)
  have hh : ∀ j l, ContDiff ℝ ∞ (fun y => c j l y * w j y) := fun j l => (hc j l).mul (hw j)
  have hhs : ∀ j l, HasCompactSupport (fun y => c j l y * w j y) := fun j l =>
    HasCompactSupport.intro hK fun x hx => by rw [hwK j x hx, mul_zero]
  have hpt : ∀ x, (∑ j, (x j : ℂ) * w j x) * cexp (I * τ * F x) =
      ∑ j, ∑ l, (1 / (I * τ)) * ((c j l x * w j x) *
        fderiv ℝ (fun y => cexp (I * τ * F y)) x (Pi.single l 1)) := by
    intro x
    rw [(hEd x).fderiv]
    simp only [_root_.smul_apply, smul_eq_mul]
    by_cases hx : x ∈ K
    · rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [← hid x hx j, Finset.sum_mul, Finset.sum_mul]
      refine Finset.sum_congr rfl fun l _ => ?_
      unfold coordDeriv
      field_simp [ofReal_ne_zero.mpr hτ]
    · have h0 : ∀ j, w j x = 0 := fun j => hwK j x hx
      simp [h0]
  have hint : ∀ j l, Integrable (fun x => (c j l x * w j x) *
      fderiv ℝ (fun y => cexp (I * τ * F y)) x (Pi.single l 1)) := fun j l =>
    ((hh j l).continuous.mul ((hEc.continuous_fderiv (by simp)).clm_apply
      continuous_const)).integrable_of_hasCompactSupport (hhs j l).mul_right
  have hint' : ∀ j, Integrable (fun x => ∑ l, (1 / (I * τ)) * ((c j l x * w j x) *
      fderiv ℝ (fun y => cexp (I * τ * F y)) x (Pi.single l 1))) := fun j =>
    integrable_finsetSum _ fun l _ => (hint j l).const_mul _
  rw [show (fun x => (∑ j, (x j : ℂ) * w j x) * cexp (I * τ * F x)) = _ from funext hpt,
    integral_finsetSum _ fun j _ => hint' j]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [integral_finsetSum _ fun l _ => (hint j l).const_mul _, Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [integral_const_mul]
  have hibp := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := volume)
    (f := fun y => c j l y * w j y) (g := fun y => cexp (I * τ * F y)) (v := Pi.single l 1)
    ((((hh j l).continuous_fderiv (by simp)).clm_apply continuous_const).mul
      hEc.continuous |>.integrable_of_hasCompactSupport
        ((hhs j l).fderiv_apply (𝕜 := ℝ) _).mul_right)
    (hint j l)
    (((hh j l).continuous.mul hEc.continuous).integrable_of_hasCompactSupport (hhs j l).mul_right)
    (fun x _ => ((hh j l).differentiable (by simp)) x)
    (fun x _ => (hEc.differentiable (by simp)) x)
  rw [hibp]
  unfold coordDeriv
  ring

/-! ### The uniform bound -/

/-- `|e^{iτz}| ≤ 1` for `τ ≥ 0` and `Im z ≥ 0`. -/
theorem norm_cexp_phase_le {τ : ℝ} (hτ : 0 ≤ τ) {z : ℂ} (hz : 0 ≤ z.im) :
    ‖cexp (I * τ * z)‖ ≤ 1 := by
  rw [Complex.norm_exp, Real.exp_le_one_iff]
  have : (I * τ * z).re = -(τ * z.im) := by
    simp only [mul_re, mul_im, I_re, I_im, ofReal_re, ofReal_im]; ring
  rw [this]
  linarith [mul_nonneg hτ hz]

/-- `|-(iτ)⁻¹| = τ⁻¹` for `τ > 0`. -/
theorem norm_neg_one_div_I_mul {τ : ℝ} (hτ : 0 < τ) : ‖-(1 / (I * (τ : ℂ)))‖ = τ⁻¹ := by
  rw [norm_neg, norm_div, norm_one, norm_mul, norm_I, one_mul, Complex.norm_real,
    Real.norm_of_nonneg hτ.le, one_div]

/-- The crude bound `|∫ v e^{iτF_s}| ≤ C` for `τ ≥ 0`, uniformly in
`s ∈ [0, 1]`, when `Im F_s ≥ 0` on `K`. -/
theorem exists_bound_vanish_zero (hK : IsCompact K) {v : ℝ → (Fin n → ℝ) → ℂ}
    (hv : Vanish K 0 v) {F : ℝ → (Fin n → ℝ) → ℂ}
    (hFim : ∀ s ∈ Icc (0 : ℝ) 1, ∀ x ∈ K, 0 ≤ (F s x).im) :
    ∃ C, ∀ s ∈ Icc (0 : ℝ) 1, ∀ τ : ℝ, 0 ≤ τ →
      ‖∫ x, v s x * cexp (I * τ * F s x)‖ ≤ C := by
  obtain ⟨M, hM⟩ := (isCompact_Icc.prod hK).exists_bound_of_continuousOn
    hv.1.continuous.continuousOn
  refine ⟨M * volume.real K, fun s hs τ hτ => ?_⟩
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := K)
    fun x hx => by rw [hv.2 s x hx, zero_mul]]
  refine norm_setIntegral_le_of_norm_le_const hK.measure_lt_top fun x hx => ?_
  have h1 : ‖v s x‖ ≤ M := hM (s, x) ⟨hs, hx⟩
  rw [norm_mul]
  calc ‖v s x‖ * ‖cexp (I * τ * F s x)‖ ≤ M * 1 :=
        mul_le_mul h1 (norm_cexp_phase_le hτ (hFim s hs x hx)) (norm_nonneg _)
          ((norm_nonneg _).trans h1)
    _ = M := mul_one M

/-- **Uniform bound** (Hörmander, *ALPDO I*, (7.7.1)'): for phases `F_s` with `Im F_s ≥ 0` on `K`
and coefficients with `∑ₗ cⱼₗ ∂ₗF_s = xⱼ` on `K`, an amplitude vanishing to order `p` gives
`|∫ v e^{iτF_s}| ≤ C τ^{-⌊p/2⌋}`, uniformly in `s ∈ [0, 1]`. -/
theorem exists_bound_vanish (hK : IsCompact K) {F : ℝ → (Fin n → ℝ) → ℂ}
    (hF : ∀ s, ContDiff ℝ ∞ (F s))
    (hFim : ∀ s ∈ Icc (0 : ℝ) 1, ∀ x ∈ K, 0 ≤ (F s x).im)
    {c : Fin n → Fin n → ℝ → (Fin n → ℝ) → ℂ}
    (hc : ∀ j l, ContDiff ℝ ∞ (fun p : ℝ × (Fin n → ℝ) => c j l p.1 p.2))
    (hid : ∀ s ∈ Icc (0 : ℝ) 1, ∀ x ∈ K, ∀ j, ∑ l, c j l s x * coordDeriv (F s) l x = x j) :
    ∀ (p : ℕ) {v : ℝ → (Fin n → ℝ) → ℂ}, Vanish K p v →
      ∃ C, ∀ s ∈ Icc (0 : ℝ) 1, ∀ τ : ℝ, 1 ≤ τ →
        ‖∫ x, v s x * cexp (I * τ * F s x)‖ ≤ C * (τ ^ (p / 2))⁻¹
  | 0, v, hv => by
    obtain ⟨C, hC⟩ := exists_bound_vanish_zero hK hv hFim
    exact ⟨C, fun s hs τ hτ => by simpa using hC s hs τ (by linarith)⟩
  | 1, v, hv => by
    obtain ⟨C, hC⟩ := exists_bound_vanish_zero hK (vanish_mono hv) hFim
    exact ⟨C, fun s hs τ hτ => by simpa using hC s hs τ (by linarith)⟩
  | q + 2, v, ⟨w, hw, hv⟩ => by
    have hv' : ∀ j l, Vanish K q (fun s x => coordDeriv (fun y => c j l s y * w j s y) l x) :=
      fun j l => vanish_coordDeriv hK.isClosed l (vanish_mul (hc j l) (hw j))
    choose C hC using fun j l => exists_bound_vanish hK hF hFim hc hid q (hv' j l)
    refine ⟨∑ j, ∑ l, C j l, fun s hs τ hτ => ?_⟩
    have hτ0 : 0 < τ := by linarith
    have hibp := integral_ibp_step (hF s) hK (w := fun j => w j s)
      (fun j => (hw j).contDiff_slice s) (fun j x hx => (hw j).eq_zero s hx)
      (c := fun j l => c j l s)
      (fun j l => (hc j l).comp ((contDiff_const (c := s)).prodMk contDiff_id)) (hid s hs) hτ0.ne'
    have hrw : (fun x => v s x * cexp (I * τ * F s x)) =
        fun x => (∑ j, (x j : ℂ) * w j s x) * cexp (I * τ * F s x) :=
      funext fun x => by rw [hv s x]
    have hq : (q + 2) / 2 = q / 2 + 1 := by omega
    rw [hrw, hibp, norm_mul, norm_neg_one_div_I_mul hτ0, hq, pow_succ, mul_inv, Finset.sum_mul]
    calc τ⁻¹ * ‖∑ j, ∑ l, ∫ x, coordDeriv (fun y => c j l s y * w j s y) l x *
          cexp (I * τ * F s x)‖
        ≤ τ⁻¹ * ∑ j, ∑ l, C j l * (τ ^ (q / 2))⁻¹ := by
          gcongr
          exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => (norm_sum_le _ _).trans
            (Finset.sum_le_sum fun l _ => hC j l s hs τ hτ))
      _ = ∑ j, (∑ l, C j l) * ((τ ^ (q / 2))⁻¹ * τ⁻¹) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [Finset.sum_mul, Finset.mul_sum]
          exact Finset.sum_congr rfl fun l _ => by ring

/-! ### Quadratic phases -/

/-- With the quadratic phase `⟨Ax, x⟩/2`, an amplitude vanishing to order `2m + 1` gives
`O(τ^{-n/2-1-m})` (Hörmander, *ALPDO I*, Lemma 7.7.3 and integration by parts). -/
theorem exists_bound_quad {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsSymm)
    (hIm : ∀ x, 0 ≤ (qform A x).im) (hdet : A.det ≠ 0) (hK : IsCompact K) :
    ∀ (m : ℕ) {v : ℝ → (Fin n → ℝ) → ℂ}, Vanish K (2 * m + 1) v → ∀ s₀ : ℝ,
      ∃ C, ∀ᶠ τ : ℝ in atTop, ‖∫ x, v s₀ x * cexp (I * τ * (qform A x / 2))‖ ≤
        C * τ ^ (-((n : ℝ) / 2) - 1 - m)
  | 0, v, hv, s₀ => by
    obtain ⟨C, τ₀, _, h⟩ := quadratic_phase hA hIm hdet (hv.contDiff_slice s₀)
      (HasCompactSupport.intro hK fun x hx => hv.eq_zero s₀ hx)
    refine ⟨C, eventually_atTop.mpr ⟨τ₀, fun τ hτ => ?_⟩⟩
    have := h τ hτ
    rw [hv.apply_zero s₀, mul_zero, sub_zero] at this
    simp only [mul_div_assoc] at this
    simpa using this
  | m + 1, v, hv, s₀ => by
    obtain ⟨w, hw, hv⟩ := hv
    have hw' : ∀ j, Vanish K (2 * m + 1 + 1) (w j) := fun j => by
      have := hw j
      rwa [show 2 * (m + 1) = 2 * m + 1 + 1 by ring] at this
    have hv' : ∀ j l, Vanish K (2 * m + 1)
        (fun s x => coordDeriv (fun y => A⁻¹ j l * w j s y) l x) := fun j l =>
      vanish_coordDeriv hK.isClosed l (vanish_mul (c := fun _ _ => A⁻¹ j l) contDiff_const (hw' j))
    choose C hC using fun j l => exists_bound_quad hA hIm hdet hK m (hv' j l) s₀
    have hev : ∀ᶠ τ : ℝ in atTop, ∀ j l,
        ‖∫ x, coordDeriv (fun y => A⁻¹ j l * w j s₀ y) l x * cexp (I * τ * (qform A x / 2))‖ ≤
          C j l * τ ^ (-((n : ℝ) / 2) - 1 - m) :=
      eventually_all.mpr fun j => eventually_all.mpr fun l => hC j l
    refine ⟨∑ j, ∑ l, C j l, (hev.and (eventually_gt_atTop 0)).mono fun τ ⟨hb, hτ0⟩ => ?_⟩
    have hunit : IsUnit A.det := isUnit_iff_ne_zero.mpr hdet
    have hibp := integral_ibp_step (F := fun x => qform A x / 2) ((contDiff_qform A).div_const 2)
      hK (w := fun j => w j s₀) (fun j => (hw j).contDiff_slice s₀)
      (fun j x hx => (hw j).eq_zero s₀ hx) (c := fun j l _ => A⁻¹ j l)
      (fun _ _ => contDiff_const) (fun x _ j => by
        simp only [coordDeriv_qform_half hA]
        change (A⁻¹ *ᵥ (A *ᵥ cvec x)) j = _
        rw [mulVec_mulVec, nonsing_inv_mul A hunit, one_mulVec]
        rfl) hτ0.ne'
    have hrw : (fun x => v s₀ x * cexp (I * τ * (qform A x / 2))) =
        fun x => (∑ j, (x j : ℂ) * w j s₀ x) * cexp (I * τ * (qform A x / 2)) :=
      funext fun x => by rw [hv s₀ x]
    have he : (-((n : ℝ) / 2) - 1 - ((m + 1 : ℕ) : ℝ)) = (-((n : ℝ) / 2) - 1 - m) - 1 := by
      push_cast; ring
    rw [hrw, hibp, norm_mul, norm_neg_one_div_I_mul hτ0, he, Real.rpow_sub_one hτ0.ne']
    calc τ⁻¹ * ‖∑ j, ∑ l, ∫ x, coordDeriv (fun y => A⁻¹ j l * w j s₀ y) l x *
          cexp (I * τ * (qform A x / 2))‖
        ≤ τ⁻¹ * ∑ j, ∑ l, C j l * τ ^ (-((n : ℝ) / 2) - 1 - m) := by
          gcongr
          exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => (norm_sum_le _ _).trans
            (Finset.sum_le_sum fun l _ => hb j l))
      _ = (∑ j, ∑ l, C j l) * (τ ^ (-((n : ℝ) / 2) - 1 - m) / τ) := by
          rw [Finset.sum_mul, Finset.mul_sum]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [Finset.sum_mul, Finset.mul_sum]
          exact Finset.sum_congr rfl fun l _ => by ring

end Lightlike.Oscillatory
