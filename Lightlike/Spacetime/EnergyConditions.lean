import Lightlike.Spacetime.Lorentzian

/-!
# Energy conditions (GE14, stage 1)

Pointwise energy conditions of a symmetric bilinear form `T` (the stress-energy tensor at a point) on a Lorentzian vector space `(V, g)`:
`NullEC`, `WeakEC`, `StrongEC` (dimension four) and `DominantEC` (Curiel, *A Primer on Energy Conditions*, section 2.1, physical forms).
Proved: reverse Cauchy-Schwarz for a timelike vector, the sign rule for timelike vectors in a Lorentz frame (`lorentz_sign`), co-oriented timelike vectors pair with a
timelike vector with a common sign (`lorentz_coorient`), the `g`-trace in a Lorentz frame (`traceG_eq_sum`); trust checks: dust with `ρ ≥ 0` satisfies all four,
a positive cosmological constant violates the strong condition, a scalar field at a point of vanishing gradient with a negative potential violates the weak one; the effective forms for a perfect fluid (`fluid_nullEC_iff`: `ρ + p ≥ 0`, `fluid_weakEC_iff`: `ρ ≥ 0` and `ρ + p ≥ 0`, `fluid_strongEC_iff`: `ρ + p ≥ 0` and `ρ + 3p ≥ 0`, `fluid_dominantEC_iff`: `|p| ≤ ρ`).

**Limits.** Pointwise statements on a vector space; no manifold or time-orientation field, the stress-energy is a form at a point, not a field.
-/

open Module

noncomputable section
namespace Lightlike

variable {V : Type*} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]

/-- The `g`-trace of a bilinear form `T`: the trace of the endomorphism `g⁻¹ T` (basis-free). -/
def traceG [FiniteDimensional ℝ V] (g T : V →L[ℝ] V →L[ℝ] ℝ) (hg : g.toBilinForm.Nondegenerate) : ℝ :=
  LinearMap.trace ℝ V (((g.toBilinForm).toDual hg).symm.toLinearMap ∘ₗ T.toBilinForm)


/-- **The `g`-trace in a Lorentz frame**: `tr_g T = Σ ηᵢᵢ T(eᵢ, eᵢ)`. -/
theorem traceG_eq_sum [FiniteDimensional ℝ V] {n : ℕ} (g T : V →L[ℝ] V →L[ℝ] ℝ) (hg : g.toBilinForm.Nondegenerate)
    (e : Module.Basis (Fin n) ℝ V) (he : ∀ i j, g (e i) (e j) = eta n i j) :
    traceG g T hg = ∑ i, etaDiag i * T (e i) (e i) := by
  unfold traceG
  rw [LinearMap.trace_eq_matrix_trace ℝ e]
  have key : ∀ x : V, (((g.toBilinForm).toDual hg).symm.toLinearMap ∘ₗ T.toBilinForm) x =
      ∑ k, (etaDiag k * T x (e k)) • e k := by
    intro x
    show ((g.toBilinForm).toDual hg).symm (T.toBilinForm x) = _
    rw [LinearEquiv.symm_apply_eq]
    refine e.ext fun l => ?_
    simp only [LinearMap.BilinForm.toDual_def, map_sum, map_smul, ContinuousLinearMap.coe_coe]
    have hd : ∀ k l, (g.toBilinForm.toDual hg) (e k) (e l) = eta n k l := fun k l => he k l
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, hd, smul_eq_mul, eta_apply]
    rw [Finset.sum_eq_single l]
    · simp only [if_true]
      have h := etaDiag_mul_self l
      show (T x) (e l) = etaDiag l * (T x) (e l) * etaDiag l
      calc (T x) (e l) = (etaDiag l * etaDiag l) * (T x) (e l) := by rw [h, one_mul]
        _ = _ := by ring
    · intro k _ hk; simp [hk]
    · simp
  simp only [Matrix.trace, Matrix.diag, LinearMap.toMatrix_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [key]
  simp [map_sum, Finsupp.single_apply]


/-- real inequality behind the reverse Cauchy–Schwarz inequality of Lorentzian geometry -/
theorem lorentz_ineq {a b p sx sy : ℝ} (hsx : 0 ≤ sx) (hsy : 0 ≤ sy) (hp : p ^ 2 ≤ sx * sy)
    (ha : sx < a ^ 2) (hb : sy < b ^ 2) :
    (a ^ 2 - sx) * (b ^ 2 - sy) ≤ (a * b - p) ^ 2 := by
  set u := Real.sqrt sx with hu
  set w := Real.sqrt sy with hw
  have hu2 : u ^ 2 = sx := Real.sq_sqrt hsx
  have hw2 : w ^ 2 = sy := Real.sq_sqrt hsy
  have hu0 : 0 ≤ u := Real.sqrt_nonneg _
  have hw0 : 0 ≤ w := Real.sqrt_nonneg _
  have hpuw : |p| ≤ u * w := by
    apply abs_le_of_sq_le_sq' _ (mul_nonneg hu0 hw0) |>.elim (fun h1 h2 => abs_le.2 ⟨h1, h2⟩)
    rw [mul_pow, hu2, hw2]; exact hp
  have hau : u < |a| := by
    rw [← abs_of_nonneg hu0]; exact sq_lt_sq.1 (by rw [hu2]; exact ha)
  have hbw : w < |b| := by
    rw [← abs_of_nonneg hw0]; exact sq_lt_sq.1 (by rw [hw2]; exact hb)
  have h1 : u * w ≤ |a| * |b| := mul_le_mul hau.le hbw.le hw0 (abs_nonneg _)
  have h2 : |a| * |b| - u * w ≤ |a * b - p| := by
    have := abs_sub_abs_le_abs_sub (a * b) p
    rw [abs_mul] at this
    linarith [abs_le.1 (le_refl |p|)]
  have h3 : (|a| * |b| - u * w) ^ 2 ≤ (a * b - p) ^ 2 := by
    rw [← sq_abs (a * b - p)]
    exact pow_le_pow_left₀ (by linarith) h2 2
  have h4 : (a ^ 2 - sx) * (b ^ 2 - sy) ≤ (|a| * |b| - u * w) ^ 2 := by
    rw [← hu2, ← hw2]
    have : (|a| * |b| - u * w) ^ 2 - (a ^ 2 - u ^ 2) * (b ^ 2 - w ^ 2) = (|a| * w - u * |b|) ^ 2 := by
      have e1 : a ^ 2 = |a| ^ 2 := (sq_abs a).symm
      have e2 : b ^ 2 = |b| ^ 2 := (sq_abs b).symm
      rw [e1, e2]; ring
    nlinarith [sq_nonneg (|a| * w - u * |b|)]
  linarith


section Frame
variable {V : Type*} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]

/-- the form in coordinates of a Lorentz frame, time first -/
theorem lorentz_apply {m : ℕ} {g : V →L[ℝ] V →L[ℝ] ℝ} (e : Module.Basis (Fin (m + 1)) ℝ V)
    (he : ∀ i j, g (e i) (e j) = eta (m + 1) i j) (v w : V) :
    g v w = -(e.repr v 0 * e.repr w 0) + ∑ i : Fin m, e.repr v i.succ * e.repr w i.succ := by
  rw [IsLorentzianForm.apply_eq_sum e he, Fin.sum_univ_succ]
  simp [etaDiag]

/-- **Reverse Cauchy–Schwarz inequality**: for a timelike `u`, `g(u, v)² ≥ g(u, u) g(v, v)`. -/
theorem lorentz_reverse_cs {m : ℕ} {g : V →L[ℝ] V →L[ℝ] ℝ} (hg : IsLorentzianForm (m + 1) g) {u : V}
    (hu : g u u < 0) (v : V) : g u u * g v v ≤ g u v ^ 2 := by
  obtain ⟨e, he⟩ := hg
  rw [lorentz_apply e he u u, lorentz_apply e he v v, lorentz_apply e he u v] at *
  set a := e.repr u 0
  set b := e.repr v 0
  set sx := ∑ i : Fin m, e.repr u i.succ * e.repr u i.succ
  set sy := ∑ i : Fin m, e.repr v i.succ * e.repr v i.succ
  set p := ∑ i : Fin m, e.repr u i.succ * e.repr v i.succ
  have hsx : 0 ≤ sx := Finset.sum_nonneg fun i _ => mul_self_nonneg _
  have hsy : 0 ≤ sy := Finset.sum_nonneg fun i _ => mul_self_nonneg _
  have hcs : p ^ 2 ≤ sx * sy := by
    have := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun i : Fin m => e.repr u i.succ) (fun i => e.repr v i.succ)
    simpa [sq, p, sx, sy] using this
  by_cases hv : -(b * b) + sy < 0
  · have := lorentz_ineq hsx hsy hcs (a := a) (b := b) (by nlinarith) (by nlinarith)
    nlinarith
  · push_neg at hv
    nlinarith [sq_nonneg (-(a * b) + p)]


/-- for timelike `x, y` the sign of `g(x, y)` is opposite to that of the product of the time components -/
theorem lorentz_sign {m : ℕ} {g : V →L[ℝ] V →L[ℝ] ℝ} (e : Module.Basis (Fin (m + 1)) ℝ V)
    (he : ∀ i j, g (e i) (e j) = eta (m + 1) i j) {x y : V} (hx : g x x < 0) (hy : g y y < 0) :
    g x y * (e.repr x 0 * e.repr y 0) < 0 := by
  rw [lorentz_apply e he x x] at hx
  rw [lorentz_apply e he y y] at hy
  rw [lorentz_apply e he x y]
  set a := e.repr x 0
  set b := e.repr y 0
  set sx := ∑ i : Fin m, e.repr x i.succ * e.repr x i.succ
  set sy := ∑ i : Fin m, e.repr y i.succ * e.repr y i.succ
  set p := ∑ i : Fin m, e.repr x i.succ * e.repr y i.succ
  have hsx : 0 ≤ sx := Finset.sum_nonneg fun i _ => mul_self_nonneg _
  have hsy : 0 ≤ sy := Finset.sum_nonneg fun i _ => mul_self_nonneg _
  have hcs : p ^ 2 ≤ sx * sy := by
    have := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun i : Fin m => e.repr x i.succ) (fun i => e.repr y i.succ)
    simpa [sq, p, sx, sy] using this
  have hxa : sx < a ^ 2 := by nlinarith
  have hyb : sy < b ^ 2 := by nlinarith
  -- |p| < |a b|
  have hp : p ^ 2 < (a * b) ^ 2 := by
    calc p ^ 2 ≤ sx * sy := hcs
      _ < a ^ 2 * b ^ 2 := by nlinarith [mul_pos (sub_pos.2 hxa) (sub_pos.2 hyb)]
      _ = (a * b) ^ 2 := by ring
  have hab : 0 < (a * b) ^ 2 := lt_of_le_of_lt (sq_nonneg p) hp
  have habp : |p| < |a * b| := sq_lt_sq.1 hp
  have : p * (a * b) ≤ |p| * |a * b| := by
    rw [← abs_mul]; exact le_abs_self _
  have hpos : 0 < |a * b| := lt_of_le_of_lt (abs_nonneg p) habp
  have h5 : |p| * |a * b| < |a * b| * |a * b| := mul_lt_mul_of_pos_right habp hpos
  have h6 : |a * b| * |a * b| = (a * b) * (a * b) := abs_mul_abs_self (a * b)
  nlinarith

end Frame


section Conditions
variable {V : Type*} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]

/-- **Co-oriented timelike vectors pair with a timelike vector with the same sign.** -/
theorem lorentz_coorient {m : ℕ} {g : V →L[ℝ] V →L[ℝ] ℝ} (hg : IsLorentzianForm (m + 1) g) {u ξ η : V}
    (hu : g u u < 0) (hξ : g ξ ξ < 0) (hη : g η η < 0) (hξη : g ξ η < 0) : 0 < g u ξ * g u η := by
  obtain ⟨e, he⟩ := hg
  have h1 := lorentz_sign e he hu hξ
  have h2 := lorentz_sign e he hu hη
  have h3 := lorentz_sign e he hξ hη
  set a := e.repr u 0
  set b := e.repr ξ 0
  set c := e.repr η 0
  have hbc : 0 < b * c := by
    by_contra h
    push_neg at h
    nlinarith
  have ha : 0 < a ^ 2 := by
    have : a ≠ 0 := by
      intro h0
      rw [h0] at h1
      simp at h1
    positivity
  have : g u ξ * g u η * (a ^ 2 * (b * c)) = (g u ξ * (a * b)) * (g u η * (a * c)) := by ring
  have hpos : 0 < (g u ξ * (a * b)) * (g u η * (a * c)) := mul_pos_of_neg_of_neg h1 h2
  rw [← this] at hpos
  exact (mul_pos_iff_of_pos_right (by positivity)).1 hpos

end Conditions


section Definitions
variable {V : Type*} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]

/-- **Null energy condition**: `T(k, k) ≥ 0` for every null vector `k`. -/
def NullEC (g T : V →L[ℝ] V →L[ℝ] ℝ) : Prop := ∀ k : V, g k k = 0 → 0 ≤ T k k

/-- **Weak energy condition**: `T(v, v) ≥ 0` for every timelike vector `v`. -/
def WeakEC (g T : V →L[ℝ] V →L[ℝ] ℝ) : Prop := ∀ v : V, g v v < 0 → 0 ≤ T v v

/-- **Strong energy condition** (dimension four): `(T − ½ tr_g T · g)(v, v) ≥ 0` for every timelike vector `v`. -/
def StrongEC [FiniteDimensional ℝ V] (g T : V →L[ℝ] V →L[ℝ] ℝ) (hg : IsLorentzianForm 4 g) : Prop :=
  ∀ v : V, g v v < 0 → 0 ≤ T v v - (1 / 2) * traceG g T hg.bilinForm_nondegenerate * g v v

/-- The vector `T^a_n ξ^n`: the `g`-dual of the covector `T(ξ, ·)`. -/
def raiseT [FiniteDimensional ℝ V] (g T : V →L[ℝ] V →L[ℝ] ℝ) (hg : g.toBilinForm.Nondegenerate) (ξ : V) : V :=
  ((g.toBilinForm).toDual hg).symm (T.toBilinForm ξ)

/-- **Dominant energy condition** (dimension four, Curiel's physical form): for timelike `ξ`, `T(ξ, ξ) ≥ 0` and `T^a_n ξ^n` is causal;
for co-oriented timelike `ξ, η` (`g(ξ, η) < 0`), `T(ξ, η) ≥ 0`. -/
def DominantEC [FiniteDimensional ℝ V] (g T : V →L[ℝ] V →L[ℝ] ℝ) (hg : IsLorentzianForm 4 g) : Prop :=
  (∀ ξ : V, g ξ ξ < 0 → 0 ≤ T ξ ξ ∧
      g (raiseT g T hg.bilinForm_nondegenerate ξ) (raiseT g T hg.bilinForm_nondegenerate ξ) ≤ 0) ∧
    ∀ ξ η : V, g ξ ξ < 0 → g η η < 0 → g ξ η < 0 → 0 ≤ T ξ η

/-- The stress-energy of dust with four-velocity `u` and density `ρ`: `ρ u ⊗ u` (with `u` lowered by `g`). -/
def dustT (g : V →L[ℝ] V →L[ℝ] ℝ) (u : V) (ρ : ℝ) : V →L[ℝ] V →L[ℝ] ℝ :=
  ρ • (g u).smulRight (g u)

theorem dustT_apply (g : V →L[ℝ] V →L[ℝ] ℝ) (u : V) (ρ : ℝ) (v w : V) : dustT g u ρ v w = ρ * (g u v * g u w) := by
  simp [dustT]

end Definitions


section Checks
variable {V : Type*} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]

/-- The `g`-trace of `ρ u ⊗ u` is `ρ g(u, u)`. -/
theorem traceG_dust [FiniteDimensional ℝ V] {g : V →L[ℝ] V →L[ℝ] ℝ} (hg : IsLorentzianForm 4 g) (u : V) (ρ : ℝ) :
    traceG g (dustT g u ρ) hg.bilinForm_nondegenerate = ρ * g u u := by
  obtain ⟨e, he⟩ := hg
  rw [traceG_eq_sum g (dustT g u ρ) _ e he]
  have hgu : ∀ i, g u (e i) = etaDiag i * e.repr u i := fun i => by
    rw [IsLorentzianForm.apply_eq_sum e he]
    simp [Finset.sum_eq_single i, Module.Basis.repr_self, Finsupp.single_apply]
  have huu : g u u = ∑ i, etaDiag i * (e.repr u i * e.repr u i) := by
    rw [IsLorentzianForm.apply_eq_sum e he]
    exact Finset.sum_congr rfl fun i _ => by ring
  simp only [dustT_apply, hgu, huu, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h := etaDiag_mul_self i
  calc etaDiag i * (ρ * (etaDiag i * e.repr u i * (etaDiag i * e.repr u i)))
      = (etaDiag i * etaDiag i) * (etaDiag i * ρ * (e.repr u i * e.repr u i)) := by ring
    _ = ρ * (etaDiag i * (e.repr u i * e.repr u i)) := by rw [h]; ring

/-- `T^a_n ξ^n = ρ g(u, ξ) u` for dust. -/
theorem raiseT_dust [FiniteDimensional ℝ V] {g : V →L[ℝ] V →L[ℝ] ℝ} (hg : IsLorentzianForm 4 g) (u : V) (ρ : ℝ) (ξ : V) :
    raiseT g (dustT g u ρ) hg.bilinForm_nondegenerate ξ = (ρ * g u ξ) • u := by
  unfold raiseT
  rw [LinearEquiv.symm_apply_eq]
  refine LinearMap.ext fun w => ?_
  simp [dustT, LinearMap.BilinForm.toDual_def]
  ring


/-- **Dust with `ρ ≥ 0` satisfies all four energy conditions** (trust check of GE14). -/
theorem dust_energyConditions [FiniteDimensional ℝ V] {g : V →L[ℝ] V →L[ℝ] ℝ} (hg : IsLorentzianForm 4 g) {u : V}
    (hu : g u u = -1) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    NullEC g (dustT g u ρ) ∧ WeakEC g (dustT g u ρ) ∧ StrongEC g (dustT g u ρ) hg ∧ DominantEC g (dustT g u ρ) hg := by
  have hsq : ∀ v, 0 ≤ dustT g u ρ v v := fun v => by
    rw [dustT_apply]; nlinarith [mul_self_nonneg (g u v)]
  refine ⟨fun k _ => hsq k, fun v _ => hsq v, ?_, ?_, ?_⟩
  · intro v hv
    rw [traceG_dust hg, hu, dustT_apply]
    have h1 := lorentz_reverse_cs hg (u := u) (by rw [hu]; norm_num) v
    rw [hu] at h1
    nlinarith [mul_nonneg hρ (neg_nonneg.2 hv.le)]
  · intro ξ hξ
    refine ⟨hsq ξ, ?_⟩
    rw [raiseT_dust hg]
    simp only [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul, hu]
    nlinarith [mul_self_nonneg (ρ * g u ξ)]
  · intro ξ η hξ hη hξη
    rw [dustT_apply]
    have := lorentz_coorient hg (u := u) (by rw [hu]; norm_num) hξ hη hξη
    exact mul_nonneg hρ this.le

end Checks


section MoreChecks
variable {V : Type*} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]

/-- The stress-energy of a cosmological constant with vacuum energy density `ρΛ = Λ / (8πG)`: `T = −ρΛ g`. -/
def cosmoT (g : V →L[ℝ] V →L[ℝ] ℝ) (ρΛ : ℝ) : V →L[ℝ] V →L[ℝ] ℝ := (-ρΛ) • g

/-- The `g`-trace of `g` is the dimension. -/
theorem traceG_self [FiniteDimensional ℝ V] {g : V →L[ℝ] V →L[ℝ] ℝ} (hg : IsLorentzianForm 4 g) :
    traceG g g hg.bilinForm_nondegenerate = 4 := by
  obtain ⟨e, he⟩ := hg
  rw [traceG_eq_sum g g _ e he]
  simp only [he, eta_apply, if_true]
  simp [etaDiag_mul_self]

/-- **A positive cosmological constant satisfies the weak (and null) energy condition and violates the strong one** (trust check of GE14). -/
theorem cosmo_energyConditions [FiniteDimensional ℝ V] {g : V →L[ℝ] V →L[ℝ] ℝ} (hg : IsLorentzianForm 4 g) {ρΛ : ℝ}
    (hρ : 0 < ρΛ) :
    NullEC g (cosmoT g ρΛ) ∧ WeakEC g (cosmoT g ρΛ) ∧ ¬ StrongEC g (cosmoT g ρΛ) hg := by
  have hT : ∀ v, cosmoT g ρΛ v v = -ρΛ * g v v := fun v => by simp [cosmoT]
  refine ⟨fun k hk => by rw [hT, hk]; simp, fun v hv => by rw [hT]; nlinarith, ?_⟩
  intro hS
  obtain ⟨v, hv⟩ := hg.exists_timelike (by norm_num)
  have h := hS v hv
  have htr : traceG g (cosmoT g ρΛ) hg.bilinForm_nondegenerate = -4 * ρΛ := by
    obtain ⟨e, he⟩ := hg
    rw [traceG_eq_sum g _ _ e he]
    have : ∀ i : Fin 4, etaDiag i * cosmoT g ρΛ (e i) (e i) = -ρΛ := fun i => by
      simp only [cosmoT, he, eta_apply, if_true, ContinuousLinearMap.smul_apply, smul_eq_mul]
      calc etaDiag i * (-ρΛ * etaDiag i) = -ρΛ * (etaDiag i * etaDiag i) := by ring
        _ = -ρΛ := by rw [etaDiag_mul_self]; ring
    simp only [this]
    simp
  rw [htr, hT] at h
  nlinarith

end MoreChecks


section Scalar
variable {V : Type*} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]

/-- The stress-energy of a Klein–Gordon field with potential `V(φ)` at a point where `dφ` is given: `T = dφ ⊗ dφ − (½ |dφ|² + V) g`. -/
def scalarT [FiniteDimensional ℝ V] (g : V →L[ℝ] V →L[ℝ] ℝ) (hg : IsLorentzianForm 4 g) (dφ : V →L[ℝ] ℝ) (Vp : ℝ) :
    V →L[ℝ] V →L[ℝ] ℝ :=
  dφ.smulRight dφ - ((1 / 2) * traceG g (dφ.smulRight dφ) hg.bilinForm_nondegenerate + Vp) • g

/-- **A Klein–Gordon field with negative potential violates the weak energy condition** at a point where `dφ = 0` (trust check of GE14). -/
theorem scalar_negative_potential_violates_weak [FiniteDimensional ℝ V] {g : V →L[ℝ] V →L[ℝ] ℝ} (hg : IsLorentzianForm 4 g)
    {Vp : ℝ} (hV : Vp < 0) : ¬ WeakEC g (scalarT g hg 0 Vp) := by
  intro hW
  obtain ⟨v, hv⟩ := hg.exists_timelike (by norm_num)
  have h := hW v hv
  have h0 : traceG g ((0 : V →L[ℝ] ℝ).smulRight (0 : V →L[ℝ] ℝ)) hg.bilinForm_nondegenerate = 0 := by
    have h00 : ContinuousLinearMap.toBilinForm (0 : V →L[ℝ] V →L[ℝ] ℝ) = 0 := by
      ext x y; simp [ContinuousLinearMap.toBilinForm]
    simp [traceG, h00]
  simp only [scalarT, h0] at h
  simp at h
  nlinarith

end Scalar

section Fluid
variable {V : Type*} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]

theorem lorentz_symm_aux {n : ℕ} {g : V →L[ℝ] V →L[ℝ] ℝ} (hg : IsLorentzianForm n g) (v w : V) : g v w = g w v := hg.symm v w

/-- **A unit spacelike vector orthogonal to a timelike one exists** (dimension at least two). -/
theorem exists_orth_spacelike {m : ℕ} {g : V →L[ℝ] V →L[ℝ] ℝ} (hg : IsLorentzianForm (m + 2) g) {u : V}
    (hu : g u u < 0) : ∃ w : V, g u w = 0 ∧ g w w = 1 := by
  obtain ⟨e, he⟩ := hg
  have hcoord := lorentz_apply (m := m + 1) (g := g) e he
  set a := e.repr u 0 with ha
  set b := e.repr u (Fin.succ 0) with hb
  have hu' : g u u = -(a * a) + ∑ i : Fin (m + 1), e.repr u i.succ * e.repr u i.succ := hcoord u u
  have hb2 : b * b ≤ ∑ i : Fin (m + 1), e.repr u i.succ * e.repr u i.succ :=
    Finset.single_le_sum (f := fun i : Fin (m + 1) => e.repr u i.succ * e.repr u i.succ)
      (fun i _ => mul_self_nonneg _) (Finset.mem_univ 0)
  have ha0 : a ≠ 0 := by
    intro h0; rw [h0] at hu'
    have : 0 ≤ ∑ i : Fin (m + 1), e.repr u i.succ * e.repr u i.succ := Finset.sum_nonneg fun i _ => mul_self_nonneg _
    linarith
  let w0 : V := (b / a) • e 0 + e (Fin.succ 0)
  have hc0 : e.repr w0 0 = b / a := by
    simp [w0, Module.Basis.repr_self, Finsupp.single_apply, Fin.succ_ne_zero]
  have hs : ∀ j : Fin (m + 1), (j.succ : Fin (m + 2)) = 1 ↔ j = 0 := fun j => by
    rw [← Fin.succ_zero_eq_one, Fin.succ_inj]
  have hcj : ∀ j : Fin (m + 1), e.repr w0 j.succ = if j = 0 then 1 else 0 := by
    intro j
    simp [w0, Module.Basis.repr_self, Finsupp.single_apply, Fin.succ_ne_zero, Fin.succ_inj, eq_comm, hs]
  have hsum : ∀ f : Fin (m + 1) → ℝ, ∑ i : Fin (m + 1), e.repr u i.succ * (e.repr w0 i.succ) = e.repr u (Fin.succ 0) := by
    intro f
    simp only [hcj]
    simp
  have hsum2 : ∑ i : Fin (m + 1), e.repr w0 i.succ * e.repr w0 i.succ = 1 := by
    simp only [hcj]
    simp
  have hw0 : g u w0 = 0 := by
    rw [hcoord u w0, hc0, hsum (fun _ => 0)]
    field_simp
    ring
  have hww : g w0 w0 = 1 - (b / a) ^ 2 := by
    rw [hcoord w0 w0, hc0, hsum2]; ring
  have hpos : 0 < g w0 w0 := by
    rw [hww]
    have hab : (b / a) ^ 2 < 1 := by
      rw [div_pow, div_lt_one (by positivity)]
      nlinarith
    linarith
  refine ⟨(Real.sqrt (g w0 w0))⁻¹ • w0, ?_, ?_⟩
  · simp [hw0]
  · simp only [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]
    have h2 : Real.sqrt (g w0 w0) * Real.sqrt (g w0 w0) = g w0 w0 := Real.mul_self_sqrt hpos.le
    have h3 : Real.sqrt (g w0 w0) ≠ 0 := (Real.sqrt_pos.2 hpos).ne'
    field_simp
    linarith


/-- The stress-energy of a perfect fluid with four-velocity `u`, energy density `ρ` and pressure `p`: `(ρ + p) u ⊗ u + p g`. -/
def fluidT (g : V →L[ℝ] V →L[ℝ] ℝ) (u : V) (ρ p : ℝ) : V →L[ℝ] V →L[ℝ] ℝ :=
  dustT g u (ρ + p) + p • g

theorem fluidT_apply (g : V →L[ℝ] V →L[ℝ] ℝ) (u : V) (ρ p : ℝ) (v w : V) :
    fluidT g u ρ p v w = (ρ + p) * (g u v * g u w) + p * g v w := by
  simp [fluidT, dustT_apply]

/-- The `g`-trace of a perfect fluid: `−(ρ + p) + 4p = 3p − ρ`. -/
theorem traceG_fluid [FiniteDimensional ℝ V] {g : V →L[ℝ] V →L[ℝ] ℝ} (hg : IsLorentzianForm 4 g) {u : V}
    (hu : g u u = -1) (ρ p : ℝ) :
    traceG g (fluidT g u ρ p) hg.bilinForm_nondegenerate = 3 * p - ρ := by
  have hd := traceG_dust hg u (ρ + p)
  have hs := traceG_self hg
  obtain ⟨e, he⟩ := hg
  rw [traceG_eq_sum g _ _ e he] at hd hs ⊢
  have : ∀ i, etaDiag i * fluidT g u ρ p (e i) (e i) =
      etaDiag i * dustT g u (ρ + p) (e i) (e i) + p * (etaDiag i * g (e i) (e i)) := fun i => by
    rw [fluidT_apply, dustT_apply]; ring
  simp only [this, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [hd, hs, hu]; ring

/-- the limit used to extract `ρ + p ≥ 0`: a continuous function nonnegative for positive arguments is nonnegative at `0` -/
theorem nonneg_of_pos_nonneg {f : ℝ → ℝ} (hf : Continuous f) (h : ∀ ε : ℝ, 0 < ε → 0 ≤ f ε) : 0 ≤ f 0 := by
  have h1 : Filter.Tendsto f (nhdsWithin 0 (Set.Ioi 0)) (nhds (f 0)) := hf.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  exact ge_of_tendsto h1 (Filter.eventually_of_mem (self_mem_nhdsWithin : Set.Ioi (0 : ℝ) ∈ nhdsWithin 0 (Set.Ioi 0)) h)


section FluidIff
variable [FiniteDimensional ℝ V] {g : V →L[ℝ] V →L[ℝ] ℝ} {u : V} {ρ p : ℝ}

/-- the null vector `u + w` and the timelike vectors `u + w + ε u` of a unit timelike `u` -/
theorem null_timelike_family (hg : IsLorentzianForm 4 g) (hu : g u u = -1) :
    ∃ k : V, g k k = 0 ∧ g u k = -1 ∧ ∀ ε : ℝ, g (k + ε • u) (k + ε • u) = -(2 * ε) - ε ^ 2 ∧ g u (k + ε • u) = -1 - ε := by
  obtain ⟨w, hw1, hw2⟩ := exists_orth_spacelike (m := 2) hg (u := u) (by rw [hu]; norm_num)
  have hwu : g w u = 0 := by
    have := lorentz_symm_aux hg u w
    linarith
  refine ⟨u + w, ?_, ?_, fun ε => ?_⟩
  · simp only [map_add, ContinuousLinearMap.add_apply, hu, hw1, hw2, hwu]; ring
  · simp only [map_add, ContinuousLinearMap.add_apply, hu, hw1]; ring
  · constructor
    · simp only [map_add, map_smul, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul, hu, hw1, hw2, hwu]
      ring
    · simp only [map_add, map_smul, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul, hu, hw1]
      ring


/-- **Perfect fluid, null energy condition**: `ρ + p ≥ 0`. -/
theorem fluid_nullEC_iff (hg : IsLorentzianForm 4 g) (hu : g u u = -1) :
    NullEC g (fluidT g u ρ p) ↔ 0 ≤ ρ + p := by
  obtain ⟨k, hk0, hk1, -⟩ := null_timelike_family hg hu
  constructor
  · intro h
    have := h k hk0
    rw [fluidT_apply, hk0, hk1] at this
    linarith
  · intro h k' hk'
    rw [fluidT_apply, hk']
    nlinarith [mul_self_nonneg (g u k')]

/-- **Perfect fluid, weak energy condition**: `ρ ≥ 0` and `ρ + p ≥ 0`. -/
theorem fluid_weakEC_iff (hg : IsLorentzianForm 4 g) (hu : g u u = -1) :
    WeakEC g (fluidT g u ρ p) ↔ 0 ≤ ρ ∧ 0 ≤ ρ + p := by
  obtain ⟨k, hk0, hk1, hfam⟩ := null_timelike_family hg hu
  constructor
  · intro h
    have hρ : 0 ≤ ρ := by
      have := h u (by rw [hu]; norm_num)
      rw [fluidT_apply, hu] at this
      nlinarith
    refine ⟨hρ, ?_⟩
    have hf : 0 ≤ (fun ε : ℝ => (ρ + p) * (1 + ε) ^ 2 + p * (-(2 * ε) - ε ^ 2)) 0 := by
      refine nonneg_of_pos_nonneg (f := fun ε : ℝ => (ρ + p) * (1 + ε) ^ 2 + p * (-(2 * ε) - ε ^ 2)) (by fun_prop) fun ε hε => ?_
      have := h (k + ε • u) (by rw [(hfam ε).1]; nlinarith)
      rw [fluidT_apply, (hfam ε).1, (hfam ε).2] at this
      nlinarith
    simpa using hf
  · rintro ⟨hρ, hρp⟩ v hv
    rw [fluidT_apply]
    have h1 := lorentz_reverse_cs hg (u := u) (by rw [hu]; norm_num) v
    rw [hu] at h1
    nlinarith [mul_nonneg hρp (sub_nonneg.2 h1), mul_nonneg hρ (neg_nonneg.2 hv.le)]

/-- **Perfect fluid, strong energy condition**: `ρ + p ≥ 0` and `ρ + 3p ≥ 0`. -/
theorem fluid_strongEC_iff (hg : IsLorentzianForm 4 g) (hu : g u u = -1) :
    StrongEC g (fluidT g u ρ p) hg ↔ 0 ≤ ρ + p ∧ 0 ≤ ρ + 3 * p := by
  obtain ⟨k, hk0, hk1, hfam⟩ := null_timelike_family hg hu
  have htr := traceG_fluid hg hu ρ p
  constructor
  · intro h
    have h3 : 0 ≤ ρ + 3 * p := by
      have := h u (by rw [hu]; norm_num)
      rw [htr, fluidT_apply, hu] at this
      nlinarith
    refine ⟨?_, h3⟩
    have hf : 0 ≤ (fun ε : ℝ => (ρ + p) * (1 + ε) ^ 2 + p * (-(2 * ε) - ε ^ 2)
        - (1 / 2) * (3 * p - ρ) * (-(2 * ε) - ε ^ 2)) 0 := by
      refine nonneg_of_pos_nonneg (f := fun ε : ℝ => (ρ + p) * (1 + ε) ^ 2 + p * (-(2 * ε) - ε ^ 2)
        - (1 / 2) * (3 * p - ρ) * (-(2 * ε) - ε ^ 2)) (by fun_prop) fun ε hε => ?_
      have := h (k + ε • u) (by rw [(hfam ε).1]; nlinarith)
      rw [htr, fluidT_apply, (hfam ε).1, (hfam ε).2] at this
      nlinarith
    simpa using hf
  · rintro ⟨hρp, h3⟩ v hv
    rw [htr, fluidT_apply]
    have h1 := lorentz_reverse_cs hg (u := u) (by rw [hu]; norm_num) v
    rw [hu] at h1
    nlinarith [mul_nonneg hρp (sub_nonneg.2 h1), mul_nonneg h3 (neg_nonneg.2 hv.le)]

end FluidIff


end Fluid

section DEC
variable {V : Type*} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]
variable [FiniteDimensional ℝ V] {g : V →L[ℝ] V →L[ℝ] ℝ} {u : V} {ρ p : ℝ}

/-- **Cauchy–Schwarz in the orthogonal complement of a timelike vector**: for `x, y ⟂ u`, `g(x, y)² ≤ g(x, x) g(y, y)`. -/
theorem orth_cs {n : ℕ} (hg : IsLorentzianForm (n + 1) g) (hu : g u u < 0) {x y : V} (hx : g u x = 0) (hy : g u y = 0) :
    g x y ^ 2 ≤ g x x * g y y := by
  have hpsd : ∀ z : V, g u z = 0 → 0 ≤ g z z := fun z hz => by
    have := lorentz_reverse_cs hg hu z
    rw [hz] at this
    nlinarith
  have hq : ∀ t : ℝ, 0 ≤ g y y * (t * t) + (2 * g x y) * t + g x x := fun t => by
    have h := hpsd (x + t • y) (by simp [hx, hy])
    have hs : g y x = g x y := hg.symm y x
    simp only [map_add, map_smul, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul, hs] at h
    nlinarith
  by_cases hyy : g y y = 0
  · -- then g x y = 0, else a large t violates positivity
    have : g x y = 0 := by
      by_contra hne
      have h := hq (-(g x x + 1) / (2 * g x y))
      have ht : (2 * g x y) * (-(g x x + 1) / (2 * g x y)) = -(g x x + 1) := by field_simp
      rw [hyy, ht] at h
      linarith
    rw [this, hyy]; simp
  · have hpos : 0 < g y y := lt_of_le_of_ne (hpsd y hy) (Ne.symm hyy)
    have := discrim_le_zero hq
    simp only [discrim] at this
    nlinarith


/-- For a unit timelike `u` and co-oriented timelike `ξ, η`: `−g(ξ, η) ≤ 2 g(u, ξ) g(u, η)`. -/
theorem neg_pair_le {n : ℕ} (hg : IsLorentzianForm (n + 1) g) (hu : g u u = -1) {ξ η : V} (hξ : g ξ ξ < 0) (hη : g η η < 0)
    (hξη : g ξ η < 0) : -g ξ η ≤ 2 * (g u ξ * g u η) := by
  have hu' : g u u < 0 := by rw [hu]; norm_num
  have hAB := lorentz_coorient hg hu' hξ hη hξη
  set A := g u ξ with hA
  set B := g u η with hB
  have hs : ∀ x y : V, g x y = g y x := fun x y => hg.symm x y
  set ξp : V := ξ + A • u
  set ηp : V := η + B • u
  have hξp : g u ξp = 0 := by simp [ξp, hA, hu]
  have hηp : g u ηp = 0 := by simp [ηp, hB, hu]
  have hcs := orth_cs hg hu' hξp hηp
  have e1 : g ξp ξp = g ξ ξ + A ^ 2 := by
    simp only [ξp, map_add, map_smul, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul, hu, hs ξ u, ← hA]
    ring
  have e2 : g ηp ηp = g η η + B ^ 2 := by
    simp only [ηp, map_add, map_smul, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul, hu, hs η u, ← hB]
    ring
  have e3 : g ξ η = g ξp ηp - A * B := by
    have : ξ = ξp - A • u := by simp [ξp]
    have : η = ηp - B • u := by simp [ηp]
    simp only [ξp, ηp, map_add, map_smul, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul, hu, hs ξ u,
      hs η u, ← hA, ← hB, hs u ξ, hs u η]
    ring
  rw [e1, e2] at hcs
  have hxx : 0 ≤ g ξp ξp := by
    have := lorentz_reverse_cs hg hu' ξp; rw [hξp] at this; nlinarith
  have hyy : 0 ≤ g ηp ηp := by
    have := lorentz_reverse_cs hg hu' ηp; rw [hηp] at this; nlinarith
  rw [e1] at hxx; rw [e2] at hyy
  have h1 : g ξp ηp ^ 2 ≤ (A * B) ^ 2 := by
    calc g ξp ηp ^ 2 ≤ (g ξ ξ + A ^ 2) * (g η η + B ^ 2) := hcs
      _ ≤ A ^ 2 * B ^ 2 := by nlinarith
      _ = (A * B) ^ 2 := by ring
  have h2 := abs_le_of_sq_le_sq' h1 hAB.le
  rw [e3]; linarith [h2.1, h2.2]


/-- `T^a_n ξ^n = (ρ + p) g(u, ξ) u + p ξ` for a perfect fluid. -/
theorem raiseT_fluid (hg : IsLorentzianForm 4 g) (u : V) (ρ p : ℝ) (ξ : V) :
    raiseT g (fluidT g u ρ p) hg.bilinForm_nondegenerate ξ = ((ρ + p) * g u ξ) • u + p • ξ := by
  unfold raiseT
  rw [LinearEquiv.symm_apply_eq]
  refine LinearMap.ext fun w => ?_
  simp [fluidT_apply, LinearMap.BilinForm.toDual_def]
  ring

/-- **Perfect fluid, dominant energy condition**: `|p| ≤ ρ`. -/
theorem fluid_dominantEC_iff (hg : IsLorentzianForm 4 g) (hu : g u u = -1) :
    DominantEC g (fluidT g u ρ p) hg ↔ |p| ≤ ρ := by
  have hu' : g u u < 0 := by rw [hu]; norm_num
  constructor
  · rintro ⟨h1, h2⟩
    have hW : WeakEC g (fluidT g u ρ p) := fun v hv => (h1 v hv).1
    obtain ⟨hρ, hρp⟩ := (fluid_weakEC_iff hg hu).1 hW
    obtain ⟨w, hw1, hw2⟩ := exists_orth_spacelike (m := 2) hg hu'
    have hwu : g w u = 0 := by rw [hg.symm w u]; exact hw1
    have hf : 0 ≤ (fun ε : ℝ => ρ * (1 + ε) ^ 2 - p) 0 := by
      refine nonneg_of_pos_nonneg (f := fun ε : ℝ => ρ * (1 + ε) ^ 2 - p) (by fun_prop) fun ε hε => ?_
      have hξ : g ((1 + ε) • u + w) ((1 + ε) • u + w) < 0 := by
        simp only [map_add, map_smul, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul, hu, hw1, hw2,
          hwu]
        nlinarith
      have hη : g ((1 + ε) • u - w) ((1 + ε) • u - w) < 0 := by
        simp only [map_sub, map_add, map_smul, ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply, smul_eq_mul, hu, hw1,
          hw2, hwu]
        nlinarith
      have hco : g ((1 + ε) • u + w) ((1 + ε) • u - w) < 0 := by
        simp only [map_sub, map_add, map_smul, ContinuousLinearMap.sub_apply, ContinuousLinearMap.add_apply,
          ContinuousLinearMap.smul_apply, smul_eq_mul, hu, hw1, hw2, hwu]
        nlinarith
      have := h2 _ _ hξ hη hco
      rw [fluidT_apply] at this
      simp only [map_sub, map_add, map_smul, ContinuousLinearMap.sub_apply, ContinuousLinearMap.add_apply,
        ContinuousLinearMap.smul_apply, smul_eq_mul, hu, hw1, hw2, hwu] at this
      nlinarith
    have hp : p ≤ ρ := by simpa using hf
    exact abs_le.2 ⟨by linarith, hp⟩
  · intro h
    have hρ : 0 ≤ ρ := (abs_nonneg p).trans h
    have hρp : 0 ≤ ρ + p := by linarith [neg_abs_le p]
    have hW := (fluid_weakEC_iff hg hu).2 ⟨hρ, hρp⟩
    refine ⟨fun ξ hξ => ⟨hW ξ hξ, ?_⟩, fun ξ η hξ hη hξη => ?_⟩
    · rw [raiseT_fluid hg]
      simp only [map_add, map_smul, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul, hu,
        hg.symm u ξ]
      have hρ2 : p ^ 2 ≤ ρ ^ 2 := by nlinarith [abs_nonneg p, sq_abs p]
      nlinarith [mul_nonneg (sq_nonneg (g ξ u)) (sub_nonneg.2 hρ2), mul_nonneg (sq_nonneg p) (neg_nonneg.2 hξ.le)]
    · have hAB := lorentz_coorient hg hu' hξ hη hξη
      have hle := neg_pair_le hg hu hξ hη hξη
      rw [fluidT_apply]
      rcases le_or_gt 0 p with hp | hp
      · rw [abs_of_nonneg hp] at h
        nlinarith
      · nlinarith

end DEC


end Lightlike
