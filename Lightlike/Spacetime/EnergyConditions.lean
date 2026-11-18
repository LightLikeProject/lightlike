import Lightlike.Spacetime.Lorentzian

/-!
# Energy conditions (GE14, stage 1)

Pointwise energy conditions of a symmetric bilinear form `T` (the stress-energy tensor at a point) on a Lorentzian vector space `(V, g)`:
`NullEC`, `WeakEC`, `StrongEC` (dimension four) and `DominantEC` (Curiel, *A Primer on Energy Conditions*, section 2.1, physical forms).
Proved: reverse Cauchy-Schwarz for a timelike vector, the sign rule for timelike vectors in a Lorentz frame (`lorentz_sign`), co-oriented timelike vectors pair with a
timelike vector with a common sign (`lorentz_coorient`), the `g`-trace in a Lorentz frame (`traceG_eq_sum`); trust checks: dust with `ρ ≥ 0` satisfies all four,
a positive cosmological constant violates the strong condition, a scalar field at a point of vanishing gradient with a negative potential violates the weak one.

**Limits.** Pointwise statements on a vector space; no manifold or time-orientation field, perfect fluids only through the checks above.
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

end Lightlike
