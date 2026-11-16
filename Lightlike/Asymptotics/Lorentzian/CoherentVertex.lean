import Lightlike.Asymptotics.Lorentzian.NormLowest

/-!
# The coherent principal-series vertex is the Lorentzian vertex of BDFHP

`eprlVertex_eq_lorVertex`: for every Immirzi parameter, every family of doubled spins `J` and SU(2)
data `G`, the amplitude `Lightlike.Lorentz.eprlVertex` (finite for every spin, LL-0046) on the
product of coherent arrays equals `(haarScalarFactor haarC SL2C.haar)^4` times `lorVertex` with
the constants `(n_e + 1)/π`. The proof assembles `link_integral_explicit` (one link as an integral
over the chart) over the ten links:

* the sum over the magnetic configurations is the product over the links (`sum_magBox_linkProd`);
* the contracted integrand of a product array is the product of the link sums
  (`eprlIntegrand_iotaProd`), and the ten links are the ten edges (`linkProd_eq_prod_edges`);
* the inner integral over `ℂ^10` is a product of ten integrals (`integral_fintype_prod_eq_prod`);
* the integration variable is conjugated, `X = conj V` (`conjSL`; BDFHP, arXiv:0907.2440,
  footnote 4, p. 11), which preserves the Haar measure (`map_conjSL_haar`: the Haar character of
  an involution is `1`);
* LL-0046 integrates against `haar4 = Measure.pi haarC`, where `haarC` is `haarScalarFactor haarC
  SL2C.haar` times `SL2C.haar` (`pi_const_smul`), which gives the explicit factor.

`integrable_lorOuter` is the finiteness corollary: the outer integrand of `lorVertex` is integrable
(from LL-0046 through the identity). The integrability of the inner integral over `ℂ^10` for almost
every `SL(2,ℂ)^4` point is not part of this file.

**Limits.** Only the lowest SU(2) level of each representation (the EPRL labels `k = j`); boundary
arrays that are products of coherent states (not the SU(2)-invariant Livine–Speziale intertwiner,
and no `ε` twist); SU(2) boundary data; the boundary spinors of `lorVertex` are `ḡ` at the source
end and `w g` at the target end of each edge; `ρ_e` and `p_e` are the same free parameter; the
constants `c_ab dk_ab` and the sign `(-1)^χ` of BDFHP are not compared.
-/

open MeasureTheory Finset Matrix
open scoped NNReal ENNReal ComplexConjugate
open Lightlike Lightlike.Spin4 Lightlike.SU2 Lightlike.Lorentz Lightlike.SpinFoam
open Lightlike.Asymptotics.EPRL

namespace Lightlike.Asymptotics.Lorentzian



/-- Entrywise complex conjugation on `SL(2,ℂ)`. -/
noncomputable def conjSL : SL2C →* SL2C := Matrix.SpecialLinearGroup.map (starRingEnd ℂ)

theorem conjSL_coe (x : SL2C) : ((conjSL x : SL2C) : Matrix (Fin 2) (Fin 2) ℂ) =
    (x : Matrix (Fin 2) (Fin 2) ℂ).map star := rfl

theorem conjSL_conjSL (x : SL2C) : conjSL (conjSL x) = x := by
  ext i j; simp [conjSL_coe]

theorem continuous_conjSL : Continuous conjSL := by
  refine Continuous.subtype_mk ?_ _
  exact (continuous_subtype_val.matrix_map continuous_star)

/-- Conjugation as a continuous multiplicative equivalence. -/
noncomputable def conjEquiv : SL2C ≃ₜ* SL2C where
  toMulEquiv := MulEquiv.mk' (Equiv.mk conjSL conjSL conjSL_conjSL conjSL_conjSL) conjSL.map_mul
  continuous_toFun := continuous_conjSL
  continuous_invFun := continuous_conjSL

/-- **Complex conjugation preserves the Haar measure of `SL(2,ℂ)`**: it is an involutive
continuous automorphism, so its Haar character `c` satisfies `c = c⁻¹` and `c > 0`, hence `c = 1`
(`mulEquivHaarChar_smul_map`, `mulEquivHaarChar_symm`). -/
theorem map_conjSL_haar : SL2C.haar.map conjSL = SL2C.haar := by
  have h := mulEquivHaarChar_smul_map SL2C.haar conjEquiv
  have hs : conjEquiv.symm = conjEquiv := by
    ext x; rfl
  have h1 : mulEquivHaarChar conjEquiv = 1 := by
    have h2 := mulEquivHaarChar_symm (φ := conjEquiv)
    rw [hs] at h2
    have hpos := mulEquivHaarChar_pos conjEquiv
    set c := mulEquivHaarChar conjEquiv
    have hc : c ≠ 0 := hpos.ne'
    have : c * c = 1 := by
      calc c * c = c * c⁻¹ := by rw [← h2]
        _ = 1 := mul_inv_cancel₀ hc
    have hr : (c : ℝ) * c = 1 := by exact_mod_cast this
    have hr1 : (c : ℝ) = 1 := by nlinarith [c.2]
    exact_mod_cast hr1
  rw [h1, one_smul] at h
  exact h



/-- The ten links `a < b`. -/
abbrev LinkIdx := {p : Fin 5 × Fin 5 // p.1 < p.2}

/-- `linkProd` as a product over the subtype of links. -/
theorem linkProd_eq_prod_subtype {M : Type*} [CommMonoid M] (f : Fin 5 → Fin 5 → M) :
    linkProd f = ∏ p : LinkIdx, f p.1.1 p.1.2 := by
  unfold linkProd
  have h : (∏ p : LinkIdx, f p.1.1 p.1.2) =
      ∏ p ∈ univ.filter (fun p : Fin 5 × Fin 5 => p.1 < p.2), f p.1 p.2 :=
    (Finset.prod_subtype (univ.filter fun p : Fin 5 × Fin 5 => p.1 < p.2)
      (p := fun p : Fin 5 × Fin 5 => p.1 < p.2) (fun p => by simp) (fun p => f p.1 p.2)).symm
  rw [h, Finset.prod_filter, Fintype.prod_prod_type]
  refine Finset.prod_congr rfl fun a _ => ?_
  rw [← Finset.prod_filter]
  congr 1
  ext b
  simp

/-- **The sum over the magnetic configurations is the product over the links of the double sums.** -/
theorem sum_magBox_linkProd (J : Sym2 (Fin 5) → ℕ) (F : Fin 5 → Fin 5 → ℕ → ℕ → ℂ) :
    ∑ m ∈ magBox J, linkProd (fun a b => F a b (m a b) (m b a)) =
      linkProd (fun a b => ∑ m1 ∈ range (J s(a, b) + 1), ∑ m2 ∈ range (J s(a, b) + 1), F a b m1 m2) := by
  classical
  set T : LinkIdx → Finset (ℕ × ℕ) := fun p =>
    range (J s(p.1.1, p.1.2) + 1) ×ˢ range (J s(p.1.1, p.1.2) + 1) with hT
  have hR : linkProd (fun a b => ∑ m1 ∈ range (J s(a, b) + 1), ∑ m2 ∈ range (J s(a, b) + 1),
      F a b m1 m2) = ∑ ρ ∈ Fintype.piFinset T, ∏ p : LinkIdx, F p.1.1 p.1.2 (ρ p).1 (ρ p).2 := by
    rw [linkProd_eq_prod_subtype, ← Finset.prod_univ_sum (fun p : LinkIdx => T p)
      (fun p x => F p.1.1 p.1.2 x.1 x.2)]
    refine Finset.prod_congr rfl fun p _ => ?_
    rw [hT, Finset.sum_product]
  rw [hR]
  let jf : (LinkIdx → ℕ × ℕ) → Fin 5 → Fin 5 → ℕ := fun ρ a b =>
    if h : a < b then (ρ ⟨(a, b), h⟩).1 else if h : b < a then (ρ ⟨(b, a), h⟩).2 else 0
  refine Finset.sum_bij' (fun m _ => fun p : LinkIdx => (m p.1.1 p.1.2, m p.1.2 p.1.1))
    (fun ρ _ => jf ρ) ?_ ?_ ?_ ?_ ?_
  · intro m hm
    rw [magBox, Fintype.mem_piFinset] at hm
    rw [Fintype.mem_piFinset]
    intro p
    have h1 := Fintype.mem_piFinset.mp (hm p.1.1) p.1.2
    have h2 := Fintype.mem_piFinset.mp (hm p.1.2) p.1.1
    have hne : p.1.1 ≠ p.1.2 := p.2.ne
    simp only [hne, ite_false] at h1
    simp only [Ne.symm hne, ite_false] at h2
    rw [Sym2.eq_swap] at h2
    simp only [hT, Finset.mem_product, Finset.mem_range]
    exact ⟨Finset.mem_range.mp h1, Finset.mem_range.mp h2⟩
  · intro ρ hρ
    rw [Fintype.mem_piFinset] at hρ
    rw [magBox, Fintype.mem_piFinset]
    intro a
    rw [Fintype.mem_piFinset]
    intro b
    by_cases hab : a = b
    · subst hab; simp [jf]
    · simp only [hab, ite_false]
      rcases lt_or_gt_of_ne hab with h | h
      · have := hρ ⟨(a, b), h⟩
        simp only [hT, Finset.mem_product, Finset.mem_range] at this
        simp only [jf, h, dite_true, Finset.mem_range]
        exact this.1
      · have := hρ ⟨(b, a), h⟩
        simp only [hT, Finset.mem_product, Finset.mem_range] at this
        simp only [jf, not_lt.mpr h.le, h, dite_true, Finset.mem_range]
        rw [Sym2.eq_swap (a := a) (b := b)]
        exact this.2
  · intro m hm
    rw [magBox, Fintype.mem_piFinset] at hm
    funext a b
    by_cases hab : a = b
    · subst hab
      have := Fintype.mem_piFinset.mp (hm a) a
      simp at this
      simp [jf, this]
    · rcases lt_or_gt_of_ne hab with h | h
      · simp [jf, h]
      · simp [jf, not_lt.mpr h.le, h]
  · intro ρ hρ
    funext p
    have h := p.2
    simp [jf, h, not_lt.mpr h.le]
  · intro m hm
    rw [linkProd_eq_prod_subtype]




/-- **The two ends of every link**: the product over the nodes and their four legs counts each link
once at each end, `∏_a ∏_j f(a, a.succAbove j) = ∏_{a<b} f(a, b) f(b, a)`. -/
theorem prod_succAbove_eq_linkProd {M : Type*} [CommSemiring M] (f : Fin 5 → Fin 5 → M) :
    ∏ a : Fin 5, ∏ j : Fin 4, f a (a.succAbove j) = linkProd fun a b => f a b * f b a := by
  unfold linkProd
  simp only [Fin.prod_univ_five]
  rw [show Ioi (0 : Fin 5) = {1, 2, 3, 4} by decide, show Ioi (1 : Fin 5) = {2, 3, 4} by decide,
    show Ioi (2 : Fin 5) = {3, 4} by decide, show Ioi (3 : Fin 5) = {4} by decide,
    show Ioi (4 : Fin 5) = ∅ by decide]
  simp only [Fin.prod_univ_four, Fin.succAbove]
  simp
  ring

/-- The coefficient array of a product of per-leg vectors: `u a b` is the vector at the node `a` on
the leg towards `b`. -/
def iotaProd (u : Fin 5 → Fin 5 → ℕ → ℂ) : Fin 5 → (Fin 4 → ℕ) → ℂ :=
  fun a m => ∏ j : Fin 4, u a (a.succAbove j) (m j)

/-- **The contracted integrand of a product array is the product over the links** of the contracted
link sums `Σ_{m, m'} u_{ab}(m) u_{ba}(m') D_{m m'}(V_a⁻¹ V_b)`. -/
theorem eprlIntegrand_iotaProd (γ : ℝ) (J : Sym2 (Fin 5) → ℕ) (u : Fin 5 → Fin 5 → ℕ → ℂ)
    (x : Fin 4 → SL2C) :
    eprlIntegrand γ J (iotaProd u) x =
      linkProd (fun a b => ∑ m1 ∈ range (J s(a, b) + 1), ∑ m2 ∈ range (J s(a, b) + 1),
        u a b m1 * u b a m2 * eprlCoeff γ (J s(a, b)) m1 m2 ((gauge x a)⁻¹ * gauge x b)) := by
  rw [← sum_magBox_linkProd J (fun a b m1 m2 =>
    u a b m1 * u b a m2 * eprlCoeff γ (J s(a, b)) m1 m2 ((gauge x a)⁻¹ * gauge x b))]
  unfold eprlIntegrand
  refine Finset.sum_congr rfl fun m _ => ?_
  unfold intwCoeff eprlLinks iotaProd
  rw [prod_succAbove_eq_linkProd (fun a b => u a b (m a b)), ← linkProd_mul]



/-- The product of `n` copies of a scaled measure is the scaled product measure. -/
theorem pi_const_smul {X : Type*} [MeasurableSpace X] (μ : Measure X) [SigmaFinite μ]
    (c : ℝ≥0) (n : ℕ) :
    Measure.pi (fun _ : Fin n => c • μ) = c ^ n • Measure.pi (fun _ : Fin n => μ) := by
  refine Measure.pi_eq (μ := fun _ : Fin n => c • μ) (fun s hs => ?_)
  simp only [Measure.smul_apply, Measure.pi_pi, ENNReal.smul_def, smul_eq_mul, Finset.prod_mul_distrib,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  norm_cast


/-- **The ten links as the ten edges**: `linkProd f = ∏_{e : Fin 10} f (edgeSrc e) (edgeTgt e)`. -/
theorem linkProd_eq_prod_edges {M : Type*} [CommMonoid M] (f : Fin 5 → Fin 5 → M) :
    linkProd f = ∏ e : Fin 10, f (edgeSrc e) (edgeTgt e) := by
  unfold linkProd
  simp only [Fin.prod_univ_five]
  rw [show Ioi (0 : Fin 5) = {1, 2, 3, 4} by decide, show Ioi (1 : Fin 5) = {2, 3, 4} by decide,
    show Ioi (2 : Fin 5) = {3, 4} by decide, show Ioi (3 : Fin 5) = {4} by decide,
    show Ioi (4 : Fin 5) = ∅ by decide]
  simp [Fin.prod_univ_succ, edgeSrc, edgeTgt]
  simp only [mul_comm, mul_left_comm]

/-- The coherent vector as a function of a natural index (`0` outside the range). -/
noncomputable def cohVecN (n : ℕ) (g : Matrix (Fin 2) (Fin 2) ℂ) (k : ℕ) : ℂ :=
  if h : k < dsp (n : ℤ) 0 + 1 then cohVec n g ⟨k, h⟩ else 0

/-- **One link, over natural indices**: `link_integral_explicit` with sums over `range (n+1)`. -/
theorem link_sum_range (γ : ℝ) (n : ℕ) (g1 g2 : SU2) (a b : SL2C) :
    ∑ m1 ∈ range (n + 1), ∑ m2 ∈ range (n + 1),
        conj (cohVecN n (g1 : Matrix (Fin 2) (Fin 2) ℂ) m1) *
          cohVecN n (g2 : Matrix (Fin 2) (Fin 2) ℂ) m2 * eprlCoeff γ n m1 m2 (a⁻¹ * b) =
      ((((n : ℝ) + 1) / Real.pi : ℝ) : ℂ) *
        ∫ w : ℂ, Complex.exp (triAction ((n : ℝ) / 2) (eprlRho γ n)
            (spinAct ((a : Matrix (Fin 2) (Fin 2) ℂ)ᵀ) (lorSpinor w))
            (firstCol ((g1 : Matrix (Fin 2) (Fin 2) ℂ).map star))
            (spinAct ((b : Matrix (Fin 2) (Fin 2) ℂ)ᵀ) (lorSpinor w))
            (firstCol (wM * (g2 : Matrix (Fin 2) (Fin 2) ℂ)))) *
          (((‖spinAct ((a : Matrix (Fin 2) (Fin 2) ℂ)ᵀ) (lorSpinor w)‖ ^ 2 *
            ‖spinAct ((b : Matrix (Fin 2) (Fin 2) ℂ)ᵀ) (lorSpinor w)‖ ^ 2)⁻¹ : ℝ) : ℂ) := by
  rw [← link_integral_explicit γ n g1 g2 a b]
  have hd : dsp (n : ℤ) 0 = n := dsp_natCast_zero' n
  have e1 : ∀ h : ℕ → ℂ, ∑ m ∈ range (n + 1), h m = ∑ m : Fin (dsp (n : ℤ) 0 + 1), h m := by
    intro h
    calc ∑ m ∈ range (n + 1), h m = ∑ m ∈ range (dsp (n : ℤ) 0 + 1), h m := by rw [hd]
      _ = ∑ m : Fin (dsp (n : ℤ) 0 + 1), h m := Finset.sum_range (fun m => h m)
  rw [e1]
  refine Finset.sum_congr rfl fun m1 _ => ?_
  rw [e1]
  refine Finset.sum_congr rfl fun m2 _ => ?_
  simp [cohVecN, Nat.lt_succ_iff.mp m1.2, Nat.lt_succ_iff.mp m2.2]

/-- The doubled spin of the edge `e`. -/
def edgeSpin (J : Sym2 (Fin 5) → ℕ) (e : Fin 10) : ℕ := J s(edgeSrc e, edgeTgt e)

/-- `edgeSrc e < edgeTgt e` for every edge. -/
theorem edgeSrc_lt_edgeTgt (e : Fin 10) : edgeSrc e < edgeTgt e := by
  fin_cases e <;> decide

/-- The per-leg coherent vectors: at the node `a` on the leg towards `b`, conjugated when `a < b`
(the bra slot of `eprlCoeff`). -/
noncomputable def uCoh (J : Sym2 (Fin 5) → ℕ) (G : Fin 5 → Fin 5 → SU2) :
    Fin 5 → Fin 5 → ℕ → ℂ := fun a b k =>
  if a < b then conj (cohVecN (J s(a, b)) (G a b : Matrix (Fin 2) (Fin 2) ℂ) k)
  else cohVecN (J s(a, b)) (G a b : Matrix (Fin 2) (Fin 2) ℂ) k

/-- The boundary data of `lorVertex` for the coherent array: `ḡ` at the source end of an edge and
`w g` at the target end. -/
noncomputable def bdry (G : Fin 5 → Fin 5 → SU2) : BdryData := fun e s =>
  if s = 0 then (G (edgeSrc e) (edgeTgt e) : Matrix (Fin 2) (Fin 2) ℂ).map star
  else wM * (G (edgeTgt e) (edgeSrc e) : Matrix (Fin 2) (Fin 2) ℂ)

/-- `conjSL` commutes with the gauge fixing. -/
theorem gauge_conjSL (x : Fin 4 → SL2C) (a : Fin 5) :
    gauge (fun i => conjSL (x i)) a = conjSL (gauge x a) := by
  induction a using Fin.lastCases with
  | last => simp only [Lightlike.Lorentz.gauge_last, map_one]
  | cast i => simp only [Lightlike.Lorentz.gauge_castSucc]

/-- **The integrand of the coherent EPRL vertex is `∏ (nₑ+1)/π` times the chart integral of
`lorIntegrand`**, at the point `X = conj (gauge x)`. -/
theorem eprlIntegrand_coh (γ : ℝ) (J : Sym2 (Fin 5) → ℕ) (G : Fin 5 → Fin 5 → SU2)
    (x : Fin 4 → SL2C) :
    eprlIntegrand γ J (iotaProd (uCoh J G)) x =
      (∏ e : Fin 10, ((((edgeSpin J e : ℝ) + 1) / Real.pi : ℝ) : ℂ)) *
        ∫ w : Fin 10 → ℂ, lorIntegrand (fun e => (edgeSpin J e : ℝ) / 2)
          (fun e => eprlRho γ (edgeSpin J e)) (bdry G) (fun a => conjSL (gauge x a)) w := by
  rw [eprlIntegrand_iotaProd, linkProd_eq_prod_edges]
  set Fe : Fin 10 → ℂ → ℂ := fun e w => Complex.exp (triAction ((edgeSpin J e : ℝ) / 2)
    (eprlRho γ (edgeSpin J e))
    (spinAct ((gauge x (edgeSrc e) : Matrix (Fin 2) (Fin 2) ℂ)ᵀ) (lorSpinor w))
    (firstCol ((G (edgeSrc e) (edgeTgt e) : Matrix (Fin 2) (Fin 2) ℂ).map star))
    (spinAct ((gauge x (edgeTgt e) : Matrix (Fin 2) (Fin 2) ℂ)ᵀ) (lorSpinor w))
    (firstCol (wM * (G (edgeTgt e) (edgeSrc e) : Matrix (Fin 2) (Fin 2) ℂ)))) *
    (((‖spinAct ((gauge x (edgeSrc e) : Matrix (Fin 2) (Fin 2) ℂ)ᵀ) (lorSpinor w)‖ ^ 2 *
      ‖spinAct ((gauge x (edgeTgt e) : Matrix (Fin 2) (Fin 2) ℂ)ᵀ) (lorSpinor w)‖ ^ 2)⁻¹ : ℝ) : ℂ)
    with hFe
  have hlink : ∀ e : Fin 10, ∑ m1 ∈ range (J s(edgeSrc e, edgeTgt e) + 1),
      ∑ m2 ∈ range (J s(edgeSrc e, edgeTgt e) + 1),
        uCoh J G (edgeSrc e) (edgeTgt e) m1 * uCoh J G (edgeTgt e) (edgeSrc e) m2 *
          eprlCoeff γ (J s(edgeSrc e, edgeTgt e)) m1 m2
            ((gauge x (edgeSrc e))⁻¹ * gauge x (edgeTgt e)) =
      ((((edgeSpin J e : ℝ) + 1) / Real.pi : ℝ) : ℂ) * ∫ w : ℂ, Fe e w := by
    intro e
    have hlt := edgeSrc_lt_edgeTgt e
    have h2 : ¬ edgeTgt e < edgeSrc e := not_lt.mpr hlt.le
    simp only [uCoh, hlt, h2, ite_true, ite_false]
    rw [show (s(edgeTgt e, edgeSrc e) : Sym2 (Fin 5)) = s(edgeSrc e, edgeTgt e) from Sym2.eq_swap]
    exact link_sum_range γ (J s(edgeSrc e, edgeTgt e)) (G (edgeSrc e) (edgeTgt e))
      (G (edgeTgt e) (edgeSrc e)) (gauge x (edgeSrc e)) (gauge x (edgeTgt e))
  rw [Finset.prod_congr rfl (fun e _ => hlink e), Finset.prod_mul_distrib]
  congr 1
  rw [← integral_fintype_prod_eq_prod (fun (e : Fin 10) (w : ℂ) => Fe e w) (μ := fun _ => volume)]
  rw [← volume_pi]
  refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
  unfold lorIntegrand lorAction lorEdgeDensity
  rw [Complex.exp_sum, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun e _ => ?_
  have hX : ∀ a : Fin 5, ((conjSL (gauge x a) : SL2C) : Matrix (Fin 2) (Fin 2) ℂ)ᴴ =
      ((gauge x a : SL2C) : Matrix (Fin 2) (Fin 2) ℂ)ᵀ := by
    intro a
    ext i j
    simp [conjSL_coe, Matrix.conjTranspose_apply, Matrix.transpose_apply]
  simp only [hFe, hX, bdry, ite_true]
  simp only [show ¬((1 : Fin 2) = 0) by decide, ite_false]


/-- Conjugation of the four free variables preserves the product Haar measure. -/
theorem measurePreserving_conjPi :
    MeasurePreserving (fun (x : Fin 4 → SL2C) i => conjSL (x i))
      (Measure.pi fun _ : Fin 4 => SL2C.haar) (Measure.pi fun _ : Fin 4 => SL2C.haar) := by
  refine ⟨measurable_pi_iff.mpr fun i => continuous_conjSL.measurable.comp (measurable_pi_apply i), ?_⟩
  have hsf : SigmaFinite (Measure.map (⇑conjSL) SL2C.haar) := by
    rw [map_conjSL_haar]; infer_instance
  rw [Measure.pi_map_pi (μ := fun _ : Fin 4 => SL2C.haar) (f := fun _ => ⇑conjSL)
    (fun _ => continuous_conjSL.measurable.aemeasurable)]
  simp only [map_conjSL_haar]

/-- Conjugation of the four free variables is a measurable embedding (it is an involution). -/
theorem measurableEmbedding_conjPi :
    MeasurableEmbedding (fun (x : Fin 4 → SL2C) i => conjSL (x i)) := by
  have hc : Continuous (fun (x : Fin 4 → SL2C) i => conjSL (x i)) :=
    continuous_pi fun i => continuous_conjSL.comp (continuous_apply i)
  let e : (Fin 4 → SL2C) ≃ₜ (Fin 4 → SL2C) :=
    { toFun := fun x i => conjSL (x i)
      invFun := fun x i => conjSL (x i)
      left_inv := fun x => by funext i; exact conjSL_conjSL _
      right_inv := fun x => by funext i; exact conjSL_conjSL _
      continuous_toFun := hc
      continuous_invFun := hc }
  exact e.isClosedEmbedding.measurableEmbedding

/-- **The coherent principal-series vertex is the Lorentzian vertex of BDFHP.** For every Immirzi
parameter `γ`, doubled spins `J` and SU(2) data `G`, the EPRL amplitude of `Lightlike.Lorentz.EPRL`
on the product of coherent arrays equals `(Measure.haarScalarFactor haarC SL2C.haar)^4` times `lorVertex`
with the constants `c_e = (n_e + 1)/π` (`n_e` the doubled spin of the edge `e`), `j_e = n_e/2`,
`p_e = ρ_e = γ (n_e/2 + 1)`, and the boundary data `bdry G`.

The factor `(Measure.haarScalarFactor haarC SL2C.haar)^4` appears because `haar4` of LL-0046 is the
product of four copies of the chart measure `haarC`, which is `Measure.haarScalarFactor haarC SL2C.haar`
times `SL2C.haar`, while `lorVertex` integrates against `SL2C.haar`; it is not claimed to be `1`.

`lorVertex` is an iterated integral (`SL(2,ℂ)^4` outside, `ℂ^10` inside): no joint bound on
`SL(2,ℂ)^4 × ℂ^10` is needed, because the inner integral is a product over the ten links
(`integral_fintype_prod_eq_prod`) and the integrability of the outer one is that of LL-0046.
Only the lowest SU(2) level and product coherent boundary data are covered; the variable of
integration is conjugated, `X = conj (V)` (BDFHP footnote 4, p. 11). -/
theorem eprlVertex_eq_lorVertex (γ : ℝ) (J : Sym2 (Fin 5) → ℕ) (G : Fin 5 → Fin 5 → SU2) :
    eprlVertex γ J (iotaProd (uCoh J G)) =
      (((((Measure.haarScalarFactor haarC SL2C.haar) ^ 4 : ℝ≥0) : ℝ)) : ℂ) *
        lorVertex (fun e => (edgeSpin J e : ℝ) / 2) (fun e => eprlRho γ (edgeSpin J e))
          (fun e => ((((edgeSpin J e : ℝ) + 1) / Real.pi : ℝ) : ℂ)) (bdry G) := by
  rw [eprlVertex_eq_integral]
  set j : Fin 10 → ℝ := fun e => (edgeSpin J e : ℝ) / 2 with hj
  set p : Fin 10 → ℝ := fun e => eprlRho γ (edgeSpin J e) with hp
  set Φ : (Fin 4 → SL2C) → ℂ := fun x => ∫ w : Fin 10 → ℂ, lorIntegrand j p (bdry G) (gauge x) w
    with hΦ
  set C : ℂ := ∏ e : Fin 10, ((((edgeSpin J e : ℝ) + 1) / Real.pi : ℝ) : ℂ) with hCdef
  have hgc' : ∀ x : Fin 4 → SL2C, (fun a => conjSL (gauge x a)) =
      gauge (fun i => conjSL (x i)) := fun x => funext fun a => (gauge_conjSL x a).symm
  have hpt : ∀ x : Fin 4 → SL2C, eprlIntegrand γ J (iotaProd (uCoh J G)) x =
      C * Φ (fun i => conjSL (x i)) := by
    intro x
    rw [eprlIntegrand_coh, hgc' x]
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt), integral_const_mul]
  obtain ⟨s, hs⟩ : ∃ s : ℝ≥0, s = Measure.haarScalarFactor haarC SL2C.haar := ⟨_, rfl⟩
  have hC : haarC = s • SL2C.haar := by rw [hs]; exact haarC_eq_smul
  have hmeas : haar4 = s ^ 4 • Measure.pi fun _ : Fin 4 => SL2C.haar := by
    have : haar4 = Measure.pi fun _ : Fin 4 => s • SL2C.haar := by
      unfold haar4; rw [hC]
    rw [this]
    exact pi_const_smul SL2C.haar s 4
  rw [← hs, hmeas, integral_smul_nnreal_measure,
    measurePreserving_conjPi.integral_comp measurableEmbedding_conjPi Φ]
  unfold lorVertex
  rw [NNReal.smul_def, Complex.real_smul]
  simp only [hΦ, hCdef]
  ring


/-- **Finiteness of the outer integral of the coherent Lorentzian vertex**: for every spin family
and SU(2) data, `x ↦ ∫_{ℂ^10} lorIntegrand (gauge x) dw` is integrable on `SL(2,ℂ)^4` against the
product of Haar measures. This is the finiteness of LL-0046 (`integrable_eprlIntegrand`) transported
through `eprlVertex_eq_lorVertex`; no joint bound on `SL(2,ℂ)^4 × ℂ^10` is used. -/
theorem integrable_lorOuter (γ : ℝ) (J : Sym2 (Fin 5) → ℕ) (G : Fin 5 → Fin 5 → SU2) :
    Integrable (fun x : Fin 4 → SL2C => ∫ w : Fin 10 → ℂ,
        lorIntegrand (fun e => (edgeSpin J e : ℝ) / 2) (fun e => eprlRho γ (edgeSpin J e))
          (bdry G) (gauge x) w)
      (Measure.pi fun _ : Fin 4 => SL2C.haar) := by
  set j : Fin 10 → ℝ := fun e => (edgeSpin J e : ℝ) / 2 with hj
  set p : Fin 10 → ℝ := fun e => eprlRho γ (edgeSpin J e) with hp
  set Φ : (Fin 4 → SL2C) → ℂ := fun x => ∫ w : Fin 10 → ℂ, lorIntegrand j p (bdry G) (gauge x) w
    with hΦ
  set C : ℂ := ∏ e : Fin 10, ((((edgeSpin J e : ℝ) + 1) / Real.pi : ℝ) : ℂ) with hCdef
  have hC0 : C ≠ 0 := by
    refine Finset.prod_ne_zero_iff.mpr fun e _ => ?_
    have : (0 : ℝ) < ((edgeSpin J e : ℝ) + 1) / Real.pi := by positivity
    exact_mod_cast this.ne'
  have hgc' : ∀ x : Fin 4 → SL2C, (fun a => conjSL (gauge x a)) =
      gauge (fun i => conjSL (x i)) := fun x => funext fun a => (gauge_conjSL x a).symm
  have hpt : ∀ x : Fin 4 → SL2C, eprlIntegrand γ J (iotaProd (uCoh J G)) x =
      C * Φ (fun i => conjSL (x i)) := by
    intro x
    rw [eprlIntegrand_coh, hgc' x]
  have h1 := integrable_eprlIntegrand γ J (iotaProd (uCoh J G))
  have h2 : Integrable (fun x : Fin 4 → SL2C => Φ (fun i => conjSL (x i))) haar4 := by
    have : Integrable (fun x : Fin 4 → SL2C => C * Φ (fun i => conjSL (x i))) haar4 := by
      exact h1.congr (Filter.Eventually.of_forall hpt)
    exact (this.const_mul C⁻¹).congr (Filter.Eventually.of_forall fun x => by
      show C⁻¹ * (C * Φ fun i => conjSL (x i)) = Φ fun i => conjSL (x i)
      rw [← mul_assoc, inv_mul_cancel₀ hC0, one_mul])
  obtain ⟨s, hs⟩ : ∃ s : ℝ≥0, s = Measure.haarScalarFactor haarC SL2C.haar := ⟨_, rfl⟩
  have hC : haarC = s • SL2C.haar := by rw [hs]; exact haarC_eq_smul
  have hs0 : s ≠ 0 := by rw [hs]; exact haarScalarFactor_haarC_ne_zero
  have hmeas : haar4 = s ^ 4 • Measure.pi fun _ : Fin 4 => SL2C.haar := by
    have : haar4 = Measure.pi fun _ : Fin 4 => s • SL2C.haar := by
      unfold haar4; rw [hC]
    rw [this]
    exact pi_const_smul SL2C.haar s 4
  rw [hmeas, ENNReal.smul_def] at h2
  have h3 := (integrable_smul_measure (by simpa using hs0) (by simp)).mp h2
  exact (measurePreserving_conjPi.integrable_comp_emb measurableEmbedding_conjPi).mp h3

/-- **Spin-zero value of one link at the identity**: the left side of `link_integral_explicit` is
`D_{00}(1) = 1`, so the chart integral of `e^S` times the density of `Ω` is `π`. -/
theorem link_value_spin_zero (γ : ℝ) :
    ∫ w : ℂ, Complex.exp (triAction (((0 : ℕ) : ℝ) / 2) (eprlRho γ 0)
        (spinAct (((1 : SL2C) : Matrix (Fin 2) (Fin 2) ℂ)ᵀ) (lorSpinor w))
        (firstCol (((1 : SU2) : Matrix (Fin 2) (Fin 2) ℂ).map star))
        (spinAct (((1 : SL2C) : Matrix (Fin 2) (Fin 2) ℂ)ᵀ) (lorSpinor w))
        (firstCol (wM * ((1 : SU2) : Matrix (Fin 2) (Fin 2) ℂ)))) *
      (((‖spinAct (((1 : SL2C) : Matrix (Fin 2) (Fin 2) ℂ)ᵀ) (lorSpinor w)‖ ^ 2 *
        ‖spinAct (((1 : SL2C) : Matrix (Fin 2) (Fin 2) ℂ)ᵀ) (lorSpinor w)‖ ^ 2)⁻¹ : ℝ) : ℂ) =
      (Real.pi : ℂ) := by
  have h := link_integral_explicit γ 0 1 1 1 1
  have hd : dsp ((0 : ℕ) : ℤ) 0 = 0 := dsp_natCast_zero' 0
  have hL : ∑ m : Fin (dsp ((0 : ℕ) : ℤ) 0 + 1), ∑ m' : Fin (dsp ((0 : ℕ) : ℤ) 0 + 1),
      conj (cohVec 0 (((1 : SU2) : Matrix (Fin 2) (Fin 2) ℂ)) m) *
        cohVec 0 (((1 : SU2) : Matrix (Fin 2) (Fin 2) ℂ)) m' *
          eprlCoeff γ 0 m m' ((1 : SL2C)⁻¹ * 1) = 1 := by
    have hm : ∀ m : Fin (dsp ((0 : ℕ) : ℤ) 0 + 1), (m : ℕ) = 0 := fun m => by
      have := m.2; omega
    have hc : ∀ m : Fin (dsp ((0 : ℕ) : ℤ) 0 + 1),
        cohVec 0 (((1 : SU2) : Matrix (Fin 2) (Fin 2) ℂ)) m = 1 := by
      intro m
      have h0 : (m : ℕ) = 0 := hm m
      have e1 : cohVec 0 (((1 : SU2) : Matrix (Fin 2) (Fin 2) ℂ)) m =
          cohState 0 (((1 : SU2) : Matrix (Fin 2) (Fin 2) ℂ))
            (Fin.cast (by rw [dsp_natCast_zero']) m) := rfl
      rw [e1, show (Fin.cast (by rw [dsp_natCast_zero']) m : Fin (0 + 1)) = 0 from Fin.ext h0]
      simp [cohState, spinMat_one]
    have hterm : ∀ m m' : Fin (dsp ((0 : ℕ) : ℤ) 0 + 1),
        conj (cohVec 0 (((1 : SU2) : Matrix (Fin 2) (Fin 2) ℂ)) m) *
          cohVec 0 (((1 : SU2) : Matrix (Fin 2) (Fin 2) ℂ)) m' *
            eprlCoeff γ 0 m m' ((1 : SL2C)⁻¹ * 1) = 1 := by
      intro m m'
      rw [hc m, hc m', inv_one, mul_one, hm m, hm m']
      simpa using eprlCoeff_one (γ := γ) (J := 0) (m := 0) (m' := 0) le_rfl le_rfl
    simp only [hterm, Finset.sum_const, Finset.card_univ, Fintype.card_fin, hd]
    simp
  rw [hL] at h
  have hc : ((((((0 : ℕ) : ℝ) + 1) / Real.pi : ℝ)) : ℂ) ≠ 0 := by
    have : (0 : ℝ) < (((0 : ℕ) : ℝ) + 1) / Real.pi := by positivity
    exact_mod_cast this.ne'
  refine mul_left_cancel₀ hc ?_
  rw [← h]
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_pos.ne'
  push_cast
  field_simp
  ring

end Lightlike.Asymptotics.Lorentzian
