module

public import Lightlike.Lorentz.StarBound
public import Lightlike.Lorentz.Continuity

/-!
# The Lorentzian EPRL vertex amplitude and its finiteness

The Lorentzian EPRL spin foam model (Engle, Pereira, Rovelli and Livine 2008) assigns to a
4-simplex with SU(2) spins `j_{ab}` on its ten triangles (the links `a < b` of the complete graph
on its five tetrahedra `a = 0, …, 4`) and SU(2) intertwiners `ι_a` on its tetrahedra the vertex
amplitude

  `A_v = ∫ dV₀ ⋯ dV₃ [⊗_a ι_a] · ∏_{a<b} D^{(ρ_{ab}, k_{ab})}_{j m_{ab}, j m_{ba}}(V_a⁻¹ V_b)`,
  `V₄ = 1`,

where `D^{(ρ,k)}_{jm, jm'}(g) = ⟨Y e_m, π_{ρ,k}(g) Y e_{m'}⟩` are matrix coefficients of the unitary
principal series of SL(2,ℂ) between the vectors `Y e_m` of its lowest SU(2) subspace, of spin
`j = k`, and the indices `m_{ab}` at the tetrahedron `a` are contracted with `ι_a`. One of the five
integrations is dropped (`V₄ = 1`): the integrand is invariant under `V_a ↦ W V_a`, so the full
integral over five copies diverges (Engle and Pereira 2009, eq. (22)).

The labels are the EPRL ones in the form of Ding and Rovelli: `k = j` and `ρ = γ(j + 1)`, for
which the second Casimir `kρ` equals `γ j(j+1)`, `γ` times the SU(2) Casimir (`EPRLTests.lean`).
Engle and Pereira (2009, eq. (23)) write the amplitude as `A_v[2j, 2γj; j, ι]` in the labels
`(n, ρ_EP)` of the original paper, which selects `ρ_EP = γn` with `C₂ = nρ_EP`. These are
`n = 2k` and `ρ_EP = 2ρ` in this library's normalisation (`C₂ = kρ`), so their label is `ρ = γj`
here, not Ding and Rovelli's `γ(j + 1)`. The finiteness theorem holds for every choice of labels
(`integrable_linkProd_inner`).

## Conventions

* The representation `principalSeries n ρ` has `k = n/2` and the standard `ρ`
  (`SmoothVectors.lean`), so the EPRL label `k = j` is `n = 2j = J`, with `J` the doubled spin.
* `eprlVec γ J m` is the image of the `m`-th standard basis vector of spin `J/2` (`m ≤ J`) under
  the isometry `suV J ρ 0` onto the lowest SU(2) subspace; for `m > J` it is `0`.
* Spins are `J : Sym2 (Fin 5) → ℕ`, one doubled spin per link `{a, b}`. A magnetic configuration
  is `m : Fin 5 → Fin 5 → ℕ`, `m a b` being the index at the end `a` of the link to `b`; the finite
  set `magBox J` contains those with `m a b ≤ J {a, b}` and `m a a = 0`.
* An intertwiner is any family of coefficients `ι a : (Fin 4 → ℕ) → ℂ`, read on the four legs of
  `a` in the order `b = a.succAbove 0, …, a.succAbove 3` and contracted with the indices `m a b`
  as they stand. On a link `a < b`, the identity
  `⟨Y e_m, π(V_a⁻¹ V_b) Y e_{m'}⟩ = ⟨π(V_a) Y e_m, π(V_b) Y e_{m'}⟩` puts `m a b` in the bra,
  so at the tetrahedron `a` the legs `b > a` are bra legs and the legs `b < a` ket legs. The
  EPRL contraction of SU(2)-invariant intertwiners twists the bra legs by the structure map `ε`
  (`e_m ↦ ±e_{J−m}`), which identifies the dual of spin `j` with spin `j`. `eprlVertex` does not
  apply the twist, so on invariant intertwiners it is **not** shown to equal the amplitude of
  Engle and Pereira. Finiteness is unaffected: the twisted coefficients are again a family of
  coefficients, and the theorems hold for every family.
* The measure is `haar4 = haarC⁴`; another normalisation of the Haar measure rescales the
  amplitude by a positive constant.

## Main results

* `integrable_linkProd_inner`: for **any** principal series labels on the ten links and any
  decaying vectors (in particular any SU(2)-finite vectors), the product of the ten matrix
  coefficients is integrable over the four free copies of SL(2,ℂ).
* `integrable_eprlLinks`, `integrable_eprlIntegrand`: the EPRL integrand is integrable.
* `eprlVertex_eq_integral`: the vertex amplitude, defined as the contraction of the coefficients
  `ι` with the integrals of the ten-coefficient products, is the absolutely convergent integral of
  the contracted integrand.

The proof combines the matrix-coefficient bound `|D(g)| ≤ C I(g)` (`KernelBound.lean`) with the
star Hölder bound `∫ ∏_{a<b} I(V_a⁻¹ V_b) < ∞` (`StarBound.lean`).

## References

* J. Engle, R. Pereira, C. Rovelli and E. Livine, *LQG vertex with finite Immirzi parameter*,
  Nucl. Phys. B 799 (2008) 136, arXiv:0711.0146.
* J. Engle and R. Pereira, *Regularization and finiteness of the Lorentzian loop quantum gravity
  vertices*, Phys. Rev. D 79 (2009) 084034, arXiv:0805.4696, eqs. (22)–(30).
* Y. Ding and C. Rovelli, *Physical boundary Hilbert space and volume operator in the Lorentzian
  new spin-foam theory*, arXiv:1006.1294, eq. (24) (the labels `ρ = γ(j + 1)`, `k = j`).
-/

@[expose] public section

open MeasureTheory Finset Filter
open scoped ENNReal InnerProductSpace

namespace Lightlike.Lorentz

/-! ## Products over the ten links -/

lemma linkProd_mul {M : Type*} [CommMonoid M] (f g : Fin 5 → Fin 5 → M) :
    linkProd (fun a b => f a b * g a b) = linkProd f * linkProd g := by
  unfold linkProd; simp only [prod_mul_distrib]

lemma norm_linkProd_le {f : Fin 5 → Fin 5 → ℂ} {B : Fin 5 → Fin 5 → ℝ}
    (h : ∀ a b, ‖f a b‖ ≤ B a b) : ‖linkProd f‖ ≤ linkProd B := by
  unfold linkProd
  rw [norm_prod]
  refine prod_le_prod₀ (fun a _ => norm_nonneg _) fun a _ => ?_
  rw [norm_prod]
  exact prod_le_prod₀ (fun b _ => norm_nonneg _) fun b _ => h a b

lemma continuous_gauge_apply (a : Fin 5) : Continuous fun x : Fin 4 → SL2C => gauge x a := by
  induction a using Fin.lastCases with
  | last => simp only [gauge_last]; exact continuous_const
  | cast i => simp only [gauge_castSucc]; exact continuous_apply i

lemma continuous_gauge_link (a b : Fin 5) :
    Continuous fun x : Fin 4 → SL2C => (gauge x a)⁻¹ * gauge x b :=
  (continuous_gauge_apply a).inv.mul (continuous_gauge_apply b)

/-- The product of the ten kernels `I(V_a⁻¹ V_b)` is integrable over the four free vertices. -/
theorem integrable_linkProd_kernelI :
    Integrable (fun x : Fin 4 → SL2C =>
      linkProd fun a b => kernelI ((gauge x a)⁻¹ * gauge x b)) haar4 := by
  have hm : AEMeasurable (fun x : Fin 4 → SL2C =>
      linkProd fun a b => kernelE ((gauge x a)⁻¹ * gauge x b)) haar4 := by
    unfold linkProd
    exact (Finset.measurable_prod _ fun a _ => Finset.measurable_prod _ fun b _ =>
      measurable_kernelE.comp ((measurable_gauge_apply a).inv.mul
        (measurable_gauge_apply b))).aemeasurable
  refine (integrable_toReal_of_lintegral_ne_top hm lintegral_linkProd_kernelE_lt_top.ne).congr
    (Eventually.of_forall fun x => ?_)
  simp only [linkProd, ENNReal.toReal_prod, kernelE, ENNReal.toReal_ofReal (kernelI_pos _).le]

/-- **Integrability of the ten-coefficient product**, for any labels. For any principal series
labels `(n_{ab}, ρ_{ab})` and any vectors `u_{ab}`, `v_{ab}` that decay like `(1 + |z|²)⁻¹`, the
function `(V₀, …, V₃) ↦ ∏_{a<b} ⟨u_{ab}, π_{n_{ab},ρ_{ab}}(V_a⁻¹ V_b) v_{ab}⟩`, `V₄ = 1`, is
integrable for the Haar measure. -/
theorem integrable_linkProd_inner (n : Fin 5 → Fin 5 → ℤ) (ρ : Fin 5 → Fin 5 → ℝ)
    (u v : Fin 5 → Fin 5 → L2C) (hu : ∀ a b, ∃ C, DecaysWith C (u a b))
    (hv : ∀ a b, ∃ C, DecaysWith C (v a b)) :
    Integrable (fun x : Fin 4 → SL2C => linkProd fun a b =>
      ⟪u a b, principalSeries (n a b) (ρ a b) ((gauge x a)⁻¹ * gauge x b) (v a b)⟫_ℂ) haar4 := by
  choose C hC using hu
  choose D hD using hv
  refine (integrable_linkProd_kernelI.const_mul (linkProd fun a b => C a b * D a b)).mono' ?_
    (Eventually.of_forall fun x => ?_)
  · refine Continuous.aestronglyMeasurable ?_
    unfold linkProd
    refine continuous_finsetProd _ fun a _ => continuous_finsetProd _ fun b _ => ?_
    exact continuous_const.inner
      ((continuous_principalSeries (n a b) (ρ a b) (v a b)).comp (continuous_gauge_link a b))
  · rw [← linkProd_mul]
    exact norm_linkProd_le fun a b =>
      norm_inner_principalSeries_le (hC a b) (hD a b) _ _ _

/-! ## The EPRL labels and vectors -/

/-- The EPRL label `ρ = γ (j + 1)` for the doubled spin `J = 2j`. -/
noncomputable def eprlRho (γ : ℝ) (J : ℕ) : ℝ := γ * ((J : ℝ) / 2 + 1)

/-- The lowest SU(2) subspace of `π_{J,ρ}` has spin `J/2`: `dsp J 0 = J`. -/
lemma dsp_natCast_zero (J : ℕ) : dsp (J : ℤ) 0 = J := by
  rw [dsp_eq]; simp

/-- The **EPRL vector** `Y e_m`: the image of the `m`-th standard basis vector of spin `J/2` in the
lowest SU(2) subspace of `π_{J, γ(J/2+1)}`, and `0` for `m > J`. -/
noncomputable def eprlVec (γ : ℝ) (J m : ℕ) : L2C :=
  if h : m < dsp (J : ℤ) 0 + 1 then
    suV (J : ℤ) (eprlRho γ J) 0 (EuclideanSpace.single (⟨m, h⟩ : Fin (dsp (J : ℤ) 0 + 1)) 1)
  else 0

/-- The **EPRL matrix coefficient** `D^{(γ(j+1), j)}_{jm, jm'}(g) = ⟨Y e_m, π(g) Y e_{m'}⟩`. -/
noncomputable def eprlCoeff (γ : ℝ) (J m m' : ℕ) (g : SL2C) : ℂ :=
  ⟪eprlVec γ J m, principalSeries (J : ℤ) (eprlRho γ J) g (eprlVec γ J m')⟫_ℂ

/-- `0 ∈ L²` decays with constant `0`. -/
lemma decaysWith_zero : DecaysWith 0 (0 : L2C) := by
  filter_upwards [Lp.coeFn_zero ℂ 2 (volume : Measure ℂ)] with z hz
  simp

lemma exists_decaysWith_eprlVec (γ : ℝ) (J m : ℕ) : ∃ C, DecaysWith C (eprlVec γ J m) := by
  unfold eprlVec
  split_ifs
  · exact exists_decaysWith_suV _ _ _ _
  · exact ⟨0, decaysWith_zero⟩

/-- `‖Y e_m‖ = 1` for `m ≤ J`: `Y` is an isometry. -/
theorem norm_eprlVec {γ : ℝ} {J m : ℕ} (hm : m ≤ J) : ‖eprlVec γ J m‖ = 1 := by
  have h : m < dsp (J : ℤ) 0 + 1 := by rw [dsp_natCast_zero]; omega
  simp only [eprlVec, h, ↓reduceDIte, LinearIsometry.norm_map, PiLp.norm_single, norm_one]

/-- **`D(1)` is the identity**: `D_{jm, jm'}(1) = δ_{mm'}` for `m, m' ≤ J`. -/
theorem eprlCoeff_one {γ : ℝ} {J m m' : ℕ} (hm : m ≤ J) (hm' : m' ≤ J) :
    eprlCoeff γ J m m' 1 = if m = m' then 1 else 0 := by
  have h : m < dsp (J : ℤ) 0 + 1 := by rw [dsp_natCast_zero]; omega
  have h' : m' < dsp (J : ℤ) 0 + 1 := by rw [dsp_natCast_zero]; omega
  simp only [eprlCoeff, map_one, eprlVec, h, h', ↓reduceDIte]
  simp [EuclideanSpace.inner_single_left, PiLp.single_apply, Fin.ext_iff]

/-! ## The vertex amplitude -/

/-- The magnetic configurations: `m a b ≤ J {a, b}` for `a ≠ b`, and `m a a = 0`. -/
def magBox (J : Sym2 (Fin 5) → ℕ) : Finset (Fin 5 → Fin 5 → ℕ) :=
  Fintype.piFinset fun a => Fintype.piFinset fun b =>
    if a = b then {0} else range (J s(a, b) + 1)

/-- The product of the ten EPRL matrix coefficients for the magnetic configuration `m`, as a
function of the four free vertices `V₀, …, V₃` (`V₄ = 1`). -/
noncomputable def eprlLinks (γ : ℝ) (J : Sym2 (Fin 5) → ℕ) (m : Fin 5 → Fin 5 → ℕ)
    (x : Fin 4 → SL2C) : ℂ :=
  linkProd fun a b => eprlCoeff γ (J s(a, b)) (m a b) (m b a) ((gauge x a)⁻¹ * gauge x b)

/-- The coefficient `∏_a ι_a(m_{a,·})` of the intertwiners on the configuration `m`. -/
def intwCoeff (ι : Fin 5 → (Fin 4 → ℕ) → ℂ) (m : Fin 5 → Fin 5 → ℕ) : ℂ :=
  ∏ a, ι a fun j => m a (a.succAbove j)

/-- **The Lorentzian vertex amplitude of the coefficients `ι`**, of the form of Engle–Pereira
2009, eq. (30): `ι` contracted, without conjugation and without the `ε` twist, with the integrals
`∫ ∏_{a<b} D_{j m_{ab}, j m_{ba}}(V_a⁻¹ V_b) dV₀ ⋯ dV₃`. For SU(2)-invariant intertwiners the EPRL
amplitude needs the `ε` twist on the bra legs `b > a` (module docstring); it is not defined here,
and `eprlVertex` is not claimed to equal it. -/
noncomputable def eprlVertex (γ : ℝ) (J : Sym2 (Fin 5) → ℕ) (ι : Fin 5 → (Fin 4 → ℕ) → ℂ) : ℂ :=
  ∑ m ∈ magBox J, intwCoeff ι m * ∫ x, eprlLinks γ J m x ∂haar4

/-- The contracted integrand `∑_m ι(m) ∏_{a<b} D_{j m_{ab}, j m_{ba}}(V_a⁻¹ V_b)`. -/
noncomputable def eprlIntegrand (γ : ℝ) (J : Sym2 (Fin 5) → ℕ) (ι : Fin 5 → (Fin 4 → ℕ) → ℂ)
    (x : Fin 4 → SL2C) : ℂ :=
  ∑ m ∈ magBox J, intwCoeff ι m * eprlLinks γ J m x

/-- **Each EPRL ten-coefficient product is integrable**, for every Immirzi parameter `γ`, all
spins and all magnetic indices. -/
theorem integrable_eprlLinks (γ : ℝ) (J : Sym2 (Fin 5) → ℕ) (m : Fin 5 → Fin 5 → ℕ) :
    Integrable (eprlLinks γ J m) haar4 :=
  integrable_linkProd_inner (fun a b => (J s(a, b) : ℤ)) (fun a b => eprlRho γ (J s(a, b)))
    (fun a b => eprlVec γ (J s(a, b)) (m a b)) (fun a b => eprlVec γ (J s(a, b)) (m b a))
    (fun _ _ => exists_decaysWith_eprlVec _ _ _) (fun _ _ => exists_decaysWith_eprlVec _ _ _)

/-- **Finiteness of the Lorentzian EPRL vertex amplitude**: the contracted integrand is integrable
for every Immirzi parameter, all spins and all intertwiners. -/
theorem integrable_eprlIntegrand (γ : ℝ) (J : Sym2 (Fin 5) → ℕ) (ι : Fin 5 → (Fin 4 → ℕ) → ℂ) :
    Integrable (eprlIntegrand γ J ι) haar4 := by
  unfold eprlIntegrand
  exact integrable_finsetSum _ fun m _ => (integrable_eprlLinks γ J m).const_mul _

/-- **Finiteness, as a Lebesgue integral**: `∫ |integrand| < ∞`. -/
theorem lintegral_enorm_eprlIntegrand_lt_top (γ : ℝ) (J : Sym2 (Fin 5) → ℕ)
    (ι : Fin 5 → (Fin 4 → ℕ) → ℂ) : ∫⁻ x, ‖eprlIntegrand γ J ι x‖ₑ ∂haar4 < ∞ :=
  (integrable_eprlIntegrand γ J ι).hasFiniteIntegral

/-- **The vertex amplitude is the absolutely convergent integral of the contracted integrand.**
Together with `integrable_eprlIntegrand` this says that `eprlVertex` is a genuine integral, not
the junk value `0` that Lean assigns to the integral of a non-integrable function. -/
theorem eprlVertex_eq_integral (γ : ℝ) (J : Sym2 (Fin 5) → ℕ) (ι : Fin 5 → (Fin 4 → ℕ) → ℂ) :
    eprlVertex γ J ι = ∫ x, eprlIntegrand γ J ι x ∂haar4 := by
  unfold eprlIntegrand eprlVertex
  rw [integral_finsetSum _ fun m _ => (integrable_eprlLinks γ J m).const_mul _]
  simp only [integral_const_mul]

end Lightlike.Lorentz
