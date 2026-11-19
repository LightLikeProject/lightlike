import Lightlike.Poincare.ConeL2

/-!
# The canonical system of imprimitivity of the massive one-particle representations

A *system of imprimitivity* (Freitag, Def. V.4.2) for a unitary representation `π` of a group `G` acting on a locally
compact space `Y` is a regular `*`-homomorphism `S : C_c(Y) → B(H)` with `π(g) S(f) π(g)⁻¹ = S(f ∘ g⁻¹)`
(`IsSystemOfImprimitivity`). For the induced representation `U` of `SL(2,ℂ)` on `L²(μ; ℂ^{n+1})` over the mass shell,
multiplication by functions of the momentum is one (`isSystemOfImprimitivity_inducedL2`, Freitag, Prop. V.4.4: every
induced representation is imprimitive); the multiplications also commute with the translations
(`translL2_bcfMul`).

## References

* E. Freitag, *Unitary representations of the Poincaré group, Wigner classification* (lecture notes, Heidelberg),
  Chapter V, §4, Definition 4.1 (regular homomorphisms), Definition 4.2 (systems of imprimitivity) and
  Proposition 4.4 (induced representations are imprimitive), pages 139–140.
-/

open MeasureTheory Matrix Lightlike.Lorentz Lightlike.SU2 Filter Topology BoundedContinuousFunction
open scoped InnerProductSpace

namespace Lightlike.Poincare

noncomputable section

/-! ## Multiplication by a bounded continuous function -/

variable {X E : Type*} [MeasurableSpace X] [TopologicalSpace X] [OpensMeasurableSpace X]
  [SecondCountableTopologyEither X ℂ] {μ : Measure X} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

lemma memLp_bcfMul (g : X →ᵇ ℂ) (f : Lp E 2 μ) : MemLp (fun x => g x • f x) 2 μ :=
  (Lp.memLp f).of_le_mul (g.continuous.aestronglyMeasurable.smul (Lp.aestronglyMeasurable f))
    (Filter.Eventually.of_forall fun x => by
      rw [norm_smul]; exact mul_le_mul_of_nonneg_right (g.norm_coe_le_norm x) (norm_nonneg _))

/-- Multiplication by a bounded continuous function, a bounded operator of `L²` of norm at most `‖g‖`. -/
def bcfMul (g : X →ᵇ ℂ) : Lp E 2 μ →L[ℂ] Lp E 2 μ :=
  LinearMap.mkContinuous
    { toFun := fun f => (memLp_bcfMul g f).toLp _
      map_add' := fun f h => by
        apply Lp.ext
        filter_upwards [(memLp_bcfMul g (f + h)).coeFn_toLp, Lp.coeFn_add f h,
          Lp.coeFn_add ((memLp_bcfMul (μ := μ) g f).toLp _) ((memLp_bcfMul (μ := μ) g h).toLp _),
          (memLp_bcfMul (μ := μ) g f).coeFn_toLp, (memLp_bcfMul (μ := μ) g h).coeFn_toLp] with x h1 h2 h3 h4 h5
        rw [h1, h3, Pi.add_apply, h4, h5, h2, Pi.add_apply, smul_add]
      map_smul' := fun c f => by
        apply Lp.ext
        filter_upwards [(memLp_bcfMul g (c • f)).coeFn_toLp, Lp.coeFn_smul c f,
          Lp.coeFn_smul c ((memLp_bcfMul (μ := μ) g f).toLp _), (memLp_bcfMul (μ := μ) g f).coeFn_toLp]
          with x h1 h2 h3 h4
        rw [h1, RingHom.id_apply, h3, Pi.smul_apply, h4, h2, Pi.smul_apply, smul_comm] }
    ‖g‖ (fun f => by
      change ‖(memLp_bcfMul (μ := μ) g f).toLp _‖ ≤ ‖g‖ * ‖f‖
      rw [Lp.norm_toLp, Lp.norm_def]
      have hfg : ∀ᵐ x ∂μ, ‖g x • (f : X → E) x‖ ≤ ‖g‖ * ‖(f : X → E) x‖ :=
        Filter.Eventually.of_forall fun x => by
          rw [norm_smul]; exact mul_le_mul_of_nonneg_right (g.norm_coe_le_norm x) (norm_nonneg _)
      have h := eLpNorm_le_mul_eLpNorm_of_ae_le_mul (memLp_bcfMul (μ := μ) g f).aestronglyMeasurable hfg 2
      calc (eLpNorm (fun x => g x • f x) 2 μ).toReal ≤ (ENNReal.ofReal ‖g‖ * eLpNorm (⇑f) 2 μ).toReal :=
            ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (Lp.eLpNorm_ne_top f)) h
        _ = ‖g‖ * (eLpNorm (⇑f) 2 μ).toReal := by
            rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (norm_nonneg _)])

lemma coeFn_bcfMul (g : X →ᵇ ℂ) (f : Lp E 2 μ) :
    (bcfMul (μ := μ) g f : X → E) =ᵐ[μ] fun x => g x • f x :=
  (memLp_bcfMul g f).coeFn_toLp

lemma bcfMul_mul (g h : X →ᵇ ℂ) : bcfMul (μ := μ) (E := E) (g * h) = bcfMul g * bcfMul h := by
  ext f : 1
  apply Lp.ext
  filter_upwards [coeFn_bcfMul (μ := μ) (g * h) f, coeFn_bcfMul (μ := μ) g (bcfMul h f),
    coeFn_bcfMul (μ := μ) h f] with x h1 h2 h3
  rw [ContinuousLinearMap.mul_apply, h1, h2, h3, BoundedContinuousFunction.coe_mul, Pi.mul_apply, mul_smul]

/-- The adjoint of multiplication by `g` is multiplication by `ḡ`. -/
lemma inner_bcfMul (g : X →ᵇ ℂ) (f f' : Lp E 2 μ) :
    ⟪bcfMul (μ := μ) (star g) f, f'⟫_ℂ = ⟪f, bcfMul (μ := μ) g f'⟫_ℂ := by
  rw [MeasureTheory.L2.inner_def, MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_bcfMul (μ := μ) (star g) f, coeFn_bcfMul (μ := μ) g f'] with x h1 h2
  rw [h1, h2, inner_smul_left, inner_smul_right]
  simp

lemma bcfMul_one : bcfMul (μ := μ) (E := E) (1 : X →ᵇ ℂ) = 1 := by
  ext f : 1
  apply Lp.ext
  filter_upwards [coeFn_bcfMul (μ := μ) (1 : X →ᵇ ℂ) f] with x h
  rw [h]
  simp

/-! ## Systems of imprimitivity -/

/-- **A system of imprimitivity** (Freitag, Def. V.4.2) for a map `π` from a group `G` acting on `Y` to the bounded
operators of a Hilbert space: a bounded `*`-homomorphism `S` from the compactly supported continuous functions,
non-degenerate, and covariant: `π(g) S(f) = S(f ∘ g⁻¹) π(g)`. -/
structure IsSystemOfImprimitivity {G Y H : Type*} [Group G] [MulAction G Y] [TopologicalSpace Y]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] (π : G → H →L[ℂ] H) (S : (Y →ᵇ ℂ) → H →L[ℂ] H) : Prop where
  map_mul : ∀ f g, S (f * g) = S f * S g
  map_star : ∀ f x y, ⟪S (star f) x, y⟫_ℂ = ⟪x, S f y⟫_ℂ
  norm_le : ∀ f, ‖S f‖ ≤ ‖f‖
  map_one : S 1 = 1
  covariant : ∀ (g : G) (f : Y →ᵇ ℂ) (f' : Y →ᵇ ℂ), (∀ y, f' y = f (g⁻¹ • y)) → π g * S f = S f' * π g

variable {m : ℝ} {μ' : Measure (MassShell m)}

instance : MulAction SL2C (MassShell m) where
  smul A P := shellAct A P
  one_smul P := shellAct_one P
  mul_smul A B P := shellAct_mul A B P

lemma smul_shell (A : SL2C) (P : MassShell m) : A • P = shellAct A P := rfl

/-- **Covariance**: `U(A) (g ψ) = (g ∘ A⁻¹) U(A) ψ`. -/
lemma inducedL2_bcfMul (hm : 0 < m) (n : ℕ) (hμ : ∀ A : SL2C, MeasurePreserving (shellAct A) μ' μ') (A : SL2C)
    (g g' : MassShell m →ᵇ ℂ) (hg : ∀ Q, g' Q = g (shellAct A⁻¹ Q)) (f : Lp (Spinor n) 2 μ') :
    inducedL2 hm n hμ A (bcfMul g f) = bcfMul g' (inducedL2 hm n hμ A f) := by
  apply Lp.ext
  have h3 := (hμ A⁻¹).quasiMeasurePreserving.ae_eq_comp (coeFn_bcfMul (μ := μ') g f)
  filter_upwards [coeFn_inducedL2 hm n hμ A (bcfMul g f), coeFn_bcfMul (μ := μ') g' (inducedL2 hm n hμ A f),
    coeFn_inducedL2 hm n hμ A f, h3] with Q h1 h2 h4 h5
  simp only [Function.comp_apply] at h5
  rw [h1, h2, h4, h5, uAct_smul, hg]

/-- **The multiplications commute with the translations.** -/
lemma translL2_bcfMul (n : ℕ) (a : Transl) (g : MassShell m →ᵇ ℂ) (f : Lp (Spinor n) 2 μ') :
    translL2 n a (bcfMul g f) = bcfMul g (translL2 n a f) := by
  apply Lp.ext
  filter_upwards [coeFn_translL2 n a (bcfMul g f), coeFn_bcfMul (μ := μ') g (translL2 n a f),
    coeFn_bcfMul (μ := μ') g f, coeFn_translL2 n a f] with Q h1 h2 h3 h4
  rw [h1, h2, h3, h4, smul_comm]

/-- **The canonical system of imprimitivity** of the massive induced representation (Freitag, Prop. V.4.4). -/
theorem isSystemOfImprimitivity_inducedL2 (hm : 0 < m) (n : ℕ)
    (hμ : ∀ A : SL2C, MeasurePreserving (shellAct A) μ' μ') :
    IsSystemOfImprimitivity (G := SL2C) (Y := MassShell m)
      (fun A => (inducedL2 hm n hμ A).toContinuousLinearMap) (fun g => bcfMul (μ := μ') (E := Spinor n) g) where
  map_mul := bcfMul_mul
  map_star := inner_bcfMul
  norm_le f := LinearMap.mkContinuous_norm_le _ (norm_nonneg f) _
  map_one := bcfMul_one
  covariant A g g' hg := by
    ext f : 1
    exact inducedL2_bcfMul hm n hμ A g g' hg f

end

end Lightlike.Poincare
