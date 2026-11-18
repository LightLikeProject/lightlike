import Lightlike.OperatorAlgebras.FockExists
import Lightlike.OperatorAlgebras.GramUnitary

/-!
# The cyclic-vector reduction of Shale's criterion

Helper lemmas for `T-OP2-P5` (`Tasks/OP/T_OP2_P5.lean`): a Bogoliubov transformation `T` is implemented in a
Fock representation iff there is a vector `Ψ` with `⟪Ψ, W f Ψ⟫ = exp (-‖T f‖² / 4)` for all `f`.

`⇒`: `Ψ = U⁻¹ Ω`. `⇐`: the vectors `W f Ψ` and `W (T f) Ω` have the same Gram matrix (the transformation preserves
the symplectic form), `Ψ` is cyclic by the irreducibility (`fockRep_cyclic`), and the Gram unitary
(`exists_unitary_of_gram_eq`) intertwines the Weyl operators.
-/

open scoped InnerProductSpace

universe u

namespace Lightlike.OperatorAlgebras

variable {h : Type u} [NormedAddCommGroup h] [InnerProductSpace ℂ h]
  {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- **`⇒`**: an implementing unitary gives a vector with Gaussian characteristic function. -/
lemma gaussian_vector_of_implements (R : FockRep h K) (T : Bogoliubov h)
    (hT : Implements R.toCCRRep T) :
    ∃ Ψ : K, ∀ f, ⟪Ψ, R.W f Ψ⟫_ℂ = Complex.exp (-(‖T.toEquiv f‖ ^ 2 / 4 : ℝ)) := by
  obtain ⟨U, hU⟩ := hT
  refine ⟨U.symm R.Ω, fun f => ?_⟩
  have h1 : R.W f (U.symm R.Ω) = U.symm (R.W (T.toEquiv f) R.Ω) := by
    apply U.injective
    rw [hU, LinearIsometryEquiv.apply_symm_apply, LinearIsometryEquiv.apply_symm_apply]
  rw [h1, LinearIsometryEquiv.inner_map_map, R.vacuum_expectation]

lemma symp_neg_left (f g : h) : symp h (-f) g = -symp h f g := by simp [symp, inner_neg_left]

/-- **The Gram matrix of the vectors `W f Ψ`** equals that of `W (T f) Ω`, given the Gaussian characteristic
function of `Ψ`. -/
lemma gram_gaussian_vector (R : FockRep h K) (T : Bogoliubov h) {Ψ : K}
    (hΨ : ∀ f, ⟪Ψ, R.W f Ψ⟫_ℂ = Complex.exp (-(‖T.toEquiv f‖ ^ 2 / 4 : ℝ))) (f g : h) :
    ⟪R.W f Ψ, R.W g Ψ⟫_ℂ = ⟪R.W (T.toEquiv f) R.Ω, R.W (T.toEquiv g) R.Ω⟫_ℂ := by
  rw [R.inner_W_Ω]
  have h1 : ⟪R.W f Ψ, R.W g Ψ⟫_ℂ = ⟪Ψ, R.W (-f) (R.W g Ψ)⟫_ℂ := by
    rw [← (R.W (-f)).inner_map_map, R.toCCRRep.W_neg_W]
  rw [h1, R.weyl, inner_smul_right, hΨ]
  unfold fockGram
  have e1 : T.toEquiv (-f + g) = -T.toEquiv f + T.toEquiv g := by
    rw [map_add, map_neg]
  have e2 : symp h (-T.toEquiv f) (T.toEquiv g) = symp h (-f) g := by
    rw [symp_neg_left, symp_neg_left, T.symp_map]
  rw [e1, e2]

/-- **`⇐`**: a cyclic vector with Gaussian characteristic function gives an implementing unitary. -/
lemma implements_of_gaussian_vector (R : FockRep h K) (T : Bogoliubov h) {Ψ : K}
    (hΨ : ∀ f, ⟪Ψ, R.W f Ψ⟫_ℂ = Complex.exp (-(‖T.toEquiv f‖ ^ 2 / 4 : ℝ)))
    (hcyc : (Submodule.span ℂ (Set.range fun f => R.W f Ψ)).topologicalClosure = ⊤) :
    Implements R.toCCRRep T := by
  set Φ₁ : (h →₀ ℂ) →ₗ[ℂ] K := Finsupp.linearCombination ℂ (fun f : h => R.W f Ψ) with hΦ₁
  set Φ₂ : (h →₀ ℂ) →ₗ[ℂ] K :=
    Finsupp.linearCombination ℂ (fun f : h => R.W (T.toEquiv f) R.Ω) with hΦ₂
  have hd₁ : Dense ((LinearMap.range Φ₁ : Submodule ℂ K) : Set K) := by
    have hr : LinearMap.range Φ₁ = Submodule.span ℂ (Set.range fun f => R.W f Ψ) :=
      Finsupp.range_linearCombination _
    rw [hr, Submodule.dense_iff_topologicalClosure_eq_top]; exact hcyc
  have hd₂ : Dense ((LinearMap.range Φ₂ : Submodule ℂ K) : Set K) := by
    have hr : LinearMap.range Φ₂ = Submodule.span ℂ (Set.range fun f => R.W (T.toEquiv f) R.Ω) :=
      Finsupp.range_linearCombination _
    have hrange : (Set.range fun f : h => R.W (T.toEquiv f) R.Ω) = Set.range fun g : h => R.W g R.Ω := by
      ext x
      simp only [Set.mem_range]
      constructor
      · rintro ⟨f, rfl⟩; exact ⟨T.toEquiv f, rfl⟩
      · rintro ⟨g, rfl⟩; exact ⟨T.toEquiv.symm g, by simp⟩
    rw [hr, hrange, Submodule.dense_iff_topologicalClosure_eq_top]; exact R.cyclic
  obtain ⟨U, hU⟩ := exists_unitary_of_gram_eq (Φ₁ := Φ₁) (Φ₂ := Φ₂) (fun x y => by
    simp only [hΦ₁, hΦ₂, Finsupp.linearCombination_single, one_smul]
    exact gram_gaussian_vector R T hΨ x y) hd₁ hd₂
  have hUg : ∀ g, U (R.W g Ψ) = R.W (T.toEquiv g) R.Ω := fun g => by
    have := hU (Finsupp.single g 1)
    simpa [hΦ₁, hΦ₂] using this
  have hUΨ : U Ψ = R.Ω := by
    have := hUg 0
    simpa [R.toCCRRep.W_zero_apply] using this
  refine ⟨U, fun f ψ => ?_⟩
  have hdense : Dense ((Submodule.span ℂ (Set.range fun f => R.W f Ψ) : Submodule ℂ K) : Set K) := by
    rw [Submodule.dense_iff_topologicalClosure_eq_top]; exact hcyc
  have hc1 : Continuous fun x : K => U (R.W f x) := U.continuous.comp (R.W f).continuous
  have hc2 : Continuous fun x : K => R.W (T.toEquiv f) (U x) := (R.W _).continuous.comp U.continuous
  have := Continuous.ext_on hdense hc1 hc2 (fun x hx => by
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨g, rfl⟩ := hy
      rw [R.weyl, map_smul, hUg, hUg, R.weyl, T.toEquiv.map_add, T.symp_map]
    | zero => simp
    | add a b _ _ ha hb => simp only [map_add, ha, hb]
    | smul c a _ ha => simp only [map_smul, ha])
  exact congrFun this ψ

end Lightlike.OperatorAlgebras
