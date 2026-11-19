import Lightlike.OperatorAlgebras.CompactDual
import Lightlike.OperatorAlgebras.TraceClass.RankOnePairing

/-!
# The dual of the compact operators is the trace class

Final bricks of `T-OP6-P1` (`K* ≅ S¹`): a finite-rank operator is a finite sum of rank-one operators; a continuous functional `f` on the
compact operators agrees with the trace pairing with its operator `T` (`compactFunctionalOperator`) on rank-one operators, hence on
finite-rank operators, hence on all compact operators by density (`exists_finiteRank_approx`).
-/

open scoped InnerProductSpace

namespace Lightlike.OperatorAlgebras

open TraceClass

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A finite-rank operator is a finite sum of rank-one operators `|vₖ⟩⟨F† vₖ|`, `v` an orthonormal basis of the range. -/
theorem finiteRank_eq_sum_rankOne (F : H →L[ℂ] H) [FiniteDimensional ℂ (LinearMap.range (F : H →ₗ[ℂ] H))] :
    ∃ (n : ℕ) (u v : Fin n → H), F = ∑ k, InnerProductSpace.rankOne ℂ (u k) (v k) := by
  let U : Submodule ℂ H := LinearMap.range (F : H →ₗ[ℂ] H)
  let b := stdOrthonormalBasis ℂ U
  refine ⟨Module.finrank ℂ U, fun k => (b k : H), fun k => (ContinuousLinearMap.adjoint F) (b k : H), ?_⟩
  ext z
  have hz : (⟨F z, ⟨z, rfl⟩⟩ : U) = ∑ k, ⟪b k, (⟨F z, ⟨z, rfl⟩⟩ : U)⟫_ℂ • b k := (b.sum_repr' _).symm
  have := congrArg (fun w : U => (w : H)) hz
  simp only [Submodule.coe_sum, Submodule.coe_smul] at this
  rw [ContinuousLinearMap.sum_apply]
  simp only [InnerProductSpace.rankOne_apply, ContinuousLinearMap.adjoint_inner_left]
  convert this using 2
  rfl

/-- The trace-class operator of a continuous functional on the compact operators. -/
noncomputable def compactFunctionalTraceClass (f : CompactOps H →L[ℂ] ℂ) : TraceClass H :=
  TraceClass.ofOperator (compactFunctionalOperator f) (isTraceClass_compactFunctionalOperator f)

/-- **On rank-one operators the functional is the trace pairing with its operator**. -/
theorem compactFunctional_rankOne (f : CompactOps H →L[ℂ] ℂ) (x y : H) :
    f (rankOneCompact x y) = TraceClass.tracePairing (InnerProductSpace.rankOne ℂ x y) (compactFunctionalTraceClass f) := by
  rw [TraceClass.tracePairing_rankOne_left]
  exact (compactFunctionalOperator_inner f x y).symm

/-- **On finite-rank compact operators the functional is the trace pairing**. -/
theorem compactFunctional_finiteRank (f : CompactOps H →L[ℂ] ℂ) (K : CompactOps H)
    [FiniteDimensional ℂ (LinearMap.range ((K : H →L[ℂ] H) : H →ₗ[ℂ] H))] :
    f K = TraceClass.tracePairing K.1 (compactFunctionalTraceClass f) := by
  obtain ⟨n, u, v, hK⟩ := finiteRank_eq_sum_rankOne (K : H →L[ℂ] H)
  have hK' : K = ∑ k, rankOneCompact (u k) (v k) := by
    apply Subtype.ext
    rw [hK]
    simp [rankOneCompact]
  rw [hK', map_sum]
  have : (∑ k, rankOneCompact (u k) (v k) : CompactOps H).1 = ∑ k, InnerProductSpace.rankOne ℂ (u k) (v k) := by
    simp [rankOneCompact]
  rw [this, ← TraceClass.tracePairingContinuousLinearMap_apply, map_sum, ContinuousLinearMap.sum_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [compactFunctional_rankOne]; rfl

/-- **The functional is the trace pairing with its operator, on every compact operator** (density of the finite-rank operators). -/
theorem compactFunctional_eq (f : CompactOps H →L[ℂ] ℂ) (K : CompactOps H) :
    f K = TraceClass.tracePairing K.1 (compactFunctionalTraceClass f) := by
  set Tf := compactFunctionalTraceClass f with hTf
  have hΨ : ∀ A : H →L[ℂ] H, ‖TraceClass.tracePairing A Tf‖ ≤ ‖A‖ * ‖Tf‖ := fun A =>
    ((TraceClass.tracePairing A).le_opNorm Tf).trans
      (mul_le_mul_of_nonneg_right (TraceClass.norm_tracePairing_le A) (norm_nonneg _))
  refine eq_of_forall_dist_le fun ε hε => ?_
  set δ : ℝ := ε / (‖f‖ + ‖Tf‖ + 1) with hδ
  have hpos : 0 < ‖f‖ + ‖Tf‖ + 1 := by positivity
  have hδpos : 0 < δ := div_pos hε hpos
  obtain ⟨F, hFfd, hF⟩ := exists_finiteRank_approx (K : H →L[ℂ] H) K.2 hδpos
  haveI := hFfd
  let Fc : CompactOps H := ⟨F, isCompactOperator_of_finiteDimensional_range F⟩
  have hFc : f Fc = TraceClass.tracePairing F Tf := compactFunctional_finiteRank f Fc
  have hdiff : ‖(K : H →L[ℂ] H) - F‖ ≤ δ := hF
  rw [dist_eq_norm]
  have hsplit : f K - TraceClass.tracePairing K.1 Tf =
      f (K - Fc) - TraceClass.tracePairing ((K : H →L[ℂ] H) - F) Tf := by
    have hlin : TraceClass.tracePairing ((K : H →L[ℂ] H) - F) Tf =
        TraceClass.tracePairing (K : H →L[ℂ] H) Tf - TraceClass.tracePairing F Tf := by
      rw [← TraceClass.tracePairingContinuousLinearMap_apply, map_sub, ContinuousLinearMap.sub_apply]; rfl
    rw [map_sub, hFc, hlin]; ring
  rw [hsplit]
  calc ‖f (K - Fc) - TraceClass.tracePairing ((K : H →L[ℂ] H) - F) Tf‖
      ≤ ‖f (K - Fc)‖ + ‖TraceClass.tracePairing ((K : H →L[ℂ] H) - F) Tf‖ := norm_sub_le _ _
    _ ≤ ‖f‖ * δ + δ * ‖Tf‖ := by
        gcongr
        · exact (f.le_opNorm _).trans (by gcongr; exact hdiff)
        · exact (hΨ _).trans (by gcongr)
    _ ≤ ε := by
        have : (‖f‖ + ‖Tf‖) * δ ≤ ε := by
          rw [hδ, ← mul_div_assoc, div_le_iff₀ hpos]; nlinarith [norm_nonneg f, norm_nonneg Tf]
        nlinarith

/-- **`𝒦(H)* ≅ 𝒮₁(H)`**: every continuous functional on the compact operators is the trace pairing with a unique trace-class operator
of trace norm `‖f‖`. -/
theorem compact_dual_eq_traceClass_proof (f : CompactOps H →L[ℂ] ℂ) :
    ∃ T : TraceClass H, (∀ K : CompactOps H, f K = TraceClass.tracePairing K.1 T) ∧ ‖T‖ = ‖f‖ ∧
      ∀ T' : TraceClass H, (∀ K : CompactOps H, f K = TraceClass.tracePairing K.1 T') → T' = T := by
  refine ⟨compactFunctionalTraceClass f, compactFunctional_eq f, ?_, ?_⟩
  · apply le_antisymm
    · rw [TraceClass.norm_eq_traceNorm]
      exact traceNorm_compactFunctionalOperator_le f
    · refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun K => ?_
      rw [compactFunctional_eq f K]
      calc ‖TraceClass.tracePairing K.1 (compactFunctionalTraceClass f)‖
          ≤ ‖TraceClass.tracePairing K.1‖ * ‖compactFunctionalTraceClass f‖ := (TraceClass.tracePairing K.1).le_opNorm _
        _ ≤ ‖K.1‖ * ‖compactFunctionalTraceClass f‖ :=
            mul_le_mul_of_nonneg_right (TraceClass.norm_tracePairing_le K.1) (norm_nonneg _)
        _ = ‖compactFunctionalTraceClass f‖ * ‖K‖ := by rw [mul_comm]; rfl
  · intro T' hT'
    apply Subtype.ext
    ext x
    apply ext_inner_left ℂ
    intro y
    have h1 := hT' (rankOneCompact x y)
    rw [compactFunctional_rankOne] at h1
    have h3 : TraceClass.tracePairing (InnerProductSpace.rankOne ℂ x y) (compactFunctionalTraceClass f) =
        TraceClass.tracePairing (InnerProductSpace.rankOne ℂ x y) T' := h1
    rw [TraceClass.tracePairing_rankOne_left, TraceClass.tracePairing_rankOne_left] at h3
    exact h3.symm

end Lightlike.OperatorAlgebras
