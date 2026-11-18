import Lightlike.OperatorAlgebras.Yosida

/-!
# The resolvent identity and commuting approximants

Helper lemmas for the task `T-OP1-P2` (Stone's theorem, existence). The resolvents `R z = (A - z)⁻¹` of a
self-adjoint `A` at non-real points satisfy `R z - R w = (z - w) R z R w`, hence commute, hence the
approximants `A_n` (`Yosida.lean`) commute with each other.
-/

open scoped InnerProductSpace LinearPMap

namespace Lightlike.OperatorAlgebras

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {A : H →ₗ.[ℂ] H}

/-- **The resolvent identity**: `R z y - R w y = (z - w) R z (R w y)`. -/
lemma resolvent_identity (hA : IsSelfAdjoint A) {z w : ℂ} (hz : z.im ≠ 0) (hw : w.im ≠ 0) (y : H) :
    resolventCLM hA hz y - resolventCLM hA hw y = (z - w) • resolventCLM hA hz (resolventCLM hA hw y) := by
  set v : A.domain := ⟨resolventCLM hA hw y, resolvent_mem hA hw y⟩ with hv
  have h1 : (A v : H) - w • (v : H) = y := resolvent_spec hA hw y
  have h2 := resolvent_shift hA hz v
  have h3 : y = ((A v : H) - z • (v : H)) + (z - w) • (v : H) := by
    rw [← h1, sub_smul]; abel
  have h4 : resolventCLM hA hz y = (v : H) + (z - w) • resolventCLM hA hz (v : H) := by
    conv_lhs => rw [h3]
    rw [map_add, h2, map_smul]
  rw [h4]
  have : (v : H) = resolventCLM hA hw y := rfl
  rw [this]; abel

/-- **Resolvents commute.** -/
lemma resolvent_commute (hA : IsSelfAdjoint A) {z w : ℂ} (hz : z.im ≠ 0) (hw : w.im ≠ 0) (y : H) :
    resolventCLM hA hz (resolventCLM hA hw y) = resolventCLM hA hw (resolventCLM hA hz y) := by
  by_cases hzw : z = w
  · subst hzw; rfl
  have e1 := resolvent_identity hA hz hw y
  have e2 := resolvent_identity hA hw hz y
  have hne : z - w ≠ 0 := sub_ne_zero.2 hzw
  have e3 : (z - w) • resolventCLM hA hz (resolventCLM hA hw y) =
      (z - w) • resolventCLM hA hw (resolventCLM hA hz y) := by
    rw [← e1]
    have : resolventCLM hA hw y - resolventCLM hA hz y =
        (w - z) • resolventCLM hA hw (resolventCLM hA hz y) := e2
    rw [← neg_sub, this, ← neg_smul, neg_sub]
  exact smul_right_injective H hne e3

lemma commute_resolventCLM (hA : IsSelfAdjoint A) {z w : ℂ} (hz : z.im ≠ 0) (hw : w.im ≠ 0) :
    Commute (resolventCLM hA hz) (resolventCLM hA hw) := by
  refine ContinuousLinearMap.ext fun y => ?_
  exact resolvent_commute hA hz hw y

/-- **The approximants commute**: `A_n A_m = A_m A_n`. -/
theorem approx_commute (hA : IsSelfAdjoint A) (n m : ℕ) : Commute (approx hA n) (approx hA m) := by
  have hn : ((Complex.I * (tn n : ℂ))).im ≠ 0 := by simpa using (tn_pos n).ne'
  have hn' : (-(Complex.I * (tn n : ℂ))).im ≠ 0 := by simpa using (tn_pos n).ne'
  have hm : ((Complex.I * (tn m : ℂ))).im ≠ 0 := by simpa using (tn_pos m).ne'
  have hm' : (-(Complex.I * (tn m : ℂ))).im ≠ 0 := by simpa using (tn_pos m).ne'
  have h1 : Commute (resP hA n) (resP hA m) := commute_resolventCLM hA hn hm
  have h2 : Commute (resP hA n) (resM hA m) := commute_resolventCLM hA hn hm'
  have h3 : Commute (resM hA n) (resP hA m) := commute_resolventCLM hA hn' hm
  have h4 : Commute (resM hA n) (resM hA m) := commute_resolventCLM hA hn' hm'
  unfold approx
  exact (((h1.add_right h2).add_left (h3.add_right h4))).smul_left _ |>.smul_right _

/-- **The approximants are self-adjoint** as bounded operators. -/
theorem approx_isSelfAdjoint (hA : IsSelfAdjoint A) (n : ℕ) : IsSelfAdjoint (approx hA n) :=
  ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.2 fun y w => approx_selfadjoint hA n y w

end Lightlike.OperatorAlgebras
