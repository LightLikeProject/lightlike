import Mathlib
import Lightlike.TemperleyLieb.Contraction

/-!
# Absorption of the sub-blocks of a projector

`jwAt q (s+1) n · jwAt q s (n+1) = jwAt q s (n+1)`: the projector on `n+1` strands absorbs the projector on its last
`n` strands (the first `n` strands are `JwProps.absL`); this is the mirror image.
-/

namespace Lightlike.TemperleyLieb

open Finsupp

variable {k : Type*} [Field k]

/-- The projector on `n + 1` strands absorbs, on the left, the projector on its last `n` strands. -/
theorem jwAt_absorb_suffix_left (q : kˣ) (s n : ℕ) (hd : ∀ j, j < n + 1 → chebD (loopVal q) j ≠ 0) :
    jwAt q (s + 1) n * jwAt q s (n + 1) = jwAt q s (n + 1) := by
  set N := s + n + 1 with hN
  have hρ := reflectOp_mul_self (k := k) N
  have m1 : jwAt q s (n + 1) = reflectOp k N * jwAt q 0 (n + 1) * reflectOp k N := by
    have := jwAt_mirror (k := k) q 0 s (n + 1) hd
    rwa [show 0 + s + (n + 1) = N by omega] at this
  have m2 : jwAt q (s + 1) n = reflectOp k N * jwAt q 0 n * reflectOp k N := by
    have := jwAt_mirror (k := k) q 0 (s + 1) n (fun j hj => hd j (by omega))
    rwa [show 0 + (s + 1) + n = N by omega] at this
  have hp := jwProps_of_le (isTL_shift q 0) (n + 1) hd (n + 1) le_rfl
  have h1 : jwAt q 0 n * jwAt q 0 (n + 1) = jwAt q 0 (n + 1) := hp.absL n (by omega)
  rw [m1, m2]
  calc reflectOp k N * jwAt q 0 n * reflectOp k N * (reflectOp k N * jwAt q 0 (n + 1) * reflectOp k N)
      = reflectOp k N * (jwAt q 0 n * jwAt q 0 (n + 1)) * reflectOp k N := by
        simp only [mul_assoc, ← mul_assoc (reflectOp k N) (reflectOp k N), hρ, one_mul]
    _ = _ := by rw [h1]

/-- The projector on `n + 1` strands absorbs, on the right, the projector on its last `n` strands. -/
theorem jwAt_absorb_suffix_right (q : kˣ) (s n : ℕ) (hd : ∀ j, j < n + 1 → chebD (loopVal q) j ≠ 0) :
    jwAt q s (n + 1) * jwAt q (s + 1) n = jwAt q s (n + 1) := by
  set N := s + n + 1 with hN
  have hρ := reflectOp_mul_self (k := k) N
  have m1 : jwAt q s (n + 1) = reflectOp k N * jwAt q 0 (n + 1) * reflectOp k N := by
    have := jwAt_mirror (k := k) q 0 s (n + 1) hd
    rwa [show 0 + s + (n + 1) = N by omega] at this
  have m2 : jwAt q (s + 1) n = reflectOp k N * jwAt q 0 n * reflectOp k N := by
    have := jwAt_mirror (k := k) q 0 (s + 1) n (fun j hj => hd j (by omega))
    rwa [show 0 + (s + 1) + n = N by omega] at this
  have hp := jwProps_of_le (isTL_shift q 0) (n + 1) hd (n + 1) le_rfl
  have h1 : jwAt q 0 (n + 1) * jwAt q 0 n = jwAt q 0 (n + 1) := hp.absR n (by omega)
  rw [m1, m2]
  calc reflectOp k N * jwAt q 0 (n + 1) * reflectOp k N * (reflectOp k N * jwAt q 0 n * reflectOp k N)
      = reflectOp k N * (jwAt q 0 (n + 1) * jwAt q 0 n) * reflectOp k N := by
        simp only [mul_assoc, ← mul_assoc (reflectOp k N) (reflectOp k N), hρ, one_mul]
    _ = _ := by rw [h1]

/-- The product of the two projectors of a vertex: `Q(a,b) = p_a · p_b'` on the strands `0..a-1` and `a..a+b-1`. -/
noncomputable def Qab (q : kˣ) (a b : ℕ) : Module.End k (ModelSpace k) := jwAt q 0 a * jwAt q a b

/-- **The cup absorbs into the product**: `Q(α+1, β+1) cup_α = Q(α+1,β+1) cup_α Q(α,β)`. -/
theorem Qab_cup (q : kˣ) (α β : ℕ) (hd : ∀ j, j ≤ α + β + 1 → chebD (loopVal q) j ≠ 0) :
    Qab q (α + 1) (β + 1) * cupOp q α = Qab q (α + 1) (β + 1) * cupOp q α * Qab q α β := by
  have h1 : jwAt q 0 (α + 1) * jwAt q 0 α = jwAt q 0 (α + 1) := by
    have hp := jwProps_of_le (isTL_shift q 0) (α + 1) (fun j hj => hd j (by omega)) (α + 1) le_rfl
    exact hp.absR α (by omega)
  have h2 : jwAt q (α + 1) (β + 1) * jwAt q (α + 2) β = jwAt q (α + 1) (β + 1) :=
    jwAt_absorb_suffix_right q (α + 1) β (fun j hj => hd j (by omega))
  have h3 : jwAt q 0 α * jwAt q (α + 2) β = jwAt q (α + 2) β * jwAt q 0 α := jwAt_comm_far q (by omega)
  have h4 : jwAt q 0 (α + 1) * jwAt q (α + 2) β = jwAt q (α + 2) β * jwAt q 0 (α + 1) :=
    jwAt_comm_far q (by omega)
  have h5 : jwAt q (α + 1) (β + 1) * jwAt q 0 α = jwAt q 0 α * jwAt q (α + 1) (β + 1) :=
    (jwAt_comm_far q (by omega)).symm
  have hQ : Qab q (α + 1) (β + 1) = Qab q (α + 1) (β + 1) * (jwAt q 0 α * jwAt q (α + 2) β) := by
    unfold Qab
    calc jwAt q 0 (α + 1) * jwAt q (α + 1) (β + 1)
        = jwAt q 0 (α + 1) * (jwAt q (α + 1) (β + 1) * jwAt q (α + 2) β) := by rw [h2]
      _ = jwAt q 0 (α + 1) * jwAt q (α + 1) (β + 1) * jwAt q (α + 2) β := by rw [mul_assoc]
      _ = jwAt q 0 (α + 1) * jwAt q 0 α * jwAt q (α + 1) (β + 1) * jwAt q (α + 2) β := by
          rw [h1]
      _ = _ := by
          simp only [mul_assoc]
          rw [← mul_assoc (jwAt q (α + 1) (β + 1)), h5]
          simp only [mul_assoc]
  have hc1 : jwAt q 0 α * cupOp q α = cupOp q α * jwAt q 0 α :=
    (cup_mul_jwAt_near q (m := α) (s := 0) (n := α) (by omega)).symm
  have hc2 : jwAt q (α + 2) β * cupOp q α = cupOp q α * jwAt q α β :=
    (cup_mul_jwAt_far q (m := α) (s := α) (le_refl _) β).symm
  calc Qab q (α + 1) (β + 1) * cupOp q α
      = Qab q (α + 1) (β + 1) * (jwAt q 0 α * (jwAt q (α + 2) β * cupOp q α)) := by
        conv_lhs => rw [hQ]
        simp only [mul_assoc]
    _ = Qab q (α + 1) (β + 1) * (jwAt q 0 α * (cupOp q α * jwAt q α β)) := by rw [hc2]
    _ = Qab q (α + 1) (β + 1) * ((jwAt q 0 α * cupOp q α) * jwAt q α β) := by rw [mul_assoc]
    _ = Qab q (α + 1) (β + 1) * (cupOp q α * jwAt q 0 α * jwAt q α β) := by rw [hc1]
    _ = Qab q (α + 1) (β + 1) * cupOp q α * Qab q α β := by unfold Qab; simp only [mul_assoc]

/-- The coefficient `s = d_{a-2}/d_{a-1}` of the projector recursion, `0` for `a = 1`. -/
noncomputable def sCoef (q : kˣ) (a : ℕ) : k :=
  if 2 ≤ a then chebD (loopVal q) (a - 2) / chebD (loopVal q) (a - 1) else 0

/-- Contraction when the first block has one strand. -/
theorem contraction_abstract_one {A : Type*} [Ring A] [Algebra k A] (δ t : k) (c u Pr Pr2 Eb capb : A)
    (h_cu : c * u = algebraMap k A δ) (h_Pr_c : c * Pr = Pr2 * c) (h_Pr_u : u * Pr2 = Pr * u)
    (h_cEb : c * Eb = capb) (h_capb_u : capb * u = 1) (h_Pr2_idem : Pr2 * Pr2 = Pr2) :
    c * (Pr - t • (Pr * Eb * Pr)) * u = (δ - t) • Pr2 := by
  have R2 : ∀ x, c * (Pr * x) = Pr2 * (c * x) := fun x => by rw [← mul_assoc, h_Pr_c, mul_assoc]
  have R3 : ∀ x, c * (Eb * x) = capb * x := fun x => by rw [← mul_assoc, h_cEb]
  have R5 : ∀ x, Pr * (u * x) = u * (Pr2 * x) := fun x => by rw [← mul_assoc, ← h_Pr_u, mul_assoc]
  have R7 : ∀ x, capb * (u * x) = x := fun x => by rw [← mul_assoc, h_capb_u, one_mul]
  have P5 : Pr * u = u * Pr2 := h_Pr_u.symm
  have S0 : c * Pr * u = δ • Pr2 := by
    simp only [mul_assoc, R2, h_cu, Algebra.algebraMap_eq_smul_one, mul_smul_comm, mul_one]
  have S1 : c * (Pr * Eb * Pr) * u = Pr2 := by
    simp only [mul_assoc, R2, R3, R5, P5, h_capb_u, R7, mul_one, h_Pr2_idem]
  simp only [mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc, S0, S1]
  module

/-- Contraction when the second block has one strand. -/
theorem contraction_abstract_one' {A : Type*} [Ring A] [Algebra k A] (δ s : k) (c u Pl Ea capa : A)
    (h_cu : c * u = algebraMap k A δ) (h_Pl_c : c * Pl = Pl * c) (h_Pl_u : u * Pl = Pl * u)
    (h_cEa : c * Ea = capa) (h_capa_u : capa * u = 1) (h_Pl_idem : Pl * Pl = Pl) :
    c * (Pl - s • (Pl * Ea * Pl)) * u = (δ - s) • Pl := by
  have R1 : ∀ x, c * (Pl * x) = Pl * (c * x) := fun x => by rw [← mul_assoc, h_Pl_c, mul_assoc]
  have R4 : ∀ x, c * (Ea * x) = capa * x := fun x => by rw [← mul_assoc, h_cEa]
  have R6 : ∀ x, Pl * (u * x) = u * (Pl * x) := fun x => by rw [← mul_assoc, ← h_Pl_u, mul_assoc]
  have R8 : ∀ x, capa * (u * x) = x := fun x => by rw [← mul_assoc, h_capa_u, one_mul]
  have P6 : Pl * u = u * Pl := h_Pl_u.symm
  have S0 : c * Pl * u = δ • Pl := by
    simp only [mul_assoc, R1, h_cu, Algebra.algebraMap_eq_smul_one, mul_smul_comm, mul_one]
  have S1 : c * (Pl * Ea * Pl) * u = Pl := by
    simp only [mul_assoc, R1, R4, R6, P6, R8, h_capa_u, mul_one, h_Pl_idem]
  simp only [mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc, S0, S1]
  module

/-- **Contraction for all block sizes** (`a = α + 1`, `b = β + 1`):
`cap_α Q(a,b) cup_α = (δ - s_a - s_b) Q(a-1,b-1) + s_a s_b Q(a-1,b-1) e_{a-2} Q(a-1,b-1)`. -/
theorem contraction_all (q : kˣ) (α β : ℕ) (hd : ∀ j, j ≤ α + β + 1 → chebD (loopVal q) j ≠ 0) :
    capOp q α * Qab q (α + 1) (β + 1) * cupOp q α =
      (loopVal q - sCoef q (α + 1) - sCoef q (β + 1)) • Qab q α β +
        (sCoef q (α + 1) * sCoef q (β + 1)) • (Qab q α β * modelE q (α - 1) * Qab q α β) := by
  rcases α with _ | α <;> rcases β with _ | β
  · -- a = b = 1
    simp [Qab, sCoef, jwAt, jw_zero, jw_one, cap_cup, loopVal]
    simp only [Algebra.algebraMap_eq_smul_one]
    module
  · -- a = 1, b = β + 2
    have hPr : jwAt q 1 (β + 2) = jwAt q 2 (β + 1) -
        (chebD (loopVal q) β / chebD (loopVal q) (β + 1)) •
          (jwAt q 2 (β + 1) * modelE q 1 * jwAt q 2 (β + 1)) :=
      jwAt_succ_succ_left q 1 β (fun j hj => hd j (by omega))
    have p2 := jwProps_of_le (isTL_shift q 0) (β + 1) (fun j hj => hd j (by omega)) (β + 1) le_rfl
    have h1 : jwAt q 0 1 = 1 := by unfold jwAt; exact jw_one
    have h0 : jwAt q 0 0 = 1 := by unfold jwAt; exact jw_zero
    have hs : sCoef q (0 + 1) = 0 := by simp [sCoef]
    have ht : sCoef q (β + 1 + 1) = chebD (loopVal q) β / chebD (loopVal q) (β + 1) := by
      simp [sCoef]
    simp only [Qab, h1, h0, one_mul, hs, ht, hPr, sub_zero, zero_mul, zero_smul, add_zero, zero_sub]
    exact contraction_abstract_one (loopVal q) _ (capOp q 0) (cupOp q 0) (jwAt q 2 (β + 1))
      (jwAt q 0 (β + 1)) (modelE q 1) (capOp q 1) (cap_cup q 0) (cap_mul_jwAt_far q (le_refl 0) _)
      (cup_mul_jwAt_far q (le_refl 0) _) (cap_mul_e_succ q 0) (cap_succ_cup q 0) p2.idem
  · -- a = α + 2, b = 1
    have hPl : jwAt q 0 (α + 2) = jwAt q 0 (α + 1) -
        (chebD (loopVal q) α / chebD (loopVal q) (α + 1)) •
          (jwAt q 0 (α + 1) * modelE q α * jwAt q 0 (α + 1)) := jw_succ_succ α
    have p1 := jwProps_of_le (isTL_shift q 0) (α + 1) (fun j hj => hd j (by omega)) (α + 1) le_rfl
    have h1 : jwAt q (α + 2) 1 = 1 := by unfold jwAt; exact jw_one
    have h0 : jwAt q (α + 1) 0 = 1 := by unfold jwAt; exact jw_zero
    have hs : sCoef q (α + 1 + 1) = chebD (loopVal q) α / chebD (loopVal q) (α + 1) := by
      simp [sCoef]
    have ht : sCoef q (0 + 1) = 0 := by simp [sCoef]
    simp only [Qab, h1, h0, mul_one, hs, ht, hPl, sub_zero, zero_mul, mul_zero, zero_smul, add_zero]
    exact contraction_abstract_one' (loopVal q) _ (capOp q (α + 1)) (cupOp q (α + 1)) (jwAt q 0 (α + 1))
      (modelE q α) (capOp q α) (cap_cup q (α + 1)) (cap_mul_jwAt_near q (m := α + 1) (s := 0) (n := α + 1) (by omega))
      (cup_mul_jwAt_near q (m := α + 1) (s := 0) (n := α + 1) (by omega)) (cap_mul_e_pred q α)
      (cap_cup_succ q α) p1.idem
  · -- a = α + 2, b = β + 2
    have := contraction q α β (fun j hj => hd j (by omega))
    simp only [Qab, sCoef, show 2 ≤ α + 1 + 1 by omega, show 2 ≤ β + 1 + 1 by omega, if_true]
    simpa using this

/-- The scalar by which `Q e_{a-1} Q` acts on the vertex with `i` arcs. -/
noncomputable def lamRec (q : kˣ) : ℕ → ℕ → ℕ → k
  | _, _, 0 => 0
  | a, b, i + 1 => loopVal q - sCoef q a - sCoef q b + sCoef q a * sCoef q b * lamRec q (a - 1) (b - 1) i

/-- The vertex operator with `i` arcs: `V(a,b;i) = Q(a,b) · nestCup (a-i) i · p_{a+b-2i}`. -/
noncomputable def Vop (q : kˣ) (a b i : ℕ) : Module.End k (ModelSpace k) :=
  Qab q a b * nestCup q (a - i) i * jwAt q 0 (a + b - 2 * i)

/-- `Q(a,b)` is idempotent. -/
theorem Qab_idem (q : kˣ) (a b : ℕ) (hd : ∀ j, j < max a b → chebD (loopVal q) j ≠ 0) :
    Qab q a b * Qab q a b = Qab q a b := by
  have p1 := jwProps_of_le (isTL_shift q 0) a (fun j hj => hd j (lt_of_lt_of_le hj (le_max_left _ _))) a le_rfl
  have p2 := jwProps_of_le (isTL_shift q a) b (fun j hj => hd j (lt_of_lt_of_le hj (le_max_right _ _))) b le_rfl
  have hc : jwAt q 0 a * jwAt q a b = jwAt q a b * jwAt q 0 a := jwAt_comm_far q (by omega)
  unfold Qab
  calc jwAt q 0 a * jwAt q a b * (jwAt q 0 a * jwAt q a b)
      = jwAt q 0 a * (jwAt q a b * jwAt q 0 a) * jwAt q a b := by simp only [mul_assoc]
    _ = jwAt q 0 a * (jwAt q 0 a * jwAt q a b) * jwAt q a b := by rw [← hc]
    _ = (jwAt q 0 a * jwAt q 0 a) * (jwAt q a b * jwAt q a b) := by simp only [mul_assoc]
    _ = jwAt q 0 a * jwAt q a b := by
        have e1 : jwAt q 0 a * jwAt q 0 a = jwAt q 0 a := p1.idem
        have e2 : jwAt q a b * jwAt q a b = jwAt q a b := p2.idem
        rw [e1, e2]

/-- `Q(a,b)` acts on the full projector by a scalar. -/
theorem Qab_mul_full (q : kˣ) (a b : ℕ) (hd : ∀ j, j < a + b → chebD (loopVal q) j ≠ 0) :
    ∃ κ : k, Qab q a b * jwAt q 0 (a + b) = κ • jwAt q 0 (a + b) := by
  have hp := jwProps_of_le (isTL_shift q 0) (a + b) hd (a + b) le_rfl
  have hjw : jwAt q 0 (a + b) = jw (loopVal q) (modelE q) (a + b) := rfl
  have hL : ∀ j < a + b - 1, modelE q j * jwAt q 0 (a + b) = 0 := fun j hj => by
    rw [hjw]; exact hp.killL j (by omega)
  have hR : ∀ j < a + b - 1, jwAt q 0 (a + b) * modelE q j = 0 := fun j hj => by
    rw [hjw]; exact hp.killR j (by omega)
  have hQ : Qab q a b ∈ CSub q (a + b - 1) := by
    unfold Qab
    refine Subalgebra.mul_mem _ ?_ ?_
    · exact tlSub_mono (m := 0 + a - 1) (n := a + b - 1) (by omega) (jwAt_mem q 0 a)
    · have := jwAt_mem q a b
      exact this
  obtain ⟨κ, -, h2⟩ := absorb (k := k) (e := modelE q) (p := jwAt q 0 (a + b)) hL hR _ hQ
  exact ⟨κ, h2⟩

end Lightlike.TemperleyLieb
