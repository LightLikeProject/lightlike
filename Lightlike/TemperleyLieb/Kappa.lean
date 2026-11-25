import Mathlib
import Lightlike.TemperleyLieb.Contraction

/-!
# Absorption of the sub-blocks of a projector, the eigen-equation and the vertex norm

`jwAt q (s+1) n · jwAt q s (n+1) = jwAt q s (n+1)`: the projector on `n+1` strands absorbs the projector on its last
`n` strands (the first `n` strands are `JwProps.absL`); this is the mirror image.  `contraction_all` is the
contraction of the junction for every block size, `vertex_eigen` shows that `Q e_{a-1} Q` acts on the vertex with `i`
arcs by the scalar `lamRec a b i`, and `vertex_norm_value` that `p_c (nestCap Q nestCup) p_c = kapRec a b i · p_c`,
with `kapRec a b (i+1) = lamRec a b (i+1) · kapRec (a-1) (b-1) i`.
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

/-- **The eigen-equation**: `Q e_{a-1} Q` acts on the vertex with `i` arcs by `lamRec a b i`. -/
theorem vertex_eigen (q : kˣ) : ∀ (i a b : ℕ), 1 ≤ a → 1 ≤ b → i ≤ a → i ≤ b →
    (∀ j, j ≤ a + b → chebD (loopVal q) j ≠ 0) →
    (Qab q a b * modelE q (a - 1) * Qab q a b) * Vop q a b i = lamRec q a b i • Vop q a b i := by
  intro i
  induction i with
  | zero =>
    intro a b ha hb _ _ hd
    obtain ⟨κ, hκ⟩ := Qab_mul_full q a b (fun j hj => hd j (by omega))
    have hQ := Qab_idem q a b (fun j hj => hd j (by omega))
    have hp := jwProps_of_le (isTL_shift q 0) (a + b) (fun j hj => hd j (by omega)) (a + b) le_rfl
    have hjw : jwAt q 0 (a + b) = jw (loopVal q) (modelE q) (a + b) := rfl
    have hk : modelE q (a - 1) * jwAt q 0 (a + b) = 0 := by
      rw [hjw]; exact hp.killL (a - 1) (by omega)
    simp only [Vop, nestCup, mul_one, Nat.sub_zero, mul_zero, Nat.add_zero, lamRec, zero_smul]
    calc Qab q a b * modelE q (a - 1) * Qab q a b * (Qab q a b * jwAt q 0 (a + b))
        = Qab q a b * modelE q (a - 1) * (Qab q a b * Qab q a b) * jwAt q 0 (a + b) := by
          simp only [mul_assoc]
      _ = Qab q a b * modelE q (a - 1) * Qab q a b * jwAt q 0 (a + b) := by rw [hQ]
      _ = 0 := by
          rw [mul_assoc (Qab q a b * modelE q (a - 1)), hκ, mul_smul_comm, mul_assoc (Qab q a b), hk]
          simp
  | succ i' ih =>
    intro a b ha hb hia hib hd
    obtain ⟨α, rfl⟩ : ∃ α, a = α + 1 := ⟨a - 1, by omega⟩
    obtain ⟨β, rfl⟩ : ∃ β, b = β + 1 := ⟨b - 1, by omega⟩
    have hd' : ∀ j, j ≤ α + β + 1 → chebD (loopVal q) j ≠ 0 := fun j hj => hd j (by omega)
    have hQ := Qab_idem q (α + 1) (β + 1) (fun j hj => hd j (by omega))
    have hQ2 := Qab_idem q α β (fun j hj => hd j (by omega))
    -- decomposition of the vertex
    have hV : Vop q (α + 1) (β + 1) (i' + 1) =
        Qab q (α + 1) (β + 1) * cupOp q α * Vop q α β i' := by
      have hl : α + 1 - (i' + 1) = α - i' := by omega
      have hc : α + 1 + (β + 1) - 2 * (i' + 1) = α + β - 2 * i' := by omega
      have hl2 : α - i' + i' = α := by omega
      unfold Vop
      rw [hl, hc]
      have hnest : nestCup q (α - i') (i' + 1) = cupOp q α * nestCup q (α - i') i' := by
        simp only [nestCup, hl2]
      rw [hnest]
      calc Qab q (α + 1) (β + 1) * (cupOp q α * nestCup q (α - i') i') * jwAt q 0 (α + β - 2 * i')
          = (Qab q (α + 1) (β + 1) * cupOp q α) * nestCup q (α - i') i' * jwAt q 0 (α + β - 2 * i') := by
            simp only [mul_assoc]
        _ = (Qab q (α + 1) (β + 1) * cupOp q α * Qab q α β) * nestCup q (α - i') i' *
              jwAt q 0 (α + β - 2 * i') := by rw [← Qab_cup q α β hd']
        _ = _ := by simp only [mul_assoc]
    have hQV : Qab q α β * Vop q α β i' = Vop q α β i' := by
      unfold Vop
      rw [← mul_assoc, ← mul_assoc, hQ2]
    have hX := contraction_all q α β hd'
    have key : (capOp q α * Qab q (α + 1) (β + 1) * cupOp q α) * Vop q α β i' =
        lamRec q (α + 1) (β + 1) (i' + 1) • Vop q α β i' := by
      rw [hX, add_mul, smul_mul_assoc, smul_mul_assoc, hQV]
      by_cases hαβ : 1 ≤ α ∧ 1 ≤ β
      · have hih := ih α β hαβ.1 hαβ.2 (by omega) (by omega) (fun j hj => hd j (by omega))
        rw [hih]
        simp only [lamRec, Nat.add_sub_cancel, smul_smul]
        module
      · have hc2 : sCoef q (α + 1) * sCoef q (β + 1) = 0 := by
          rcases Nat.eq_zero_or_pos α with h0 | h0
          · subst h0; simp [sCoef]
          · have : β = 0 := by omega
            subst this; simp [sCoef]
        rw [hc2]
        simp only [lamRec, Nat.add_sub_cancel, hc2, zero_smul, add_zero, zero_mul]
    rw [hV, Nat.add_sub_cancel]
    calc Qab q (α + 1) (β + 1) * modelE q α * Qab q (α + 1) (β + 1) *
          (Qab q (α + 1) (β + 1) * cupOp q α * Vop q α β i')
        = Qab q (α + 1) (β + 1) * modelE q α * (Qab q (α + 1) (β + 1) * Qab q (α + 1) (β + 1)) *
          cupOp q α * Vop q α β i' := by simp only [mul_assoc]
      _ = Qab q (α + 1) (β + 1) * (cupOp q α * capOp q α) * Qab q (α + 1) (β + 1) *
          cupOp q α * Vop q α β i' := by rw [hQ, cup_cap]
      _ = Qab q (α + 1) (β + 1) * cupOp q α * ((capOp q α * Qab q (α + 1) (β + 1) * cupOp q α) *
          Vop q α β i') := by simp only [mul_assoc]
      _ = lamRec q (α + 1) (β + 1) (i' + 1) • (Qab q (α + 1) (β + 1) * cupOp q α * Vop q α β i') := by
          rw [key, mul_smul_comm]

/-- The projector on `n + r` strands absorbs the projector on its last `n` strands, on the left. -/
theorem jwAt_absorb_suffix_all (q : kˣ) (s : ℕ) : ∀ (r n : ℕ),
    (∀ j, j < n + r → chebD (loopVal q) j ≠ 0) →
    jwAt q (s + r) n * jwAt q s (n + r) = jwAt q s (n + r) := by
  intro r
  induction r with
  | zero =>
    intro n hd
    have hp := jwProps_of_le (isTL_shift q s) n (fun j hj => hd j (by omega)) n le_rfl
    exact hp.idem
  | succ r ih =>
    intro n hd
    have h1 := ih (n + 1) (fun j hj => hd j (by omega))
    have h2 := jwAt_absorb_suffix_left q (s + r) n (fun j hj => hd j (by omega))
    have e1 : n + 1 + r = n + (r + 1) := by omega
    rw [e1] at h1
    calc jwAt q (s + (r + 1)) n * jwAt q s (n + (r + 1))
        = jwAt q (s + r + 1) n * jwAt q s (n + (r + 1)) := rfl
      _ = jwAt q (s + r + 1) n * (jwAt q (s + r) (n + 1) * jwAt q s (n + (r + 1))) := by rw [h1]
      _ = (jwAt q (s + r + 1) n * jwAt q (s + r) (n + 1)) * jwAt q s (n + (r + 1)) := by rw [mul_assoc]
      _ = _ := by rw [h2, h1]

/-- The norm of the vertex with `i` arcs, as a recursion. -/
noncomputable def kapRec (q : kˣ) : ℕ → ℕ → ℕ → k
  | _, _, 0 => 1
  | a, b, i + 1 => lamRec q a b (i + 1) * kapRec q (a - 1) (b - 1) i

/-- `Q(a,b)` acts on the full projector as the identity. -/
theorem Qab_mul_full_eq (q : kˣ) (a b : ℕ) (hd : ∀ j, j < a + b → chebD (loopVal q) j ≠ 0) :
    Qab q a b * jwAt q 0 (a + b) = jwAt q 0 (a + b) := by
  have h1 := jwAt_absorb_suffix_all q 0 a b (fun j hj => hd j (by omega))
  rw [show b + a = a + b by omega, zero_add] at h1
  have hp := jwProps_of_le (isTL_shift q 0) (a + b) hd (a + b) le_rfl
  have h2 : jwAt q 0 a * jwAt q 0 (a + b) = jwAt q 0 (a + b) := hp.absL a (by omega)
  unfold Qab
  rw [mul_assoc, h1, h2]

/-- **The value of the vertex norm**: `p_c (nestCap Q nestCup) p_c = kapRec a b i · p_c`. -/
theorem vertex_norm_value (q : kˣ) : ∀ (i a b : ℕ), i ≤ a → i ≤ b →
    (∀ j, j ≤ a + b → chebD (loopVal q) j ≠ 0) →
    jwAt q 0 (a + b - 2 * i) * (nestCap q (a - i) i * Qab q a b * nestCup q (a - i) i) *
        jwAt q 0 (a + b - 2 * i) = kapRec q a b i • jwAt q 0 (a + b - 2 * i) := by
  intro i
  induction i with
  | zero =>
    intro a b _ _ hd
    have hp := jwProps_of_le (isTL_shift q 0) (a + b) (fun j hj => hd j (by omega)) (a + b) le_rfl
    have hQP := Qab_mul_full_eq q a b (fun j hj => hd j (by omega))
    have hidem : jwAt q 0 (a + b) * jwAt q 0 (a + b) = jwAt q 0 (a + b) := hp.idem
    simp only [nestCap, nestCup, one_mul, mul_one, Nat.sub_zero, mul_zero, Nat.add_zero, kapRec, one_smul]
    rw [mul_assoc, hQP, hidem]
  | succ i' ih =>
    intro a b hia hib hd
    obtain ⟨α, rfl⟩ : ∃ α, a = α + 1 := ⟨a - 1, by omega⟩
    obtain ⟨β, rfl⟩ : ∃ β, b = β + 1 := ⟨b - 1, by omega⟩
    have hd' : ∀ j, j ≤ α + β + 1 → chebD (loopVal q) j ≠ 0 := fun j hj => hd j (by omega)
    have hl : α + 1 - (i' + 1) = α - i' := by omega
    have hc : α + 1 + (β + 1) - 2 * (i' + 1) = α + β - 2 * i' := by omega
    have hl2 : α - i' + i' = α := by omega
    have hQ2 := Qab_idem q α β (fun j hj => hd j (by omega))
    have hX := contraction_all q α β hd'
    have ih' := ih α β (by omega) (by omega) (fun j hj => hd j (by omega))
    have hcap : nestCap q (α - i') (i' + 1) = nestCap q (α - i') i' * capOp q α := by
      simp only [nestCap, hl2]
    have hcup : nestCup q (α - i') (i' + 1) = cupOp q α * nestCup q (α - i') i' := by
      simp only [nestCup, hl2]
    rw [hl, hc, hcap, hcup]
    have hmid : nestCap q (α - i') i' * capOp q α * Qab q (α + 1) (β + 1) * (cupOp q α * nestCup q (α - i') i') =
        nestCap q (α - i') i' * (capOp q α * Qab q (α + 1) (β + 1) * cupOp q α) * nestCup q (α - i') i' := by
      simp only [mul_assoc]
    rw [hmid, hX]
    have hJ : (1 ≤ α ∧ 1 ≤ β) →
        nestCap q (α - i') i' * (Qab q α β * modelE q (α - 1) * Qab q α β) * nestCup q (α - i') i' *
            jwAt q 0 (α + β - 2 * i') =
          lamRec q α β i' • (nestCap q (α - i') i' * Qab q α β * nestCup q (α - i') i' *
            jwAt q 0 (α + β - 2 * i')) := by
      intro hαβ
      have hih := vertex_eigen q i' α β hαβ.1 hαβ.2 (by omega) (by omega) (fun j hj => hd j (by omega))
      unfold Vop at hih
      calc nestCap q (α - i') i' * (Qab q α β * modelE q (α - 1) * Qab q α β) * nestCup q (α - i') i' *
            jwAt q 0 (α + β - 2 * i')
          = nestCap q (α - i') i' * ((Qab q α β * modelE q (α - 1) * Qab q α β) *
              (Qab q α β * nestCup q (α - i') i' * jwAt q 0 (α + β - 2 * i'))) := by
            simp only [mul_assoc]
            rw [← mul_assoc (Qab q α β) (Qab q α β), hQ2]
        _ = _ := by rw [hih, mul_smul_comm]; simp only [mul_assoc]
    by_cases hαβ : 1 ≤ α ∧ 1 ≤ β
    · have h1 := hJ hαβ
      calc jwAt q 0 (α + β - 2 * i') * (nestCap q (α - i') i' *
            ((loopVal q - sCoef q (α + 1) - sCoef q (β + 1)) • Qab q α β +
              (sCoef q (α + 1) * sCoef q (β + 1)) • (Qab q α β * modelE q (α - 1) * Qab q α β)) *
            nestCup q (α - i') i') * jwAt q 0 (α + β - 2 * i')
          = (loopVal q - sCoef q (α + 1) - sCoef q (β + 1)) •
              (jwAt q 0 (α + β - 2 * i') * (nestCap q (α - i') i' * Qab q α β * nestCup q (α - i') i') *
                jwAt q 0 (α + β - 2 * i')) +
            (sCoef q (α + 1) * sCoef q (β + 1)) •
              (jwAt q 0 (α + β - 2 * i') * (nestCap q (α - i') i' * (Qab q α β * modelE q (α - 1) * Qab q α β) *
                nestCup q (α - i') i') * jwAt q 0 (α + β - 2 * i')) := by
            simp only [mul_add, add_mul, mul_smul_comm, smul_mul_assoc]
        _ = _ := by
            have e2 : jwAt q 0 (α + β - 2 * i') * (nestCap q (α - i') i' * (Qab q α β * modelE q (α - 1) * Qab q α β) *
                nestCup q (α - i') i') * jwAt q 0 (α + β - 2 * i') =
                lamRec q α β i' • (kapRec q α β i' • jwAt q 0 (α + β - 2 * i')) := by
              calc jwAt q 0 (α + β - 2 * i') * (nestCap q (α - i') i' * (Qab q α β * modelE q (α - 1) * Qab q α β) *
                    nestCup q (α - i') i') * jwAt q 0 (α + β - 2 * i')
                  = jwAt q 0 (α + β - 2 * i') * (nestCap q (α - i') i' * (Qab q α β * modelE q (α - 1) * Qab q α β) *
                    nestCup q (α - i') i' * jwAt q 0 (α + β - 2 * i')) := by simp only [mul_assoc]
                _ = jwAt q 0 (α + β - 2 * i') * (lamRec q α β i' • (nestCap q (α - i') i' * Qab q α β *
                    nestCup q (α - i') i' * jwAt q 0 (α + β - 2 * i'))) := by rw [h1]
                _ = lamRec q α β i' • (jwAt q 0 (α + β - 2 * i') * (nestCap q (α - i') i' * Qab q α β *
                    nestCup q (α - i') i') * jwAt q 0 (α + β - 2 * i')) := by
                    rw [mul_smul_comm]; simp only [mul_assoc]
                _ = lamRec q α β i' • (kapRec q α β i' • jwAt q 0 (α + β - 2 * i')) := by rw [ih']
            rw [e2, ih']
            simp only [kapRec, lamRec, Nat.add_sub_cancel, smul_smul]
            module
    · have hc2 : sCoef q (α + 1) * sCoef q (β + 1) = 0 := by
        rcases Nat.eq_zero_or_pos α with h0 | h0
        · subst h0; simp [sCoef]
        · have : β = 0 := by omega
          subst this; simp [sCoef]
      simp only [hc2, zero_smul, add_zero, mul_add, add_mul, mul_smul_comm, smul_mul_assoc, ih']
      simp only [kapRec, lamRec, Nat.add_sub_cancel, hc2, smul_smul, zero_mul, add_zero]

end Lightlike.TemperleyLieb
