import Lightlike.Regge.Linear3.LinearizedTorus
import Lightlike.Regge.Linear3.InterpTaylor
import Lightlike.Regge.Linear3.SaintVenantCore

/-!
# `Q_n (h)` as a lattice sum of hinge densities

The coefficient `Q_n (h) = Σ_e (a_e / (2 ℓ_e)) δ_e'(0)` of the linearized Regge action on the periodic Kuhn complex
(`LinearizedTorus.lean`) is a sum over the cells `z` of the lattice and the seven edge classes `k` of
`(1/n) · (A_h / (2 |w_k|)) · (-Σ_{(σ,h) in class k} dth h (atilV) / |w_k|)` (`Qn_lattice`), where
`A_h = hAt` is the unit-scale degree of freedom of the hinge edge and `atilV` the six unit-scale degrees of
freedom of the incidence `(σ, h)` at the hinge midpoint, `atil = ∫₀¹ D ⬝ hf (v + ε (k_a + t D)) D dt`. The
unit-scale variation is `n²` times the degree of freedom `μ_e` of the corners (`muVec_eq_atilV`, `muE_scaled`):
the corners of the tetrahedra are the hinge midpoint plus `ε` times the relative positions (`cornerPt_eq`).

## Main results

* `atil`, `atilV`, `hAt`: the unit-scale degrees of freedom.
* `muVec_eq_atilV`: `n² μ_e` of the corners is `atil`.
* `Qn_lattice`: `Q_n` as a lattice sum over the hinges.

**Limits.** `n ≥ 3`, `hf` invariant under integer translations; this file is the exact rewriting at finite
`n`, the limit `n → ∞` is `LinearizedLimit.lean`.
-/

open Real Finset Filter Topology Matrix
namespace Lightlike.Regge.Linear3
open Lightlike.Regge Lightlike.Regge.Conv3

variable (n : ℕ) [NeZero n]

/-- The corner `a` of the incidence `(σ, h)` relative to the hinge midpoint, as a vector of `ℝ³`. -/
noncomputable def kposv (σ h : Fin 6) (a : Fin 4) : Fin 3 → ℝ := fun i => kpos σ h a i

/-- **The unit-scale degree of freedom** of the edge from corner `a` to corner `b` of the incidence `(σ, h)` at
the hinge midpoint `v` and scale `ε`: `∫₀¹ D ⬝ hf (v + ε (k_a + t D)) D dt`, `D = k_b - k_a`. -/
noncomputable def atil (hf : (Fin 3 → ℝ) → Matrix (Fin 3) (Fin 3) ℝ) (ε : ℝ) (v : Fin 3 → ℝ) (σ h : Fin 6)
    (a b : Fin 4) : ℝ :=
  ∫ t in (0 : ℝ)..1, (kposv σ h b - kposv σ h a) ⬝ᵥ
    (hf (v + ε • (kposv σ h a + t • (kposv σ h b - kposv σ h a))) *ᵥ (kposv σ h b - kposv σ h a))

/-- The six unit-scale degrees of freedom `(pq, pr, qr, ps, qs, rs)` of the incidence `(σ, h)`. -/
noncomputable def atilV (hf : (Fin 3 → ℝ) → Matrix (Fin 3) (Fin 3) ℝ) (ε : ℝ) (v : Fin 3 → ℝ) (σ h : Fin 6) :
    Fin 6 → ℝ :=
  ![atil hf ε v σ h (hP h) (hQ h), atil hf ε v σ h (hP h) (hR h), atil hf ε v σ h (hQ h) (hR h),
    atil hf ε v σ h (hP h) (hS h), atil hf ε v σ h (hQ h) (hS h), atil hf ε v σ h (hR h) (hS h)]

/-- **The corners are the hinge midpoint plus `ε` times the relative positions.** -/
theorem cornerPt_eq (σ h : Fin 6) (k : Fin 7) (hc : Cond (dirsN k) σ h) (zv : Fin 3 → ℤ) (a : Fin 4) :
    cornerPt n (fun i => zv i - koff (hP h) (perms σ i)) σ a =
      (fun i => ((zv i : ℤ) + dirs k i / 2) / n) + (1 / (n : ℝ)) • kposv σ h a := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  have hd : ∀ i, dirs k i = kv (hQ h) (perms σ i) - kv (hP h) (perms σ i) := fun i => by
    have := (cond_iff_real (dirsN k) σ h).1 hc
    rcases (by fin_cases i <;> simp : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl
    · rw [← dirsN_cast]; exact this.1.symm
    · rw [← dirsN_cast]; exact this.2.1.symm
    · rw [← dirsN_cast]; exact this.2.2.symm
  funext i
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, cornerPt, kposv, kpos, hd i]
  have h1 : ((koff a (perms σ i) : ℕ) : ℝ) = kv a (perms σ i) := koff_cast a _
  have h2 : ((koff (hP h) (perms σ i) : ℕ) : ℝ) = kv (hP h) (perms σ i) := koff_cast _ _
  push_cast
  rw [h1, h2]
  field_simp
  ring


theorem muE_scaled (hf : (Fin 3 → ℝ) → Matrix (Fin 3) (Fin 3) ℝ) (v ka kb : Fin 3 → ℝ) (ε : ℝ) :
    muE hf (v + ε • ka) (v + ε • kb) = ε ^ 2 * ∫ t in (0 : ℝ)..1, (kb - ka) ⬝ᵥ
      (hf (v + ε • (ka + t • (kb - ka))) *ᵥ (kb - ka)) := by
  unfold muE
  rw [← intervalIntegral.integral_const_mul]
  congr 1
  funext t
  have e1 : (v + ε • kb) - (v + ε • ka) = ε • (kb - ka) := by
    funext i; simp; ring
  have e2 : v + ε • ka + t • (ε • (kb - ka)) = v + ε • (ka + t • (kb - ka)) := by
    funext i; simp; ring
  rw [e1, e2, Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul, smul_eq_mul]
  ring

theorem muVec_eq_atilV (hn : 3 ≤ n) (hf : (Fin 3 → ℝ) → Matrix (Fin 3) (Fin 3) ℝ) (σ h : Fin 6) (k : Fin 7)
    (hc : Cond (dirsN k) σ h) (zv : Fin 3 → ℤ) :
    muVec n hf (fun i => zv i - koff (hP h) (perms σ i)) σ h =
      atilV hf (1 / (n : ℝ)) (fun i => ((zv i : ℤ) + dirs k i / 2) / n) σ h := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  have hent : ∀ a b : Fin 4, (n : ℝ) ^ 2 * muE hf (cornerPt n (fun i => zv i - koff (hP h) (perms σ i)) σ a)
      (cornerPt n (fun i => zv i - koff (hP h) (perms σ i)) σ b) =
      atil hf (1 / (n : ℝ)) (fun i => ((zv i : ℤ) + dirs k i / 2) / n) σ h a b := by
    intro a b
    rw [cornerPt_eq n σ h k hc zv a, cornerPt_eq n σ h k hc zv b, muE_scaled, atil, ← mul_assoc]
    have : (n : ℝ) ^ 2 * (1 / (n : ℝ)) ^ 2 = 1 := by field_simp
    rw [this, one_mul]
  funext i
  fin_cases i <;> simp [muVec, atilV, hent]


/-- The Euclidean length `√(Σ (dirs k)ᵢ²)` of the edge direction of the class `k`. -/
noncomputable def wn (k : Fin 7) : ℝ := √(∑ i, dirs k i ^ 2)

/-- The unit-scale degree of freedom of the hinge edge of class `k` at the midpoint `v`. -/
noncomputable def hAt (hf : (Fin 3 → ℝ) → Matrix (Fin 3) (Fin 3) ℝ) (ε : ℝ) (v : Fin 3 → ℝ) (k : Fin 7) : ℝ :=
  ∫ t in (0 : ℝ)..1, dirs k ⬝ᵥ (hf (v + ε • ((t - 1 / 2) • dirs k)) *ᵥ dirs k)

theorem hdist_edgeOf (hn : 2 ≤ n) (z : TV n) (k : Fin 7) :
    (hdist n z (z + wv n (dirsN k)) : ℝ) = ∑ i, dirs k i ^ 2 := by
  have : hdist n z (z + wv n (dirsN k)) = (univ.filter fun i : Fin 3 => dirsN k i ≠ 0).card := by
    unfold hdist
    congr 1
    refine Finset.filter_congr fun i _ => ?_
    simp only [Pi.add_apply, wv]
    constructor
    · intro h h0
      apply h
      rw [h0]; simp
    · intro h hz
      apply h
      have : ((dirsN k i : ℕ) : ZMod n) = ((0 : ℕ) : ZMod n) := by simpa using hz
      exact natCast_inj01 n (dirsN_le k i) (by norm_num) hn this
  rw [this, card_filter]
  push_cast
  refine sum_congr rfl fun i _ => ?_
  rw [← dirsN_cast]
  have := dirsN_le k i
  interval_cases hk : dirsN k i <;> simp

theorem len0_edgeOf (hn : 3 ≤ n) (z : TV n) (k : Fin 7) : len0 n (edgeOf n z k) = wn k := by
  have hw1 := dirsN_le k
  have hw0 := dirsN_ne k
  have hne : z ≠ z + wv n (dirsN k) := fun h => wv_ne_zero n (by omega) hw1 hw0 (by simpa using h.symm)
  unfold edgeOf wn
  rw [len0_pair n hne, hdist_edgeOf n (by omega)]


theorem hbase_wn (k : Fin 7) (σ h : Fin 6) (hc : Cond (dirsN k) σ h) : √(hbase h 0) = wn k := by
  have hd : ∀ i, dirs k i = kv (hQ h) (perms σ i) - kv (hP h) (perms σ i) := fun i => by
    have := (cond_iff_real (dirsN k) σ h).1 hc
    rcases (by fin_cases i <;> simp : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl
    · rw [← dirsN_cast]; exact this.1.symm
    · rw [← dirsN_cast]; exact this.2.1.symm
    · rw [← dirsN_cast]; exact this.2.2.symm
  have h0 : hbase h 0 = sqd (kv (hP h)) (kv (hQ h)) := by rw [hbase_eq h]; rfl
  have h1 : ∑ i, dirs k i ^ 2 = sqd (fun i => kv (hP h) (perms σ i)) (fun i => kv (hQ h) (perms σ i)) := by
    simp only [Fin.sum_univ_three, hd, sqd]; ring
  rw [h0, wn, h1, sqd_perm]


open Classical in
/-- **The coefficient `Q_n (h)` as a lattice sum over the hinges.** -/
theorem Qn_lattice (hn : 3 ≤ n) (hf : (Fin 3 → ℝ) → Matrix (Fin 3) (Fin 3) ℝ)
    (hper : ∀ (p : Fin 3 → ℝ) (e : Fin 3 → ℤ), hf (p + fun i => (e i : ℝ)) = hf p) :
    Qn n (by omega) hf = ∑ k : Fin 7, ∑ z : Fin 3 → Fin n,
      (1 / (n : ℝ)) * (hAt hf (1 / (n : ℝ)) (hingeMid n k z) k / (2 * wn k)) *
        (-(∑ σ : Fin 6, ∑ h : Fin 6, if InClass (dirs k) σ h then
          dth h (atilV hf (1 / (n : ℝ)) (hingeMid n k z) σ h) else 0) / wn k) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  rw [Qn_eq n hn hf hper]
  refine sum_congr rfl fun k _ => ?_
  let E : (Fin 3 → Fin n) ≃ TV n := Equiv.piCongrRight fun _ => (valEquiv n).symm
  rw [← Equiv.sum_comp E]
  refine sum_congr rfl fun z' _ => ?_
  have hval : ∀ i, (E z' i).val = z' i := fun i => by
    simp [E, valEquiv, ZMod.val_natCast, Nat.mod_eq_of_lt (z' i).2]
  have hw1 := dirsN_le k
  have hw0 := dirsN_ne k
  have hwn : 0 < wn k := by
    have : 0 < ∑ i, dirs k i ^ 2 := by
      obtain ⟨i, hi⟩ := hw0
      have : (0 : ℝ) < dirs k i ^ 2 := by
        rw [← dirsN_cast]; have : (0 : ℝ) < dirsN k i := by exact_mod_cast Nat.pos_of_ne_zero hi
        positivity
      exact lt_of_lt_of_le this (Finset.single_le_sum (f := fun i => dirs k i ^ 2) (fun j _ => by positivity)
        (Finset.mem_univ i))
    exact Real.sqrt_pos.2 this
  -- the hinge edge
  have hmu : lenD n (muE hf) (edgeOf n (E z') k) = (1 / (n : ℝ)) ^ 2 *
      hAt hf (1 / (n : ℝ)) (hingeMid n k z') k := by
    rw [lenD_edgeOf n hn]
    have hx : liftPt n (E z') = hingeMid n k z' + (1 / (n : ℝ)) • (-(1 / 2 : ℝ) • dirs k) := by
      funext i
      simp [liftPt, hval, hingeMid]; field_simp; ring
    have hy : liftPt n (E z') + (fun i => ((dirsN k i : ℕ) : ℝ) / n) =
        hingeMid n k z' + (1 / (n : ℝ)) • ((1 / 2 : ℝ) • dirs k) := by
      funext i
      simp [liftPt, hval, hingeMid, dirsN_cast]; field_simp; ring
    rw [hy, hx, muE_scaled, hAt]
    congr 1
    congr 1
    funext t
    have e1 : (1 / 2 : ℝ) • dirs k - (-(1 / 2 : ℝ) • dirs k) = dirs k := by funext i; simp; ring
    have e2 : -(1 / 2 : ℝ) • dirs k + t • dirs k = (t - 1 / 2) • dirs k := by funext i; simp; ring
    rw [e1, e2]
  have hlen : lenMesh n (edgeOf n (E z') k) = wn k / n := by
    rw [lenMesh, len0_edgeOf n hn]
  have hin : ∑ σ : Fin 6, ∑ h : Fin 6, (if Cond (dirsN k) σ h then
      dth h (muVec n hf (fun i => (((E z' i).val : ℕ) : ℤ) - koff (hP h) (perms σ i)) σ h) /
        √(hbase h 0) else 0) =
      (∑ σ : Fin 6, ∑ h : Fin 6, if InClass (dirs k) σ h then
        dth h (atilV hf (1 / (n : ℝ)) (hingeMid n k z') σ h) else 0) / wn k := by
    rw [Finset.sum_div]
    refine sum_congr rfl fun σ _ => ?_
    rw [Finset.sum_div]
    refine sum_congr rfl fun h _ => ?_
    by_cases hc : Cond (dirsN k) σ h
    · have hc' : InClass (dirs k) σ h := (cond_iff_inClass k σ h).1 hc
      simp only [hc, hc', ite_true]
      rw [hbase_wn k σ h hc]
      congr 2
      have hv : hingeMid n k z' = fun i => ((((E z' i).val : ℕ) : ℤ) + dirs k i / 2) / n := by
        funext i; simp [hingeMid, hval]
      rw [hv]
      exact muVec_eq_atilV n hn hf σ h k hc (fun i => (((E z' i).val : ℕ) : ℤ))
    · have hc' : ¬ InClass (dirs k) σ h := fun h' => hc ((cond_iff_inClass k σ h).2 h')
      simp [hc, hc']
  rw [hin, hmu, hlen]
  field_simp

end Lightlike.Regge.Linear3
