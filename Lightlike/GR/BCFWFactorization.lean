import Lightlike.GR.ColourOrdered

/-!
# On-shell recursion: complex shifts and the residue formula

* **The BCFW shift** (Elvang-Huang (3.8)): `|î] = |i] + z|j]`, `|ĵ⟩ = |j⟩ − z|i⟩` (`bcfwSquare`,
  `bcfwAngle`). It keeps every momentum null ((B), `mdot_nullMom_self`), preserves momentum conservation
  ((A), `conserved_bcfw`), and shifts a channel momentum `P_I` with `i ∈ I`, `j ∉ I` by `z r`,
  `r = −|j]⟨i|` null, so that `P̂_I² = P_I² + 2z P_I · r` is linear in `z` ((C), (3.2), `momSum_bcfw`,
  `mdot_momSum_bcfw`), vanishing at `z_I = −P_I²/(2 P_I · r)` ((3.3), `mdot_momSum_bcfw_eq`).
* **The residue formula** (Elvang-Huang (3.4) with `B_n = 0`): a rational function `Â = P/Q` with simple
  poles at the distinct points `z_I` (`Q = Π (z − z_I)`) and vanishing at infinity (`deg P < deg Q`) is
  the sum of its pole parts (`eval_div_nodal`), its residues are `lim (z − z_I) Â(z)`
  (`tendsto_residue`), it tends to `0` at infinity (`tendsto_cocompact_zero`), and for `z_I ≠ 0`,
  `Â(0) = −Σ_I Res_{z = z_I} Â(z)/z` (`eval_zero_eq_neg_sum_residues`). With the factorization of the
  residues (3.5) as a hypothesis this is the recursion (3.7) (`recursion_of_factorization`).
* **The MHV sector, proved** (Elvang-Huang Exercises 3.2–3.3, p. 37, and (3.13)–(3.21), pp. 37–39): under the
  `[1, 2⟩` shift the Parke-Taylor amplitude `Â(z)` (`ptShift`, gluons `1, 2` are `0, 1` here) is
  `⟨12⟩⁴/(⟨12⟩⟨2̂3⟩⟨34⟩ ⋯ ⟨n1⟩)` with only `⟨2̂3⟩ = ⟨23⟩ − z⟨13⟩` shifted (`ptShift_eq`), so it is `P/Q` with
  a single simple pole and `deg P < deg Q` (`ptShift_rational`, `degree_ptShift_numerator`); the pole is where
  the channel momentum `P̂₂₃ = p̂₂ + p₃` goes on shell, `P̂₂₃² = ⟨2̂3⟩[23]` (`ptShift_channel`), with
  `|2̂⟩ ∝ |3⟩` there (`ptShift_onshell`); and the residue of `Â(z)/z` factorizes as (3.5),
  `−Â_{n−1}(1̂⁻, P̂⁻, 4⁺, …, n⁺) Â₃(−P̂⁺, 2̂⁻, 3⁺)/P₂₃²`, for every choice of the spinors of the on-shell `P̂`
  (`ptShift_factorization`, with the anti-MHV three-point amplitude `antiMHV3`, (2.78)). Colour-ordered trees
  of other helicity sectors are not defined in the library, so for them (3.5) stays a hypothesis.

## References

* H. Elvang, Y. Huang, *Scattering Amplitudes*, arXiv:1308.1697, §3.1, pp. 34–36: the shifts (3.1), the
  properties (A)–(C), (3.2)–(3.3), Cauchy's theorem (3.4), the factorization of residues (3.5), the
  large-`z` condition (3.6) and the recursion (3.7); §3.2, p. 36, the BCFW shift (3.8); pp. 37–39, Exercises
  3.2–3.3 and the MHV computation (3.13)–(3.21); the anti-MHV three-point amplitude (2.78), p. 23.
-/

open Matrix Polynomial

noncomputable section

namespace Lightlike.SpinorHelicity

/-! ## The BCFW shift -/

/-- The square spinors after the `[i, j⟩` shift: `|î] = |i] + z|j]`. -/
def bcfwSquare {n : ℕ} (l : Fin n → Fin 2 → ℂ) (i j : Fin n) (z : ℂ) : Fin n → Fin 2 → ℂ :=
  Function.update l i (l i + z • l j)

/-- The angle spinors after the `[i, j⟩` shift: `|ĵ⟩ = |j⟩ − z|i⟩`. -/
def bcfwAngle {n : ℕ} (lt : Fin n → Fin 2 → ℂ) (i j : Fin n) (z : ℂ) : Fin n → Fin 2 → ℂ :=
  Function.update lt j (lt j - z • lt i)

/-- **(A) The shift preserves momentum conservation.** -/
theorem conserved_bcfw {n : ℕ} {l lt : Fin n → Fin 2 → ℂ} (h : Conserved l lt) {i j : Fin n}
    (hij : i ≠ j) (z : ℂ) : Conserved (bcfwSquare l i j z) (bcfwAngle lt i j z) := by
  intro a b
  have hsplit : ∀ F : Fin n → ℂ, ∑ k, F k = F i + F j + ∑ k ∈ (Finset.univ.erase i).erase j, F k := by
    intro F
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i),
      ← Finset.add_sum_erase _ _ (Finset.mem_erase.2 ⟨hij.symm, Finset.mem_univ j⟩)]
    ring
  have hrest : ∀ k ∈ (Finset.univ.erase i).erase j,
      bcfwSquare l i j z k a * bcfwAngle lt i j z k b = l k a * lt k b := by
    intro k hk
    have hkj : k ≠ j := Finset.ne_of_mem_erase hk
    have hki : k ≠ i := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hk)
    simp [bcfwSquare, bcfwAngle, Function.update_of_ne hki, Function.update_of_ne hkj]
  rw [hsplit, Finset.sum_congr rfl hrest]
  have h0 := h a b
  rw [hsplit] at h0
  simp only [bcfwSquare, bcfwAngle, Function.update_self, Function.update_of_ne hij,
    Function.update_of_ne hij.symm, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  linear_combination h0

lemma nullMom_add_smul_left (a b c : Fin 2 → ℂ) (z : ℂ) :
    nullMom (a + z • b) c = nullMom a c + z • nullMom b c := by
  funext μ
  fin_cases μ <;> simp [nullMom, momOf, vecMulVec_apply] <;> ring

lemma nullMom_sub_smul_right (a b c : Fin 2 → ℂ) (z : ℂ) :
    nullMom a (b - z • c) = nullMom a b - z • nullMom a c := by
  funext μ
  fin_cases μ <;> simp [nullMom, momOf, vecMulVec_apply] <;> ring

/-- The channel momentum `P_I = Σ_{k ∈ I} p_k`. -/
def momSum {n : ℕ} (l lt : Fin n → Fin 2 → ℂ) (I : Finset (Fin n)) : Fin 4 → ℂ :=
  ∑ k ∈ I, nullMom (l k) (lt k)

/-- **(C) The shifted channel momentum** for `i ∈ I`, `j ∉ I`: `P̂_I = P_I + z r`, `r = −|j]⟨i|`. -/
theorem momSum_bcfw {n : ℕ} (l lt : Fin n → Fin 2 → ℂ) {i j : Fin n} (hij : i ≠ j)
    {I : Finset (Fin n)} (hi : i ∈ I) (hj : j ∉ I) (z : ℂ) :
    momSum (bcfwSquare l i j z) (bcfwAngle lt i j z) I =
      momSum l lt I + z • nullMom (l j) (lt i) := by
  unfold momSum
  rw [← Finset.add_sum_erase _ _ hi, ← Finset.add_sum_erase _ _ hi]
  have hrest : ∀ k ∈ I.erase i, nullMom (bcfwSquare l i j z k) (bcfwAngle lt i j z k) =
      nullMom (l k) (lt k) := by
    intro k hk
    have hki : k ≠ i := Finset.ne_of_mem_erase hk
    have hkj : k ≠ j := fun e => hj (e ▸ Finset.mem_of_mem_erase hk)
    simp [bcfwSquare, bcfwAngle, Function.update_of_ne hki, Function.update_of_ne hkj]
  rw [Finset.sum_congr rfl hrest]
  simp only [bcfwSquare, bcfwAngle, Function.update_self, Function.update_of_ne hij,
    nullMom_add_smul_left]
  abel

lemma mdot_add_smul (p r : Fin 4 → ℂ) (z : ℂ) :
    mdot (p + z • r) (p + z • r) = mdot p p + 2 * z * mdot p r + z ^ 2 * mdot r r := by
  simp only [mdot, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring

/-- **(C), (3.2): `P̂_I²` is linear in `z`**: `P̂_I² = P_I² + 2z P_I · r`. -/
theorem mdot_momSum_bcfw {n : ℕ} (l lt : Fin n → Fin 2 → ℂ) {i j : Fin n} (hij : i ≠ j)
    {I : Finset (Fin n)} (hi : i ∈ I) (hj : j ∉ I) (z : ℂ) :
    mdot (momSum (bcfwSquare l i j z) (bcfwAngle lt i j z) I)
        (momSum (bcfwSquare l i j z) (bcfwAngle lt i j z) I) =
      mdot (momSum l lt I) (momSum l lt I) +
        2 * z * mdot (momSum l lt I) (nullMom (l j) (lt i)) := by
  rw [momSum_bcfw l lt hij hi hj, mdot_add_smul, mdot_nullMom_self]
  ring

/-- **(3.3)**: `P̂_I² = −(P_I²/z_I)(z − z_I)` with `z_I = −P_I²/(2 P_I · r)`, if `P_I² ≠ 0 ≠ P_I · r`. -/
theorem mdot_momSum_bcfw_eq {n : ℕ} (l lt : Fin n → Fin 2 → ℂ) {i j : Fin n} (hij : i ≠ j)
    {I : Finset (Fin n)} (hi : i ∈ I) (hj : j ∉ I)
    (hP : mdot (momSum l lt I) (momSum l lt I) ≠ 0)
    (hPr : mdot (momSum l lt I) (nullMom (l j) (lt i)) ≠ 0) (z : ℂ) :
    let zI := -mdot (momSum l lt I) (momSum l lt I) / (2 * mdot (momSum l lt I) (nullMom (l j) (lt i)))
    mdot (momSum (bcfwSquare l i j z) (bcfwAngle lt i j z) I)
        (momSum (bcfwSquare l i j z) (bcfwAngle lt i j z) I) =
      -(mdot (momSum l lt I) (momSum l lt I) / zI) * (z - zI) := by
  intro zI
  rw [mdot_momSum_bcfw l lt hij hi hj]
  simp only [zI]
  field_simp
  ring

/-! ## The residue formula -/

section Residues

variable {ι : Type*} [DecidableEq ι] (s : Finset ι) (v : ι → ℂ)

/-- The residue of `P / Π (z − z_I)` at the simple pole `z_I`: `P(z_I) / Π_{J ≠ I} (z_I − z_J)`. -/
def residue (P : ℂ[X]) (i : ι) : ℂ := Lagrange.nodalWeight s v i * P.eval (v i)

/-- **Partial fractions**: for `deg P < #poles`, `P/Q = Σ_I Res_I / (z − z_I)` away from the poles. -/
theorem eval_div_nodal {P : ℂ[X]} (hv : Set.InjOn v s) (hdeg : P.degree < s.card) {x : ℂ}
    (hx : ∀ i ∈ s, x ≠ v i) :
    P.eval x / (Lagrange.nodal s v).eval x = ∑ i ∈ s, residue s v P i / (x - v i) := by
  have hQ : (Lagrange.nodal s v).eval x ≠ 0 := Lagrange.eval_nodal_not_at_node hx
  conv_lhs => rw [Lagrange.eq_interpolate hv hdeg]
  rw [Lagrange.eval_interpolate_not_at_node _ hx, mul_div_cancel_left₀ _ hQ]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [residue]
  ring

/-- **The residue is the limit `(z − z_I) Â(z)`.** -/
theorem tendsto_residue {P : ℂ[X]} (hv : Set.InjOn v s) {i : ι}
    (hi : i ∈ s) :
    Filter.Tendsto (fun x => (x - v i) * (P.eval x / (Lagrange.nodal s v).eval x))
      (nhdsWithin (v i) {v i}ᶜ) (nhds (residue s v P i)) := by
  -- `(x − z_I) Â(x) = P(x) / Π_{J ≠ I} (x − z_J)`, continuous at `z_I`
  have hQ : ∀ x, x ≠ v i → (x - v i) * (P.eval x / (Lagrange.nodal s v).eval x) =
      P.eval x / (Lagrange.nodal (s.erase i) v).eval x := by
    intro x hx
    rw [Lagrange.eval_nodal, Lagrange.eval_nodal, ← Finset.mul_prod_erase _ _ hi]
    have : x - v i ≠ 0 := sub_ne_zero.2 hx
    field_simp
  have hcont : ContinuousAt (fun x => P.eval x / (Lagrange.nodal (s.erase i) v).eval x) (v i) := by
    have hne : (Lagrange.nodal (s.erase i) v).eval (v i) ≠ 0 := by
      rw [Lagrange.eval_nodal]
      refine Finset.prod_ne_zero_iff.2 fun j hj => sub_ne_zero.2 fun e => ?_
      exact Finset.ne_of_mem_erase hj (hv (Finset.mem_of_mem_erase hj) hi e.symm)
    exact (P.continuous.continuousAt).div (Polynomial.continuous _).continuousAt hne
  have hval : P.eval (v i) / (Lagrange.nodal (s.erase i) v).eval (v i) = residue s v P i := by
    rw [residue, Lagrange.nodalWeight_eq_eval_nodal_erase_inv, div_eq_mul_inv, mul_comm]
  rw [← hval]
  exact (hcont.tendsto.mono_left nhdsWithin_le_nhds).congr' (Filter.eventually_of_mem
    self_mem_nhdsWithin fun x hx => (hQ x hx).symm)

/-- **`Â` vanishes at infinity** (the pole at `z = ∞` of (3.4) is absent, `B_n = 0`, as in (3.6)). -/
theorem tendsto_cocompact_zero {P : ℂ[X]} (hv : Set.InjOn v s) (hdeg : P.degree < s.card) :
    Filter.Tendsto (fun x => P.eval x / (Lagrange.nodal s v).eval x) (Filter.cocompact ℂ)
      (nhds 0) := by
  have hev : ∀ᶠ x in Filter.cocompact ℂ,
      ∑ i ∈ s, residue s v P i / (x - v i) = P.eval x / (Lagrange.nodal s v).eval x := by
    have hfin : ((s.image v : Finset ℂ) : Set ℂ)ᶜ ∈ Filter.cocompact ℂ :=
      (s.image v).finite_toSet.isCompact.compl_mem_cocompact
    filter_upwards [hfin] with x hx
    refine (eval_div_nodal s v hv hdeg fun i hi e => hx ?_).symm
    rw [e]; exact Finset.mem_coe.2 (Finset.mem_image_of_mem v hi)
  have hterm : ∀ i ∈ s, Filter.Tendsto (fun x => residue s v P i / (x - v i))
      (Filter.cocompact ℂ) (nhds 0) := by
    intro i _
    have hsub : Filter.Tendsto (fun x : ℂ => x - v i) (Filter.cocompact ℂ) (Filter.cocompact ℂ) :=
      (Homeomorph.subRight (v i)).isClosedEmbedding.tendsto_cocompact
    have hinv : Filter.Tendsto (fun x : ℂ => (x - v i)⁻¹) (Filter.cocompact ℂ) (nhds 0) := by
      rw [← Metric.cobounded_eq_cocompact] at hsub ⊢
      exact Filter.tendsto_inv₀_cobounded.comp hsub
    simpa [div_eq_mul_inv] using hinv.const_mul (residue s v P i)
  have := tendsto_finsetSum s hterm
  rw [Finset.sum_const_zero] at this
  exact this.congr' hev

/-- **The residue formula** (Elvang-Huang (3.4) with `B_n = 0`): for poles `z_I ≠ 0`,
`Â(0) = −Σ_I Res_{z = z_I} Â(z)/z = −Σ_I Res_I / z_I`. -/
theorem eval_zero_eq_neg_sum_residues {P : ℂ[X]} (hv : Set.InjOn v s) (hdeg : P.degree < s.card)
    (h0 : ∀ i ∈ s, v i ≠ 0) :
    P.eval 0 / (Lagrange.nodal s v).eval 0 = -∑ i ∈ s, residue s v P i / v i := by
  rw [eval_div_nodal s v hv hdeg fun i hi e => h0 i hi e.symm, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [zero_sub, div_neg]

/-- **The recursion** (Elvang-Huang (3.7)): if the residues factorize as in (3.5),
`Res_{z = z_I} Â(z)/z = −Â_L(z_I) Â_R(z_I) / P_I²`, then `A = Â(0) = Σ_I Â_L(z_I) Â_R(z_I) / P_I²`. -/
theorem recursion_of_factorization {P : ℂ[X]} (hv : Set.InjOn v s) (hdeg : P.degree < s.card)
    (h0 : ∀ i ∈ s, v i ≠ 0) (AL AR Psq : ι → ℂ)
    (hfac : ∀ i ∈ s, residue s v P i / v i = -(AL i * AR i / Psq i)) :
    P.eval 0 / (Lagrange.nodal s v).eval 0 = ∑ i ∈ s, AL i * AR i / Psq i := by
  rw [eval_zero_eq_neg_sum_residues s v hv hdeg h0, Finset.sum_congr rfl hfac,
    Finset.sum_neg_distrib, neg_neg]

end Residues

/-! ## The MHV sector -/

lemma finRotate_small {m : ℕ} (k : Fin (m + 4)) (hk : (k : ℕ) < 3) :
    ((finRotate (m + 4) k : Fin (m + 4)) : ℕ) = k + 1 := by
  rw [coe_finRotate]
  split_ifs with h
  · have := congrArg Fin.val h; simp [Fin.val_last] at this; omega
  · rfl

/-- Splitting the cyclic denominator of `m + 4` gluons at the first three brackets. -/
lemma cycDen_four {m : ℕ} (s : Fin (m + 4) → Fin 2 → ℂ) :
    cycDen s = angleBr (s 0) (s 1) * angleBr (s 1) (s 2) * angleBr (s 2) (s 3) *
      ∏ k : Fin (m + 1), angleBr (s k.succ.succ.succ) (s (finRotate (m + 4) k.succ.succ.succ)) := by
  unfold cycDen
  rw [Fin.prod_univ_succ, Fin.prod_univ_succ, Fin.prod_univ_succ]
  have h1 : 1 % (m + 4) = 1 := Nat.mod_eq_of_lt (by omega)
  have h2 : 2 % (m + 4) = 2 := Nat.mod_eq_of_lt (by omega)
  have h3 : 3 % (m + 4) = 3 := Nat.mod_eq_of_lt (by omega)
  have r0 : finRotate (m + 4) 0 = 1 := Fin.ext (by rw [finRotate_small 0 (by simp)]; simp [h1])
  have r1 : finRotate (m + 4) 1 = 2 := Fin.ext (by rw [finRotate_small 1 (by simp [h1])]; simp [h1, h2])
  have r2 : finRotate (m + 4) 2 = 3 := Fin.ext (by rw [finRotate_small 2 (by simp [h2])]; simp [h2, h3])
  simp only [Fin.succ_zero_eq_one, Fin.succ_one_eq_two, r0, r1, r2]
  ring_nf

/-- Splitting the cyclic denominator of `m + 3` gluons at the first two brackets. -/
lemma cycDen_three {m : ℕ} (s : Fin (m + 3) → Fin 2 → ℂ) :
    cycDen s = angleBr (s 0) (s 1) * angleBr (s 1) (s 2) *
      ∏ k : Fin (m + 1), angleBr (s k.succ.succ) (s (finRotate (m + 3) k.succ.succ)) := by
  unfold cycDen
  rw [Fin.prod_univ_succ, Fin.prod_univ_succ]
  have h1 : 1 % (m + 3) = 1 := Nat.mod_eq_of_lt (by omega)
  have h2 : 2 % (m + 3) = 2 := Nat.mod_eq_of_lt (by omega)
  have r0 : finRotate (m + 3) 0 = 1 := by
    apply Fin.ext; rw [coe_finRotate]; split_ifs with h
    · have := congrArg Fin.val h; simp [Fin.val_last] at this
    · simp [h1]
  have r1 : finRotate (m + 3) 1 = 2 := by
    apply Fin.ext; rw [coe_finRotate]; split_ifs with h
    · have := congrArg Fin.val h; simp [Fin.val_last, h1] at this
    · simp [h1, h2]
  simp only [Fin.succ_zero_eq_one, r0, r1]
  ring

/-- The rotation commutes with the shift of the last `m + 1` indices. -/
lemma finRotate_succ_succ_succ {m : ℕ} (k : Fin (m + 1)) (s : Fin (m + 4) → Fin 2 → ℂ)
    (b : Fin 2 → ℂ) :
    (Fin.cons (s 0) (Fin.cons b (fun k : Fin (m + 1) => s k.succ.succ.succ)) :
      Fin (m + 3) → Fin 2 → ℂ) (finRotate (m + 3) k.succ.succ) =
      s (finRotate (m + 4) k.succ.succ.succ) := by
  by_cases hk : k = Fin.last m
  · subst hk
    have h1 : finRotate (m + 3) (Fin.last m).succ.succ = 0 := by
      rw [show (Fin.last m).succ.succ = Fin.last (m + 2) from by ext; simp, finRotate_last]
    have h2 : finRotate (m + 4) (Fin.last m).succ.succ.succ = 0 := by
      rw [show (Fin.last m).succ.succ.succ = Fin.last (m + 3) from by ext; simp, finRotate_last]
    rw [h1, h2]; rfl
  · have hk' : (k : ℕ) < m := by
      have := k.isLt; rcases Nat.lt_or_ge (k : ℕ) m with h | h
      · exact h
      · exact absurd (Fin.ext (by simp [Fin.val_last]; omega)) hk
    set k' : Fin (m + 1) := ⟨k + 1, by omega⟩
    have h1 : finRotate (m + 3) k.succ.succ = k'.succ.succ := by
      apply Fin.ext; rw [coe_finRotate]; split_ifs with h
      · have := congrArg Fin.val h; simp [Fin.val_last] at this; omega
      · simp [k']
    have h2 : finRotate (m + 4) k.succ.succ.succ = k'.succ.succ.succ := by
      apply Fin.ext; rw [coe_finRotate]; split_ifs with h
      · have := congrArg Fin.val h; simp [Fin.val_last] at this; omega
      · simp [k']
    rw [h1, h2]; rfl

lemma finRotate_succ_succ_succ_ne_one {m : ℕ} (k : Fin (m + 1)) :
    finRotate (m + 4) k.succ.succ.succ ≠ 1 := by
  intro h
  have := congrArg Fin.val h
  rw [coe_finRotate] at this
  split_ifs at this <;> simp at this

lemma angleBr_smul_right' (t : ℂ) (a b : Fin 2 → ℂ) : angleBr a (t • b) = t * angleBr a b := by
  simp only [angleBr_eq, Pi.smul_apply, smul_eq_mul]; ring

lemma angleBr_smul_left' (t : ℂ) (a b : Fin 2 → ℂ) : angleBr (t • a) b = t * angleBr a b := by
  simp only [angleBr_eq, Pi.smul_apply, smul_eq_mul]; ring

/-! ## The MHV sector: the shifted Parke-Taylor amplitude (Elvang-Huang Exercises 3.2–3.3, (3.13)–(3.21)) -/

section MHV

variable {m : ℕ} (l lt : Fin (m + 4) → Fin 2 → ℂ)

/-- The Parke-Taylor amplitude `A_n[1⁻ 2⁻ 3⁺ ⋯ n⁺]` under the `[1, 2⟩` shift (gluons `0, 1` here):
`Â(z)`. -/
def ptShift (z : ℂ) : ℂ :=
  parkeTaylor (bcfwAngle lt 0 1 z 0) (bcfwAngle lt 0 1 z 1) (bcfwAngle lt 0 1 z)

/-- The brackets `⟨34⟩ ⋯ ⟨n1⟩` of the cyclic denominator after `⟨23⟩` (gluons `3, …, n−1, 0` here). -/
def restProd : ℂ :=
  ∏ k : Fin (m + 1), angleBr (lt k.succ.succ.succ) (lt (finRotate (m + 4) k.succ.succ.succ))

/-- **The shifted Parke-Taylor amplitude**: only `⟨2̂3⟩ = ⟨23⟩ − z⟨13⟩` depends on `z` (gluons `1, 2, 0`
here: `⟨1̂2⟩ = ⟨12⟩ − z⟨02⟩`). -/
theorem ptShift_eq (z : ℂ) :
    ptShift lt z = angleBr (lt 0) (lt 1) ^ 4 / (angleBr (lt 0) (lt 1) *
      (angleBr (lt 1) (lt 2) - z * angleBr (lt 0) (lt 2)) * angleBr (lt 2) (lt 3) * restProd lt) := by
  have e : ∀ k, k ≠ 1 → bcfwAngle lt 0 1 z k = lt k := fun k hk => Function.update_of_ne hk _ _
  have e1 : bcfwAngle lt 0 1 z 1 = lt 1 - z • lt 0 := Function.update_self _ _ _
  have v1 : ((1 : Fin (m + 4)) : ℕ) = 1 := by simp
  have v2 : ((2 : Fin (m + 4)) : ℕ) = 2 := by simp
  have v3 : ((3 : Fin (m + 4)) : ℕ) = 3 := by simp
  have n0 : (0 : Fin (m + 4)) ≠ 1 := zero_ne_one
  have n2 : (2 : Fin (m + 4)) ≠ 1 := fun h => by have := congrArg Fin.val h; omega
  have n3 : (3 : Fin (m + 4)) ≠ 1 := fun h => by have := congrArg Fin.val h; omega
  have nk : ∀ k : Fin (m + 1), (k.succ.succ.succ : Fin (m + 4)) ≠ 1 := fun k h => by
    have := congrArg Fin.val h; simp at this
  have hp : ∏ k : Fin (m + 1), angleBr (bcfwAngle lt 0 1 z k.succ.succ.succ)
      (bcfwAngle lt 0 1 z (finRotate (m + 4) k.succ.succ.succ)) = restProd lt :=
    Finset.prod_congr rfl fun k _ => by rw [e _ (nk k), e _ (finRotate_succ_succ_succ_ne_one k)]
  unfold ptShift parkeTaylor
  rw [cycDen_four, hp, e1, e 0 n0, e 2 n2, e 3 n3]
  have h01 : angleBr (lt 0) (lt 1 - z • lt 0) = angleBr (lt 0) (lt 1) := by
    simp only [angleBr_eq, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]; ring
  have h12 : angleBr (lt 1 - z • lt 0) (lt 2) = angleBr (lt 1) (lt 2) - z * angleBr (lt 0) (lt 2) := by
    simp only [angleBr_eq, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]; ring
  rw [h01, h12]

/-- **`Â(z)` is `P/Q` with a single simple pole** at `z* = ⟨12⟩/⟨02⟩` and `deg P < deg Q`
(Elvang-Huang Exercises 3.2–3.3: it falls off as `1/z`). -/
theorem ptShift_rational (h01 : angleBr (lt 0) (lt 1) ≠ 0) (h02 : angleBr (lt 0) (lt 2) ≠ 0)
    (h23 : angleBr (lt 2) (lt 3) ≠ 0) (hR : restProd lt ≠ 0) {z : ℂ}
    (hz : z ≠ angleBr (lt 1) (lt 2) / angleBr (lt 0) (lt 2)) :
    ptShift lt z = (Polynomial.C (-(angleBr (lt 0) (lt 1) ^ 3 /
        (angleBr (lt 0) (lt 2) * angleBr (lt 2) (lt 3) * restProd lt)))).eval z /
      (Lagrange.nodal (Finset.univ : Finset Unit)
        (fun _ => angleBr (lt 1) (lt 2) / angleBr (lt 0) (lt 2))).eval z := by
  have hd : angleBr (lt 1) (lt 2) - z * angleBr (lt 0) (lt 2) ≠ 0 := by
    intro h; apply hz; field_simp; linear_combination -h
  rw [ptShift_eq, Lagrange.eval_nodal, Polynomial.eval_C]
  simp only [Finset.univ_unique, Finset.prod_singleton]
  rw [show z - angleBr (lt 1) (lt 2) / angleBr (lt 0) (lt 2) =
      -(angleBr (lt 1) (lt 2) - z * angleBr (lt 0) (lt 2)) / angleBr (lt 0) (lt 2) by
    field_simp; ring]
  field_simp

lemma degree_ptShift_numerator :
    (Polynomial.C (-(angleBr (lt 0) (lt 1) ^ 3 /
        (angleBr (lt 0) (lt 2) * angleBr (lt 2) (lt 3) * restProd lt)))).degree <
      (Finset.univ : Finset Unit).card := by
  simpa using (Polynomial.degree_C_le).trans_lt (by norm_num : (0 : WithBot ℕ) < 1)

/-- **The pole is where the channel momentum `P̂₂₃ = p̂₂ + p₃` goes on shell**:
`P̂² = ⟨2̂3⟩[23]` (gluons `1, 2` here). -/
theorem ptShift_channel (z : ℂ) :
    mdot (nullMom (l 1) (bcfwAngle lt 0 1 z 1) + nullMom (l 2) (lt 2))
        (nullMom (l 1) (bcfwAngle lt 0 1 z 1) + nullMom (l 2) (lt 2)) =
      (angleBr (lt 1) (lt 2) - z * angleBr (lt 0) (lt 2)) * squareBr (l 1) (l 2) := by
  have hm : ∀ p q : Fin 4 → ℂ, mdot (p + q) (p + q) = mdot p p + 2 * mdot p q + mdot q q := by
    intro p q; simp only [mdot, Pi.add_apply]; ring
  rw [hm, mdot_nullMom_self, mdot_nullMom_self, ← angleBr_mul_squareBr]
  have e1 : bcfwAngle lt 0 1 z 1 = lt 1 - z • lt 0 := Function.update_self _ _ _
  rw [e1]
  simp only [angleBr_eq, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- **At the pole the shifted angle spinor is proportional**: `|1̂⟩ = (⟨01⟩/⟨02⟩) |2⟩` (Schouten), so the
on-shell channel momentum is `P̂ = −(c|1] + |2])⟨2|`. -/
theorem ptShift_onshell (h02 : angleBr (lt 0) (lt 2) ≠ 0) :
    bcfwAngle lt 0 1 (angleBr (lt 1) (lt 2) / angleBr (lt 0) (lt 2)) 1 =
      (angleBr (lt 0) (lt 1) / angleBr (lt 0) (lt 2)) • lt 2 := by
  rw [show bcfwAngle lt 0 1 _ 1 = _ from Function.update_self _ _ _]
  funext a
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  field_simp
  simp only [angleBr_eq]
  fin_cases a <;> simp <;> ring

/-- The anti-MHV three-point amplitude `A₃[a⁺ b⁺ c⁻] = [ab]³/([bc][ca])` (Elvang-Huang (2.78)). -/
def antiMHV3 (la lb lc : Fin 2 → ℂ) : ℂ := squareBr la lb ^ 3 / (squareBr lb lc * squareBr lc la)

/-- **The residue factorizes** (Elvang-Huang (3.5), (3.18)–(3.21)): for any spinors `|P̂]`, `⟨P̂|` of the
on-shell channel momentum `P̂₂₃ = −(c|2] + |3])⟨3|` at the pole (gluons `1, 2` here), the residue of
`Â(z)/z` at `z*` is `−Â_{n−1}(1̂⁻, P̂⁻, 4⁺, …, n⁺) Â₃(−P̂⁺, 2̂⁻, 3⁺) / P₂₃²`. -/
theorem ptShift_factorization (h01 : angleBr (lt 0) (lt 1) ≠ 0) (h02 : angleBr (lt 0) (lt 2) ≠ 0)
    (h12 : angleBr (lt 1) (lt 2) ≠ 0) (h23 : angleBr (lt 2) (lt 3) ≠ 0) (hR : restProd lt ≠ 0)
    (hs12 : squareBr (l 1) (l 2) ≠ 0) {lP ltP : Fin 2 → ℂ}
    (hP : vecMulVec lP ltP =
      vecMulVec ((angleBr (lt 0) (lt 1) / angleBr (lt 0) (lt 2)) • l 1 + l 2) (lt 2))
    (hP0 : vecMulVec lP ltP ≠ 0) :
    -(angleBr (lt 0) (lt 1) ^ 3 / (angleBr (lt 0) (lt 2) * angleBr (lt 2) (lt 3) * restProd lt)) /
        (angleBr (lt 1) (lt 2) / angleBr (lt 0) (lt 2)) =
      -(parkeTaylor (lt 0) ltP
          (Fin.cons (lt 0) (Fin.cons ltP (fun k : Fin (m + 1) => lt k.succ.succ.succ)) :
            Fin (m + 3) → Fin 2 → ℂ) *
        antiMHV3 (l 2) lP (l 1)) /
        (angleBr (lt 1) (lt 2) * squareBr (l 1) (l 2)) := by
  obtain ⟨t, ht, hl, hlt⟩ := exists_littleGroup_of_eq hP.symm (by rw [← hP]; exact hP0)
  set c := angleBr (lt 0) (lt 1) / angleBr (lt 0) (lt 2) with hc
  -- the denominator of the `(n−1)`-point amplitude
  have hden : cycDen (Fin.cons (lt 0) (Fin.cons ltP (fun k : Fin (m + 1) => lt k.succ.succ.succ)) :
      Fin (m + 3) → Fin 2 → ℂ) = angleBr (lt 0) ltP * angleBr ltP (lt 3) * restProd lt := by
    rw [cycDen_three]
    have i2 : (2 : Fin (m + 3)) = (0 : Fin (m + 1)).succ.succ := by
      apply Fin.ext; simp
    have v3 : ((3 : Fin (m + 4)) : ℕ) = 3 := by simp
    have i3 : ((0 : Fin (m + 1)).succ.succ.succ : Fin (m + 4)) = 3 := by
      rw [Fin.ext_iff, Fin.val_succ, Fin.val_succ, Fin.val_succ, Fin.val_zero, v3]
    rw [i2]
    simp only [Fin.cons_zero, Fin.cons_one, Fin.cons_succ, i3]
    unfold restProd
    congr 1
    exact Finset.prod_congr rfl fun k _ => by rw [finRotate_succ_succ_succ k lt ltP]
  subst hl hlt
  have hs1 : squareBr (l 2) (t⁻¹ • (c • l 1 + l 2)) = t⁻¹ * c * squareBr (l 2) (l 1) := by
    simp only [squareBr_eq, Pi.smul_apply, Pi.add_apply, smul_eq_mul]; ring
  have hs2 : squareBr (t⁻¹ • (c • l 1 + l 2)) (l 1) = t⁻¹ * squareBr (l 2) (l 1) := by
    simp only [squareBr_eq, Pi.smul_apply, Pi.add_apply, smul_eq_mul]; ring
  have hq : squareBr (l 2) (l 1) = -squareBr (l 1) (l 2) := squareBr_antisymm _ _
  have hc0 : c ≠ 0 := div_ne_zero h01 h02
  unfold parkeTaylor antiMHV3
  rw [hden, angleBr_smul_right', angleBr_smul_left', hs1, hs2, hq]
  rw [hc]
  field_simp

end MHV


end Lightlike.SpinorHelicity
