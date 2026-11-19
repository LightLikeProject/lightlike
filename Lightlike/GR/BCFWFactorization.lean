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

## References

* H. Elvang, Y. Huang, *Scattering Amplitudes*, arXiv:1308.1697, §3.1, pp. 34–36: the shifts (3.1), the
  properties (A)–(C), (3.2)–(3.3), Cauchy's theorem (3.4), the factorization of residues (3.5), the
  large-`z` condition (3.6) and the recursion (3.7); §3.2, p. 36, the BCFW shift (3.8).
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

end Lightlike.SpinorHelicity
