import Lightlike.Spacetime.EnergyConditions

/-!
# The energy conditions of the electromagnetic field (GE14, stage 3)

For an antisymmetric field strength `F` on a Lorentzian vector space and its stress-energy
`T_ab = F_ac F_b^c − ¼ F_cd F^cd g_ab` (`emT`):

* `exists_frame_of_timelike`: every unit timelike vector is the time vector of a Lorentz frame (a boost of a given frame);
  `lorentz_repr`, `exists_basis_of_orthonormal`;
* `emA_frame`, `g_emA_emA`, `emF2_frame`: `A = g⁻¹F`, `g(Av, Aw)` and `F_ab F^ab` in a Lorentz frame;
* `emT_frame_00`: the energy density `T(e₀, e₀) = ½ Σᵢ F₀ᵢ² + ¼ Σᵢⱼ Fᵢⱼ²`; **`em_weakEC`**: the weak condition (any dimension);
* `antisymm_op_bound`: `|A E|² ≤ ½ |A|² |E|²` for an antisymmetric matrix `A`; `em_poynting`: the Poynting bound
  `Σᵢ T(e₀, eᵢ)² ≤ T(e₀, e₀)²` (any dimension); **`em_dominantEC`**: the dominant condition (any dimension);
  `emT_traceless`: `T` is traceless in four dimensions; `emT_trace_frame`: `tr_g T = (1 − n/4) F_ab F^ab`;
  **`em_strongEC_dim`**: the strong condition `(T − tr_g T/(n − 2) g)(v, v) ≥ 0` in dimension `n ≥ 3`;
* `em_weakEC_of_eq`, **`em_strongEC_of_eq`**, `em_dominantEC_of_eq`: the conditions `WeakEC`, `StrongEC`, `DominantEC` for a
  continuous form equal to `emT`.

Source read: E.-A. Kontou and K. Sanders, *Energy conditions in general relativity and quantum field theory*, arXiv 2003.01815,
§2.3, pp. 13-15: the stress tensor (15) (ours, `m = 0`), the energy density (36), the trace (37), (38), and Table 2: the Maxwell
field satisfies the NEC, WEC, DEC and SEC.

**Limits.** Pointwise statements on a vector space (the field version is `EnergyConditionsField.lean`); `StrongEC` of
`EnergyConditions.lean` is the four-dimensional condition (`em_strongEC_of_eq`), the strong condition in dimension `n ≥ 3` is
`em_strongEC_dim`.
-/

open Module

noncomputable section
namespace Lightlike

variable {V : Type*} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]

/-- The coordinates in a Lorentz frame: `e.repr v i = ηᵢᵢ g(v, eᵢ)`. -/
theorem lorentz_repr {n : ℕ} {g : V →L[ℝ] V →L[ℝ] ℝ} (e : Module.Basis (Fin n) ℝ V)
    (he : ∀ i j, g (e i) (e j) = eta n i j) (v : V) (i : Fin n) : e.repr v i = etaDiag i * g v (e i) := by
  conv_rhs => rw [← e.sum_repr v]
  simp only [map_sum, map_smul, FunLike.coe_sum, Finset.sum_apply, smul_apply, smul_eq_mul, he, eta_apply]
  rw [Finset.sum_eq_single i]
  · simp only [ite_true]
    rw [← mul_assoc, mul_comm (etaDiag i), mul_assoc, etaDiag_mul_self, mul_one]
  · intro j _ hj; simp [hj]
  · simp

/-- **An `η`-orthonormal family is a Lorentz frame.** -/
theorem exists_basis_of_orthonormal [FiniteDimensional ℝ V] {n : ℕ} {g : V →L[ℝ] V →L[ℝ] ℝ}
    (hg : IsLorentzianForm n g) (f : Fin n → V) (hf : ∀ i j, g (f i) (f j) = eta n i j) :
    ∃ e : Module.Basis (Fin n) ℝ V, ∀ i, e i = f i := by
  have hli : LinearIndependent ℝ f := by
    rw [Fintype.linearIndependent_iff]
    intro c hc j
    have h := congrArg (fun v => g v (f j)) hc
    simp only [map_sum, map_smul, FunLike.coe_sum, Finset.sum_apply, smul_apply, smul_eq_mul, hf,
      eta_apply, map_zero, zero_apply] at h
    rw [Finset.sum_eq_single j (fun i _ hi => by simp [hi]) (by simp)] at h
    simp only [ite_true] at h
    exact (mul_eq_zero.1 h).resolve_right (etaDiag_ne_zero j)
  obtain ⟨e₀, -⟩ := hg
  have hcard : Fintype.card (Fin n) = finrank ℝ V := by
    rw [Module.finrank_eq_card_basis e₀]
  exact ⟨Module.Basis.mk hli (hli.span_eq_top_of_card_eq_finrank' hcard).ge, fun i => by simp⟩

/-- **Every unit timelike vector is the time vector of a Lorentz frame** (the boost of a given frame). -/
theorem exists_frame_of_timelike [FiniteDimensional ℝ V] {m : ℕ} {g : V →L[ℝ] V →L[ℝ] ℝ}
    (hg : IsLorentzianForm (m + 1) g) {u : V} (hu : g u u = -1) :
    ∃ e : Module.Basis (Fin (m + 1)) ℝ V, (∀ i j, g (e i) (e j) = eta (m + 1) i j) ∧ e 0 = u := by
  have hsymm : ∀ v w, g v w = g w v := hg.symm
  obtain ⟨e, he⟩ := hg
  -- a unit timelike `t = ± e₀` with `γ = -g(t, u) > 0`
  obtain ⟨t, htt, hts, hγ⟩ : ∃ t : V, g t t = -1 ∧ (∀ j : Fin m, g (e j.succ) t = 0) ∧ 0 < -g t u := by
    have h00 : g (e 0) (e 0) = -1 := by simp [he, eta_apply, etaDiag]
    have h0j : ∀ j : Fin m, g (e j.succ) (e 0) = 0 := fun j => by
      simp [he, eta_apply, Fin.succ_ne_zero]
    have hne : g (e 0) u ≠ 0 := by
      intro h0
      have hrev := lorentz_reverse_cs (⟨e, he⟩ : IsLorentzianForm (m + 1) g) (u := e 0) (by rw [h00]; norm_num) u
      rw [h00, hu, h0] at hrev
      norm_num at hrev
    rcases lt_or_gt_of_ne hne with h | h
    · exact ⟨e 0, h00, h0j, by linarith⟩
    · refine ⟨-e 0, by simp [h00], fun j => by simp [h0j j], by simp; linarith⟩
  set γ := -g t u with hγdef
  set c : Fin m → ℝ := fun j => g (e j.succ) u / (1 + γ) with hc
  set f : Fin (m + 1) → V := Fin.cons u (fun j => e j.succ + c j • (t + u)) with hfdef
  have h1γ : 1 + γ ≠ 0 := by linarith
  have htu : g (t + u) (t + u) = -2 * (1 + γ) := by
    simp only [map_add, add_apply, htt, hu, hsymm u t]; rw [hγdef]; ring
  have hspat : ∀ j k : Fin m, g (e j.succ) (e k.succ) = if j = k then 1 else 0 := fun j k => by
    simp [he, eta_apply, etaDiag, Fin.succ_inj]
  have hu_tu : g u (t + u) = -(1 + γ) := by
    simp only [map_add, hu, hsymm u t]; rw [hγdef]; ring
  have hej_tu : ∀ j : Fin m, g (e j.succ) (t + u) = (1 + γ) * c j := fun j => by
    simp only [map_add, hts j, zero_add, hc]; field_simp
  have hf0 : ∀ j : Fin m, g u (f j.succ) = 0 := fun j => by
    simp only [hfdef, Fin.cons_succ, map_add, map_smul, smul_eq_mul, hu_tu, hsymm u (e j.succ), hc]
    field_simp; ring
  have hfjk : ∀ j k : Fin m, g (f j.succ) (f k.succ) = if j = k then 1 else 0 := fun j k => by
    have hA : g (f j.succ) (f k.succ) = g (e j.succ) (e k.succ) + c k * g (e j.succ) (t + u)
        + c j * g (t + u) (e k.succ) + c j * c k * g (t + u) (t + u) := by
      simp only [hfdef, Fin.cons_succ, map_add, map_smul, add_apply, smul_apply, smul_eq_mul]; ring
    rw [hA, hsymm (t + u) (e k.succ), hej_tu j, hej_tu k, htu, hspat]
    field_simp
    ring
  have horth : ∀ i j, g (f i) (f j) = eta (m + 1) i j := by
    intro i j
    refine Fin.cases ?_ (fun i' => ?_) i <;> refine Fin.cases ?_ (fun j' => ?_) j
    · simp [hfdef, hu, eta_apply, etaDiag]
    · rw [show f 0 = u from rfl, hf0 j']; simp [eta_apply, (Fin.succ_ne_zero j').symm]
    · rw [show f 0 = u from rfl, hsymm, hf0 i']; simp [eta_apply, Fin.succ_ne_zero]
    · rw [hfjk]; simp [eta_apply, etaDiag, Fin.succ_inj]
  obtain ⟨e', he'⟩ := exists_basis_of_orthonormal (⟨e, he⟩ : IsLorentzianForm (m + 1) g) f horth
  exact ⟨e', fun i j => by rw [he', he']; exact horth i j, by rw [he']; rfl⟩

end Lightlike

namespace Lightlike
section EMFrame
variable {V : Type*} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V] [FiniteDimensional ℝ V]
  {n : ℕ} {g : V →L[ℝ] V →L[ℝ] ℝ} (e : Module.Basis (Fin n) ℝ V) (he : ∀ i j, g (e i) (e j) = eta n i j)
  (hnd : g.toBilinForm.Nondegenerate) (F : LinearMap.BilinForm ℝ V)
include he

/-- `A v = Σₖ ηₖₖ F(v, eₖ) eₖ` in a Lorentz frame. -/
theorem emA_frame (v : V) : emA g hnd F v = ∑ k, (etaDiag k * F v (e k)) • e k := by
  conv_lhs => rw [← e.sum_repr (emA g hnd F v)]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [lorentz_repr e he, g_emA]

/-- `g(A v, A w) = Σₖ ηₖₖ F(v, eₖ) F(w, eₖ)`. -/
theorem g_emA_emA (v w : V) : g (emA g hnd F v) (emA g hnd F w) = ∑ k, etaDiag k * F v (e k) * F w (e k) := by
  rw [g_emA, emA_frame e he hnd F w, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_smul, smul_eq_mul]; ring

/-- `F_ab F^ab = Σₗₖ ηₗₗ ηₖₖ F(eₗ, eₖ)²` for an antisymmetric `F`. -/
theorem emF2_frame (hF : ∀ v w, F v w = -F w v) :
    emF2 g hnd F = ∑ l, ∑ k, etaDiag l * etaDiag k * F (e l) (e k) ^ 2 := by
  unfold emF2
  rw [LinearMap.trace_eq_matrix_trace ℝ e]
  simp only [Matrix.trace, Matrix.diag, LinearMap.toMatrix_apply, LinearMap.comp_apply]
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [lorentz_repr e he, g_emA, hF, emA_frame e he hnd F (e l), map_sum]
  simp only [map_smul, smul_eq_mul, Finset.mul_sum, mul_neg, neg_neg]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

end EMFrame
end Lightlike

namespace Lightlike

section EMWeak
variable {V : Type*} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V] [FiniteDimensional ℝ V]
  {m : ℕ} {g : V →L[ℝ] V →L[ℝ] ℝ} (hnd : g.toBilinForm.Nondegenerate) {F : LinearMap.BilinForm ℝ V}

/-- **The electromagnetic energy density in a Lorentz frame**: `T(e₀, e₀) = ½ Σᵢ F₀ᵢ² + ¼ Σᵢⱼ Fᵢⱼ²`. -/
theorem emT_frame_00 (e : Module.Basis (Fin (m + 1)) ℝ V) (he : ∀ i j, g (e i) (e j) = eta (m + 1) i j)
    (hF : ∀ v w, F v w = -F w v) :
    emT g hnd F (e 0) (e 0) = (1 / 2) * ∑ i : Fin m, F (e 0) (e i.succ) ^ 2 +
      (1 / 4) * ∑ i : Fin m, ∑ j : Fin m, F (e i.succ) (e j.succ) ^ 2 := by
  have hdiag : ∀ v, F v v = 0 := fun v => by have := hF v v; linarith
  have h00 : g (e 0) (e 0) = -1 := by simp [he, eta_apply, etaDiag]
  have hη0 : etaDiag (0 : Fin (m + 1)) = -1 := by simp [etaDiag]
  have hηs : ∀ i : Fin m, etaDiag i.succ = 1 := fun i => by simp [etaDiag]
  unfold emT
  rw [g_emA_emA e he hnd F, emF2_frame e he hnd F hF, h00, Fin.sum_univ_succ, Fin.sum_univ_succ]
  simp only [Fin.sum_univ_succ, hdiag, hη0, hηs]
  have hs : ∀ i : Fin m, F (e i.succ) (e 0) ^ 2 = F (e 0) (e i.succ) ^ 2 := fun i => by rw [hF]; ring
  simp only [hs, Finset.sum_add_distrib]
  ring_nf
  simp only [Finset.sum_neg_distrib]
  ring

/-- `T(c v, c w) = c² T(v, w)`. -/
theorem emT_smul (c : ℝ) (v w : V) : emT g hnd F (c • v) (c • w) = c * c * emT g hnd F v w := by
  simp only [emT, map_smul, smul_apply, smul_eq_mul]
  ring

/-- **The electromagnetic field satisfies the weak energy condition** (any dimension): `T(v, v) ≥ 0` for timelike `v`
(Kontou and Sanders, arXiv 2003.01815, §2.3, eq. (36) and Table 2). -/
theorem em_weakEC (hg : IsLorentzianForm (m + 1) g) (hF : ∀ v w, F v w = -F w v) (v : V) (hv : g v v < 0) :
    0 ≤ emT g hnd F v v := by
  set s := Real.sqrt (-g v v) with hs
  have hs0 : 0 < s := Real.sqrt_pos.2 (by linarith)
  set u := s⁻¹ • v with hu
  have huu : g u u = -1 := by
    simp only [hu, map_smul, smul_apply, smul_eq_mul]
    have h2 : s * s = -g v v := Real.mul_self_sqrt (by linarith)
    field_simp
    linarith
  obtain ⟨e, he, he0⟩ := exists_frame_of_timelike hg huu
  have hvu : v = s • u := by simp [hu, smul_smul, hs0.ne']
  rw [hvu, emT_smul, ← he0, emT_frame_00 hnd e he hF]
  have h1 : 0 ≤ ∑ i : Fin m, F (e 0) (e i.succ) ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have h2 : 0 ≤ ∑ i : Fin m, ∑ j : Fin m, F (e i.succ) (e j.succ) ^ 2 :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _
  have := mul_self_nonneg s
  positivity

end EMWeak
end Lightlike

namespace Lightlike

section EMDominant
variable {V : Type*} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V] [FiniteDimensional ℝ V]
  {g : V →L[ℝ] V →L[ℝ] ℝ} (hnd : g.toBilinForm.Nondegenerate) {F : LinearMap.BilinForm ℝ V}

/-- `T(v, Σ cₖ wₖ) = Σ cₖ T(v, wₖ)`. -/
theorem emT_sum_right {ι : Type*} (s : Finset ι) (c : ι → ℝ) (w : ι → V) (v : V) :
    emT g hnd F v (∑ k ∈ s, c k • w k) = ∑ k ∈ s, c k * emT g hnd F v (w k) := by
  simp only [emT, map_sum, map_smul, smul_eq_mul, Finset.mul_sum]
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun k _ => by ring

/-- Sums over three indices are invariant under the cyclic shift of the indices. -/
theorem sum_cyc3 {m : ℕ} (f : Fin m → Fin m → Fin m → ℝ) :
    ∑ i, ∑ j, ∑ k, f j k i = ∑ i, ∑ j, ∑ k, f i j k := by
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun j _ => Finset.sum_comm

/-- For an antisymmetric matrix `A`, `|A E|² ≤ ½ ‖A‖² |E|²` (the sum of squares of the cyclic sums is `6` times the gap). -/
theorem antisymm_op_bound {m : ℕ} (A : Fin m → Fin m → ℝ) (hA : ∀ i j, A i j = -A j i) (E : Fin m → ℝ) :
    ∑ i, (∑ k, A i k * E k) ^ 2 ≤ (1 / 2) * (∑ i, ∑ j, A i j ^ 2) * ∑ k, E k ^ 2 := by
  set S : Fin m → ℝ := fun i => ∑ k, A i k * E k with hS
  have hS' : ∀ j, ∑ i, A i j * E i = -S j := fun j => by
    simp only [hS, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun i _ => by rw [hA]; ring
  have hpos : 0 ≤ ∑ i, ∑ j, ∑ k, (A i j * E k + A j k * E i + A k i * E j) ^ 2 :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun k _ => sq_nonneg _
  have expand : ∀ i j k, (A i j * E k + A j k * E i + A k i * E j) ^ 2 =
      A i j ^ 2 * E k ^ 2 + A j k ^ 2 * E i ^ 2 + A k i ^ 2 * E j ^ 2 +
      2 * (A i j * E i * (A j k * E k)) + 2 * (A j k * E j * (A k i * E i)) + 2 * (A k i * E k * (A i j * E j)) := by
    intro i j k; ring
  simp only [expand, Finset.sum_add_distrib] at hpos
  have t1 : ∑ i, ∑ j, ∑ k, A i j ^ 2 * E k ^ 2 = (∑ i, ∑ j, A i j ^ 2) * ∑ k, E k ^ 2 := by
    simp only [Finset.sum_mul, Finset.mul_sum]
    exact (sum_cyc3 (fun a b c => A a b ^ 2 * E c ^ 2)).symm
  have t2 : ∑ i, ∑ j, ∑ k, A j k ^ 2 * E i ^ 2 = ∑ i, ∑ j, ∑ k, A i j ^ 2 * E k ^ 2 :=
    sum_cyc3 (fun a b c => A a b ^ 2 * E c ^ 2)
  have t3 : ∑ i, ∑ j, ∑ k, A k i ^ 2 * E j ^ 2 = ∑ i, ∑ j, ∑ k, A i j ^ 2 * E k ^ 2 :=
    (sum_cyc3 (fun a b c => A b c ^ 2 * E a ^ 2)).trans t2
  have c1 : ∑ i, ∑ j, ∑ k, 2 * (A i j * E i * (A j k * E k)) = -2 * ∑ j, S j ^ 2 := by
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    have : ∑ i, ∑ k, 2 * (A i j * E i * (A j k * E k)) = 2 * ((∑ i, A i j * E i) * ∑ k, A j k * E k) := by
      rw [Finset.sum_mul_sum, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by rw [Finset.mul_sum]
    rw [this, hS' j]; simp only [hS]; ring
  have c2 : ∑ i, ∑ j, ∑ k, 2 * (A j k * E j * (A k i * E i)) = ∑ i, ∑ j, ∑ k, 2 * (A i j * E i * (A j k * E k)) :=
    sum_cyc3 (fun a b c => 2 * (A a b * E a * (A b c * E c)))
  have c3 : ∑ i, ∑ j, ∑ k, 2 * (A k i * E k * (A i j * E j)) = ∑ i, ∑ j, ∑ k, 2 * (A i j * E i * (A j k * E k)) :=
    (sum_cyc3 (fun a b c => 2 * (A b c * E b * (A c a * E a)))).trans c2
  rw [t2, t3, c2, c3, t1, c1] at hpos
  show ∑ i, S i ^ 2 ≤ 1 / 2 * (∑ i, ∑ j, A i j ^ 2) * ∑ k, E k ^ 2
  linarith

/-- **The Poynting bound in a Lorentz frame**: `Σᵢ T(e₀, eᵢ)² ≤ T(e₀, e₀)²` (`|E × B| ≤ |E| |B|` in four dimensions; in general
`|F E|² ≤ ½ |F|² |E|²` for the antisymmetric spatial part). -/
theorem em_poynting {m : ℕ} (e : Module.Basis (Fin (m + 1)) ℝ V) (he : ∀ i j, g (e i) (e j) = eta (m + 1) i j)
    (hF : ∀ v w, F v w = -F w v) :
    ∑ i : Fin m, emT g hnd F (e 0) (e i.succ) ^ 2 ≤ emT g hnd F (e 0) (e 0) ^ 2 := by
  have hdiag : ∀ v, F v v = 0 := fun v => by have := hF v v; linarith
  have h0i : ∀ i : Fin m, g (e 0) (e i.succ) = 0 := fun i => by
    simp [he, eta_apply, (Fin.succ_ne_zero i).symm]
  set E : Fin m → ℝ := fun k => F (e 0) (e k.succ) with hE
  set A : Fin m → Fin m → ℝ := fun i k => F (e i.succ) (e k.succ) with hAdef
  have hA : ∀ i k, A i k = -A k i := fun i k => hF _ _
  have hS : ∀ i : Fin m, emT g hnd F (e 0) (e i.succ) = ∑ k, A i k * E k := by
    intro i
    unfold emT
    rw [g_emA_emA e he hnd F, h0i, Fin.sum_univ_succ, hdiag]
    simp only [mul_zero, zero_mul, zero_add, sub_zero, etaDiag, Fin.val_succ, ite_false, one_mul,
      Nat.succ_ne_zero, hAdef, hE]
    exact Finset.sum_congr rfl fun k _ => by ring
  have hT : emT g hnd F (e 0) (e 0) = (1 / 2) * ∑ k, E k ^ 2 + (1 / 4) * ∑ i, ∑ k, A i k ^ 2 :=
    emT_frame_00 hnd e he hF
  simp only [hS, hT]
  have hb := antisymm_op_bound A hA E
  have hN : 0 ≤ ∑ i, ∑ k, A i k ^ 2 := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun k _ => sq_nonneg _
  have hQ : 0 ≤ ∑ k, E k ^ 2 := Finset.sum_nonneg fun k _ => sq_nonneg _
  nlinarith [sq_nonneg ((1 / 2) * ∑ k, E k ^ 2 - (1 / 4) * ∑ i, ∑ k, A i k ^ 2)]

/-- `T(c v, w) = c T(v, w)`. -/
theorem emT_smul_left (c : ℝ) (v w : V) : emT g hnd F (c • v) w = c * emT g hnd F v w := by
  simp only [emT, map_smul, smul_apply, smul_eq_mul]
  ring

theorem emT_symm (hg : ∀ v w, g v w = g w v) (v w : V) : emT g hnd F v w = emT g hnd F w v := by
  simp only [emT, hg v w]
  rw [hg (emA g hnd F v)]

/-- **The electromagnetic field satisfies the dominant energy condition** (any dimension; Kontou and Sanders,
arXiv 2003.01815, §2.3 and Table 2): for timelike `ξ`, `T(ξ, ξ) ≥ 0` and the vector `T^a_n ξ^n` (the `w` with
`g(w, ·) = T(ξ, ·)`) is causal; for co-oriented timelike `ξ, η`, `T(ξ, η) ≥ 0`. -/
theorem em_dominantEC {m : ℕ} (hg : IsLorentzianForm (m + 1) g) (hF : ∀ v w, F v w = -F w v) :
    (∀ ξ : V, g ξ ξ < 0 → 0 ≤ emT g hnd F ξ ξ ∧ ∃ w : V, (∀ v, g w v = emT g hnd F ξ v) ∧ g w w ≤ 0) ∧
      ∀ ξ η : V, g ξ ξ < 0 → g η η < 0 → g ξ η < 0 → 0 ≤ emT g hnd F ξ η := by
  have hsymm : ∀ v w, g v w = g w v := hg.symm
  -- the adapted frame of a timelike vector
  have frame : ∀ ξ : V, g ξ ξ < 0 → ∃ s : ℝ, 0 < s ∧ ∃ e : Module.Basis (Fin (m + 1)) ℝ V,
      (∀ i j, g (e i) (e j) = eta (m + 1) i j) ∧ ξ = s • e 0 := by
    intro ξ hξ
    set s := Real.sqrt (-g ξ ξ)
    have hs0 : 0 < s := Real.sqrt_pos.2 (by linarith)
    have huu : g (s⁻¹ • ξ) (s⁻¹ • ξ) = -1 := by
      simp only [map_smul, smul_apply, smul_eq_mul]
      have h2 : s * s = -g ξ ξ := Real.mul_self_sqrt (by linarith)
      field_simp
      linarith
    obtain ⟨e, he, he0⟩ := exists_frame_of_timelike hg huu
    exact ⟨s, hs0, e, he, by rw [he0, smul_smul, mul_inv_cancel₀ hs0.ne', one_smul]⟩
  refine ⟨fun ξ hξ => ⟨em_weakEC hnd hg hF ξ hξ, ?_⟩, fun ξ η hξ hη hξη => ?_⟩
  · obtain ⟨s, hs0, e, he, hξe⟩ := frame ξ hξ
    refine ⟨∑ k, (etaDiag k * emT g hnd F ξ (e k)) • e k, fun v => ?_, ?_⟩
    · conv_rhs => rw [← e.sum_repr v, emT_sum_right]
      simp only [map_sum, map_smul, smul_apply, smul_eq_mul, sum_apply]
      conv_lhs => rw [← e.sum_repr v]
      simp only [map_sum, map_smul, smul_eq_mul, he, eta_apply]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [Finset.sum_eq_single l (fun k _ hk => by simp [Ne.symm hk]) (by simp)]
      simp only [ite_true]
      have := etaDiag_mul_self l
      linear_combination (e.repr v l * emT g hnd F ξ (e l)) * this
    · simp only [map_sum, map_smul, smul_apply, smul_eq_mul, sum_apply, he, eta_apply]
      have hW : ∀ k, ∑ l, etaDiag l * emT g hnd F ξ (e l) * (if l = k then etaDiag l else 0) =
          emT g hnd F ξ (e k) := by
        intro k
        rw [Finset.sum_eq_single k (fun l _ hl => by simp [hl]) (by simp)]
        simp only [ite_true]
        have := etaDiag_mul_self k
        linear_combination (emT g hnd F ξ (e k)) * this
      simp only [hW]
      rw [Fin.sum_univ_succ]
      have hP := em_poynting hnd e he hF
      have hk : ∀ k, emT g hnd F ξ (e k) = s * emT g hnd F (e 0) (e k) := fun k => by rw [hξe, emT_smul_left]
      simp only [hk]
      have hη0 : etaDiag (0 : Fin (m + 1)) = -1 := by simp [etaDiag]
      have hηs : ∀ i : Fin m, etaDiag i.succ = 1 := fun i => by simp [etaDiag]
      simp only [hη0, hηs, one_mul]
      have hsum : ∑ x : Fin m, s * emT g hnd F (e 0) (e x.succ) * (s * emT g hnd F (e 0) (e x.succ)) =
          s ^ 2 * ∑ x : Fin m, emT g hnd F (e 0) (e x.succ) ^ 2 := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun x _ => by ring
      rw [hsum]
      nlinarith [sq_nonneg s, mul_le_mul_of_nonneg_left hP (sq_nonneg s)]
  · obtain ⟨s, hs0, e, he, hξe⟩ := frame ξ hξ
    have hη' : η = ∑ k, e.repr η k • e k := (e.sum_repr η).symm
    rw [hξe, emT_smul_left, hη', emT_sum_right, Fin.sum_univ_succ]
    have hT0 := em_weakEC hnd hg hF (e 0) (by simp [he, eta_apply, etaDiag])
    have hP := em_poynting hnd e he hF
    set b0 := e.repr η 0
    set P := ∑ i : Fin m, e.repr η i.succ * emT g hnd F (e 0) (e i.succ)
    set T00 := emT g hnd F (e 0) (e 0)
    -- `b₀ > 0` (co-orientation) and `Σ bᵢ² < b₀²` (η timelike)
    have hb0 : 0 < b0 := by
      have h1 : b0 = etaDiag 0 * g η (e 0) := lorentz_repr e he η 0
      have h2 : g η (e 0) = s⁻¹ * g ξ η := by
        rw [hsymm, hξe]; simp only [map_smul, smul_apply, smul_eq_mul]; field_simp
      have hη0 : etaDiag (0 : Fin (m + 1)) = -1 := by simp [etaDiag]
      rw [h1, h2, hη0]
      have : 0 < s⁻¹ := inv_pos.2 hs0
      nlinarith
    have hbb : ∑ i : Fin m, e.repr η i.succ ^ 2 < b0 ^ 2 := by
      have := lorentz_apply (m := m) e he η η
      rw [this] at hη
      have : ∀ i : Fin m, e.repr η i.succ * e.repr η i.succ = e.repr η i.succ ^ 2 := fun i => by ring
      simp only [this] at hη
      nlinarith
    have hcs : P ^ 2 ≤ (∑ i : Fin m, e.repr η i.succ ^ 2) * ∑ i : Fin m, emT g hnd F (e 0) (e i.succ) ^ 2 :=
      Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun i : Fin m => e.repr η i.succ)
        (fun i => emT g hnd F (e 0) (e i.succ))
    have hB0 : 0 ≤ ∑ i : Fin m, e.repr η i.succ ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
    have hS0 : 0 ≤ ∑ i : Fin m, emT g hnd F (e 0) (e i.succ) ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
    have hP2 : P ^ 2 ≤ (b0 * T00) ^ 2 := by
      calc P ^ 2 ≤ _ := hcs
        _ ≤ b0 ^ 2 * T00 ^ 2 := mul_le_mul hbb.le hP hS0 (sq_nonneg _)
        _ = (b0 * T00) ^ 2 := by ring
    have hab := abs_le_of_sq_le_sq' hP2 (mul_nonneg hb0.le hT0)
    have : 0 ≤ b0 * T00 + P := by linarith [hab.1]
    nlinarith [this]


/-- **The electromagnetic stress-energy is traceless in four dimensions**: `Σₗ ηₗₗ T(eₗ, eₗ) = 0` in a Lorentz frame. -/
theorem emT_traceless (e : Module.Basis (Fin 4) ℝ V) (he : ∀ i j, g (e i) (e j) = eta 4 i j)
    (hF : ∀ v w, F v w = -F w v) : ∑ l, etaDiag l * emT g hnd F (e l) (e l) = 0 := by
  have h1 : ∀ l, etaDiag l * emT g hnd F (e l) (e l) =
      ∑ k, etaDiag l * etaDiag k * F (e l) (e k) ^ 2 - (1 / 4) * emF2 g hnd F := by
    intro l
    unfold emT
    rw [g_emA_emA e he hnd F, he, eta_apply]
    simp only [ite_true]
    rw [mul_sub, Finset.mul_sum]
    have := etaDiag_mul_self l
    rw [Finset.sum_congr rfl fun k _ => show etaDiag l * (etaDiag k * F (e l) (e k) * F (e l) (e k)) =
      etaDiag l * etaDiag k * F (e l) (e k) ^ 2 by ring]
    linear_combination (-(1 / 4) * emF2 g hnd F) * this
  simp only [h1, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [← emF2_frame e he hnd F hF]
  ring

variable {T : V →L[ℝ] V →L[ℝ] ℝ}

/-- **The weak condition** for a continuous form `T` equal to the electromagnetic stress-energy. -/
theorem em_weakEC_of_eq (hg : IsLorentzianForm 4 g) (hF : ∀ v w, F v w = -F w v)
    (hT : ∀ v w, T v w = emT g hnd F v w) : WeakEC g T := fun v hv => by
  rw [hT]; exact em_weakEC hnd hg hF v hv

/-- **The strong condition** for the electromagnetic stress-energy (four dimensions; Kontou and Sanders, §2.3, eq. (38)):
it is traceless, so the strong condition is the weak one. -/
theorem em_strongEC_of_eq (hg : IsLorentzianForm 4 g) (hF : ∀ v w, F v w = -F w v)
    (hT : ∀ v w, T v w = emT g hnd F v w) : StrongEC g T hg := by
  intro v hv
  obtain ⟨e, he⟩ := id hg
  have htr : traceG g T hg.bilinForm_nondegenerate = 0 := by
    rw [traceG_eq_sum g T _ e he]
    simp only [hT]
    exact emT_traceless hnd e he hF
  rw [htr, hT]
  simpa using em_weakEC hnd hg hF v hv

/-- **The dominant condition** for a continuous form `T` equal to the electromagnetic stress-energy (four dimensions). -/
theorem em_dominantEC_of_eq (hg : IsLorentzianForm 4 g) (hF : ∀ v w, F v w = -F w v)
    (hT : ∀ v w, T v w = emT g hnd F v w) : DominantEC g T hg := by
  obtain ⟨h1, h2⟩ := em_dominantEC hnd hg hF
  refine ⟨fun ξ hξ => ⟨by rw [hT]; exact (h1 ξ hξ).1, ?_⟩, fun ξ η hξ hη hξη => by rw [hT]; exact h2 ξ η hξ hη hξη⟩
  obtain ⟨w, hw, hww⟩ := (h1 ξ hξ).2
  have hnd' := hg.bilinForm_nondegenerate
  have hraise : ∀ v, g (raiseT g T hnd' ξ) v = T ξ v := fun v => by
    have e1 := ((g.toBilinForm).toDual hnd').apply_symm_apply (T.toBilinForm ξ)
    have := LinearMap.congr_fun e1 v
    rw [LinearMap.BilinForm.toDual_def] at this
    exact this
  have heq : raiseT g T hnd' ξ = w := by
    have hnd2 := hg.nondegenerate
    refine sub_eq_zero.1 (hnd2 _ fun v => ?_)
    rw [map_sub, sub_apply, hraise, hw, hT, sub_self]
  rw [heq]; exact hww


/-- `F_ab F^ab = −2 Σᵢ F₀ᵢ² + Σᵢⱼ Fᵢⱼ²` in a Lorentz frame. -/
theorem emF2_split {m : ℕ} (e : Module.Basis (Fin (m + 1)) ℝ V) (he : ∀ i j, g (e i) (e j) = eta (m + 1) i j)
    (hF : ∀ v w, F v w = -F w v) :
    emF2 g hnd F = -2 * ∑ i : Fin m, F (e 0) (e i.succ) ^ 2 + ∑ i : Fin m, ∑ j : Fin m, F (e i.succ) (e j.succ) ^ 2 := by
  have hdiag : ∀ v, F v v = 0 := fun v => by have := hF v v; linarith
  have hη0 : etaDiag (0 : Fin (m + 1)) = -1 := by simp [etaDiag]
  have hηs : ∀ i : Fin m, etaDiag i.succ = 1 := fun i => by simp [etaDiag]
  have hs : ∀ i : Fin m, F (e i.succ) (e 0) ^ 2 = F (e 0) (e i.succ) ^ 2 := fun i => by rw [hF]; ring
  rw [emF2_frame e he hnd F hF, Fin.sum_univ_succ]
  simp only [Fin.sum_univ_succ, hdiag, hη0, hηs, hs, Finset.sum_add_distrib]
  ring_nf
  simp only [Finset.sum_neg_distrib]
  ring

/-- The `g`-trace of the electromagnetic stress-energy in a Lorentz frame of dimension `n`: `(1 − n/4) F_ab F^ab`. -/
theorem emT_trace_frame {m : ℕ} (e : Module.Basis (Fin (m + 1)) ℝ V) (he : ∀ i j, g (e i) (e j) = eta (m + 1) i j)
    (hF : ∀ v w, F v w = -F w v) :
    ∑ l, etaDiag l * emT g hnd F (e l) (e l) = (1 - ((m : ℝ) + 1) / 4) * emF2 g hnd F := by
  have h1 : ∀ l, etaDiag l * emT g hnd F (e l) (e l) =
      ∑ k, etaDiag l * etaDiag k * F (e l) (e k) ^ 2 - (1 / 4) * emF2 g hnd F := by
    intro l
    unfold emT
    rw [g_emA_emA e he hnd F, he, eta_apply]
    simp only [ite_true]
    rw [mul_sub, Finset.mul_sum]
    have := etaDiag_mul_self l
    rw [Finset.sum_congr rfl fun k _ => show etaDiag l * (etaDiag k * F (e l) (e k) * F (e l) (e k)) =
      etaDiag l * etaDiag k * F (e l) (e k) ^ 2 by ring]
    linear_combination (-(1 / 4) * emF2 g hnd F) * this
  simp only [h1, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [← emF2_frame e he hnd F hF]
  push_cast
  ring

/-- **The strong energy condition of the electromagnetic field in dimension `n = m + 1 ≥ 3`** (Kontou and Sanders, §2.3,
eqs. (37)-(38)): `(T − tr_g T/(n − 2) · g)(v, v) ≥ 0` for timelike `v`, for a continuous form `T` equal to `emT`. -/
theorem em_strongEC_dim {m : ℕ} (hm : 2 ≤ m) (hg : IsLorentzianForm (m + 1) g) (hF : ∀ v w, F v w = -F w v)
    {T : V →L[ℝ] V →L[ℝ] ℝ} (hT : ∀ v w, T v w = emT g hnd F v w) (v : V) (hv : g v v < 0) :
    0 ≤ T v v - (1 / ((m : ℝ) - 1)) * traceG g T hg.bilinForm_nondegenerate * g v v := by
  set s := Real.sqrt (-g v v) with hs
  have hs0 : 0 < s := Real.sqrt_pos.2 (by linarith)
  have hs2 : s * s = -g v v := Real.mul_self_sqrt (by linarith)
  have huu : g (s⁻¹ • v) (s⁻¹ • v) = -1 := by
    simp only [map_smul, smul_apply, smul_eq_mul]
    field_simp
    linarith
  obtain ⟨e, he, he0⟩ := exists_frame_of_timelike hg huu
  have hvu : v = s • e 0 := by rw [he0, smul_smul, mul_inv_cancel₀ hs0.ne', one_smul]
  have htr : traceG g T hg.bilinForm_nondegenerate = (1 - ((m : ℝ) + 1) / 4) * emF2 g hnd F := by
    rw [traceG_eq_sum g T _ e he]
    simp only [hT]
    exact emT_trace_frame hnd e he hF
  rw [htr, hT, hvu, emT_smul, emT_frame_00 hnd e he hF, emF2_split hnd e he hF]
  have hgv : g (s • e 0) (s • e 0) = -(s * s) := by
    simp only [map_smul, smul_apply, smul_eq_mul, he, eta_apply, ite_true, etaDiag]
    simp
  rw [hgv]
  set Q := ∑ i : Fin m, F (e 0) (e i.succ) ^ 2
  set N := ∑ i : Fin m, ∑ j : Fin m, F (e i.succ) (e j.succ) ^ 2
  have hQ : 0 ≤ Q := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hN : 0 ≤ N := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _
  have hm1 : (1 : ℝ) ≤ (m : ℝ) - 1 := by
    have : (2 : ℝ) ≤ m := by exact_mod_cast hm
    linarith
  have hm0 : (0 : ℝ) < (m : ℝ) - 1 := by linarith
  have key : s * s * ((1 / 2) * Q + (1 / 4) * N) -
      1 / ((m : ℝ) - 1) * ((1 - ((m : ℝ) + 1) / 4) * (-2 * Q + N)) * -(s * s) =
      s * s * ((((m : ℝ) - 2) / ((m : ℝ) - 1)) * Q + (1 / (2 * ((m : ℝ) - 1))) * N) := by
    field_simp
    ring
  rw [key]
  have hcoef1 : 0 ≤ ((m : ℝ) - 2) / ((m : ℝ) - 1) := by
    apply div_nonneg _ hm0.le
    have : (2 : ℝ) ≤ m := by exact_mod_cast hm
    linarith
  have hcoef2 : 0 ≤ 1 / (2 * ((m : ℝ) - 1)) := by positivity
  have := mul_self_nonneg s
  positivity

end EMDominant
end Lightlike
