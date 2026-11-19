import Lightlike.FieldTheory.Forest.Partial
import Lightlike.FieldTheory.Forest.Graph
import Lightlike.FieldTheory.Forest.Cube
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# The Brydges–Kennedy Taylor forest formula

For a smooth function `H` from `ℝ^{P_n}` to a Banach space, `P_n` the links (unordered pairs of distinct points)
of `{1, …, n}` (Abdesselam–Rivasseau, *Trees, forests and jungles*, hep-th/9409094, Theorem III.1, eq. (III.2),
p. 13):

`H(1) = ∑_F ∫_{[0,1]^F} ∏_{l ∈ F} dh_l (∏_{l ∈ F} ∂/∂x_l) H (X^F(h))`,

the sum over the forests `F` (`forests`), `X^F(h)_l = h^F_l(h)` the infimum of the `h` along the path of `F` joining
the ends of `l`, and `0` if there is none (`forestPoint`; the ultrametric `ultra` of `Graph.lean`).

`forest_formula_restrict` is (III.2) with the integral over `[0,1]^F`; `forest_formula` writes it as the integral over
the whole cube `[0,1]^{P_n}` of a function of the coordinates in `F` only. The proof is Gurau–Rivasseau–Sfondrini's
(*Renormalization: an advanced overview*, arXiv:1401.5003, proof of Theorem 6.1, pp. 107-109), an iterated Taylor
interpolation of the entries between different clusters of the current forest, here as an induction on the
number of links without orderings: with `T_k = ∑_{|F| = k} ∫ (∂^F H)(Y^F)`, `Y^F` the point with the entries between
different clusters of `F` equal to `min_F h` (`stepTerm`), the fundamental theorem of calculus in that common entry
gives `T_k = ∑_{|F| = k} ∫ (∂^F H)(X^F) + T_{k+1}` (`T_succ`): the new link is the one with the smallest parameter
(`interp_insert_update`), and ties have measure zero.

## Main results

* `forest_formula_restrict`: the forest formula (III.2), the integrals over `[0,1]^F`.
* `forest_formula`: the same with the integrals over the whole cube `[0,1]^{P_n}`.
* `forestPoint_eq_path_inf`: `X^F(h)_l` is the infimum of the `h` along the path of `F` joining the ends of `l`.
* `T_succ`: the Taylor step `T_k = ∑_{|F| = k} ∫ (∂^F H)(X^F) + T_{k+1}`.

## References

* A. Abdesselam, V. Rivasseau, arXiv:hep-th/9409094, Theorem III.1, eq. (III.2), p. 13.
* R. Gurau, V. Rivasseau, A. Sfondrini, arXiv:1401.5003, Theorem 6.1, eq. (6.1), p. 107, and its proof, pp. 107-109.
-/

open MeasureTheory Set Function Finset
open scoped ContDiff

namespace Lightlike.FieldTheory.Forest

variable {n : ℕ}

lemma link_cases (e : Link n) : ∃ a b : Fin n, a ≠ b ∧ e.1 = s(a, b) := by
  obtain ⟨e, he⟩ := e
  induction e using Sym2.ind with
  | _ a b => exact ⟨a, b, fun h => he (Sym2.mk_isDiag_iff.2 h), rfl⟩

lemma linked_iff_of_eq {S : Finset (Link n)} {e : Link n} {a b : Fin n} (h : e.1 = s(a, b)) :
    Linked S e ↔ Joined S a b := by
  unfold Linked; rw [h]; rfl

lemma ultraL_of_eq {F : Finset (Link n)} {w : Link n → ℝ} {e : Link n} {a b : Fin n} (h : e.1 = s(a, b)) :
    ultraL F w e = ultra F w a b := by
  unfold ultraL; rw [h]; rfl

lemma ultra_le_of_eqOn {F : Finset (Link n)} {w w' : Link n → ℝ} (h : ∀ l ∈ F, w l = w' l) (a b : Fin n) :
    ultra F w a b ≤ ultra F w' a b := by
  have habove : ∀ t, above F w t = above F w' t := fun t => by
    ext m; simp only [mem_above]; exact and_congr_right fun hm => by rw [h m hm]
  rcases ultra_cases F w a b with h0 | ⟨l, hl, hj, he⟩
  · rw [h0]; exact ultra_nonneg _ _ _ _
  · rw [habove, h l hl] at hj
    rw [he, h l hl]
    exact le_ultra hl hj

/-- The ultrametric of `F` depends only on the parameters of the links of `F`. -/
lemma ultra_congr {F : Finset (Link n)} {w w' : Link n → ℝ} (h : ∀ l ∈ F, w l = w' l) (a b : Fin n) :
    ultra F w a b = ultra F w' a b :=
  le_antisymm (ultra_le_of_eqOn h a b) (ultra_le_of_eqOn (fun l hl => (h l hl).symm) a b)

/-- `interp F w s`: on the links whose ends `F` joins, the ultrametric of `F`; on the others, `s`. -/
noncomputable def interp (F : Finset (Link n)) (w : Link n → ℝ) (s : ℝ) : Link n → ℝ := by
  classical exact fun e => if Linked F e then ultraL F w e else s

/-- **The point `X^F(w)`** of (III.2): the ultrametric of `F` on the links whose ends `F` joins, `0` on the others. -/
noncomputable def forestPoint (F : Finset (Link n)) (w : Link n → ℝ) : Link n → ℝ := interp F w 0

lemma interp_of_linked {F : Finset (Link n)} {w : Link n → ℝ} {s : ℝ} {e : Link n} (h : Linked F e) :
    interp F w s e = ultraL F w e := by
  classical simp [interp, h]

lemma interp_of_not_linked {F : Finset (Link n)} {w : Link n → ℝ} {s : ℝ} {e : Link n} (h : ¬ Linked F e) :
    interp F w s e = s := by
  classical simp [interp, h]

/-- The links whose ends `F` does not join. -/
noncomputable def transLinks (F : Finset (Link n)) : Finset (Link n) := by
  classical exact univ.filter fun e => ¬ Linked F e

lemma mem_transLinks {F : Finset (Link n)} {e : Link n} : e ∈ transLinks F ↔ ¬ Linked F e := by
  classical simp [transLinks]

lemma notMem_of_mem_transLinks {F : Finset (Link n)} {e : Link n} (he : e ∈ transLinks F) : e ∉ F :=
  fun h => mem_transLinks.1 he (linked_of_mem h)

lemma interp_eq (F : Finset (Link n)) (w : Link n → ℝ) (s : ℝ) :
    interp F w s = interp F w 0 + s • ∑ e ∈ transLinks F, Pi.single e (1 : ℝ) := by
  classical
  funext e
  simp only [Pi.add_apply, Pi.smul_apply, Finset.sum_apply, smul_eq_mul, Pi.single_apply]
  by_cases he : Linked F e
  · have : e ∉ transLinks F := fun h => mem_transLinks.1 h he
    rw [interp_of_linked he, interp_of_linked he, Finset.sum_ite_eq]
    simp [this]
  · have : e ∈ transLinks F := mem_transLinks.2 he
    rw [interp_of_not_linked he, interp_of_not_linked he, Finset.sum_ite_eq]
    simp [this]

lemma continuous_interp_s (F : Finset (Link n)) (w : Link n → ℝ) : Continuous fun s : ℝ => interp F w s := by
  rw [show (fun s : ℝ => interp F w s) = fun s => interp F w 0 + s • ∑ e ∈ transLinks F, Pi.single e (1 : ℝ) from
    funext (interp_eq F w)]
  exact continuous_const.add (continuous_id.smul continuous_const)

lemma continuous_interp {F : Finset (Link n)} (hF : IsForest F) {s : (Link n → ℝ) → ℝ} (hs : Continuous s) :
    Continuous fun w => interp F w (s w) := by
  refine continuous_pi fun f => ?_
  obtain ⟨a, b, hab, hf⟩ := link_cases f
  by_cases h : Linked F f
  · simp only [interp_of_linked h, ultraL_of_eq hf]
    exact continuous_ultra hF hab ((linked_iff_of_eq hf).1 h)
  · simp only [interp_of_not_linked h]
    exact hs

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]

omit [CompleteSpace V] in
/-- Along the common entry `s` of the links between different clusters of `F`. -/
lemma hasDerivAt_interp {K : (Link n → ℝ) → V} (hK : ContDiff ℝ ∞ K) (F : Finset (Link n)) (w : Link n → ℝ)
    (s : ℝ) :
    HasDerivAt (fun s => K (interp F w s)) (∑ e ∈ transLinks F, pd e K (interp F w s)) s := by
  set v : Link n → ℝ := ∑ e ∈ transLinks F, Pi.single e (1 : ℝ)
  have h1 : HasDerivAt (fun s : ℝ => interp F w s) v s := by
    have h : HasDerivAt (fun y : ℝ => interp F w 0 + y • v) v s := by
      simpa using ((hasDerivAt_id s).smul_const v).const_add (interp F w 0)
    have he : (fun s : ℝ => interp F w s) = fun y : ℝ => interp F w 0 + y • v := funext (interp_eq F w)
    rw [he]; exact h
  have h2 := ((hK.differentiable (by simp)).differentiableAt (x := interp F w s)).hasFDerivAt.comp_hasDerivAt s h1
  rw [fderiv_sum_single] at h2
  exact h2

/-- The integrand of `T_k`: `(∏_{l ∈ F} ∂_l H)` at the point with the entries between different clusters of `F`
equal to `min_{l ∈ F} w_l`. -/
noncomputable def stepTerm (H : (Link n → ℝ) → V) (F : Finset (Link n)) (w : Link n → ℝ) : V :=
  pdF F H (interp F w (minF F w))

/-- **The Taylor step**: the fundamental theorem of calculus in the common entry. -/
lemma stepTerm_eq {H : (Link n → ℝ) → V} (hH : ContDiff ℝ ∞ H) (F : Finset (Link n)) (w : Link n → ℝ) :
    stepTerm H F w = pdF F H (forestPoint F w) +
      ∑ e ∈ transLinks F, ∫ s in (0 : ℝ)..minF F w, pdF (insert e F) H (interp F w s) := by
  have hK := contDiff_pdF hH F
  have hd : ∀ s, HasDerivAt (fun s => pdF F H (interp F w s))
      (∑ e ∈ transLinks F, pdF (insert e F) H (interp F w s)) s := fun s =>
    (hasDerivAt_interp hK F w s).congr_deriv (Finset.sum_congr rfl fun e he => by
      rw [pdF_insert hH (notMem_of_mem_transLinks he)])
  have hc : ∀ e, Continuous fun s => pdF (insert e F) H (interp F w s) := fun e =>
    (contDiff_pdF hH _).continuous.comp (continuous_interp_s F w)
  rw [← intervalIntegral.integral_finsetSum fun e _ => (hc e).intervalIntegrable _ _,
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hd s)
      ((continuous_finsetSum _ fun e _ => hc e).intervalIntegrable _ _), stepTerm, forestPoint]
  abel

/-- **The new link is the one with the smallest parameter**: for `0 ≤ s ≤ min_F y` and `e` between different
clusters of `F`, the point of `{e} ∪ F` at the parameters `y` with `y_e` replaced by `s` is the point of `F` with the
common entry `s`. -/
lemma interp_insert_update {F : Finset (Link n)} {e : Link n} (he : ¬ Linked F e) {y : Link n → ℝ} {s : ℝ}
    (hs0 : 0 ≤ s) (hs : s ≤ minF F y) :
    interp (insert e F) (update y e s) (minF (insert e F) (update y e s)) = interp F y s := by
  have heF : e ∉ F := fun h => he (linked_of_mem h)
  have hupd : ∀ m ∈ F, update y e s m = y m := fun m hm => update_of_ne (by rintro rfl; exact heF hm) s y
  have hmin : ∀ m ∈ F, update y e s e ≤ update y e s m := fun m hm => by
    rw [update_self, hupd m hm]; exact hs.trans (minF_le hm)
  rw [minF_insert_update heF hs]
  funext f
  obtain ⟨a, b, hab, hf⟩ := link_cases f
  by_cases hj : Joined F a b
  · have h1 : Linked F f := (linked_iff_of_eq hf).2 hj
    rw [interp_of_linked h1, interp_of_linked (h1.mono (subset_insert _ _)), ultraL_of_eq hf, ultraL_of_eq hf,
      ultra_insert_of_joined heF hmin hab hj]
    exact ultra_congr hupd a b
  · rw [interp_of_not_linked fun h => hj ((linked_iff_of_eq hf).1 h)]
    by_cases hj' : Joined (insert e F) a b
    · rw [interp_of_linked ((linked_iff_of_eq hf).2 hj'), ultraL_of_eq hf,
        ultra_insert_of_not_joined heF hmin (by rw [update_self]; exact hs0) hj hj', update_self]
    · rw [interp_of_not_linked fun h => hj' ((linked_iff_of_eq hf).1 h)]

omit [CompleteSpace V] in
lemma integrable_stepTerm {H : (Link n → ℝ) → V} (hH : ContDiff ℝ ∞ H) {F : Finset (Link n)} (hF : IsForest F) :
    Integrable (stepTerm H F) (cube (Link n)) :=
  integrable_cube_of_continuous ((contDiff_pdF hH F).continuous.comp (continuous_interp hF (continuous_minF F)))

omit [CompleteSpace V] in
lemma integrable_forestPoint {H : (Link n → ℝ) → V} (hH : ContDiff ℝ ∞ H) {F : Finset (Link n)} (hF : IsForest F) :
    Integrable (fun w => pdF F H (forestPoint F w)) (cube (Link n)) :=
  integrable_cube_of_continuous ((contDiff_pdF hH F).continuous.comp (continuous_interp hF continuous_const))

/-- The Taylor step integrated over the cube. -/
lemma integral_step {H : (Link n → ℝ) → V} (hH : ContDiff ℝ ∞ H) {F : Finset (Link n)} (hF : IsForest F) :
    ∫ w, stepTerm H F w ∂cube (Link n) = ∫ w, pdF F H (forestPoint F w) ∂cube (Link n) +
      ∑ e ∈ transLinks F, ∫ w, indicator {w | ∀ m ∈ F, w e < w m} (stepTerm H (insert e F)) w ∂cube (Link n) := by
  have hforest : ∀ e ∈ transLinks F, IsForest (insert e F) := fun e he =>
    (isForest_insert_iff hF (notMem_of_mem_transLinks he)).2 (mem_transLinks.1 he)
  have hae : stepTerm H F =ᵐ[cube (Link n)] fun w => pdF F H (forestPoint F w) +
      ∑ e ∈ transLinks F, ∫ s in (0 : ℝ)..minF F w, stepTerm H (insert e F) (update w e s) := by
    filter_upwards [ae_cube_mem] with y hy
    rw [stepTerm_eq hH F y]
    congr 1
    refine Finset.sum_congr rfl fun e he => ?_
    have hm := minF_mem_Icc (F := F) hy
    refine intervalIntegral.integral_congr fun s hs => ?_
    rw [uIcc_of_le hm.1] at hs
    simp only [stepTerm]
    rw [interp_insert_update (mem_transLinks.1 he) hs.1 hs.2]
  have hint : ∀ e ∈ transLinks F, Integrable (fun y => ∫ s in (0 : ℝ)..minF F y,
      stepTerm H (insert e F) (update y e s)) (cube (Link n)) := fun e he =>
    integrable_argmin (notMem_of_mem_transLinks he) (integrable_stepTerm hH (hforest e he))
  rw [integral_congr_ae hae, integral_add (integrable_forestPoint hH hF) (integrable_finsetSum _ hint),
    integral_finsetSum _ hint]
  congr 1
  refine Finset.sum_congr rfl fun e he => ?_
  exact (integral_indicator_argmin (notMem_of_mem_transLinks he) (integrable_stepTerm hH (hforest e he))).symm

/-- The forests of `Fin n`. -/
noncomputable def forests (n : ℕ) : Finset (Finset (Link n)) := by
  classical exact univ.filter IsForest

lemma mem_forests {F : Finset (Link n)} : F ∈ forests n ↔ IsForest F := by
  classical simp [forests]

/-- The forests with `k` links. -/
noncomputable def forestsCard (n k : ℕ) : Finset (Finset (Link n)) := (forests n).filter fun F => F.card = k

lemma mem_forestsCard {F : Finset (Link n)} {k : ℕ} : F ∈ forestsCard n k ↔ IsForest F ∧ F.card = k := by
  simp [forestsCard, mem_forests]

lemma isForest_empty : IsForest (∅ : Finset (Link n)) := by
  have : graphOf (∅ : Finset (Link n)) = ⊥ := by
    rw [graphOf]
    have hs : {e : Sym2 (Fin n) | ∃ l ∈ (∅ : Finset (Link n)), l.1 = e} = ∅ := by ext e; simp
    rw [hs, SimpleGraph.fromEdgeSet_empty]
  unfold IsForest
  rw [this]
  exact SimpleGraph.isAcyclic_bot

/-- `T_k = ∑_{|F| = k} ∫ (∂^F H)(Y^F)`. -/
noncomputable def T (H : (Link n → ℝ) → V) (k : ℕ) : V :=
  ∑ F ∈ forestsCard n k, ∫ w, stepTerm H F w ∂cube (Link n)

/-- **The recursion** `T_k = ∑_{|F| = k} ∫ (∂^F H)(X^F) + T_{k+1}`. -/
lemma T_succ {H : (Link n → ℝ) → V} (hH : ContDiff ℝ ∞ H) (k : ℕ) :
    T H k = ∑ F ∈ forestsCard n k, ∫ w, pdF F H (forestPoint F w) ∂cube (Link n) + T H (k + 1) := by
  unfold T
  rw [Finset.sum_congr rfl fun F hF => integral_step hH (mem_forestsCard.1 hF).1, Finset.sum_add_distrib]
  congr 1
  have hne : ∀ F' ∈ forestsCard n (k + 1), F'.Nonempty := fun F' hF' => by
    rw [← Finset.card_pos, (mem_forestsCard.1 hF').2]; exact Nat.succ_pos k
  rw [Finset.sum_congr rfl fun F' hF' => integral_eq_sum_argmin (hne F' hF')
    (integrable_stepTerm hH (mem_forestsCard.1 hF').1), Finset.sum_sigma', Finset.sum_sigma']
  refine Finset.sum_bij' (fun p _ => ⟨insert p.2 p.1, p.2⟩) (fun p _ => ⟨p.1.erase p.2, p.2⟩) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨F, e⟩ hp
    rw [Finset.mem_sigma, mem_forestsCard] at hp ⊢
    obtain ⟨⟨hF, hk⟩, he⟩ := hp
    have heF := notMem_of_mem_transLinks he
    exact ⟨⟨(isForest_insert_iff hF heF).2 (mem_transLinks.1 he), by rw [card_insert_of_notMem heF, hk]⟩,
      mem_insert_self _ _⟩
  · rintro ⟨F', e⟩ hp
    rw [Finset.mem_sigma, mem_forestsCard] at hp ⊢
    obtain ⟨⟨hF', hk⟩, he⟩ := hp
    have hFe : IsForest (F'.erase e) := SimpleGraph.IsAcyclic.anti (graphOf_mono (erase_subset e F')) hF'
    refine ⟨⟨hFe, by rw [card_erase_of_mem he, hk]; rfl⟩, mem_transLinks.2 ?_⟩
    have := (isForest_insert_iff hFe (notMem_erase e F')).1
    rw [insert_erase he] at this
    exact this hF'
  · rintro ⟨F, e⟩ hp
    rw [Finset.mem_sigma] at hp
    simp only [erase_insert (notMem_of_mem_transLinks hp.2)]
  · rintro ⟨F', e⟩ hp
    rw [Finset.mem_sigma] at hp
    simp only [insert_erase hp.2]
  · rintro ⟨F, e⟩ hp
    rw [Finset.mem_sigma] at hp
    have heF := notMem_of_mem_transLinks hp.2
    have hset : {w : Link n → ℝ | ∀ m ∈ F, w e < w m} = {w | ∀ m ∈ insert e F, m ≠ e → w e < w m} := by
      ext w
      simp only [mem_ofPred_eq, Finset.mem_insert]
      constructor
      · rintro h m (rfl | hm) hne
        · exact absurd rfl hne
        · exact h m hm
      · intro h m hm
        exact h m (Or.inr hm) (by rintro rfl; exact heF hm)
    simp only
    rw [hset]

lemma T_zero {H : (Link n → ℝ) → V} : T H 0 = H fun _ => 1 := by
  have h0 : forestsCard n 0 = {∅} := by
    ext F
    rw [mem_forestsCard, Finset.mem_singleton, Finset.card_eq_zero]
    exact ⟨fun h => h.2, by rintro rfl; exact ⟨isForest_empty, rfl⟩⟩
  have hp : ∀ w : Link n → ℝ, interp ∅ w (minF ∅ w) = fun _ => 1 := fun w => by
    funext e
    obtain ⟨a, b, hab, he⟩ := link_cases e
    rw [interp_of_not_linked fun h => ?_]
    · simp [minF]
    · obtain ⟨l, hl⟩ := nonempty_of_joined hab ((linked_iff_of_eq he).1 h)
      simp at hl
  simp [T, h0, stepTerm, hp]

omit [CompleteSpace V] in
lemma T_eq_zero {H : (Link n → ℝ) → V} {k : ℕ} (hk : Fintype.card (Link n) < k) : T H k = 0 := by
  have : forestsCard n k = ∅ := by
    ext F
    simp only [mem_forestsCard, Finset.notMem_empty, iff_false, not_and]
    intro _ h
    exact absurd (h ▸ card_le_univ F) (not_le.2 hk)
  simp [T, this]

/-- **The Brydges–Kennedy Taylor forest formula** (Abdesselam–Rivasseau, Theorem III.1, eq. (III.2), p. 13): for
`H` smooth from `ℝ^{P_n}` to a Banach space,
`H(1) = ∑_F ∫_{[0,1]^{P_n}} (∏_{l ∈ F} ∂/∂x_l) H (X^F(h)) dh`, the integrand depending only on the `h_l`, `l ∈ F`. -/
theorem forest_formula {H : (Link n → ℝ) → V} (hH : ContDiff ℝ ∞ H) :
    H (fun _ => 1) = ∑ F ∈ forests n, ∫ h, pdF F H (forestPoint F h) ∂cube (Link n) := by
  have hT : ∀ N : ℕ, T H 0 = ∑ k ∈ range N, ∑ F ∈ forestsCard n k,
      ∫ w, pdF F H (forestPoint F w) ∂cube (Link n) + T H N := by
    intro N
    induction N with
    | zero => simp
    | succ N ih => rw [ih, T_succ hH N, Finset.sum_range_succ]; abel
  have h := hT (Fintype.card (Link n) + 1)
  rw [T_zero, T_eq_zero (Nat.lt_succ_self _), add_zero] at h
  rw [h, ← Finset.sum_fiberwise_of_maps_to (s := forests n) (t := range (Fintype.card (Link n) + 1))
    (g := Finset.card) fun F _ => mem_range.2 (Nat.lt_succ_of_le (card_le_univ F))]
  rfl

/-- `X^F(w)` depends only on the parameters of the links of `F`. -/
lemma forestPoint_congr {F : Finset (Link n)} {w w' : Link n → ℝ} (h : ∀ l ∈ F, w l = w' l) :
    forestPoint F w = forestPoint F w' := by
  funext e
  obtain ⟨a, b, -, he⟩ := link_cases e
  by_cases hl : Linked F e
  · rw [forestPoint, forestPoint, interp_of_linked hl, interp_of_linked hl, ultraL_of_eq he, ultraL_of_eq he]
    exact ultra_congr h a b
  · rw [forestPoint, forestPoint, interp_of_not_linked hl, interp_of_not_linked hl]

/-- **`X^F` is the infimum along the path** (Abdesselam–Rivasseau, p. 3): for parameters `h ≥ 0` and a link `{a, b}`
whose ends `F` joins, `X^F(h)_{ab}` is the smallest `h_l` on the path of `F` from `a` to `b`. -/
lemma forestPoint_eq_path_inf {F : Finset (Link n)} (hF : IsForest F) {w : Link n → ℝ} (hw : ∀ l, 0 ≤ w l)
    {e : Link n} {a b : Fin n} (he : e.1 = s(a, b)) (p : (graphOf F).Walk a b) (hp : p.IsPath) :
    ∃ hab : a ≠ b, forestPoint F w e = (walkLinks F p).inf' (walkLinks_nonempty hab p) w := by
  have hab : a ≠ b := fun h => e.2 (by rw [he, h]; exact Sym2.mk_isDiag_iff.2 rfl)
  refine ⟨hab, ?_⟩
  rw [forestPoint, interp_of_linked ((linked_iff_of_eq he).2 ⟨p⟩), ultraL_of_eq he, ultra_eq_path_inf hF hab p hp]
  exact max_eq_right (Finset.le_inf' _ _ fun l _ => hw l)

/-- `X^F(h)_l = 0` on the links whose ends `F` does not join (Abdesselam–Rivasseau, p. 3). -/
lemma forestPoint_of_not_linked {F : Finset (Link n)} {w : Link n → ℝ} {e : Link n} (h : ¬ Linked F e) :
    forestPoint F w e = 0 :=
  interp_of_not_linked h

/-- **The Brydges–Kennedy Taylor forest formula over `[0, 1]^F`** (Abdesselam–Rivasseau, Theorem III.1, eq. (III.2),
p. 13): `H(1) = ∑_F ∫_{[0,1]^F} ∏_{l ∈ F} dh_l (∏_{l ∈ F} ∂/∂x_l) H (X^F(h))`, `h : F → ℝ` extended by `0`. -/
theorem forest_formula_restrict {H : (Link n → ℝ) → V} (hH : ContDiff ℝ ∞ H) :
    H (fun _ => 1) = ∑ F ∈ forests n,
      ∫ h, pdF F H (forestPoint F (extendF F h)) ∂(Measure.pi fun _ : F => unif) := by
  rw [forest_formula hH]
  refine Finset.sum_congr rfl fun F hF => ?_
  have hmp := measurePreserving_restrictF (ι := Link n) F
  have hc : Continuous fun h : F → ℝ => pdF F H (forestPoint F (extendF F h)) :=
    (contDiff_pdF hH F).continuous.comp ((continuous_interp (mem_forests.1 hF) continuous_const).comp
      (continuous_extendF F))
  rw [← hmp.map_eq, integral_map hmp.measurable.aemeasurable hc.aestronglyMeasurable]
  refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
  simp only
  rw [forestPoint_congr (w := w) (w' := extendF F fun l : F => w l) fun l hl => by rw [extendF_apply _ hl]]

end Lightlike.FieldTheory.Forest
