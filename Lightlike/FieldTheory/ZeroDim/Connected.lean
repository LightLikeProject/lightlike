import Lightlike.FieldTheory.ZeroDim.Graphs
import Mathlib.RingTheory.PowerSeries.Exp
import Mathlib.RingTheory.PowerSeries.Substitution
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Algebra.BigOperators.Field

/-!
# Connected vacuum graphs: the exponential formula

Borinsky, *Graphs in perturbation theory*, arXiv:1807.02046v1, Theorem 2.4.1, eq. (2.4.7), p. 18: the sum of all
graphs weighted by `1/|Aut Γ|` is the exponential of the sum of the connected ones, `X = e^{X_c}`, `X_c = log X`; in
zero-dimensional field theory, p. 117 (Chapter 7), `W = ħ log Z` generates the connected diagrams "as stated in
Theorem 2.4.1".

Here for the vacuum graphs of the quartic theory, with vertices `V` and half-edges `V × Fin 4`:
* a pairing of the half-edges at a vertex set `S` (`pairOn S`) is an involution of `V × Fin 4` whose fixed points are
  exactly the half-edges off `S`; `S` is *closed* under it if no edge leaves `S`, and the pairing is *connected* on
  `S` (`ConnOn`) if `S` is nonempty and has no closed subsets but `∅` and `S`;
* `existsUnique_component`: every vertex lies in exactly one closed connected set (its component);
* `card_pairOn_eq_sum`: splitting off the component of a vertex,
  `#pairings(R) = ∑_{v₀ ∈ S ⊆ R} #connected(S) · #pairings(R \ S)`;
* `numPairings_succ`: `a_{n+1} = ∑_k C(n, k) c_{k+1} a_{n-k}` for the numbers `a_n`, `c_n` of pairings and of
  connected pairings of `n` vertices;
* `vacuumSeries_eq_exp`: `Z = exp(W)` for `Z = ∑ a_n xⁿ/(24ⁿ n!)` and `W = ∑ c_n xⁿ/(24ⁿ n!)`, the generating series
  of all and of connected vacuum graphs with their symmetry factors (`sum_inv_aut`: `a_n/(24ⁿ n!)` is the sum of
  `1/|Aut Γ|` over the vacuum graphs with `n` vertices, and `coeff_connectedSeries` in `ConnectedGraphs` does the
  same for `c_n` and the connected graphs); `derivative_vacuumSeries`: `Z' = W' Z`.

Difference from the source (weaker): Theorem 2.4.1 is an identity in Borinsky's algebra `G` of formal sums of all
graphs (any vertex degrees, with legs), and p. 117 states `W = ħ log Z` for a general potential `V` with a source `j`;
here it is proved for the four-valent vacuum graphs only (the quartic potential, `j = 0`), as an identity of power
series in which a graph `Γ` counts as `x^{|V_Γ|}` (for four-valent vacuum graphs `|E_Γ| - |V_Γ| = |V_Γ|`, so this is
also Borinsky's counting by the excess, `ħ`).
-/

open Finset Function
open scoped Nat

noncomputable section

namespace Lightlike.FieldTheory

section Decomposition

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A set `S` of vertices is **closed** under `f` if `f` sends the half-edges at `S` to half-edges at `S`. -/
def Closed (f : V × Fin 4 → V × Fin 4) (S : Finset V) : Prop :=
  ∀ h : V × Fin 4, h.1 ∈ S → (f h).1 ∈ S

/-- `f` is **connected on** `S`: `S` is nonempty and its only closed subsets are `∅` and `S`. -/
def ConnOn (f : V × Fin 4 → V × Fin 4) (S : Finset V) : Prop :=
  S.Nonempty ∧ ∀ T ⊆ S, Closed f T → T = ∅ ∨ T = S

open Classical in
/-- The **pairings of the half-edges at `S`**: involutions of `V × Fin 4` whose fixed points are exactly the
half-edges at the vertices off `S`. -/
def pairOn (S : Finset V) : Finset (V × Fin 4 → V × Fin 4) :=
  univ.filter fun f => Involutive f ∧ ∀ h, f h = h ↔ h.1 ∉ S

open Classical in
/-- The **connected pairings** of the half-edges at `S`. -/
def connPairOn (S : Finset V) : Finset (V × Fin 4 → V × Fin 4) :=
  (pairOn S).filter fun f => ConnOn f S

lemma mem_pairOn {S : Finset V} {f : V × Fin 4 → V × Fin 4} :
    f ∈ pairOn S ↔ Involutive f ∧ ∀ h, f h = h ↔ h.1 ∉ S := by
  simp [pairOn]

lemma closed_of_mem_pairOn {S : Finset V} {f : V × Fin 4 → V × Fin 4} (hf : f ∈ pairOn S) : Closed f S := by
  intro h hh
  rw [mem_pairOn] at hf
  by_contra hc
  have h1 : f (f h) = f h := (hf.2 (f h)).2 hc
  rw [hf.1 h] at h1
  exact (hf.2 h).1 h1.symm hh

lemma Closed.inter {f : V × Fin 4 → V × Fin 4} {S T : Finset V} (hS : Closed f S) (hT : Closed f T) :
    Closed f (S ∩ T) :=
  fun h hh => mem_inter.2 ⟨hS h (mem_inter.1 hh).1, hT h (mem_inter.1 hh).2⟩

lemma Closed.sdiff {f : V × Fin 4 → V × Fin 4} (hf : Involutive f) {S T : Finset V} (hS : Closed f S)
    (hT : Closed f T) : Closed f (S \ T) := by
  intro h hh
  rw [mem_sdiff] at hh ⊢
  refine ⟨hS h hh.1, fun hc => hh.2 ?_⟩
  have := hT (f h) hc
  rwa [hf h] at this

/-- **The component of a vertex**: for a pairing of the half-edges at `R` and `v₀ ∈ R`, exactly one `S ⊆ R`
containing `v₀` is closed and connected. -/
theorem existsUnique_component {R : Finset V} {f : V × Fin 4 → V × Fin 4} (hf : f ∈ pairOn R) {v₀ : V}
    (hv : v₀ ∈ R) : ∃! S : Finset V, (S ⊆ R ∧ v₀ ∈ S) ∧ Closed f S ∧ ConnOn f S := by
  classical
  have hinv := (mem_pairOn.1 hf).1
  have hR : R ∈ R.powerset.filter fun T => v₀ ∈ T ∧ Closed f T :=
    mem_filter.2 ⟨mem_powerset_self R, hv, closed_of_mem_pairOn hf⟩
  obtain ⟨S, hS𝒞, hmin⟩ := (R.powerset.filter fun T => v₀ ∈ T ∧ Closed f T).exists_min_image card ⟨R, hR⟩
  simp only [mem_filter, mem_powerset] at hS𝒞 hmin
  obtain ⟨hSR, hvS, hSc⟩ := hS𝒞
  have hconn : ConnOn f S := by
    refine ⟨⟨v₀, hvS⟩, fun T hTS hTc => ?_⟩
    by_cases hvT : v₀ ∈ T
    · exact Or.inr (eq_of_subset_of_card_le hTS (hmin T ⟨hTS.trans hSR, hvT, hTc⟩))
    · left
      have hd : S \ T = S := eq_of_subset_of_card_le sdiff_subset
        (hmin (S \ T) ⟨sdiff_subset.trans hSR, mem_sdiff.2 ⟨hvS, hvT⟩, hSc.sdiff hinv hTc⟩)
      refine eq_empty_of_forall_notMem fun x hx => ?_
      have hx' : x ∈ S \ T := by rw [hd]; exact hTS hx
      exact (mem_sdiff.1 hx').2 hx
  refine ⟨S, ⟨⟨hSR, hvS⟩, hSc, hconn⟩, fun S' hS' => ?_⟩
  obtain ⟨⟨-, hvS'⟩, hS'c, hS'conn⟩ := hS'
  have hv' : v₀ ∈ S' ∩ S := mem_inter.2 ⟨hvS', hvS⟩
  have h1 : S' ∩ S = S' := by
    rcases hS'conn.2 (S' ∩ S) inter_subset_left (hS'c.inter hSc) with h | h
    · rw [h] at hv'; exact absurd hv' (notMem_empty _)
    · exact h
  have h2 : S ∩ S' = S := by
    rcases hconn.2 (S ∩ S') inter_subset_left (hSc.inter hS'c) with h | h
    · rw [inter_comm, h] at hv'; exact absurd hv' (notMem_empty _)
    · exact h
  refine Subset.antisymm ?_ ?_
  · rw [← h1]; exact inter_subset_right
  · rw [← h2]; exact inter_subset_right

/-- `f` on the half-edges at `S`, the identity elsewhere. -/
def restrictTo (f : V × Fin 4 → V × Fin 4) (S : Finset V) : V × Fin 4 → V × Fin 4 :=
  fun h => if h.1 ∈ S then f h else h

/-- `g` on the half-edges at `S`, `k` elsewhere. -/
def glue (S : Finset V) (g k : V × Fin 4 → V × Fin 4) : V × Fin 4 → V × Fin 4 :=
  fun h => if h.1 ∈ S then g h else k h

lemma restrictTo_mem {R T : Finset V} {f : V × Fin 4 → V × Fin 4} (hf : f ∈ pairOn R) (hTR : T ⊆ R)
    (hT : Closed f T) : restrictTo f T ∈ pairOn T := by
  rw [mem_pairOn] at hf ⊢
  refine ⟨fun h => ?_, fun h => ?_⟩
  · by_cases hh : h.1 ∈ T
    · simp [restrictTo, hh, hT h hh, hf.1 h]
    · simp [restrictTo, hh]
  · by_cases hh : h.1 ∈ T
    · rw [show restrictTo f T h = f h from if_pos hh]
      constructor
      · intro he; exact absurd (hTR hh) ((hf.2 h).1 he)
      · intro hn; exact absurd hh hn
    · simp [restrictTo, hh]

lemma glue_mem {R S : Finset V} (hSR : S ⊆ R) {g k : V × Fin 4 → V × Fin 4} (hg : g ∈ pairOn S)
    (hk : k ∈ pairOn (R \ S)) : glue S g k ∈ pairOn R := by
  have hgS := closed_of_mem_pairOn hg
  have hkS := closed_of_mem_pairOn hk
  rw [mem_pairOn] at hg hk ⊢
  have hk1 : ∀ h : V × Fin 4, h.1 ∉ S → (k h).1 ∉ S := by
    intro h hh
    by_cases hR : h.1 ∈ R
    · exact (mem_sdiff.1 (hkS h (mem_sdiff.2 ⟨hR, hh⟩))).2
    · rw [(hk.2 h).2 (fun hm => hR (mem_sdiff.1 hm).1)]; exact hh
  refine ⟨fun h => ?_, fun h => ?_⟩
  · by_cases hh : h.1 ∈ S
    · simp [glue, hh, hgS h hh, hg.1 h]
    · simp [glue, hh, hk1 h hh, hk.1 h]
  · by_cases hh : h.1 ∈ S
    · rw [show glue S g k h = g h from if_pos hh, hg.2 h]
      simp [hh, hSR hh]
    · rw [show glue S g k h = k h from if_neg hh, hk.2 h]
      simp [mem_sdiff, hh]

lemma closed_glue {S : Finset V} {g k : V × Fin 4 → V × Fin 4} (hg : g ∈ pairOn S) :
    Closed (glue S g k) S := by
  intro h hh
  rw [show glue S g k h = g h from if_pos hh]
  exact closed_of_mem_pairOn hg h hh

lemma connOn_congr {S : Finset V} {f g : V × Fin 4 → V × Fin 4} (hfg : ∀ h, h.1 ∈ S → f h = g h) :
    ConnOn f S ↔ ConnOn g S := by
  have hc : ∀ T ⊆ S, Closed f T ↔ Closed g T := fun T hTS =>
    ⟨fun hT h hh => by rw [← hfg h (hTS hh)]; exact hT h hh,
      fun hT h hh => by rw [hfg h (hTS hh)]; exact hT h hh⟩
  exact ⟨fun hf => ⟨hf.1, fun T hTS hT => hf.2 T hTS ((hc T hTS).2 hT)⟩,
    fun hg => ⟨hg.1, fun T hTS hT => hg.2 T hTS ((hc T hTS).1 hT)⟩⟩

open Classical in
/-- The pairings of `R` in which `S` is closed and connected are the pairs (connected pairing of `S`, pairing of
`R \ S`). -/
theorem card_fiber {R S : Finset V} (hSR : S ⊆ R) :
    ((pairOn R).filter fun f => Closed f S ∧ ConnOn f S).card =
      (connPairOn S).card * (pairOn (R \ S)).card := by
  classical
  rw [← card_product]
  refine card_nbij' (fun f => (restrictTo f S, restrictTo f (R \ S))) (fun p => glue S p.1 p.2)
    ?_ ?_ ?_ ?_
  · intro f hf
    rw [mem_coe, mem_filter] at hf
    obtain ⟨hf, hSc, hSconn⟩ := hf
    have hRc := closed_of_mem_pairOn hf
    rw [mem_coe, mem_product]
    dsimp only
    rw [connPairOn, mem_filter]
    exact ⟨⟨restrictTo_mem hf hSR hSc, (connOn_congr fun h hh => (if_pos hh).symm).1 hSconn⟩,
      restrictTo_mem hf sdiff_subset (hRc.sdiff (mem_pairOn.1 hf).1 hSc)⟩
  · rintro ⟨g, k⟩ hp
    rw [mem_coe, mem_product, connPairOn, mem_filter] at hp
    obtain ⟨⟨hg, hgconn⟩, hk⟩ := hp
    rw [mem_coe, mem_filter]
    exact ⟨glue_mem hSR hg hk, closed_glue hg, (connOn_congr fun h hh => if_pos hh).2 hgconn⟩
  · intro f hf
    rw [mem_coe, mem_filter] at hf
    have hf' := mem_pairOn.1 hf.1
    funext h
    simp only [glue, restrictTo]
    by_cases hh : h.1 ∈ S
    · simp [hh]
    · by_cases hR : h.1 ∈ R
      · simp [hh, hR]
      · simp [hh, hR, (hf'.2 h).2 hR]
  · rintro ⟨g, k⟩ hp
    rw [mem_coe, mem_product, connPairOn, mem_filter] at hp
    obtain ⟨⟨hg, -⟩, hk⟩ := hp
    dsimp only at hg hk
    have hg' := mem_pairOn.1 hg
    have hk' := mem_pairOn.1 hk
    simp only [Prod.mk.injEq]
    constructor
    · funext h
      simp only [glue, restrictTo]
      by_cases hh : h.1 ∈ S
      · simp [hh]
      · simp [hh, (hg'.2 h).2 hh]
    · funext h
      simp only [glue, restrictTo]
      by_cases hh : h.1 ∈ R \ S
      · simp [hh, (mem_sdiff.1 hh).2]
      · simp [hh, (hk'.2 h).2 hh]

/-- **Splitting off the component of a vertex**: for `v₀ ∈ R`,
`#pairings(R) = ∑_{v₀ ∈ S ⊆ R} #connected(S) · #pairings(R \ S)`. -/
theorem card_pairOn_eq_sum {R : Finset V} {v₀ : V} (hv : v₀ ∈ R) :
    (pairOn R).card =
      ∑ S ∈ R.powerset.filter (v₀ ∈ ·), (connPairOn S).card * (pairOn (R \ S)).card := by
  classical
  have key : ∀ f ∈ pairOn R,
      ((R.powerset.filter (v₀ ∈ ·)).filter fun S => Closed f S ∧ ConnOn f S).card = 1 := by
    intro f hf
    obtain ⟨S, hS, huniq⟩ := existsUnique_component hf hv
    rw [card_eq_one]
    refine ⟨S, ext fun T => ?_⟩
    simp only [mem_filter, mem_powerset, mem_singleton]
    constructor
    · rintro ⟨⟨hTR, hvT⟩, hT⟩; exact huniq T ⟨⟨hTR, hvT⟩, hT⟩
    · rintro rfl; exact ⟨hS.1, hS.2⟩
  calc (pairOn R).card = ∑ f ∈ pairOn R,
        ((R.powerset.filter (v₀ ∈ ·)).filter fun S => Closed f S ∧ ConnOn f S).card := by
        rw [sum_congr rfl key, sum_const, smul_eq_mul, mul_one]
    _ = ∑ S ∈ R.powerset.filter (v₀ ∈ ·), ((pairOn R).filter fun f => Closed f S ∧ ConnOn f S).card :=
        sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow (fun f S => Closed f S ∧ ConnOn f S)
    _ = _ := sum_congr rfl fun S hS => card_fiber (mem_powerset.1 (mem_filter.1 hS).1)

end Decomposition

section Transfer

variable {V W : Type*} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W] (ι : W ↪ V)

/-- The half-edge map of a vertex embedding. -/
def ι₄ : W × Fin 4 → V × Fin 4 := fun a => (ι a.1, a.2)

lemma ι₄_injective : Injective (ι₄ ι) := fun a b h => by
  simp only [ι₄, Prod.mk.injEq] at h
  exact Prod.ext (ι.injective h.1) h.2

/-- Extension by the identity of a map of the half-edges of `W` to the half-edges of `V`. -/
def extendHE (g : W × Fin 4 → W × Fin 4) : V × Fin 4 → V × Fin 4 :=
  Function.extend (ι₄ ι) (ι₄ ι ∘ g) id

/-- Pullback to `W` of a map of the half-edges of `V`. -/
def pullHE (F : V × Fin 4 → V × Fin 4) : W × Fin 4 → W × Fin 4 :=
  fun a => Function.extend (ι₄ ι) id (fun _ => a) (F (ι₄ ι a))

lemma extendHE_apply (g : W × Fin 4 → W × Fin 4) (a : W × Fin 4) :
    extendHE ι g (ι₄ ι a) = ι₄ ι (g a) :=
  (ι₄_injective ι).extend_apply _ _ a

lemma extendHE_apply_of_notMem (g : W × Fin 4 → W × Fin 4) {h : V × Fin 4} (hh : h.1 ∉ Set.range ι) :
    extendHE ι g h = h :=
  extend_apply' _ _ _ (by rintro ⟨a, ha⟩; exact hh ⟨a.1, by rw [← ha]; rfl⟩)

lemma pullHE_apply {F : V × Fin 4 → V × Fin 4} {a b : W × Fin 4} (hab : F (ι₄ ι a) = ι₄ ι b) :
    pullHE ι F a = b := by
  simp only [pullHE, hab]; exact (ι₄_injective ι).extend_apply _ _ b

lemma exists_of_mem_pairOn_map {S : Finset W} {F : V × Fin 4 → V × Fin 4} (hF : F ∈ pairOn (S.map ι))
    (a : W × Fin 4) : ∃ b, F (ι₄ ι a) = ι₄ ι b := by
  by_cases ha : a.1 ∈ S
  · have hc := closed_of_mem_pairOn hF (ι₄ ι a) (mem_map_of_mem ι ha)
    obtain ⟨w, -, hw⟩ := mem_map.1 hc
    exact ⟨(w, (F (ι₄ ι a)).2), Prod.ext hw.symm rfl⟩
  · refine ⟨a, ((mem_pairOn.1 hF).2 _).2 ?_⟩
    rw [show (ι₄ ι a).1 = ι a.1 from rfl, mem_map']
    exact ha

lemma pullHE_spec {S : Finset W} {F : V × Fin 4 → V × Fin 4} (hF : F ∈ pairOn (S.map ι)) (a : W × Fin 4) :
    F (ι₄ ι a) = ι₄ ι (pullHE ι F a) := by
  obtain ⟨b, hb⟩ := exists_of_mem_pairOn_map ι hF a
  rw [hb, pullHE_apply ι hb]

lemma extendHE_mem {S : Finset W} {g : W × Fin 4 → W × Fin 4} (hg : g ∈ pairOn S) :
    extendHE ι g ∈ pairOn (S.map ι) := by
  have hg' := mem_pairOn.1 hg
  rw [mem_pairOn]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · by_cases hh : h.1 ∈ Set.range ι
    · obtain ⟨w, hw⟩ := hh
      have he : h = ι₄ ι (w, h.2) := Prod.ext hw.symm rfl
      rw [he, extendHE_apply, extendHE_apply, hg'.1]
    · rw [extendHE_apply_of_notMem ι g hh, extendHE_apply_of_notMem ι g hh]
  · by_cases hh : h.1 ∈ Set.range ι
    · obtain ⟨w, hw⟩ := hh
      have he : h = ι₄ ι (w, h.2) := Prod.ext hw.symm rfl
      rw [he, extendHE_apply, (ι₄_injective ι).eq_iff, hg'.2,
        show (ι₄ ι (w, h.2)).1 = ι (w, h.2).1 from rfl, mem_map']
    · rw [extendHE_apply_of_notMem ι g hh]
      simp only [true_iff]
      intro hm
      obtain ⟨w, -, hw⟩ := mem_map.1 hm
      exact hh ⟨w, hw⟩

lemma pullHE_mem {S : Finset W} {F : V × Fin 4 → V × Fin 4} (hF : F ∈ pairOn (S.map ι)) :
    pullHE ι F ∈ pairOn S := by
  have hF' := mem_pairOn.1 hF
  rw [mem_pairOn]
  refine ⟨fun a => (ι₄_injective ι) ?_, fun a => ?_⟩
  · rw [← pullHE_spec ι hF, ← pullHE_spec ι hF, hF'.1]
  · rw [← (ι₄_injective ι).eq_iff, ← pullHE_spec ι hF, hF'.2,
      show (ι₄ ι a).1 = ι a.1 from rfl, mem_map']

lemma pullHE_extendHE (g : W × Fin 4 → W × Fin 4) : pullHE ι (extendHE ι g) = g :=
  funext fun a => pullHE_apply ι (extendHE_apply ι g a)

lemma extendHE_pullHE {S : Finset W} {F : V × Fin 4 → V × Fin 4} (hF : F ∈ pairOn (S.map ι)) :
    extendHE ι (pullHE ι F) = F := by
  funext h
  by_cases hh : h.1 ∈ Set.range ι
  · obtain ⟨w, hw⟩ := hh
    have he : h = ι₄ ι (w, h.2) := Prod.ext hw.symm rfl
    rw [he, extendHE_apply, ← pullHE_spec ι hF]
  · rw [extendHE_apply_of_notMem ι _ hh]
    refine (((mem_pairOn.1 hF).2 h).2 fun hm => hh ?_).symm
    obtain ⟨w, -, hw⟩ := mem_map.1 hm
    exact ⟨w, hw⟩

lemma closed_extendHE_map {g : W × Fin 4 → W × Fin 4} {T : Finset W} :
    Closed (extendHE ι g) (T.map ι) ↔ Closed g T := by
  constructor
  · intro hT a ha
    have := hT (ι₄ ι a) (mem_map_of_mem ι ha)
    rwa [extendHE_apply, show (ι₄ ι (g a)).1 = ι (g a).1 from rfl, mem_map'] at this
  · intro hT h hh
    obtain ⟨w, hw, hwh⟩ := mem_map.1 hh
    have he : h = ι₄ ι (w, h.2) := Prod.ext hwh.symm rfl
    rw [he, extendHE_apply, show (ι₄ ι (g (w, h.2))).1 = ι (g (w, h.2)).1 from rfl, mem_map']
    exact hT (w, h.2) hw

lemma connOn_extendHE {g : W × Fin 4 → W × Fin 4} {S : Finset W} :
    ConnOn (extendHE ι g) (S.map ι) ↔ ConnOn g S := by
  constructor
  · rintro ⟨hn, hc⟩
    refine ⟨map_nonempty.1 hn, fun T hTS hT => ?_⟩
    rcases hc (T.map ι) (map_subset_map.2 hTS) ((closed_extendHE_map ι).2 hT) with h | h
    · exact Or.inl (map_eq_empty.1 h)
    · exact Or.inr (map_injective ι h)
  · rintro ⟨hn, hc⟩
    refine ⟨map_nonempty.2 hn, fun U hUS hU => ?_⟩
    have hUe : U = (S.filter fun w => ι w ∈ U).map ι := by
      ext v
      simp only [mem_map, mem_filter]
      constructor
      · intro hv
        obtain ⟨w, hw, rfl⟩ := mem_map.1 (hUS hv)
        exact ⟨w, ⟨hw, hv⟩, rfl⟩
      · rintro ⟨w, ⟨-, hw⟩, rfl⟩; exact hw
    rw [hUe] at hU ⊢
    rcases hc _ (filter_subset _ _) ((closed_extendHE_map ι).1 hU) with h | h
    · left; rw [h, map_empty]
    · right; rw [h]

theorem card_pairOn_map (S : Finset W) : (pairOn (S.map ι)).card = (pairOn S).card :=
  (card_nbij' (extendHE ι) (pullHE ι) (fun _ hg => extendHE_mem ι hg) (fun _ hF => pullHE_mem ι hF)
    (fun g _ => pullHE_extendHE ι g) (fun _ hF => extendHE_pullHE ι hF)).symm

theorem card_connPairOn_map (S : Finset W) : (connPairOn (S.map ι)).card = (connPairOn S).card := by
  classical
  refine (card_nbij' (extendHE ι) (pullHE ι) (fun g hg => ?_) (fun F hF => ?_)
    (fun g _ => pullHE_extendHE ι g) (fun F hF => ?_)).symm
  · rw [mem_coe, connPairOn, mem_filter] at hg ⊢
    exact ⟨extendHE_mem ι hg.1, (connOn_extendHE ι).2 hg.2⟩
  · rw [mem_coe, connPairOn, mem_filter] at hF ⊢
    refine ⟨pullHE_mem ι hF.1, (connOn_extendHE ι).1 ?_⟩
    rw [extendHE_pullHE ι hF.1]; exact hF.2
  · rw [mem_coe, connPairOn, mem_filter] at hF
    exact extendHE_pullHE ι hF.1

end Transfer

/-- A finite set of vertices is the image of an embedding of `Fin #S`. -/
lemma exists_embedding_fin {V : Type*} (S : Finset V) : ∃ ι : Fin S.card ↪ V, univ.map ι = S := by
  refine ⟨S.equivFin.symm.toEmbedding.trans (Embedding.subtype _), ?_⟩
  ext v
  simp only [mem_map, mem_univ, true_and, Embedding.trans_apply, Equiv.coe_toEmbedding,
    Embedding.coe_subtype]
  constructor
  · rintro ⟨a, rfl⟩; exact (S.equivFin.symm a).2
  · intro hv; exact ⟨S.equivFin ⟨v, hv⟩, by simp⟩

/-- The number `a_k` of pairings of the `4k` half-edges of `k` four-valent vertices. -/
def numPairings (k : ℕ) : ℕ := (pairOn (univ : Finset (Fin k))).card

/-- The number `c_k` of connected pairings of `k` four-valent vertices. -/
def numConnected (k : ℕ) : ℕ := (connPairOn (univ : Finset (Fin k))).card

lemma card_pairOn_eq {V : Type*} [Fintype V] [DecidableEq V] (S : Finset V) : (pairOn S).card = numPairings S.card := by
  obtain ⟨ι, hι⟩ := exists_embedding_fin S
  calc (pairOn S).card = (pairOn (univ.map ι)).card := by rw [hι]
    _ = _ := card_pairOn_map ι univ

lemma card_connPairOn_eq {V : Type*} [Fintype V] [DecidableEq V] (S : Finset V) :
    (connPairOn S).card = numConnected S.card := by
  obtain ⟨ι, hι⟩ := exists_embedding_fin S
  calc (connPairOn S).card = (connPairOn (univ.map ι)).card := by rw [hι]
    _ = _ := card_connPairOn_map ι univ

/-- `a_n = (4n - 1)!!`, the number of the pairings of `Graphs` (`card_pairing`). -/
theorem numPairings_eq (n : ℕ) : numPairings n = (4 * n - 1)‼ := by
  classical
  rw [← card_pairing n, numPairings, pairOn, Pairing, Nat.card_eq_fintype_card, Fintype.card_subtype]
  congr 1
  ext f
  simp

lemma numPairings_zero : numPairings 0 = 1 := by
  rw [numPairings_eq]; rfl

lemma numConnected_zero : numConnected 0 = 0 := by
  classical
  rw [numConnected, Finset.card_eq_zero, connPairOn, filter_eq_empty_iff]
  intro f _ hf
  obtain ⟨x, -⟩ := hf.1
  exact x.elim0

/-- **The exponential formula as a recursion** (splitting off the component of the vertex `0`):
`a_{n+1} = ∑_{k ≤ n} C(n, k) c_{k+1} a_{n-k}`. -/
theorem numPairings_succ (n : ℕ) :
    numPairings (n + 1) =
      ∑ k ∈ range (n + 1), n.choose k * (numConnected (k + 1) * numPairings (n - k)) := by
  have h := card_pairOn_eq_sum (R := (univ : Finset (Fin (n + 1)))) (v₀ := 0) (mem_univ _)
  rw [numPairings, h]
  have hS : ∀ S ∈ (univ : Finset (Fin (n + 1))).powerset.filter (0 ∈ ·),
      (connPairOn S).card * (pairOn (univ \ S)).card =
        numConnected S.card * numPairings (n + 1 - S.card) := by
    intro S _
    rw [card_connPairOn_eq, card_pairOn_eq, card_sdiff_of_subset (subset_univ S), Finset.card_univ,
      Fintype.card_fin]
  rw [sum_congr rfl hS, sum_filter]
  have hu : (univ : Finset (Fin (n + 1))) = insert 0 (univ.erase 0) := (insert_erase (mem_univ 0)).symm
  have h0 : (0 : Fin (n + 1)) ∉ univ.erase 0 := notMem_erase 0 univ
  rw [hu, sum_powerset_insert h0]
  have hz : ∑ t ∈ (univ.erase (0 : Fin (n + 1))).powerset,
      (if (0 : Fin (n + 1)) ∈ t then numConnected t.card * numPairings (n + 1 - t.card) else 0) = 0 :=
    sum_eq_zero fun t ht => if_neg fun h => h0 (mem_powerset.1 ht h)
  rw [hz, zero_add]
  have hi : ∀ t ∈ (univ.erase (0 : Fin (n + 1))).powerset,
      (if (0 : Fin (n + 1)) ∈ insert 0 t then numConnected (insert 0 t).card *
        numPairings (n + 1 - (insert 0 t).card) else 0) =
        numConnected (t.card + 1) * numPairings (n - t.card) := by
    intro t ht
    rw [if_pos (mem_insert_self 0 t), card_insert_of_notMem fun h => h0 (mem_powerset.1 ht h)]
    congr 2
    omega
  rw [sum_congr rfl hi,
    sum_powerset_apply_card (fun m => numConnected (m + 1) * numPairings (n - m)),
    card_erase_of_mem (mem_univ _), Finset.card_univ, Fintype.card_fin, Nat.add_sub_cancel]
  simp only [smul_eq_mul]

open PowerSeries

/-- **The vacuum series** `Z = ∑_n a_n xⁿ/(24ⁿ n!)`: the vacuum graphs of the quartic theory, each with its symmetry
factor (by `sum_inv_aut`, `a_n/(24ⁿ n!) = ∑_{Γ, n vertices} 1/|Aut Γ|`). -/
def vacuumSeries : PowerSeries ℚ := mk fun n => (numPairings n : ℚ) / (24 ^ n * n.factorial)

/-- **The connected series** `W = ∑_n c_n xⁿ/(24ⁿ n!)`: the connected vacuum graphs with their symmetry factors. -/
def connectedSeries : PowerSeries ℚ := mk fun n => (numConnected n : ℚ) / (24 ^ n * n.factorial)

/-- **`Z' = W' Z`**, the coefficient form of the exponential formula. -/
theorem derivative_vacuumSeries : d⁄dX vacuumSeries = d⁄dX connectedSeries * vacuumSeries := by
  ext n
  rw [coeff_derivative, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun i j => coeff i (d⁄dX connectedSeries) * coeff j vacuumSeries)]
  simp only [coeff_derivative, vacuumSeries, connectedSeries, coeff_mk]
  rw [numPairings_succ, Nat.cast_sum, sum_div, sum_mul]
  refine sum_congr rfl fun k hk => ?_
  have hkn : k ≤ n := Nat.lt_succ_iff.1 (mem_range.1 hk)
  have hc : (n.choose k : ℚ) * k.factorial * (n - k).factorial = n.factorial := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial hkn
  have hp : (24 : ℚ) ^ (n + 1) = 24 ^ (k + 1) * 24 ^ (n - k) := by
    rw [← pow_add]; congr 1; omega
  have hch : (n.choose k : ℚ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hkn).ne'
  rw [Nat.factorial_succ n, Nat.factorial_succ k, hp]
  push_cast
  rw [← hc]
  field_simp <;> ring

/-- Uniqueness for `F' = W' F`: the constant coefficient determines `F`. -/
theorem eq_of_derivative_eq_mul {F G W : PowerSeries ℚ} (hF : d⁄dX F = d⁄dX W * F)
    (hG : d⁄dX G = d⁄dX W * G) (h0 : constantCoeff F = constantCoeff G) : F = G := by
  ext n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases n with _ | n
    · simpa using h0
    · have hF' := congrArg (coeff n) hF
      have hG' := congrArg (coeff n) hG
      rw [coeff_derivative, coeff_mul] at hF' hG'
      have hsum : ∑ p ∈ antidiagonal n, coeff p.1 (d⁄dX W) * coeff p.2 F =
          ∑ p ∈ antidiagonal n, coeff p.1 (d⁄dX W) * coeff p.2 G :=
        sum_congr rfl fun p hp => by
          rw [ih p.2 (by have := Finset.mem_antidiagonal.1 hp; omega)]
      have hn : ((n : ℚ) + 1) ≠ 0 := by positivity
      exact mul_right_cancel₀ hn (hF'.trans (hsum.trans hG'.symm))

/-- **The exponential formula** (Borinsky, Theorem 2.4.1, eq. (2.4.7), p. 18, for the vacuum graphs of the quartic
theory): `Z = exp(W)`, i.e. `∑_Γ x^{|V_Γ|}/|Aut Γ| = exp(∑_{Γ connected} x^{|V_Γ|}/|Aut Γ|)`. -/
theorem vacuumSeries_eq_exp : vacuumSeries = (exp ℚ).subst connectedSeries := by
  have h0 : constantCoeff connectedSeries = 0 := by
    rw [← coeff_zero_eq_constantCoeff_apply, connectedSeries, coeff_mk, numConnected_zero]; simp
  have hs : HasSubst connectedSeries := HasSubst.of_constantCoeff_zero' h0
  refine eq_of_derivative_eq_mul (W := connectedSeries) derivative_vacuumSeries ?_ ?_
  · rw [derivative_subst hs, derivative_exp, mul_comm]
  · have h1 := constantCoeff_subst_of_constantCoeff_zero h0 (exp ℚ)
    rw [← coeff_zero_eq_constantCoeff_apply, vacuumSeries, coeff_mk, numPairings_zero]
    simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, mul_one, div_one]
    rw [show constantCoeff ((exp ℚ).subst connectedSeries) =
      MvPowerSeries.constantCoeff ((exp ℚ).subst connectedSeries : MvPowerSeries Unit ℚ) from rfl, h1]
    simp

end Lightlike.FieldTheory
