import Lightlike.PL.PolygonSplit

/-!
# Ears of a simple polygon

An **ear** of a polygon at the index `k` is a diagonal from the vertex `k` to the vertex `k + 2`
whose open segment lies in the inside of the polygon; it cuts off the triangle on the vertices
`k`, `k + 1`, `k + 2`. A simple polygon with at least four vertices has two ears with
non-neighbouring apexes. This follows by induction from the splitting along an interior diagonal:
a part that is a triangle has its ear at the diagonal, and a part with at least four vertices has
two ears, of which at most one touches the diagonal.

## Main results

* `Lightlike.PL.Polygon.Ear`: the ear at an index
* `Lightlike.PL.Polygon.two_ears`: two ears at non-neighbouring indices
-/

open Set

namespace Lightlike.PL
namespace Polygon

variable {n : ℕ} [NeZero n]

/-- The polygon has an **ear** at the index `k`: the open diagonal from the vertex `k` to the
vertex `k + 2` lies in the inside. -/
def Ear (p : Polygon n) (k : ℕ) : Prop :=
  openSegment ℝ (p.cyc k) (p.cyc (k + 2)) ⊆ p.inside

lemma ear_rot (p : Polygon n) (β : Fin n) (k : ℕ) : (p.rot β).Ear k ↔ p.Ear (k + β) := by
  unfold Ear
  rw [rot_cyc, rot_cyc, inside_rot, Nat.add_right_comm k 2 β]

lemma ear_mod (p : Polygon n) (k : ℕ) : p.Ear (k % n) ↔ p.Ear k := by
  unfold Ear
  have h1 : p.cyc (k % n) = p.cyc k := p.cyc_mod k
  have h2 : p.cyc (k % n + 2) = p.cyc (k + 2) := by
    rw [← p.cyc_mod (k % n + 2), ← p.cyc_mod (k + 2), Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
  rw [h1, h2]

/-- **Two ears with non-neighbouring indices.** -/
def TwoEars (p : Polygon n) : Prop :=
  ∃ k₁ k₂ : ℕ, k₁ < n ∧ k₂ < n ∧ p.Ear k₁ ∧ p.Ear k₂ ∧ 2 ≤ (k₂ + n - k₁) % n ∧
    (k₂ + n - k₁) % n + 2 ≤ n

/-- Of two ears with non-neighbouring indices, one does not wrap around the end of the list of
vertices. -/
lemma TwoEars.exists_nowrap {p : Polygon n} (h : p.TwoEars) : ∃ k, k + 3 ≤ n ∧ p.Ear k := by
  obtain ⟨k₁, k₂, h1, h2, e1, e2, d1, d2⟩ := h
  by_cases hk1 : k₁ + 3 ≤ n
  · exact ⟨k₁, hk1, e1⟩
  by_cases hk2 : k₂ + 3 ≤ n
  · exact ⟨k₂, hk2, e2⟩
  exfalso
  rcases Nat.lt_or_ge k₂ k₁ with h12 | h12
  · have : k₂ + n - k₁ = n - (k₁ - k₂) := by omega
    rw [this, Nat.mod_eq_of_lt (by omega)] at d1 d2
    omega
  · have : k₂ + n - k₁ = n + (k₂ - k₁) := by omega
    rw [this, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)] at d1
    omega

omit [NeZero n] in
/-- A cyclic shift keeps two non-neighbouring indices non-neighbouring. -/
lemma shift_indices {a₀ k₁ k₂ : ℕ} (ha₀ : a₀ < n) (h₁ : k₁ + 2 ≤ k₂) (h₂ : k₂ + 2 ≤ n) :
    (k₁ + a₀) % n < n ∧ (k₂ + a₀) % n < n ∧
      2 ≤ ((k₂ + a₀) % n + n - (k₁ + a₀) % n) % n ∧
      ((k₂ + a₀) % n + n - (k₁ + a₀) % n) % n + 2 ≤ n := by
  have hn : 0 < n := by omega
  have hmod : ∀ k, k < n → (k + a₀) % n = if k + a₀ < n then k + a₀ else k + a₀ - n := by
    intro k hk
    split_ifs with h
    · exact Nat.mod_eq_of_lt h
    · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
  have hd : ∀ x y, x < n → y < n →
      (y + n - x) % n = if x ≤ y then y - x else y + n - x := by
    intro x y hx hy
    split_ifs with h
    · have : y + n - x = n + (y - x) := by omega
      rw [this, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
    · rw [Nat.mod_eq_of_lt (by omega)]
  have hxv := hmod k₁ (by omega)
  have hyv := hmod k₂ (by omega)
  have hx : (k₁ + a₀) % n < n := Nat.mod_lt _ hn
  have hy : (k₂ + a₀) % n < n := Nat.mod_lt _ hn
  refine ⟨hx, hy, ?_⟩
  rw [hd _ _ hx hy]
  generalize (k₁ + a₀) % n = x at *
  generalize (k₂ + a₀) % n = y at *
  split_ifs at hxv hyv ⊢ <;> omega

/-- **Every simple polygon with at least four vertices has two ears with non-neighbouring
indices.** -/
theorem two_ears : ∀ (n : ℕ) [NeZero n] (p : Polygon n), 4 ≤ n → p.IsSimple → p.TwoEars := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro _ p h4 hs
    obtain ⟨a₀, b, hb2, hb3, hL, hR, hdis, hspl⟩ := exists_split hs h4
    set q := p.rot a₀ with hq
    have hD : ∀ x ∈ openSegment ℝ (q.cyc 0) (q.cyc b), x ∈ q.inside := fun x hx => by
      rw [hspl]; exact Or.inr hx
    have hLear : ∃ k₁, k₁ + 2 ≤ b ∧ q.Ear k₁ := by
      by_cases hb' : b = 2
      · refine ⟨0, by omega, ?_⟩
        intro x hx
        subst hb'
        exact hD x (by simpa using hx)
      · obtain ⟨k, hk, hE⟩ := (ih (b + 1) (by omega) (q.left b) (by omega) hL).exists_nowrap
        refine ⟨k, by omega, fun x hx => ?_⟩
        have e1 : (q.left b).cyc k = q.cyc k := by
          show q.cyc (k % (b + 1)) = _
          rw [Nat.mod_eq_of_lt (by omega)]
        have e2 : (q.left b).cyc (k + 2) = q.cyc (k + 2) := by
          show q.cyc ((k + 2) % (b + 1)) = _
          rw [Nat.mod_eq_of_lt (by omega)]
        have : x ∈ (q.left b).inside := hE (by rw [e1, e2]; exact hx)
        rw [hspl]; exact Or.inl (Or.inl this)
    have hRear : ∃ k₂, b ≤ k₂ ∧ k₂ + 2 ≤ n ∧ q.Ear k₂ := by
      by_cases hb' : b + 2 = n
      · refine ⟨b, le_rfl, by omega, fun x hx => ?_⟩
        have e : q.cyc (b + 2) = q.cyc 0 := by rw [hb']; simpa using q.cyc_self_add 0
        rw [e, openSegment_symm] at hx
        exact hD x hx
      · obtain ⟨k, hk, hE⟩ := (ih (n - b + 1) (by omega) (q.right b) (by omega) hR).exists_nowrap
        refine ⟨b + k, by omega, by omega, fun x hx => ?_⟩
        have e1 : (q.right b).cyc k = q.cyc (b + k) := by
          show q.cyc (b + k % (n - b + 1)) = _
          rw [Nat.mod_eq_of_lt (by omega)]
        have e2 : (q.right b).cyc (k + 2) = q.cyc (b + k + 2) := by
          show q.cyc (b + (k + 2) % (n - b + 1)) = _
          rw [Nat.mod_eq_of_lt (by omega), Nat.add_assoc]
        have : x ∈ (q.right b).inside := hE (by rw [e1, e2]; exact hx)
        rw [hspl]; exact Or.inl (Or.inr this)
    obtain ⟨k₁, hk₁, e₁⟩ := hLear
    obtain ⟨k₂, hk₂, hk₂', e₂⟩ := hRear
    obtain ⟨hx, hy, hd1, hd2⟩ := shift_indices (n := n) (a₀ := a₀) (k₁ := k₁) (k₂ := k₂)
      a₀.2 (by omega) hk₂'
    refine ⟨(k₁ + a₀) % n, (k₂ + a₀) % n, hx, hy, ?_, ?_, hd1, hd2⟩
    · rw [ear_mod]; exact (ear_rot p a₀ k₁).1 e₁
    · rw [ear_mod]; exact (ear_rot p a₀ k₂).1 e₂

end Polygon

end Lightlike.PL
