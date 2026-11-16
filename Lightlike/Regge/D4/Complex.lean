import Lightlike.Regge.D4.Dihedral
import Lightlike.Regge.ReggeEquations
import Lightlike.FourD.Boundary

/-!
# Deficit angles and the Regge action of a 4-dimensional triangulation

In 4D Regge calculus every 4-simplex is flat, with the edge lengths `ℓ`, and curvature is
concentrated on the triangles. Around an interior triangle `t` the dihedral angles `θ_σ(t)` of the
4-simplices `σ ∋ t` add up to `2π` exactly when the geometry is flat there; the **deficit angle**
is `δ_t = 2π - Σ_{σ ∋ t} θ_σ(t)`. The **Regge action** is `Σ_t A_t δ_t`, with `A_t` the area of
the triangle (Regge 1961), completed for a triangulation with boundary by the term
`Σ_{t ∈ ∂} A_t (π - Σ_{σ ∋ t} θ_σ(t))` (Hartle–Sorkin 1981); both without `1/(8πG)`.

Triangulations are the 4-complexes `Lightlike.FourD.Complex4 V` of `FourD/` (4-simplices as 5-element
vertex sets); lengths are functions `ℓ : Finset V → ℝ` read on 2-element sets, as in 3D.

## Main results

* `angleAvg4 F ℓ σ t`: an angle formula `F ℓ p q r s u` (triangle `pqr`, opposite vertices `s, u`)
  applied to the 4-simplex `σ` at its triangle `t`, averaged over the `12` labellings, so that no
  labelling is chosen. `dihedralAt4 = angleAvg4 dihedral4`.
* `angleSum4 K ℓ t`: the sum of the dihedral angles at `t` of the 4-simplices of `K` around it
  (`K.star t`).
* `deficit4 K ℓ t = 2π - angleSum4`, `bdryAngle4 K ℓ t = π - angleSum4`.
* `bdryTris4 K`: the triangles of boundary tetrahedra (tetrahedra in one 4-simplex,
  `K.bdryTets`); `intTris4 K`: the other triangles.
* `area4 ℓ t = √(triH ℓ t) / 4`, by Heron's formula (`Lightlike.Regge.triH`, sixteen times the squared
  area, without a labelling).
* `reggeAction4 K ℓ = Σ_{t interior} A_t δ_t + Σ_{t boundary} A_t ψ_t`.

* `angleAvg4_eq`, `dihedralAt4_eq`: for a symmetric formula the average is the formula in any
  labelling.
* `triH_eq_gram2`, `area4_eq`: `16 A² = 4 · gram2`, so `A = √gram2 / 2`.
* `deficit4_smul`, `reggeAction4_smul`: deficit angles are scale invariant and the action is
  homogeneous of degree two, `S(cℓ) = c² S(ℓ)` for `c > 0`.
* `deficit4_const`: with all lengths equal, a triangle in `n` 4-simplices has
  `δ = 2π - n · arccos(1/4)`.
-/

open Real Finset

namespace Lightlike.Regge4

open Lightlike.FourD (Complex4)

variable {V : Type*} [DecidableEq V]

/-! ## Labelling-free dihedral angles -/

/-- The angle of the 4-simplex `σ` at its triangle `t` according to a formula `F ℓ p q r s u`
(triangle `pqr`, opposite vertices `s, u`), averaged over the `3! · 2 = 12` labellings of `t` and
of `σ \ t`. With `F = dihedral4` this is `dihedralAt4`; `Lightlike/Regge/D4/Tests.lean` uses other
`F` to show that wrong angle formulas fail. -/
noncomputable def angleAvg4 (F : (Finset V → ℝ) → V → V → V → V → V → ℝ) (ℓ : Finset V → ℝ)
    (σ t : Finset V) : ℝ :=
  (∑ p ∈ t, ∑ q ∈ t.erase p, ∑ r ∈ (t.erase p).erase q, ∑ s ∈ σ \ t, ∑ u ∈ (σ \ t).erase s,
    F ℓ p q r s u) / 12

/-- An angle formula is **symmetric** if it is invariant under the permutations of the triangle
and of the two opposite vertices. -/
structure IsSymm4 (F : (Finset V → ℝ) → V → V → V → V → V → ℝ) : Prop where
  /-- Swapping the first two vertices of the triangle. -/
  swap_pq : ∀ ℓ p q r s u, F ℓ q p r s u = F ℓ p q r s u
  /-- Swapping the last two vertices of the triangle. -/
  swap_qr : ∀ ℓ p q r s u, F ℓ p r q s u = F ℓ p q r s u
  /-- Swapping the two opposite vertices. -/
  swap_su : ∀ ℓ p q r s u, F ℓ p q r u s = F ℓ p q r s u

/-- The dihedral angle formula is symmetric. -/
theorem isSymm4_dihedral4 : IsSymm4 (dihedral4 (V := V)) :=
  ⟨dihedral4_swap_pq, dihedral4_swap_qr, dihedral4_swap_su⟩

/-- If every labelled value of `F` is `c`, the average is `c`. -/
theorem angleAvg4_of_forall (F : (Finset V → ℝ) → V → V → V → V → V → ℝ) (ℓ : Finset V → ℝ)
    {σ t : Finset V} (ht : #t = 3) (hst : #(σ \ t) = 2) {c : ℝ}
    (h : ∀ p ∈ t, ∀ q ∈ t.erase p, ∀ r ∈ (t.erase p).erase q, ∀ s ∈ σ \ t,
      ∀ u ∈ (σ \ t).erase s, F ℓ p q r s u = c) :
    angleAvg4 F ℓ σ t = c := by
  have e1 : ∀ p ∈ t, ∀ q ∈ t.erase p, ∀ r ∈ (t.erase p).erase q, ∀ s ∈ σ \ t,
      ∑ u ∈ (σ \ t).erase s, F ℓ p q r s u = c := by
    intro p hp q hq r hr s hs
    rw [sum_congr rfl (h p hp q hq r hr s hs), sum_const, card_erase_of_mem hs, hst]
    norm_num
  have e2 : ∀ p ∈ t, ∀ q ∈ t.erase p, ∀ r ∈ (t.erase p).erase q,
      ∑ s ∈ σ \ t, ∑ u ∈ (σ \ t).erase s, F ℓ p q r s u = 2 * c := by
    intro p hp q hq r hr
    rw [sum_congr rfl (e1 p hp q hq r hr), sum_const, hst, nsmul_eq_mul]
    norm_num
  have e3 : ∀ p ∈ t, ∀ q ∈ t.erase p, ∑ r ∈ (t.erase p).erase q,
      ∑ s ∈ σ \ t, ∑ u ∈ (σ \ t).erase s, F ℓ p q r s u = 2 * c := by
    intro p hp q hq
    rw [sum_congr rfl (e2 p hp q hq), sum_const, card_erase_of_mem hq, card_erase_of_mem hp, ht]
    norm_num
  have e4 : ∀ p ∈ t, ∑ q ∈ t.erase p, ∑ r ∈ (t.erase p).erase q,
      ∑ s ∈ σ \ t, ∑ u ∈ (σ \ t).erase s, F ℓ p q r s u = 4 * c := by
    intro p hp
    rw [sum_congr rfl (e3 p hp), sum_const, card_erase_of_mem hp, ht, nsmul_eq_mul]
    norm_num
    ring
  rw [angleAvg4, sum_congr rfl e4, sum_const, ht, nsmul_eq_mul]
  norm_num
  ring

/-- A symmetric formula takes the same value in every labelling of the triangle `{p, q, r}` and of
the opposite pair `{s, u}`. -/
theorem IsSymm4.eq_of_mem {F : (Finset V → ℝ) → V → V → V → V → V → ℝ} (hF : IsSymm4 F)
    (ℓ : Finset V → ℝ) {p q r s u p' q' r' s' u' : V}
    (hp' : p' ∈ ({p, q, r} : Finset V)) (hq' : q' ∈ ({p, q, r} : Finset V).erase p')
    (hr' : r' ∈ (({p, q, r} : Finset V).erase p').erase q') (hs' : s' ∈ ({s, u} : Finset V))
    (hu' : u' ∈ ({s, u} : Finset V).erase s') :
    F ℓ p' q' r' s' u' = F ℓ p q r s u := by
  simp only [mem_erase, mem_insert, mem_singleton] at hp' hq' hr' hs' hu'
  obtain ⟨hq1, hq2⟩ := hq'
  obtain ⟨hr1, hr2, hr3⟩ := hr'
  obtain ⟨hu1, hu2⟩ := hu'
  have key : F ℓ p' q' r' s' u' = F ℓ p' q' r' s u := by
    rcases hs' with rfl | rfl <;> rcases hu2 with rfl | rfl
    · exact absurd rfl hu1
    · rfl
    · exact hF.swap_su _ _ _ _ _ _
    · exact absurd rfl hu1
  rw [key]
  rcases hp' with rfl | rfl | rfl <;> rcases hq2 with rfl | rfl | rfl <;>
    rcases hr3 with rfl | rfl | rfl <;>
    first
    | exact absurd rfl hq1
    | exact absurd rfl hr1
    | exact absurd rfl hr2
    | rfl
    | exact hF.swap_qr _ _ _ _ _ _
    | exact hF.swap_pq _ _ _ _ _ _
    | exact (hF.swap_qr _ _ _ _ _ _).trans (hF.swap_pq _ _ _ _ _ _)
    | exact (hF.swap_pq _ _ _ _ _ _).trans (hF.swap_qr _ _ _ _ _ _)
    | exact (hF.swap_qr _ _ _ _ _ _).trans
        ((hF.swap_pq _ _ _ _ _ _).trans (hF.swap_qr _ _ _ _ _ _))

/-- **The average of a symmetric formula** over the labellings of the 4-simplex `{p, q, r, s, u}`
at its triangle `{p, q, r}` is the formula in this labelling. -/
theorem angleAvg4_eq {F : (Finset V → ℝ) → V → V → V → V → V → ℝ} (hF : IsSymm4 F)
    (ℓ : Finset V → ℝ) {p q r s u : V} (hpq : p ≠ q) (hpr : p ≠ r) (hps : p ≠ s) (hpu : p ≠ u)
    (hqr : q ≠ r) (hqs : q ≠ s) (hqu : q ≠ u) (hrs : r ≠ s) (hru : r ≠ u) (hsu : s ≠ u) :
    angleAvg4 F ℓ {p, q, r, s, u} {p, q, r} = F ℓ p q r s u := by
  have hsd : ({p, q, r, s, u} : Finset V) \ {p, q, r} = {s, u} := by
    ext x
    simp only [mem_sdiff, mem_insert, mem_singleton]
    constructor
    · rintro ⟨h1, h2⟩
      tauto
    · rintro (rfl | rfl)
      · exact ⟨by tauto, by tauto⟩
      · exact ⟨by tauto, by
          rintro (h | h | h)
          · exact hpu h.symm
          · exact hqu h.symm
          · exact hru h.symm⟩
  have h3 : #({p, q, r} : Finset V) = 3 := by
    rw [card_insert_of_notMem (by simp [hpq, hpr]), card_pair hqr]
  refine angleAvg4_of_forall F ℓ h3 (by rw [hsd, card_pair hsu]) ?_
  rw [hsd]
  intro p' hp' q' hq' r' hr' s' hs' u' hu'
  exact hF.eq_of_mem ℓ hp' hq' hr' hs' hu'

/-- The dihedral angle of the 4-simplex `σ` at its triangle `t`, without choosing a labelling. -/
noncomputable def dihedralAt4 (ℓ : Finset V → ℝ) (σ t : Finset V) : ℝ := angleAvg4 dihedral4 ℓ σ t

/-- The dihedral angle of the 4-simplex `{p, q, r, s, u}` at its triangle `{p, q, r}` is the
length formula in this labelling. -/
theorem dihedralAt4_eq (ℓ : Finset V → ℝ) {p q r s u : V} (hpq : p ≠ q) (hpr : p ≠ r)
    (hps : p ≠ s) (hpu : p ≠ u) (hqr : q ≠ r) (hqs : q ≠ s) (hqu : q ≠ u) (hrs : r ≠ s)
    (hru : r ≠ u) (hsu : s ≠ u) :
    dihedralAt4 ℓ {p, q, r, s, u} {p, q, r} = dihedral4 ℓ p q r s u :=
  angleAvg4_eq isSymm4_dihedral4 ℓ hpq hpr hps hpu hqr hqs hqu hrs hru hsu

/-- Dihedral angles are invariant under scaling all lengths. -/
theorem dihedralAt4_smul {c : ℝ} (hc : c ≠ 0) (ℓ : Finset V → ℝ) (σ t : Finset V) :
    dihedralAt4 (fun f => c * ℓ f) σ t = dihedralAt4 ℓ σ t := by
  simp only [dihedralAt4, angleAvg4, dihedral4_smul ℓ hc]

/-! ## Deficit angles and the Regge action -/

/-- The sum of the dihedral angles at `t` of the 4-simplices around it. -/
noncomputable def angleSum4 (K : Complex4 V) (ℓ : Finset V → ℝ) (t : Finset V) : ℝ :=
  ∑ σ ∈ K.star t, dihedralAt4 ℓ σ t

/-- The **deficit angle** `δ_t = 2π - Σ_{σ ∋ t} θ_σ(t)` at a triangle `t`: zero where the geometry
around an interior triangle is flat. -/
noncomputable def deficit4 (K : Complex4 V) (ℓ : Finset V → ℝ) (t : Finset V) : ℝ :=
  2 * π - angleSum4 K ℓ t

/-- The boundary angle `ψ_t = π - Σ_{σ ∋ t} θ_σ(t)` at a boundary triangle `t`. -/
noncomputable def bdryAngle4 (K : Complex4 V) (ℓ : Finset V → ℝ) (t : Finset V) : ℝ :=
  π - angleSum4 K ℓ t

/-- The boundary triangles of `K`: triangles of boundary tetrahedra (tetrahedra contained in
exactly one 4-simplex). -/
def bdryTris4 (K : Complex4 V) : Finset (Finset V) :=
  K.tris.filter fun t => ∃ τ ∈ K.bdryTets, t ⊆ τ

/-- The interior triangles of `K`: triangles contained in no boundary tetrahedron. -/
def intTris4 (K : Complex4 V) : Finset (Finset V) :=
  K.tris.filter fun t => ¬ ∃ τ ∈ K.bdryTets, t ⊆ τ

/-- Every triangle is either interior or on the boundary. -/
theorem intTris4_union_bdryTris4 (K : Complex4 V) : intTris4 K ∪ bdryTris4 K = K.tris := by
  rw [union_comm]
  exact filter_union_filter_not_eq _ _

/-- No triangle is both interior and on the boundary. -/
theorem disjoint_intTris4_bdryTris4 (K : Complex4 V) : Disjoint (intTris4 K) (bdryTris4 K) := by
  rw [disjoint_comm]
  exact disjoint_filter_filter_not _ _ _

/-- The area of the triangle `t`, by Heron's formula: `Lightlike.Regge.triH ℓ t` is sixteen times the
squared area. -/
noncomputable def area4 (ℓ : Finset V → ℝ) (t : Finset V) : ℝ := √(Lightlike.Regge.triH ℓ t) / 4

/-- The **Regge action** of a 4-dimensional triangulation: the interior term `Σ_t A_t δ_t` and the
Hartle–Sorkin boundary term `Σ_{t ∈ ∂} A_t ψ_t`. -/
noncomputable def reggeAction4 (K : Complex4 V) (ℓ : Finset V → ℝ) : ℝ :=
  ∑ t ∈ intTris4 K, area4 ℓ t * deficit4 K ℓ t + ∑ t ∈ bdryTris4 K, area4 ℓ t * bdryAngle4 K ℓ t

/-- Without boundary tetrahedra every triangle is interior. -/
theorem intTris4_of_bdryTets_eq_empty {K : Complex4 V} (h : K.bdryTets = ∅) :
    intTris4 K = K.tris := by
  simp [intTris4, h]

/-- For a closed triangulation (no boundary tetrahedra) the Regge action is `Σ_t A_t δ_t`. -/
theorem reggeAction4_of_bdryTets_eq_empty {K : Complex4 V} (h : K.bdryTets = ∅)
    (ℓ : Finset V → ℝ) : reggeAction4 K ℓ = ∑ t ∈ K.tris, area4 ℓ t * deficit4 K ℓ t := by
  simp [reggeAction4, intTris4, bdryTris4, h]

/-! ## Areas -/

/-- Heron's formula and the Gram determinant: `16 A² = 4 · gram2`. -/
theorem triH_eq_gram2 (ℓ : Finset V → ℝ) {p q r : V} (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r) :
    Lightlike.Regge.triH ℓ {p, q, r} = 4 * gram2 ℓ p q r := by
  rw [Lightlike.Regge.triH_eq ℓ hpq hpr hqr]
  simp only [Lightlike.Regge.heron, gram2, ip, sq, hpq, hpr, hqr, Ne.symm hqr, ite_true, ite_false,
    pair_comm r p, pair_comm r q]
  ring

/-- The area of a triangle is `√gram2 / 2`. -/
theorem area4_eq (ℓ : Finset V → ℝ) {p q r : V} (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r) :
    area4 ℓ {p, q, r} = √(gram2 ℓ p q r) / 2 := by
  rw [area4, triH_eq_gram2 ℓ hpq hpr hqr, Real.sqrt_mul (by norm_num),
    show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  ring

/-! ## Scaling -/

/-- Deficit angles are invariant under scaling all lengths. -/
theorem deficit4_smul {c : ℝ} (hc : c ≠ 0) (K : Complex4 V) (ℓ : Finset V → ℝ) (t : Finset V) :
    deficit4 K (fun f => c * ℓ f) t = deficit4 K ℓ t := by
  simp only [deficit4, angleSum4, dihedralAt4_smul hc]

/-- Boundary angles are invariant under scaling all lengths. -/
theorem bdryAngle4_smul {c : ℝ} (hc : c ≠ 0) (K : Complex4 V) (ℓ : Finset V → ℝ)
    (t : Finset V) : bdryAngle4 K (fun f => c * ℓ f) t = bdryAngle4 K ℓ t := by
  simp only [bdryAngle4, angleSum4, dihedralAt4_smul hc]

omit [DecidableEq V] in
/-- Areas scale by `c²`. -/
theorem area4_smul (c : ℝ) (ℓ : Finset V → ℝ) (t : Finset V) :
    area4 (fun f => c * ℓ f) t = c ^ 2 * area4 ℓ t := by
  have : Lightlike.Regge.triH (fun f => c * ℓ f) t = (c ^ 2) ^ 2 * Lightlike.Regge.triH ℓ t := by
    simp only [Lightlike.Regge.triH, mul_pow, ← mul_sum]
    ring
  rw [area4, area4, this, Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
  ring

/-- The Regge action is homogeneous of degree two: `S(cℓ) = c² S(ℓ)` for `c ≠ 0`. -/
theorem reggeAction4_smul {c : ℝ} (hc : c ≠ 0) (K : Complex4 V) (ℓ : Finset V → ℝ) :
    reggeAction4 K (fun f => c * ℓ f) = c ^ 2 * reggeAction4 K ℓ := by
  simp only [reggeAction4, deficit4_smul hc, bdryAngle4_smul hc, area4_smul, mul_add, mul_sum,
    mul_assoc]

/-! ## Equal lengths -/

/-- The vertices of a 4-simplex containing a triangle `t` can be labelled `p, q, r, s, u` with
`t = {p, q, r}`. -/
theorem exists_label4 {σ t : Finset V} (hσ : #σ = 5) (ht : #t = 3) (hts : t ⊆ σ) :
    ∃ p q r s u, p ≠ q ∧ p ≠ r ∧ p ≠ s ∧ p ≠ u ∧ q ≠ r ∧ q ≠ s ∧ q ≠ u ∧ r ≠ s ∧ r ≠ u ∧
      s ≠ u ∧ t = {p, q, r} ∧ σ = {p, q, r, s, u} := by
  obtain ⟨p, q, r, hpq, hpr, hqr, rfl⟩ := card_eq_three.mp ht
  have hd : #(σ \ {p, q, r}) = 2 := by rw [card_sdiff_of_subset hts, hσ, ht]
  obtain ⟨s, u, hsu, hsd⟩ := card_eq_two.mp hd
  have hs : s ∈ σ \ {p, q, r} := hsd ▸ by simp
  have hu : u ∈ σ \ {p, q, r} := hsd ▸ by simp
  simp only [mem_sdiff, mem_insert, mem_singleton, not_or] at hs hu
  refine ⟨p, q, r, s, u, hpq, hpr, Ne.symm hs.2.1, Ne.symm hu.2.1, hqr, Ne.symm hs.2.2.1,
    Ne.symm hu.2.2.1, Ne.symm hs.2.2.2, Ne.symm hu.2.2.2, hsu, rfl, ?_⟩
  rw [← union_sdiff_of_subset hts, hsd]
  ext x
  simp only [mem_union, mem_insert, mem_singleton]
  tauto

/-- With all lengths `a ≠ 0`, every dihedral angle is `arccos (1/4)`. -/
theorem dihedralAt4_const {a : ℝ} (ha : a ≠ 0) {σ t : Finset V} (hσ : #σ = 5) (ht : #t = 3)
    (hts : t ⊆ σ) : dihedralAt4 (fun _ => a) σ t = arccos (1 / 4) := by
  obtain ⟨p, q, r, s, u, hpq, hpr, hps, hpu, hqr, hqs, hqu, hrs, hru, hsu, rfl, rfl⟩ :=
    exists_label4 hσ ht hts
  rw [dihedralAt4_eq _ hpq hpr hps hpu hqr hqs hqu hrs hru hsu, dihedral4,
    cosDihedral4_regular ha hpq hpr hps hpu hqr hqs hqu hrs hru hsu]

/-- **Equal lengths**: a triangle in `n` 4-simplices has deficit angle `2π - n · arccos(1/4)`. -/
theorem deficit4_const (K : Complex4 V) {a : ℝ} (ha : a ≠ 0) {t : Finset V} (ht : #t = 3) :
    deficit4 K (fun _ => a) t = 2 * π - #(K.star t) * arccos (1 / 4) := by
  have : ∀ σ ∈ K.star t, dihedralAt4 (fun _ => a) σ t = arccos (1 / 4) := by
    intro σ hσ
    obtain ⟨hσK, hts⟩ := Lightlike.FourD.Complex4.mem_star.mp hσ
    exact dihedralAt4_const ha (K.card_eq σ hσK) ht hts
  rw [deficit4, angleSum4, sum_congr rfl this, sum_const, nsmul_eq_mul]

end Lightlike.Regge4
