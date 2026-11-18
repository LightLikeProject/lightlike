import Mathlib

/-!
# Discrete Gauss–Bonnet for closed triangulated surfaces

For a finite set `T` of triangles on a vertex type, in which every edge lies in exactly two triangles (a closed surface),
and angles `θ_t(v)` with `Σ_{v ∈ t} θ_t(v) = π` in every triangle (Euclidean triangles), the deficit angles
`2π - Σ_{t ∋ v} θ_t(v)` add up to `2π (V - E + F) = 2π χ` (`discrete_gauss_bonnet`). The proof is purely combinatorial: the
angle sum is `π F` (`sum_deficit`, a double count of the vertex–triangle incidences) and `3 F = 2 E` (`three_mul_card`, a double
count of the edge–triangle incidences). The angles of a Euclidean triangle add up to `π` (`sum_angleOf`, from Mathlib's
`EuclideanGeometry.angle_add_angle_add_angle_eq_pi`).

The round 2-sphere gives `4π`: the octahedron inscribed in the unit sphere (six vertices `±e_i`, eight equilateral faces, the
chordal edge lengths of the sphere) has deficit sum `4π` (`octahedron_deficit_sum`). The closedness hypothesis is needed: the
octahedron minus one face has deficit sum `2π · 6 - π · 7 = 5π`, not `2π χ = 2π` (`octOpen_deficit_sum_ne`).

## Main results

* `discrete_gauss_bonnet`: the deficit sum of a closed triangulated surface is `2π (V - E + F)`.
* `sum_angleOf`: the angles of a Euclidean triangle add up to `π`.
* `octahedron_deficit_sum`: the octahedron in the unit sphere has deficit sum `4π`.
* `octOpen_deficit_sum_ne`: wrong model, the octahedron with a face removed.

**Limits.** An abstract set of triangles with Euclidean angles; no Regge action, no convergence statement, no statement about a
triangulation of a manifold other than this closed one. Only the octahedron is checked as an instance.
-/

open Finset Real EuclideanGeometry
namespace Lightlike.Regge

variable {V : Type*} [DecidableEq V]

/-- The vertices of a set of triangles. -/
def triVerts (T : Finset (Finset V)) : Finset V := T.biUnion id

/-- The edges of a set of triangles. -/
def triEdges (T : Finset (Finset V)) : Finset (Finset V) := T.biUnion (powersetCard 2)

/-- The sum over the triangles containing `v` of the angle of the triangle at `v`. -/
noncomputable def angleAt (T : Finset (Finset V)) (θ : Finset V → V → ℝ) (v : V) : ℝ :=
  ∑ t ∈ T.filter (v ∈ ·), θ t v

/-- The deficit angle at a vertex: `2π` minus the sum of the angles of the triangles around it. -/
noncomputable def vertexDeficit (T : Finset (Finset V)) (θ : Finset V → V → ℝ) (v : V) : ℝ :=
  2 * π - angleAt T θ v

/-- **The deficit sum is `2π V - π F` when every triangle has angle sum `π`.** -/
theorem sum_deficit (T : Finset (Finset V)) (θ : Finset V → V → ℝ)
    (hθ : ∀ t ∈ T, ∑ v ∈ t, θ t v = π) :
    ∑ v ∈ triVerts T, vertexDeficit T θ v = 2 * π * (triVerts T).card - π * T.card := by
  unfold vertexDeficit angleAt
  rw [sum_sub_distrib, sum_const, nsmul_eq_mul]
  have h : ∑ v ∈ triVerts T, ∑ t ∈ T.filter (v ∈ ·), θ t v = π * T.card := by
    calc ∑ v ∈ triVerts T, ∑ t ∈ T.filter (v ∈ ·), θ t v
        = ∑ t ∈ T, ∑ v ∈ t, θ t v := by
          rw [sum_comm' (t' := T) (s' := fun t => t)]
          · intro v t
            simp only [triVerts, mem_biUnion, id, mem_filter]
            constructor
            · rintro ⟨_, ht, hv⟩; exact ⟨hv, ht⟩
            · rintro ⟨hv, ht⟩; exact ⟨⟨t, ht, hv⟩, ht, hv⟩
      _ = ∑ t ∈ T, π := sum_congr rfl hθ
      _ = π * T.card := by simp [mul_comm]
  rw [h]; ring


/-- **Three times the number of triangles is twice the number of edges** when every edge lies in exactly
two triangles. -/
theorem three_mul_card (T : Finset (Finset V)) (h3 : ∀ t ∈ T, t.card = 3)
    (hclosed : ∀ e ∈ triEdges T, (T.filter (e ⊆ ·)).card = 2) :
    3 * T.card = 2 * (triEdges T).card := by
  have h : ∑ t ∈ T, ∑ e ∈ powersetCard 2 t, (1 : ℕ) = ∑ e ∈ triEdges T, ∑ t ∈ T.filter (e ⊆ ·), (1 : ℕ) := by
    refine sum_comm' ?_
    intro t e
    simp only [triEdges, mem_biUnion, mem_powersetCard, mem_filter]
    constructor
    · rintro ⟨ht, hs, hc⟩; exact ⟨⟨ht, hs⟩, t, ht, hs, hc⟩
    · rintro ⟨⟨ht, hs⟩, a, ha, hsa, hca⟩; exact ⟨ht, hs, hca⟩
  have l : ∑ t ∈ T, ∑ e ∈ powersetCard 2 t, (1 : ℕ) = 3 * T.card := by
    rw [mul_comm, ← smul_eq_mul, ← sum_const]
    refine sum_congr rfl fun t ht => ?_
    simp [h3 t ht, Nat.choose]
  have r : ∑ e ∈ triEdges T, ∑ t ∈ T.filter (e ⊆ ·), (1 : ℕ) = 2 * (triEdges T).card := by
    rw [mul_comm, ← smul_eq_mul, ← sum_const]
    exact sum_congr rfl fun e he => by simp [hclosed e he]
  rw [← l, ← r]; exact h


/-- **Discrete Gauss–Bonnet.** For a closed set of triangles (every edge in exactly two triangles) whose angles add up
to `π` in each triangle, the deficit sum is `2π (V - E + F)`. -/
theorem discrete_gauss_bonnet (T : Finset (Finset V)) (h3 : ∀ t ∈ T, t.card = 3)
    (hclosed : ∀ e ∈ triEdges T, (T.filter (e ⊆ ·)).card = 2) (θ : Finset V → V → ℝ)
    (hθ : ∀ t ∈ T, ∑ v ∈ t, θ t v = π) :
    ∑ v ∈ triVerts T, vertexDeficit T θ v =
      2 * π * ((triVerts T).card - (triEdges T).card + T.card) := by
  rw [sum_deficit T θ hθ]
  have h := three_mul_card T h3 hclosed
  have h' : (3 : ℝ) * T.card = 2 * (triEdges T).card := by exact_mod_cast h
  nlinarith [Real.pi_pos]


section Geometric

variable {P : Type*} [NormedAddCommGroup P] [InnerProductSpace ℝ P]

/-- The angle at the vertex `v` of the triangle `t` of points `p`: the average of `∠ x v y` over the ordered pairs of the
other two vertices (`∠ x v y = ∠ y v x`, so it is the angle of the triangle at `v`). -/
noncomputable def angleOf (p : V → P) (t : Finset V) (v : V) : ℝ :=
  (∑ x ∈ t.erase v, ∑ y ∈ (t.erase v).erase x, ∠ (p x) (p v) (p y)) / 2

/-- **The angles of a Euclidean triangle add up to `π`.** -/
theorem sum_angleOf (p : V → P) (hp : Function.Injective p) {t : Finset V} (ht : t.card = 3) :
    ∑ v ∈ t, angleOf p t v = π := by
  obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := card_eq_three.1 ht
  have e1 : ({a, b, c} : Finset V).erase a = {b, c} := by
    ext x; simp only [mem_erase, mem_insert, mem_singleton]; constructor
    · rintro ⟨h, rfl | rfl | rfl⟩ <;> first | exact absurd rfl h | simp
    · rintro (rfl | rfl) <;> simp [hab.symm, hac.symm]
  have e2 : ({a, b, c} : Finset V).erase b = {a, c} := by
    ext x; simp only [mem_erase, mem_insert, mem_singleton]; constructor
    · rintro ⟨h, rfl | rfl | rfl⟩ <;> first | exact absurd rfl h | simp
    · rintro (rfl | rfl) <;> simp [hab, hbc.symm]
  have e3 : ({a, b, c} : Finset V).erase c = {a, b} := by
    ext x; simp only [mem_erase, mem_insert, mem_singleton]; constructor
    · rintro ⟨h, rfl | rfl | rfl⟩ <;> first | exact absurd rfl h | simp
    · rintro (rfl | rfl) <;> simp [hac, hbc]
  have pair2 : ∀ {x y : V} (f : V → V → ℝ), x ≠ y →
      ∑ u ∈ ({x, y} : Finset V), ∑ w ∈ ({x, y} : Finset V).erase u, f u w = f x y + f y x := by
    intro x y f hxy
    have ex : ({x, y} : Finset V).erase x = {y} := erase_insert (by simpa using hxy)
    have ey : ({x, y} : Finset V).erase y = {x} := by
      rw [pair_comm]; exact erase_insert (by simpa using hxy.symm)
    rw [sum_pair hxy, ex, ey]; simp
  have hA : angleOf p {a, b, c} a = ∠ (p b) (p a) (p c) := by
    unfold angleOf
    rw [e1, pair2 (fun x y => ∠ (p x) (p a) (p y)) hbc, angle_comm (p c) (p a) (p b)]; ring
  have hB : angleOf p {a, b, c} b = ∠ (p a) (p b) (p c) := by
    unfold angleOf
    rw [e2, pair2 (fun x y => ∠ (p x) (p b) (p y)) hac, angle_comm (p c) (p b) (p a)]; ring
  have hC : angleOf p {a, b, c} c = ∠ (p a) (p c) (p b) := by
    unfold angleOf
    rw [e3, pair2 (fun x y => ∠ (p x) (p c) (p y)) hab, angle_comm (p b) (p c) (p a)]; ring
  rw [sum_insert (by simp [hab, hac]), sum_insert (by simp [hbc]), sum_singleton, hA, hB, hC]
  have := angle_add_angle_add_angle_eq_pi (p₁ := p a) (p₂ := p b) (p c) (fun h => hab (hp h).symm)
  rw [angle_comm (p a) (p c) (p b)]
  linarith [this, angle_comm (p c) (p a) (p b)]

end Geometric


/-- The six vertices `±e₁, ±e₂, ±e₃` of the octahedron inscribed in the unit sphere of `ℝ³`. -/
noncomputable def octPts : Fin 6 → EuclideanSpace ℝ (Fin 3) :=
  ![EuclideanSpace.single 0 1, EuclideanSpace.single 0 (-1), EuclideanSpace.single 1 1,
    EuclideanSpace.single 1 (-1), EuclideanSpace.single 2 1, EuclideanSpace.single 2 (-1)]

theorem octPts_injective : Function.Injective octPts := by
  intro i j h
  have h' : ∀ k, octPts i k = octPts j k := fun k => by rw [h]
  fin_cases i <;> fin_cases j <;> first | rfl | (exfalso; have a := h' 0; have b := h' 1; have c := h' 2; simp [octPts] at a b c <;> first | (norm_num at a; done) | (norm_num at b; done) | (norm_num at c; done))

/-- The eight faces of the octahedron: one vertex of each antipodal pair `{0,1}`, `{2,3}`, `{4,5}`. -/
def octTris : Finset (Finset (Fin 6)) :=
  (({0, 1} : Finset (Fin 6)) ×ˢ ({2, 3} : Finset (Fin 6)) ×ˢ ({4, 5} : Finset (Fin 6))).image
    fun x => {x.1, x.2.1, x.2.2}

theorem octTris_card : octTris.card = 8 := by decide
theorem octTris_h3 : ∀ t ∈ octTris, t.card = 3 := by decide
theorem octTris_closed : ∀ e ∈ triEdges octTris, (octTris.filter (e ⊆ ·)).card = 2 := by decide
theorem octVerts_card : (triVerts octTris).card = 6 := by decide
theorem octEdges_card : (triEdges octTris).card = 12 := by decide


theorem octTris_angle_sum : ∀ t ∈ octTris, ∑ v ∈ t, angleOf octPts t v = π := fun t ht =>
  sum_angleOf octPts octPts_injective (octTris_h3 t ht)

/-- **The round 2-sphere gives `4π`.** The sum of the deficit angles of the octahedron inscribed in the unit sphere, with
the Euclidean angles of its eight equilateral faces, is `4π = 2π χ`. -/
theorem octahedron_deficit_sum :
    ∑ v ∈ triVerts octTris, vertexDeficit octTris (angleOf octPts) v = 4 * π := by
  rw [discrete_gauss_bonnet octTris octTris_h3 octTris_closed _ octTris_angle_sum, octVerts_card,
    octEdges_card, octTris_card]
  push_cast; ring

/-- The octahedron with one face removed. -/
def octOpen : Finset (Finset (Fin 6)) := octTris.erase {0, 2, 4}

theorem octOpen_card : octOpen.card = 7 := by decide
theorem octOpen_verts_card : (triVerts octOpen).card = 6 := by decide
theorem octOpen_edges_card : (triEdges octOpen).card = 12 := by decide
theorem octOpen_not_closed : ¬ ∀ e ∈ triEdges octOpen, (octOpen.filter (e ⊆ ·)).card = 2 := by decide

/-- **Wrong model: a surface with boundary.** The octahedron minus one face is not closed, and its deficit sum is `5π`, not
`2π (V - E + F) = 2π`: the closedness hypothesis of `discrete_gauss_bonnet` is needed. -/
theorem octOpen_deficit_sum_ne :
    ∑ v ∈ triVerts octOpen, vertexDeficit octOpen (angleOf octPts) v ≠
      2 * π * ((triVerts octOpen).card - (triEdges octOpen).card + octOpen.card) := by
  have h : ∀ t ∈ octOpen, ∑ v ∈ t, angleOf octPts t v = π := fun t ht =>
    octTris_angle_sum t (mem_of_mem_erase ht)
  rw [sum_deficit octOpen _ h, octOpen_verts_card, octOpen_edges_card, octOpen_card]
  push_cast
  intro hne
  nlinarith [Real.pi_pos]

end Lightlike.Regge
