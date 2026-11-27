import Lightlike.TuraevViro.Hexagon
import Lightlike.SpinFoam.Ooguri

/-!
# The Crane–Yetter state sum

The state sum of Crane, Kauffman and Yetter on a 4-complex at `q = e^{iπ/r}` (`r ≥ 3`): a colour in `{0, …, r - 2}`
(doubled spin) on every triangle and every tetrahedron, the signed dimension `Δ_n = (-1)^n [n + 1]` of every triangle
and of every tetrahedron, the factor `θ₁⁻¹ θ₂⁻¹` of every tetrahedron, and a vertex amplitude of every 4-simplex which is
the evaluation of the ribbon graph of Fig. 23 of Crane, Kauffman and Yetter, *State-sum invariants of 4-manifolds, I*
(J. Knot Theory Ramif. 6 (1997) 177, arXiv:hep-th/9409167), with two crossings. The factor `N^{n₀ - n₁}`,
`N = -2r / (q - q⁻¹)²`, corrects for the numbers of vertices and edges.

* `tlDelta`, `tlTheta`, `tlTet`: the Kauffman–Lins evaluations of the loop, the theta graph and the tetrahedral graph
  (Kauffman–Lins, *Temperley–Lieb recoupling theory and invariants of 3-manifolds*, Chap. 7), in doubled spins.
* `cyVertexLoc`: the closed form of the vertex of an ordered 4-simplex, from the evaluation of the diagram of Fig. 23:
  `Φ = (-1)^s A^P Σ_x Δ_x λ^{a₀ b₀}_x Π_t Tet[a_t a_{t+1} x; b_{t+1} b_t c_t] / θ(a_{t+1}, b_{t+1}, x)`, with `A = e^{iπ/(2r)}`
  and `λ = Rbr`; it is complex. `cyVertexAt` is the vertex of a 4-simplex of a complex, the complex conjugate on a
  4-simplex whose orientation is `-1`.
* `craneYetter`: the state sum.

The closed form is the specification checked numerically against the evaluation of the diagram (all admissible
colourings of a 4-simplex at `r = 3, 4, 5`), the 3-3 identity and the values `N` on `S⁴` and `N^{3/2} κ^σ` on `CP²` at
`r = 3`; those checks are numerical evidence, not proofs.
-/

open Finset Lightlike.Pentagon Lightlike.FourD

namespace Lightlike.TV

/-- **The signed dimension** `Δ_n = (-1)^n [n + 1]` of the colour `n` (doubled spin). -/
noncomputable def tlDelta (r n : ℕ) : ℝ := (-1) ^ n * qnum r (n + 1)

/-- **The theta graph** `θ(a, b, c) = (-1)^{(a+b+c)/2} [(a+b+c)/2 + 1]! [m]! [n]! [p]! / ([a]! [b]! [c]!)`,
`m = (a + b - c)/2`, `n = (b + c - a)/2`, `p = (a + c - b)/2` (Kauffman–Lins), for an admissible triad (`qAdm`), and
`0` otherwise. -/
noncomputable def tlTheta (r a b c : ℕ) : ℝ :=
  if qAdm r a b c then
    (-1) ^ ((a + b + c) / 2) * qfact r ((a + b + c) / 2 + 1) * qfact r ((a + b - c) / 2) *
      qfact r ((b + c - a) / 2) * qfact r ((a + c - b) / 2) / (qfact r a * qfact r b * qfact r c)
  else 0

/-- **The tetrahedral graph** `Tet[A B E; C D F]` (Kauffman–Lins), with the triads `(A, D, E)`, `(B, C, E)`, `(A, B, F)`,
`(C, D, F)`:
`(I! / E!) Σ_{max aᵢ ≤ z ≤ min bⱼ} (-1)^z [z + 1]! / (Π_i [z - aᵢ]! Π_j [bⱼ - z]!)`, with `a₁ = (A + D + E)/2`, …,
`b₁ = (B + D + E + F)/2`, …, `I! = Π_{i,j} [bⱼ - aᵢ]!` and `E! = [A]! [B]! [C]! [D]! [E]! [F]!`. It is `0` unless the
four triads are admissible. -/
noncomputable def tlTet (r A B E C D F : ℕ) : ℝ :=
  if qAdm r A D E ∧ qAdm r B C E ∧ qAdm r A B F ∧ qAdm r C D F then
    (∏ i : Fin 4, ∏ j : Fin 3, qfact r (![(B + D + E + F) / 2, (A + C + E + F) / 2, (A + B + C + D) / 2] j -
        ![(A + D + E) / 2, (B + C + E) / 2, (A + B + F) / 2, (C + D + F) / 2] i)) /
      (qfact r A * qfact r B * qfact r C * qfact r D * qfact r E * qfact r F) *
    ∑ z ∈ Icc (max (max ((A + D + E) / 2) ((B + C + E) / 2)) (max ((A + B + F) / 2) ((C + D + F) / 2)))
        (min (min ((B + D + E + F) / 2) ((A + C + E + F) / 2)) ((A + B + C + D) / 2)),
      (-1) ^ z * qfact r (z + 1) /
        ((∏ i : Fin 4, qfact r (z - ![(A + D + E) / 2, (B + C + E) / 2, (A + B + F) / 2, (C + D + F) / 2] i)) *
          ∏ j : Fin 3, qfact r (![(B + D + E + F) / 2, (A + C + E + F) / 2, (A + B + C + D) / 2] j - z))
  else 0

/-- **The vertex of an ordered 4-simplex** (closed form of the diagram of Fig. 23 of Crane–Kauffman–Yetter): `J F` is the
colour of the triangle `F` (a set of three local vertices `0 < … < 4`) and `I m` the colour of the tetrahedron omitting
the local vertex `m`. `Φ = (-1)^s A^P Σ_x Δ_x λ^{a₀ b₀}_x Π_{t < 5} Tet[a_t a_{t+1} x; b_{t+1} b_t c_t] / θ(a_{t+1}, b_{t+1}, x)`
with `(a₅, b₅) = (b₀, a₀)`. -/
noncomputable def cyVertexLoc (r : ℕ) (J : Finset (Fin 5) → ℕ) (I : Fin 5 → ℕ) : ℂ :=
  let j : Fin 5 → Fin 5 → Fin 5 → ℕ := fun x y z => J {x, y, z}
  let a : Fin 6 → ℕ := ![j 2 3 4, I 0, j 1 2 3, I 4, j 0 1 2, I 3]
  let b : Fin 6 → ℕ := ![I 3, j 0 1 4, I 2, j 0 3 4, I 1, j 2 3 4]
  let c : Fin 5 → ℕ := ![j 1 2 4, j 1 3 4, j 0 1 3, j 0 2 3, j 0 2 4]
  let pr : ℕ → ℤ := fun x => ((x * (x + 2) : ℕ) : ℤ)
  let P : ℤ := (-pr (I 4) + pr (I 3) - pr (I 2) - pr (I 0) + pr (j 0 1 3) + pr (j 1 2 3) + pr (j 1 3 4) +
    pr (j 2 3 4)) / 2
  let s : ℤ := (((j 1 2 3 : ℕ) + j 1 3 4 - I 0 : ℤ) + ((j 0 3 4 : ℕ) + j 0 2 3 - I 1 : ℤ) +
    ((j 2 3 4 : ℕ) + j 0 2 4 - I 1 : ℤ) + ((j 0 1 3 : ℕ) + j 0 3 4 - I 2 : ℤ) +
    ((j 0 2 4 : ℕ) + j 0 1 2 - I 3 : ℤ) + ((j 0 1 2 : ℕ) + j 0 2 3 - I 4 : ℤ)) / 2
  (-1 : ℂ) ^ s * qHalf r ^ P *
    ∑ x ∈ range (2 * (r - 2) + 1),
      if qAdm r (a 0) (b 0) x then
        (tlDelta r x : ℂ) * Rbr r (a 0) (b 0) x *
          ∏ t : Fin 5, ((tlTet r (a t.castSucc) (a t.succ) x (b t.succ) (b t.castSucc) (c t) : ℝ) : ℂ) /
            (tlTheta r (a t.succ) (b t.succ) x : ℂ)
      else 0


variable {V : Type*} [LinearOrder V]

/-- **The vertex of a 4-simplex `s`** of a coloured complex (`col` colours the triangles and the tetrahedra): the closed
form `cyVertexLoc` on the sorted vertices of `s`, complex conjugated if the orientation `o` of `s` is not `1`
(Crane–Kauffman–Yetter, p. 20: the mirror image of the diagram on a 4-simplex whose vertex order induces the other
orientation). It is `0` unless `s` has five vertices. -/
noncomputable def cyVertexAt (r : ℕ) (col : Finset V → ℕ) (s : Finset V) (o : ℤ) : ℂ :=
  if h : #s = 5 then
    let v := s.orderEmbOfFin h
    let Φ := cyVertexLoc r (fun F => col (F.map v.toEmbedding)) (fun m => col (s.erase (v m)))
    if o = 1 then Φ else (starRingEnd ℂ) Φ
  else 0

/-- **The weight of a tetrahedron** `t = {v₀ < v₁ < v₂ < v₃}` of colour `i`: `Δ_i / (θ₁ θ₂)`, with `θ₁ = θ(i, c(v₁v₂v₃), c(v₀v₁v₃))`
(the faces opposite the lowest and the third vertex) and `θ₂ = θ(i, c(v₀v₂v₃), c(v₀v₁v₂))` (the other two). -/
noncomputable def cyTetWeight (r : ℕ) (col : Finset V → ℕ) (t : Finset V) : ℝ :=
  if h : #t = 4 then
    let v := t.orderEmbOfFin h
    tlDelta r (col t) / (tlTheta r (col t) (col (t.erase (v 0))) (col (t.erase (v 2))) *
      tlTheta r (col t) (col (t.erase (v 1))) (col (t.erase (v 3))))
  else 0

/-- **The normalisation** `N = -2r / (q - q⁻¹)² = r / (2 sin²(π/r))` of the Crane–Yetter state sum. -/
noncomputable def cyN (r : ℕ) : ℝ := r / (2 * Real.sin (Real.pi / r) ^ 2)

/-- **The weight of a colouring** of the triangles and tetrahedra of `K`, for an orientation `o` of the 4-simplices:
`Π_triangles Δ · Π_tetrahedra Δ/(θ₁θ₂) · Π_4-simplices Φ`. -/
noncomputable def craneYetterWeight (r : ℕ) (K : Complex4 V) (o : Finset V → ℤ) (col : Finset V → ℕ) : ℂ :=
  (∏ f ∈ K.tris, (tlDelta r (col f) : ℂ)) * (∏ t ∈ K.tets, (cyTetWeight r col t : ℂ)) *
    ∏ s ∈ K.simps, cyVertexAt r col s (o s)

/-- **The Crane–Yetter state sum** `N^{n₀ - n₁} Σ_col weight(col)` of a 4-complex `K` with an orientation `o`, at
`q = e^{iπ/r}`: the sum over the colourings of the triangles and the tetrahedra by `{0, …, r - 2}` (doubled spins). -/
noncomputable def craneYetter (r : ℕ) (K : Complex4 V) (o : Finset V → ℤ) : ℂ :=
  (cyN r : ℂ) ^ (((K.faces 0).card : ℤ) - (K.faces 1).card) *
    ∑ c ∈ (Lightlike.SpinFoam.colFaces K).pi (fun _ => range (r - 1)),
      craneYetterWeight r K o (Lightlike.PR.extS (Lightlike.SpinFoam.colFaces K) c)


/-! ### The zero colouring and the conjugation -/

lemma qAdm_zero {r : ℕ} : qAdm r 0 0 0 := by
  unfold qAdm Lightlike.Pentagon.Tri; omega

lemma qAdm_zero_zero_iff {r x : ℕ} : qAdm r 0 0 x ↔ x = 0 := by
  unfold qAdm Lightlike.Pentagon.Tri; omega

/-- `Δ₀ = 1`. -/
lemma tlDelta_zero {r : ℕ} (hr : 2 ≤ r) : tlDelta r 0 = 1 := by
  simp [tlDelta, qnum_one hr]

/-- `θ(0, 0, 0) = 1`. -/
lemma tlTheta_zero {r : ℕ} (hr : 2 ≤ r) : tlTheta r 0 0 0 = 1 := by
  unfold tlTheta
  rw [if_pos qAdm_zero]
  simp [qfact_zero', qfact_one' hr]

/-- `Tet[0 0 0; 0 0 0] = 1`. -/
lemma tlTet_zero {r : ℕ} (hr : 2 ≤ r) : tlTet r 0 0 0 0 0 0 = 1 := by
  unfold tlTet
  rw [if_pos ⟨qAdm_zero, qAdm_zero, qAdm_zero, qAdm_zero⟩]
  simp [Fin.prod_univ_succ, qfact_zero', qfact_one' hr]

/-- `R^{00}_0 = 1`. -/
lemma Rbr_zero (r : ℕ) : Rbr r 0 0 0 = 1 := by
  simp [Rbr]

/-- **The vertex of the zero colouring is `1`.** -/
lemma cyVertexLoc_zero {r : ℕ} (hr : 2 ≤ r) : cyVertexLoc r (fun _ => 0) (fun _ => 0) = 1 := by
  unfold cyVertexLoc
  simp only [Nat.cast_zero, zero_add, sub_self, add_zero, Int.zero_ediv, zpow_zero, one_mul]
  have h1 : ∀ x : Fin 5, ![(0 : ℕ), 0, 0, 0, 0] x = 0 := by decide
  have h2 : ∀ x : Fin 5, ![(0 : ℕ), 0, 0, 0, 0, 0] x.castSucc = 0 := by decide
  rw [Finset.sum_eq_single 0]
  · simp [qAdm_zero, tlDelta_zero hr, Rbr_zero, h1, h2, tlTet_zero hr, tlTheta_zero hr]
  · intro x _ hx
    rw [if_neg]
    intro h
    exact hx (qAdm_zero_zero_iff.1 (by simpa using h))
  · intro h
    exact absurd (by simp) h

/-- **The vertex of a 4-simplex of orientation `-1` is the complex conjugate** of that of orientation `1`. -/
lemma cyVertexAt_neg (r : ℕ) (col : Finset V → ℕ) (s : Finset V) :
    cyVertexAt r col s (-1) = (starRingEnd ℂ) (cyVertexAt r col s 1) := by
  unfold cyVertexAt
  split_ifs with h h1 h2 <;> first | rfl | simp_all


/-- The weight of a tetrahedron of the zero colouring is `1`. -/
lemma cyTetWeight_zero {r : ℕ} (hr : 2 ≤ r) {t : Finset V} (ht : #t = 4) :
    cyTetWeight r (fun _ => 0) t = 1 := by
  unfold cyTetWeight
  rw [dif_pos ht]
  simp [tlDelta_zero hr, tlTheta_zero hr]

/-- The vertex of a 4-simplex of the zero colouring is `1`, for either orientation. -/
lemma cyVertexAt_zero {r : ℕ} (hr : 2 ≤ r) {s : Finset V} (hs : #s = 5) (o : ℤ) :
    cyVertexAt r (fun _ => 0) s o = 1 := by
  unfold cyVertexAt
  rw [dif_pos hs]
  have h := cyVertexLoc_zero hr
  simp only [h]
  split_ifs <;> simp

/-- **The zero colouring has weight `1`** on every complex, for every orientation. -/
theorem craneYetterWeight_zero {r : ℕ} (hr : 2 ≤ r) (K : Complex4 V) (o : Finset V → ℤ) :
    craneYetterWeight r K o (fun _ => 0) = 1 := by
  unfold craneYetterWeight
  have h1 : ∏ f ∈ K.tris, (tlDelta r ((fun _ => 0 : Finset V → ℕ) f) : ℂ) = 1 :=
    Finset.prod_eq_one fun f _ => by simp [tlDelta_zero hr]
  have h2 : ∏ t ∈ K.tets, (cyTetWeight r (fun _ => 0) t : ℂ) = 1 :=
    Finset.prod_eq_one fun t ht => by
      rw [cyTetWeight_zero hr (K.card_of_mem_faces ht)]; simp
  have h3 : ∏ s ∈ K.simps, cyVertexAt r (fun _ => 0) s (o s) = 1 :=
    Finset.prod_eq_one fun s hs => cyVertexAt_zero hr (K.card_eq s hs) _
  rw [h1, h2, h3]; simp

end Lightlike.TV
