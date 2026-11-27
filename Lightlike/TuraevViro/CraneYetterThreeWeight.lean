import Lightlike.TuraevViro.CraneYetterThree

/-!
# The weights of the Crane–Yetter state sum at `r = 3`

At `r = 3` with colours `0, 1` the weight of a triangle is `(-1)^n`, the weight of a tetrahedron is the integer
`(-1)^i θ₃(i, j_l, j_{t₃}) θ₃(i, j_{o₁}, j_{o₂})` (`θ₃ = theta3Z`), and the weight of a 4-simplex is the exact vertex
of `cyVertexLoc_three`.
-/

open Finset Lightlike.Pentagon Lightlike.FourD

namespace Lightlike.TV

variable {V : Type*} [LinearOrder V]

/-- **The weight of a triangle at `r = 3`**: `Δ_n = (-1)^n` for the colours `0, 1`. -/
lemma tlDelta_three {n : ℕ} (hn : n ≤ 1) : tlDelta 3 n = (-1 : ℝ) ^ n := by
  interval_cases n
  · simp [tlDelta3_zero]
  · simp [tlDelta3_one]

/-- **The weight of a tetrahedron at `r = 3`** with colours `0, 1`: `(-1)^i θ₃(i, j_l, j_{t₃}) θ₃(i, j_{o₁}, j_{o₂})`,
an integer in `{-1, 0, 1}`. -/
lemma cyTetWeight_three (col : Finset V → ℕ) (t : Finset V) (ht : #t = 4) (hc : ∀ f, col f ≤ 1) :
    cyTetWeight 3 col t =
      (((-1 : ℤ) ^ col t * theta3Z (col t) (col (t.erase ((t.orderEmbOfFin ht) 0)))
          (col (t.erase ((t.orderEmbOfFin ht) 2))) *
        theta3Z (col t) (col (t.erase ((t.orderEmbOfFin ht) 1))) (col (t.erase ((t.orderEmbOfFin ht) 3))) : ℤ) : ℝ) := by
  unfold cyTetWeight
  rw [dif_pos ht]
  simp only []
  rw [tlDelta_three (hc _), tlTheta3_eq _ _ _ (hc _) (hc _) (hc _), tlTheta3_eq _ _ _ (hc _) (hc _) (hc _)]
  rcases theta3Z_cases (col t) (col (t.erase ((t.orderEmbOfFin ht) 0))) (col (t.erase ((t.orderEmbOfFin ht) 2))) with
    h1 | h1 | h1 <;>
  rcases theta3Z_cases (col t) (col (t.erase ((t.orderEmbOfFin ht) 1))) (col (t.erase ((t.orderEmbOfFin ht) 3))) with
    h2 | h2 | h2 <;> simp [h1, h2, div_neg]


/-- The complex conjugate of `q^{1/2}` is its inverse. -/
lemma conj_qHalf (r : ℕ) : (starRingEnd ℂ) (qHalf r) = (qHalf r)⁻¹ := by
  unfold qHalf
  rw [← Complex.exp_conj, ← Complex.exp_neg]
  congr 1
  simp only [map_div₀, map_mul, Complex.conj_I, Complex.conj_ofReal, map_ofNat, map_natCast]
  ring

/-- The local triangle colours of the 4-simplex `s` in its sorted vertices. -/
noncomputable def locJ (col : Finset V → ℕ) (s : Finset V) (h : #s = 5) : Finset (Fin 5) → ℕ :=
  fun F => col (F.map (s.orderEmbOfFin h).toEmbedding)

/-- The local tetrahedron colours of the 4-simplex `s` in its sorted vertices. -/
noncomputable def locI (col : Finset V → ℕ) (s : Finset V) (h : #s = 5) : Fin 5 → ℕ :=
  fun m => col (s.erase ((s.orderEmbOfFin h) m))

/-- The integer sign of the vertex of the 4-simplex `s` at `r = 3`. -/
noncomputable def vertexEps3 (col : Finset V → ℕ) (s : Finset V) : ℤ :=
  if h : #s = 5 then cy3Eps (locJ col s h) (locI col s h) else 0

/-- The exponent of `q^{1/2}` in the vertex of the 4-simplex `s` of orientation `o` at `r = 3` (negated on the other
orientation, where the vertex is complex conjugated). -/
noncomputable def vertexExp3 (col : Finset V → ℕ) (s : Finset V) (o : ℤ) : ℤ :=
  if h : #s = 5 then (if o = 1 then 1 else -1) * cy3Exp (locJ col s h) (locI col s h) else 0

/-- **The vertex of a 4-simplex at `r = 3`**: an integer times a power of `q^{1/2}`. -/
lemma cyVertexAt_three (col : Finset V → ℕ) (hc : ∀ f, col f ≤ 1) {s : Finset V} (hs : #s = 5) (o : ℤ) :
    cyVertexAt 3 col s o = (vertexEps3 col s : ℂ) * qHalf 3 ^ vertexExp3 col s o := by
  unfold cyVertexAt vertexEps3 vertexExp3
  rw [dif_pos hs, dif_pos hs, dif_pos hs]
  have h := cyVertexLoc_three (locJ col s hs) (locI col s hs) (fun F => hc _) (fun m => hc _)
  have h' : cyVertexLoc 3 (fun F => col (F.map (s.orderEmbOfFin hs).toEmbedding))
      (fun m => col (s.erase ((s.orderEmbOfFin hs) m))) =
      (cy3Eps (locJ col s hs) (locI col s hs) : ℂ) * qHalf 3 ^ cy3Exp (locJ col s hs) (locI col s hs) := h
  simp only []
  rw [h']
  split_ifs with ho
  · simp
  · rw [map_mul, map_zpow₀, conj_qHalf, inv_zpow']
    simp [neg_mul]


/-- The integer weight of the tetrahedron `t` at `r = 3`. -/
noncomputable def tetEps3 (col : Finset V → ℕ) (t : Finset V) : ℤ :=
  if ht : #t = 4 then
    (-1 : ℤ) ^ col t * theta3Z (col t) (col (t.erase ((t.orderEmbOfFin ht) 0)))
        (col (t.erase ((t.orderEmbOfFin ht) 2))) *
      theta3Z (col t) (col (t.erase ((t.orderEmbOfFin ht) 1))) (col (t.erase ((t.orderEmbOfFin ht) 3)))
  else 0

/-- A product of powers of a nonzero complex number is the power of the sum of the exponents. -/
lemma prod_zpow_eq_zpow_sum {ι : Type*} (z : ℂ) (hz : z ≠ 0) (s : Finset ι) (f : ι → ℤ) :
    ∏ i ∈ s, z ^ f i = z ^ ∑ i ∈ s, f i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, zpow_add₀ hz]

/-- **The weight of a colouring at `r = 3`** with colours `0, 1`: an integer times a power of `q^{1/2}`. -/
theorem craneYetterWeight_three (K : Complex4 V) (o : Finset V → ℤ) (col : Finset V → ℕ) (hc : ∀ f, col f ≤ 1) :
    craneYetterWeight 3 K o col =
      (((∏ f ∈ K.tris, (-1 : ℤ) ^ col f) * (∏ t ∈ K.tets, tetEps3 col t) * ∏ s ∈ K.simps, vertexEps3 col s : ℤ) :
        ℂ) * qHalf 3 ^ ∑ s ∈ K.simps, vertexExp3 col s (o s) := by
  unfold craneYetterWeight
  have h1 : ∏ f ∈ K.tris, (tlDelta 3 (col f) : ℂ) = (((∏ f ∈ K.tris, (-1 : ℤ) ^ col f : ℤ)) : ℂ) := by
    rw [Int.cast_prod]
    refine Finset.prod_congr rfl fun f _ => ?_
    rw [tlDelta_three (hc f)]
    push_cast; rfl
  have h2 : ∏ t ∈ K.tets, (cyTetWeight 3 col t : ℂ) = (((∏ t ∈ K.tets, tetEps3 col t : ℤ)) : ℂ) := by
    rw [Int.cast_prod]
    refine Finset.prod_congr rfl fun t ht => ?_
    have h4 : #t = 4 := K.card_of_mem_faces ht
    rw [cyTetWeight_three col t h4 hc]
    unfold tetEps3
    rw [dif_pos h4]
    push_cast; rfl
  have h3 : ∏ s ∈ K.simps, cyVertexAt 3 col s (o s) =
      (((∏ s ∈ K.simps, vertexEps3 col s : ℤ)) : ℂ) * qHalf 3 ^ ∑ s ∈ K.simps, vertexExp3 col s (o s) := by
    rw [Finset.prod_congr rfl fun s hs => cyVertexAt_three col hc (K.card_eq s hs) (o s), Finset.prod_mul_distrib,
      prod_zpow_eq_zpow_sum _ (qHalf_ne_zero 3), Int.cast_prod]
  rw [h1, h2, h3]
  push_cast
  ring

end Lightlike.TV
