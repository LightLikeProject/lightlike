import Lightlike.Regge.Conv3.KuhnBridge
import Lightlike.Regge.Conv3.StarAngle

open Real Matrix
namespace Lightlike.Regge.Conv3

/-- `dihSq'` without the nested square roots: it is minus the derivative combination
`Nn' - Nn/2 (Pp₁'/Pp₁ + Pp₂'/Pp₂)` divided by `√(Pp₁ Pp₂ - Nn²)`. -/
theorem dihSq'_comb {a b c d e f a₁ b₁ c₁ d₁ e₁ f₁ : ℝ} (hP1 : 0 < Pp a b c) (hP2 : 0 < Pp a d e)
    (hσ : 0 < Pp a b c * Pp a d e - Nn a b c d e f ^ 2) :
    dihSq' a b c d e f a₁ b₁ c₁ d₁ e₁ f₁ =
      -(Nn' a b c d e f a₁ b₁ c₁ d₁ e₁ f₁ - Nn a b c d e f / 2 *
        (Pp' a b c a₁ b₁ c₁ / Pp a b c + Pp' a d e a₁ d₁ e₁ / Pp a d e)) /
        √(Pp a b c * Pp a d e - Nn a b c d e f ^ 2) := by
  have hP : 0 < Pp a b c * Pp a d e := mul_pos hP1 hP2
  have hs : 0 < √(Pp a b c * Pp a d e) := Real.sqrt_pos.2 hP
  have hss : √(Pp a b c * Pp a d e) ^ 2 = Pp a b c * Pp a d e := Real.sq_sqrt hP.le
  have hσp : 0 < √(Pp a b c * Pp a d e - Nn a b c d e f ^ 2) := Real.sqrt_pos.2 hσ
  have hd : √(1 - (Nn a b c d e f / √(Pp a b c * Pp a d e)) ^ 2)
      = √(Pp a b c * Pp a d e - Nn a b c d e f ^ 2) / √(Pp a b c * Pp a d e) := by
    rw [← Real.sqrt_div hσ.le, div_pow, hss]
    congr 1
    field_simp
  unfold dihSq'
  rw [hd]
  have h1 := hP1.ne'
  have h2 := hP2.ne'
  have h3 := hs.ne'
  have h4 := hσp.ne'
  field_simp
  rw [hss]

theorem Nn_bf {G : Matrix (Fin 3) (Fin 3) ℝ} (hG : Gᵀ = G) (W X Y : Fin 3 → ℝ)
    (ha : W ⬝ᵥ (G *ᵥ W) ≠ 0) :
    Nn (W ⬝ᵥ (G *ᵥ W)) (X ⬝ᵥ (G *ᵥ X)) ((X - W) ⬝ᵥ (G *ᵥ (X - W)))
      (Y ⬝ᵥ (G *ᵥ Y)) ((Y - W) ⬝ᵥ (G *ᵥ (Y - W))) ((Y - X) ⬝ᵥ (G *ᵥ (Y - X))) = bf G W X Y := by
  have hsym : ∀ a b : Fin 3 → ℝ, a ⬝ᵥ (G *ᵥ b) = b ⬝ᵥ (G *ᵥ a) := fun a b => by
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hG, dotProduct_comm]
  unfold Nn bf
  simp only [Matrix.mulVec_sub, dotProduct_sub, sub_dotProduct]
  rw [hsym W X, hsym W Y, hsym Y X]
  field_simp
  ring

theorem Pp_bf {G : Matrix (Fin 3) (Fin 3) ℝ} (hG : Gᵀ = G) (W X : Fin 3 → ℝ)
    (ha : W ⬝ᵥ (G *ᵥ W) ≠ 0) :
    Pp (W ⬝ᵥ (G *ᵥ W)) (X ⬝ᵥ (G *ᵥ X)) ((X - W) ⬝ᵥ (G *ᵥ (X - W))) = bf G W X X := by
  have hsym : ∀ a b : Fin 3 → ℝ, a ⬝ᵥ (G *ᵥ b) = b ⬝ᵥ (G *ᵥ a) := fun a b => by
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hG, dotProduct_comm]
  unfold Pp bf
  simp only [Matrix.mulVec_sub, dotProduct_sub, sub_dotProduct]
  rw [hsym W X]
  field_simp
  ring

theorem trip_sq (σ h : Fin 6) : trip (wv σ h) (xv σ h) (yv σ h) ^ 2 = 1 := by
  fin_cases σ <;> fin_cases h <;>
    simp [trip, wv, xv, yv, kpos, kv, perms, hP, hQ, hR, hS] <;> norm_num

/-- **The weighted first variation of a dihedral angle, as a rational expression.** For a positive
definite `g m` and the incidence `(σ, h)`, `√(a) Dh(q, δ)` equals minus the polynomial derivative
combination of `mul_diff_eq` over `√(det g m)`. -/
theorem sqrt_Dh_inc {g : (Fin 3 → ℝ) → Matrix (Fin 3) (Fin 3) ℝ} {m : Fin 3 → ℝ}
    (hG : (g m).PosDef) (σ h : Fin 6) (δ : Fin 6 → ℝ) :
    √(incQ g m σ h 0) * Dh (incQ g m σ h, δ) =
      -(NPoly' (incQ g m σ h 0) (incQ g m σ h 1) (incQ g m σ h 2) (incQ g m σ h 3)
          (incQ g m σ h 4) (incQ g m σ h 5) (δ 0) (δ 1) (δ 2) (δ 3) (δ 4) (δ 5) -
        NPoly (incQ g m σ h 0) (incQ g m σ h 1) (incQ g m σ h 2) (incQ g m σ h 3)
          (incQ g m σ h 4) (incQ g m σ h 5) / 2 *
          (PPoly' (incQ g m σ h 0) (incQ g m σ h 1) (incQ g m σ h 2) (δ 0) (δ 1) (δ 2) /
              PPoly (incQ g m σ h 0) (incQ g m σ h 1) (incQ g m σ h 2) +
            PPoly' (incQ g m σ h 0) (incQ g m σ h 3) (incQ g m σ h 4) (δ 0) (δ 3) (δ 4) /
              PPoly (incQ g m σ h 0) (incQ g m σ h 3) (incQ g m σ h 4))) / √((g m).det) := by
  have hs := posDef_symm hG
  have hw := wv_ne σ h
  have ha := posDef_dpos hG hw
  obtain ⟨hx, hy⟩ := bf_pos_of_trip hG hw (trip_ne σ h)
  have hdet := hG.det_pos
  have hgram := gram_id (g m) hs (wv σ h) (xv σ h) (yv σ h) ha.ne'
  have hsq := trip_sq σ h
  rw [hsq, mul_one] at hgram
  have e := incQ_eq_vec g m σ h
  set W := wv σ h; set X := xv σ h; set Y := yv σ h
  have hN := Nn_bf hs W X Y ha.ne'
  have hPx := Pp_bf hs W X ha.ne'
  have hPy := Pp_bf hs W Y ha.ne'
  have eN : Nn (incQ g m σ h 0) (incQ g m σ h 1) (incQ g m σ h 2) (incQ g m σ h 3)
      (incQ g m σ h 4) (incQ g m σ h 5) = bf (g m) W X Y := by rw [e]; simpa using hN
  have eP1 : Pp (incQ g m σ h 0) (incQ g m σ h 1) (incQ g m σ h 2) = bf (g m) W X X := by
    rw [e]; simpa using hPx
  have eP2 : Pp (incQ g m σ h 0) (incQ g m σ h 3) (incQ g m σ h 4) = bf (g m) W Y Y := by
    rw [e]; simpa using hPy
  have ha0 : incQ g m σ h 0 = W ⬝ᵥ (g m *ᵥ W) := by rw [e]; rfl
  have hσ : 0 < Pp (incQ g m σ h 0) (incQ g m σ h 1) (incQ g m σ h 2) *
      Pp (incQ g m σ h 0) (incQ g m σ h 3) (incQ g m σ h 4)
      - Nn (incQ g m σ h 0) (incQ g m σ h 1) (incQ g m σ h 2) (incQ g m σ h 3)
        (incQ g m σ h 4) (incQ g m σ h 5) ^ 2 := by
    rw [eN, eP1, eP2]
    have := div_pos hdet ha
    linarith
  have hσe : Pp (incQ g m σ h 0) (incQ g m σ h 1) (incQ g m σ h 2) *
      Pp (incQ g m σ h 0) (incQ g m σ h 3) (incQ g m σ h 4)
      - Nn (incQ g m σ h 0) (incQ g m σ h 1) (incQ g m σ h 2) (incQ g m σ h 3)
        (incQ g m σ h 4) (incQ g m σ h 5) ^ 2 = (g m).det / (incQ g m σ h 0) := by
    rw [eN, eP1, eP2, ha0]; linarith
  have key := dihSq'_comb (a₁ := δ 0) (b₁ := δ 1) (c₁ := δ 2) (d₁ := δ 3) (e₁ := δ 4) (f₁ := δ 5)
    (a := incQ g m σ h 0) (b := incQ g m σ h 1) (c := incQ g m σ h 2) (d := incQ g m σ h 3)
    (e := incQ g m σ h 4) (f := incQ g m σ h 5) (by rw [eP1]; exact hx) (by rw [eP2]; exact hy) hσ
  have ha1 : 0 < incQ g m σ h 0 := by rw [ha0]; exact ha
  have hp1 : PPoly (incQ g m σ h 0) (incQ g m σ h 1) (incQ g m σ h 2) ≠ 0 := by
    rw [← mul_Pp_eq ha1.ne']; exact (mul_pos ha1 (by rw [eP1]; exact hx)).ne'
  have hp2 : PPoly (incQ g m σ h 0) (incQ g m σ h 3) (incQ g m σ h 4) ≠ 0 := by
    rw [← mul_Pp_eq ha1.ne']; exact (mul_pos ha1 (by rw [eP2]; exact hy)).ne'
  have hmd := mul_diff_eq (a := incQ g m σ h 0) (b := incQ g m σ h 1) (c := incQ g m σ h 2)
    (d := incQ g m σ h 3) (e := incQ g m σ h 4) (f := incQ g m σ h 5) (a₁ := δ 0) (b₁ := δ 1)
    (c₁ := δ 2) (d₁ := δ 3) (e₁ := δ 4) (f₁ := δ 5) ha1.ne' hp1 hp2
  unfold Dh
  simp only
  rw [key, hσe]
  have hsq' : √((g m).det / incQ g m σ h 0) = √((g m).det) / √(incQ g m σ h 0) := Real.sqrt_div hdet.le _
  rw [hsq']
  have hsa : 0 < √(incQ g m σ h 0) := Real.sqrt_pos.2 ha1
  have hsd : 0 < √((g m).det) := Real.sqrt_pos.2 hdet
  have hsa2 : √(incQ g m σ h 0) ^ 2 = incQ g m σ h 0 := Real.sq_sqrt ha1.le
  rw [← hmd]
  field_simp
  rw [hsa2]
  ring

/-- The Gram squared length `xᵀ G x` of an edge vector `x`. -/
noncomputable def qf (G : Fin 3 → Fin 3 → ℝ) (x : Fin 3 → ℝ) : ℝ := ∑ i, ∑ j, x i * G i j * x j

/-- The bilinear second-derivative form `Σ s_k t_l ∂_l ∂_k g_ij x_i x_j`. -/
noncomputable def ddq (dd : Fin 3 → Fin 3 → Fin 3 → Fin 3 → ℝ) (s t x : Fin 3 → ℝ) : ℝ :=
  ∑ i, ∑ j, ∑ k, ∑ l, s k * t l * dd k l i j * x i * x j

/-- The second-order part of the squared length of an edge with midpoint offset `s` and edge vector
`x`, at a point where the first derivatives of the metric vanish. -/
noncomputable def rf (dd : Fin 3 → Fin 3 → Fin 3 → Fin 3 → ℝ) (s x : Fin 3 → ℝ) : ℝ :=
  ddq dd s s x / 2 + ddq dd x x x / 24

/-- The polynomial derivative combination of one incidence, for the squared lengths `q` and their
variation `r`: the right side of `mul_diff_eq`. -/
noncomputable def Einc (q r : Fin 6 → ℝ) : ℝ :=
  NPoly' (q 0) (q 1) (q 2) (q 3) (q 4) (q 5) (r 0) (r 1) (r 2) (r 3) (r 4) (r 5) -
    NPoly (q 0) (q 1) (q 2) (q 3) (q 4) (q 5) / 2 *
      (PPoly' (q 0) (q 1) (q 2) (r 0) (r 1) (r 2) / PPoly (q 0) (q 1) (q 2) +
        PPoly' (q 0) (q 3) (q 4) (r 0) (r 3) (r 4) / PPoly (q 0) (q 3) (q 4))

/-- The Gram squared lengths of the incidence `(σ, h)` for the Gram matrix `G`. -/
noncomputable def lenQ (G : Fin 3 → Fin 3 → ℝ) (σ h : Fin 6) : Fin 6 → ℝ :=
  incVec (fun _ Δ => qf G Δ) σ h

/-- The second-order parts of the squared lengths of the incidence `(σ, h)` for the second
derivatives `dd` of the metric, at a point with vanishing first derivatives. -/
noncomputable def lenR (dd : Fin 3 → Fin 3 → Fin 3 → Fin 3 → ℝ) (σ h : Fin 6) : Fin 6 → ℝ :=
  incVec (fun s Δ => rf dd s Δ) σ h

/-- The numerator of `det R / 2`: `(1/4) Σ adj_{sn} adj_{rl} [∂∂g combination]`, for the Gram matrix
`G` and the second derivatives `dd k l i j = ∂_l ∂_k g_ij`. Here `R = 2 Rnum / det²`. -/
noncomputable def Rnum (G : Fin 3 → Fin 3 → ℝ) (dd : Fin 3 → Fin 3 → Fin 3 → Fin 3 → ℝ) : ℝ :=
  (1 / 4) * ∑ s, ∑ n, ∑ r, ∑ l, (Matrix.of G).adjugate s n * (Matrix.of G).adjugate r l *
    (dd n r l s + dd s r l n - dd l r n s - dd r n l s - dd s n l r + dd l n r s)

end Lightlike.Regge.Conv3
