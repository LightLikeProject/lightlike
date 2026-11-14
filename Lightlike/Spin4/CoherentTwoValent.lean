import Lightlike.Spin4.CoherentIntertwiner
import Lightlike.Spin4.Fusion
import Lightlike.SU2.Completeness

/-!
# The norm of a 2-valent coherent intertwiner and the closure condition

For two links of spin `j = n/2`, the invariant subspace of `V_j ⊗ V_j` is the singlet, and the
norm of the Livine–Speziale coherent intertwiner is an explicit function of the two normals:

`‖ι(g₁, g₂)‖² = ((1 - ν₁·ν₂)/2)^{2j} / (2j+1)`  (`norm_sq_cohInt_two`).

It is largest, `1/(2j+1)`, exactly when the normals close (`ν₂ = -ν₁`, i.e. `j ν₁ + j ν₂ = 0`),
it vanishes for parallel normals, and otherwise it is exponentially suppressed in `j`
(`cohInt_two_suppressed`), the behaviour of coherent intertwiners whose normals do not close
(Livine–Speziale; Conrady–Freidel).

## Main results

* `matInt_spinMat_eq_zero`: `∫ D^j(g) dg = 0` for `j > 0`; `matInt_pairMat`:
  `∫ D^j(g) ⊗ D^j(g) dg = C₀ C₀ᴴ`, the projection onto the singlet.
* `norm_sq_cohInt_two`, `cohInt_two_closed`, `cohInt_two_parallel`, `cohInt_two_suppressed`.

## References

* E. R. Livine, S. Speziale, *A new spinfoam vertex for quantum gravity*, Phys. Rev. D 76 (2007)
  084028, arXiv:0705.0674.
* F. Conrady, L. Freidel, *Quantum geometry from phase space reduction*, J. Math. Phys. 50 (2009)
  123510, arXiv:0902.0351.
-/

open Matrix MeasureTheory Finset Lightlike.Pentagon PhyslibAlpha.Sl2
open scoped Kronecker

namespace Lightlike.Spin4

open SU2

variable {n : ℕ}

/-! ## A. Averages of the spin representations -/

/-- **A nontrivial irreducible representation averages to zero**: `∫ D^{z/2}(g) dg = 0`, `z > 0`. -/
theorem matInt_spinMat_eq_zero {z : ℕ} (hz : 0 < z) :
    matInt (fun g : SU2 => spinMat z g) = 0 := by
  set M := matInt (fun g : SU2 => spinMat z g)
  have hinv : ∀ h : SU2, spinMat z h * M = M := by
    intro h
    have e := matInt_mul_mul (spinMat z h) (fun g : SU2 => spinMat z g)
      (1 : Matrix (Fin (z + 1)) (Fin (z + 1)) ℂ) (continuous_spinMat_apply z)
    rw [Matrix.mul_one] at e
    rw [← e]
    simp only [Matrix.mul_one]
    have : (fun g : SU2 => spinMat z h * spinMat z g) = fun g : SU2 =>
        spinMat z ((h * g : SU2) : Matrix (Fin 2) (Fin 2) ℂ) := by
      funext g
      rw [show ((h * g : SU2) : Matrix (Fin 2) (Fin 2) ℂ) = (h : Matrix (Fin 2) (Fin 2) ℂ) * g
        from rfl, spinMat_mul]
    rw [this]
    exact matInt_mul_left (fun g : SU2 => spinMat z g) h
  ext i j
  -- the `j`-th column is an invariant vector, i.e. an intertwiner from spin `0`
  have hcol := spin_intertwiner_eq_zero (N := 0) (M := z) (by omega)
    (T := Matrix.of fun i (_ : Fin (0 + 1)) => M i j) (fun g => by
      rw [spinMat_zero', Matrix.mul_one]
      ext i' l
      have := congrFun (congrFun (hinv g) i') j
      simpa [mul_apply] using this)
  have := congrFun (congrFun hcol i) 0
  simpa using this

/-- `∫ D⁰(g) dg = 1`. -/
lemma matInt_spinMat_zero : matInt (fun g : SU2 => spinMat 0 g) = 1 := by
  simp only [spinMat_zero']
  exact matInt_const 1

lemma matInt_sum {ι κ β : Type*} (s : Finset β) (F : β → SU2 → Matrix ι κ ℂ)
    (hF : ∀ b ∈ s, ∀ i j, Continuous fun g => F b g i j) :
    matInt (fun g => ∑ b ∈ s, F b g) = ∑ b ∈ s, matInt (F b) := by
  ext i j
  simp only [matInt_apply, Matrix.sum_apply]
  exact integral_finsetSum _ fun b hb => integrable_of_continuous (hF b hb i j)

/-- The tensor square decomposes along the Clebsch–Gordan series:
`D ⊗ D = Σ_z C_z D_z C_zᴴ`. -/
lemma pairMat_eq_sum (g : SU2) :
    spinMat n g ⊗ₖ spinMat n g =
      ∑ z ∈ triSet n n, cgz n n z * spinMat z g * (cgz n n z)ᴴ := by
  calc spinMat n g ⊗ₖ spinMat n g
      = (spinMat n g ⊗ₖ spinMat n g) * ∑ z ∈ triSet n n, cgz n n z * (cgz n n z)ᴴ := by
        rw [cgz_complete, Matrix.mul_one]
    _ = _ := by
        rw [Matrix.mul_sum]
        refine Finset.sum_congr rfl fun z hz => ?_
        rw [← Matrix.mul_assoc, cgz_equivariant (mem_triSet.mp hz)]

/-- **The average of the tensor square is the singlet projector**:
`∫ D^j(g) ⊗ D^j(g) dg = C₀ C₀ᴴ`. -/
theorem matInt_pairMat :
    matInt (fun g : SU2 => spinMat n g ⊗ₖ spinMat n g) = cgz n n 0 * (cgz n n 0)ᴴ := by
  simp only [pairMat_eq_sum]
  rw [matInt_sum _ _ fun z _ i j => ?_]
  · rw [Finset.sum_eq_single 0]
    · rw [matInt_mul_mul _ _ _ (continuous_spinMat_apply 0), matInt_spinMat_zero, Matrix.mul_one]
    · intro z _ hz
      rw [matInt_mul_mul _ _ _ (continuous_spinMat_apply z),
        matInt_spinMat_eq_zero (Nat.pos_of_ne_zero hz), Matrix.mul_zero, Matrix.zero_mul]
    · intro h
      exact absurd (mem_triSet.mpr (by unfold Tri; omega)) h
  · simp only [mul_apply, conjTranspose_apply]
    exact continuous_finsetSum _ fun b _ => (continuous_finsetSum _ fun a _ =>
      continuous_const.mul (continuous_spinMat_apply z a b)).mul continuous_const

/-! ## B. Two links: the projection onto the singlet -/

lemma avgP_two_apply (k l : Fin 2 → Fin (n + 1)) :
    avgP (fun _ : Fin 2 => n) k l = (cgz n n 0 * (cgz n n 0)ᴴ) (k 0, k 1) (l 0, l 1) := by
  rw [← matInt_pairMat]
  simp only [avgP, matInt_apply, rhoN, of_apply, Fin.prod_univ_two, kroneckerMap_apply]

/-- The singlet coefficients `⟨a, b | 0 0⟩` as entries of `C₀`. -/
lemma cgz_singlet_apply (a b : Fin (n + 1)) :
    cgz n n 0 (a, b) 0 =
      if (a : ℕ) + b = n then (((-1) ^ (a : ℕ) / Real.sqrt ((n : ℝ) + 1) : ℝ) : ℂ) else 0 := by
  rw [cgz, of_apply, show (n + n - 0) / 2 = n by omega, Fin.val_zero,
    cgCoefficient_singlet_apply (Nat.lt_succ_iff.mp a.2) (Nat.lt_succ_iff.mp b.2)]
  split_ifs <;> simp

/-! ## C. The norm -/

/-- The Lagrange identity for spinors: `|⟨ψ, φ⟩|² + |det(ψ, φ)|² = ‖ψ‖²‖φ‖²`. -/
lemma normSq_det_add (α β α' β' : ℂ) :
    Complex.normSq (star α * α' + star β * β') + Complex.normSq (α * β' - β * α') =
      (Complex.normSq α + Complex.normSq β) * (Complex.normSq α' + Complex.normSq β') := by
  simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.sub_re, Complex.sub_im, Complex.star_def, Complex.conj_re, Complex.conj_im]
  ring

/-- `|det(g₁e₀, g₂e₀)|² = (1 - ν₁·ν₂)/2`. -/
lemma normSq_det (g h : SU2) :
    Complex.normSq ((g : Matrix (Fin 2) (Fin 2) ℂ) 0 0 * (h : Matrix (Fin 2) (Fin 2) ℂ) 1 0 -
      (g : Matrix (Fin 2) (Fin 2) ℂ) 1 0 * (h : Matrix (Fin 2) (Fin 2) ℂ) 0 0) =
      (1 - bloch g ⬝ᵥ bloch h) / 2 := by
  have hL :=
    normSq_det_add ((g : Matrix (Fin 2) (Fin 2) ℂ) 0 0) ((g : Matrix (Fin 2) (Fin 2) ℂ) 1 0)
    ((h : Matrix (Fin 2) (Fin 2) ℂ) 0 0) ((h : Matrix (Fin 2) (Fin 2) ℂ) 1 0)
  have hO := normSq_overlap g h
  have e : ((g : Matrix (Fin 2) (Fin 2) ℂ)ᴴ * h) 0 0 = star ((g : Matrix (Fin 2) (Fin 2) ℂ) 0 0) *
      (h : Matrix (Fin 2) (Fin 2) ℂ) 0 0 + star ((g : Matrix (Fin 2) (Fin 2) ℂ) 1 0) *
        (h : Matrix (Fin 2) (Fin 2) ℂ) 1 0 := by
    simp [mul_apply, Fin.sum_univ_two]
  rw [e] at hO
  rw [normSq_col g, normSq_col h, one_mul, hO] at hL
  linarith

/-- The singlet component of a product of coherent states:
`Σ_a (-1)^a/√(n+1) ⟨a|g₁⟩⟨n-a|g₂⟩ = (α₁β₂ - β₁α₂)^n / √(n+1)`. -/
lemma singlet_component (g h : Matrix (Fin 2) (Fin 2) ℂ) :
    ∑ a : Fin (n + 1), (((-1) ^ (a : ℕ) / Real.sqrt ((n : ℝ) + 1) : ℝ) : ℂ) *
        (cohState n g a * cohState n h (Fin.rev a)) =
      (g 0 0 * h 1 0 - g 1 0 * h 0 0) ^ n / (Real.sqrt ((n : ℝ) + 1) : ℂ) := by
  have hterm : ∀ a : Fin (n + 1), (((-1) ^ (a : ℕ) / Real.sqrt ((n : ℝ) + 1) : ℝ) : ℂ) *
      (cohState n g a * cohState n h (Fin.rev a)) =
      ((g 0 0 * h 1 0) ^ (n - a) * (-(g 1 0 * h 0 0)) ^ (a : ℕ) * (n.choose a : ℂ)) /
        (Real.sqrt ((n : ℝ) + 1) : ℂ) := by
    intro a
    have ha : (a : ℕ) ≤ n := Nat.lt_succ_iff.mp a.2
    rw [cohState_apply, cohState_apply, Fin.val_rev, show n + 1 - (a + 1) = n - a by omega,
      show n - (n - a) = (a : ℕ) by omega, Nat.choose_symm ha]
    have hsq : (Real.sqrt (n.choose a) : ℂ) * (Real.sqrt (n.choose a) : ℂ) = (n.choose a : ℂ) := by
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt (Nat.cast_nonneg _)]; push_cast; rfl
    have hs : (Real.sqrt ((n : ℝ) + 1) : ℂ) ≠ 0 := by
      exact_mod_cast (Real.sqrt_pos.mpr (by positivity : (0 : ℝ) < (n : ℝ) + 1)).ne'
    push_cast
    rw [← hsq, div_eq_mul_inv, div_eq_mul_inv]
    ring
  rw [Finset.sum_congr rfl fun a _ => hterm a, ← Finset.sum_div,
    Fin.sum_univ_eq_sum_range (fun a => (g 0 0 * h 1 0) ^ (n - a) * (-(g 1 0 * h 0 0)) ^ a *
      (n.choose a : ℂ)), show g 0 0 * h 1 0 - g 1 0 * h 0 0 = -(g 1 0 * h 0 0) + g 0 0 * h 1 0 by
      ring, add_pow]
  congr 1
  refine Finset.sum_congr rfl fun a _ => ?_
  ring

/-- **The norm of a 2-valent coherent intertwiner from its normals**:
`‖ι(g₁, g₂)‖² = ((1 - ν₁·ν₂)/2)^{2j} / (2j+1)`. -/
theorem norm_sq_cohInt_two (g : Fin 2 → SU2) :
    star (cohInt (fun _ : Fin 2 => n) g) ⬝ᵥ cohInt (fun _ : Fin 2 => n) g =
      ((((1 - bloch (g 0) ⬝ᵥ bloch (g 1)) / 2) ^ n / ((n : ℝ) + 1) : ℝ) : ℂ) := by
  set C := cgz n n 0
  set x := prodVec (fun _ : Fin 2 => n) fun a => cohState n (g a)
  -- the singlet component of the product state
  set T : ℂ := ∑ l : Fin 2 → Fin (n + 1), star (C (l 0, l 1) 0) * x l with hT
  have hP : avgP (fun _ : Fin 2 => n) *ᵥ x = fun k => C (k 0, k 1) 0 * T := by
    funext k
    simp only [mulVec, dotProduct, avgP_two_apply, mul_apply, conjTranspose_apply,
      Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, hT, Finset.mul_sum]
    exact Finset.sum_congr rfl fun l _ => by ring
  have hreal : ∀ q : Idx n n, star (C q 0) = C q 0 := fun q => by
    rw [show C q 0 = cgz n n 0 (q.1, q.2) 0 from rfl, cgz_singlet_apply]
    split_ifs <;> simp
  have hTval : T = (((g 0 : Matrix (Fin 2) (Fin 2) ℂ) 0 0 * (g 1 : Matrix (Fin 2) (Fin 2) ℂ) 1 0 -
      (g 0 : Matrix (Fin 2) (Fin 2) ℂ) 1 0 * (g 1 : Matrix (Fin 2) (Fin 2) ℂ) 0 0) ^ n /
        (Real.sqrt ((n : ℝ) + 1) : ℂ)) := by
    rw [hT, ← singlet_component]
    rw [← (piFinTwoEquiv fun _ => Fin (n + 1)).symm.sum_comp, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_eq_single (Fin.rev a)]
    · simp only [piFinTwoEquiv_symm_apply, Fin.cons_zero, Fin.cons_one, hreal, x, prodVec,
        Fin.prod_univ_two]
      rw [show C (a, a.rev) 0 = cgz n n 0 (a, a.rev) 0 from rfl, cgz_singlet_apply,
        ite_eq_left (by simp only [Fin.val_rev]; omega)]
    · intro b _ hb
      simp only [piFinTwoEquiv_symm_apply, Fin.cons_zero, Fin.cons_one, hreal]
      rw [show C (a, b) 0 = cgz n n 0 (a, b) 0 from rfl, cgz_singlet_apply,
        ite_eq_right (fun h => hb (Fin.ext (by simp only [Fin.val_rev]; omega)))]
      simp
    · simp
  rw [cohInt, inner_avgP_avgP, hP]
  have hsum : star x ⬝ᵥ (fun k => C (k 0, k 1) 0 * T) = star T * T := by
    simp only [dotProduct, Pi.star_apply]
    rw [hT, star_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [star_mul', star_star]
    ring
  rw [hsum, Complex.star_def, mul_comm, Complex.mul_conj, hTval, map_div₀, map_pow, normSq_det,
    Complex.normSq_ofReal, Real.mul_self_sqrt (by positivity)]

/-- The Bloch vectors are unit vectors. -/
lemma bloch_dot_self (g : SU2) : bloch g ⬝ᵥ bloch g = 1 := by
  have h := normSq_overlap g g
  have hu : ((g : Matrix (Fin 2) (Fin 2) ℂ))ᴴ * g = 1 :=
    Matrix.mem_unitaryGroup_iff'.mp (Matrix.specialUnitaryGroup_le_unitaryGroup g.2)
  rw [hu] at h
  simp at h
  linarith

/-- The two-link inner product of normals lies in `[-1, 1]`. -/
lemma bloch_dot_bounds (g h : SU2) :
    -1 ≤ bloch g ⬝ᵥ bloch h ∧ bloch g ⬝ᵥ bloch h ≤ 1 := by
  have h1 := normSq_overlap g h
  have h2 := normSq_det g h
  have p1 := Complex.normSq_nonneg (((g : Matrix (Fin 2) (Fin 2) ℂ)ᴴ *
    (h : Matrix (Fin 2) (Fin 2) ℂ)) 0 0)
  have p2 := Complex.normSq_nonneg ((g : Matrix (Fin 2) (Fin 2) ℂ) 0 0 *
    (h : Matrix (Fin 2) (Fin 2) ℂ) 1 0 - (g : Matrix (Fin 2) (Fin 2) ℂ) 1 0 *
      (h : Matrix (Fin 2) (Fin 2) ℂ) 0 0)
  constructor <;> linarith

/-- **Closed normals**: `ν₂ = -ν₁` (`j ν₁ + j ν₂ = 0`) gives the maximal norm `1/(2j+1)`. -/
theorem cohInt_two_closed {g : Fin 2 → SU2} (h : bloch (g 1) = -bloch (g 0)) :
    star (cohInt (fun _ : Fin 2 => n) g) ⬝ᵥ cohInt (fun _ : Fin 2 => n) g =
      ((1 / ((n : ℝ) + 1) : ℝ) : ℂ) := by
  rw [norm_sq_cohInt_two, h, dotProduct_neg, bloch_dot_self]
  norm_num

/-- **Parallel normals**: `ν₂ = ν₁` gives a vanishing coherent intertwiner (for `j > 0`). -/
theorem cohInt_two_parallel {g : Fin 2 → SU2} (h : bloch (g 1) = bloch (g 0)) (hn : 0 < n) :
    star (cohInt (fun _ : Fin 2 => n) g) ⬝ᵥ cohInt (fun _ : Fin 2 => n) g = 0 := by
  rw [norm_sq_cohInt_two, h, bloch_dot_self]
  simp [zero_pow hn.ne']

/-- **Suppression of non-closing normals**: unless `ν₂ = -ν₁`, the normalised norm
`(2j+1) ‖ι(g₁, g₂)‖² = r^{2j}` decays exponentially in `j`, with `0 ≤ r < 1`. -/
theorem cohInt_two_suppressed {g : Fin 2 → SU2} (h : bloch (g 0) ⬝ᵥ bloch (g 1) ≠ -1) :
    ∃ r : ℝ, 0 ≤ r ∧ r < 1 ∧ ∀ n : ℕ,
      ((n : ℂ) + 1) * (star (cohInt (fun _ : Fin 2 => n) g) ⬝ᵥ cohInt (fun _ : Fin 2 => n) g) =
        ((r ^ n : ℝ) : ℂ) := by
  obtain ⟨hlo, hhi⟩ := bloch_dot_bounds (g 0) (g 1)
  have hgt : -1 < bloch (g 0) ⬝ᵥ bloch (g 1) := lt_of_le_of_ne hlo (Ne.symm h)
  refine ⟨(1 - bloch (g 0) ⬝ᵥ bloch (g 1)) / 2, by linarith, by linarith, fun n => ?_⟩
  rw [norm_sq_cohInt_two]
  have hn : ((n : ℝ) + 1) ≠ 0 := by positivity
  push_cast
  field_simp

end Lightlike.Spin4
