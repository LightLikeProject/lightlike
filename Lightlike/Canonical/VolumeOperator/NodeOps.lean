import Lightlike.Canonical.VolumeOperator.SpinOps

/-!
# Edge operators on the Hilbert space of a node

Second piece of the volume operator (row G2-014, milestone CA4). A node with `k` edges carrying
spins `n e / 2` has the (non gauge-fixed) Hilbert space `Idx n = ∀ e, Fin (n e + 1) → ℂ`.
`liftOp e A` is the operator acting by the matrix `A` on the `e`-th tensor factor and trivially on
the others. This file proves that `liftOp` is a homomorphism of algebras (`liftOp_mul`,
`liftOp_add`, `liftOp_smul`, `liftOp_conjTranspose`), and that operators on different factors
commute (`liftOp_comm`).
-/

open Matrix

namespace Lightlike.Canonical.VolumeOperator

variable {k : ℕ}

/-- Basis of the node Hilbert space: one magnetic number per edge. -/
abbrev Idx (n : Fin k → ℕ) : Type := ∀ e : Fin k, Fin (n e + 1)

variable {n : Fin k → ℕ}

/-- The operator acting by `A` on the `e`-th factor and by the identity on the others. -/
def liftOp (e : Fin k) (A : Matrix (Fin (n e + 1)) (Fin (n e + 1)) ℂ) :
    Matrix (Idx n) (Idx n) ℂ :=
  Matrix.of fun m m' => if (∀ f, f ≠ e → m f = m' f) then A (m e) (m' e) else 0

lemma liftOp_apply (e : Fin k) (A : Matrix (Fin (n e + 1)) (Fin (n e + 1)) ℂ) (m m' : Idx n) :
    liftOp e A m m' = if (∀ f, f ≠ e → m f = m' f) then A (m e) (m' e) else 0 := rfl

/-- A sum over the node basis, whose summand vanishes unless `m''` agrees with `m` off `e`,
reduces to a sum over the `e`-th magnetic number. -/
lemma sum_eq_update (e : Fin k) (m : Idx n) (g : Idx n → ℂ)
    (h : ∀ m'' : Idx n, ¬ (∀ f, f ≠ e → m f = m'' f) → g m'' = 0) :
    ∑ m'', g m'' = ∑ x : Fin (n e + 1), g (Function.update m e x) := by
  rw [← Finset.sum_image (f := g) (g := fun x : Fin (n e + 1) => Function.update m e x)
    (s := Finset.univ) (fun x _ y _ hxy => Function.update_injective m e hxy)]
  symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro m'' _ hm''
  apply h
  intro hcond
  apply hm''
  rw [Finset.mem_image]
  refine ⟨m'' e, Finset.mem_univ _, ?_⟩
  funext f
  by_cases hf : f = e
  · subst hf; simp
  · rw [Function.update_of_ne hf]; exact hcond f hf

lemma liftOp_add (e : Fin k) (A B : Matrix (Fin (n e + 1)) (Fin (n e + 1)) ℂ) :
    liftOp e (A + B) = liftOp e A + liftOp e B := by
  ext m m'
  simp only [liftOp_apply, Matrix.add_apply]
  split_ifs <;> simp

lemma liftOp_smul (e : Fin k) (c : ℂ) (A : Matrix (Fin (n e + 1)) (Fin (n e + 1)) ℂ) :
    liftOp e (c • A) = c • liftOp e A := by
  ext m m'
  simp only [liftOp_apply, Matrix.smul_apply]
  split_ifs <;> simp

lemma liftOp_sub (e : Fin k) (A B : Matrix (Fin (n e + 1)) (Fin (n e + 1)) ℂ) :
    liftOp e (A - B) = liftOp e A - liftOp e B := by
  ext m m'
  simp only [liftOp_apply, Matrix.sub_apply]
  split_ifs <;> simp

lemma liftOp_conjTranspose (e : Fin k) (A : Matrix (Fin (n e + 1)) (Fin (n e + 1)) ℂ) :
    (liftOp e A)ᴴ = liftOp e Aᴴ := by
  ext m m'
  simp only [liftOp_apply, Matrix.conjTranspose_apply]
  by_cases h : ∀ f, f ≠ e → m f = m' f
  · have h' : ∀ f, f ≠ e → m' f = m f := fun f hf => (h f hf).symm
    rw [ite_eq_left h, ite_eq_left h']
  · have h' : ¬ ∀ f, f ≠ e → m' f = m f := fun H => h fun f hf => (H f hf).symm
    rw [ite_eq_right h, ite_eq_right h']
    simp

lemma liftOp_mul (e : Fin k) (A B : Matrix (Fin (n e + 1)) (Fin (n e + 1)) ℂ) :
    liftOp e (A * B) = liftOp e A * liftOp e B := by
  ext m m'
  rw [Matrix.mul_apply, sum_eq_update e m]
  · simp only [liftOp_apply, Function.update_self]
    by_cases h : ∀ f, f ≠ e → m f = m' f
    · have h1 : ∀ x : Fin (n e + 1), (∀ f, f ≠ e → m f = Function.update m e x f) := by
        intro x f hf; rw [Function.update_of_ne hf]
      have h2 : ∀ x : Fin (n e + 1), (∀ f, f ≠ e → Function.update m e x f = m' f) := by
        intro x f hf; rw [Function.update_of_ne hf]; exact h f hf
      rw [ite_eq_left h, Matrix.mul_apply]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [ite_eq_left (h1 x), ite_eq_left (h2 x)]
    · have h2 : ∀ x : Fin (n e + 1), ¬ (∀ f, f ≠ e → Function.update m e x f = m' f) := by
        intro x H; apply h; intro f hf; have := H f hf
        rwa [Function.update_of_ne hf] at this
      simp [h, h2]
  · intro m'' hm''
    simp only [liftOp_apply, ite_eq_right hm'', zero_mul]

/-- Operators acting on different tensor factors commute. -/
lemma liftOp_comm {e f : Fin k} (hef : e ≠ f) (A : Matrix (Fin (n e + 1)) (Fin (n e + 1)) ℂ)
    (B : Matrix (Fin (n f + 1)) (Fin (n f + 1)) ℂ) :
    liftOp e A * liftOp f B = liftOp f B * liftOp e A := by
  have key : ∀ (e f : Fin k) (hef : e ≠ f) (A : Matrix (Fin (n e + 1)) (Fin (n e + 1)) ℂ)
      (B : Matrix (Fin (n f + 1)) (Fin (n f + 1)) ℂ) (m m' : Idx n),
      (liftOp e A * liftOp f B) m m' =
        if (∀ g, g ≠ e → g ≠ f → m g = m' g) then A (m e) (m' e) * B (m f) (m' f) else 0 := by
    intro e f hef A B m m'
    rw [Matrix.mul_apply, Finset.sum_eq_single (Function.update m e (m' e))]
    · simp only [liftOp_apply]
      have c1 : ∀ g, g ≠ e → m g = Function.update m e (m' e) g := by
        intro g hg; rw [Function.update_of_ne hg]
      simp only [Function.update_self, Function.update_of_ne hef.symm]
      by_cases h : ∀ g, g ≠ e → g ≠ f → m g = m' g
      · have c2 : ∀ g, g ≠ f → Function.update m e (m' e) g = m' g := by
          intro g hg
          by_cases hge : g = e
          · subst hge; simp
          · rw [Function.update_of_ne hge]; exact h g hge hg
        rw [ite_eq_left c2, ite_eq_left c1, ite_eq_left h]
      · have c2 : ¬ ∀ g, g ≠ f → Function.update m e (m' e) g = m' g := by
          intro H; apply h; intro g hg1 hg2
          have := H g hg2
          rwa [Function.update_of_ne hg1] at this
        simp [c2, h]
    · intro m'' _ hne
      simp only [liftOp_apply]
      by_cases h1 : ∀ g, g ≠ e → m g = m'' g
      · by_cases h2 : ∀ g, g ≠ f → m'' g = m' g
        · exfalso; apply hne
          funext g
          by_cases hge : g = e
          · subst hge; simp [h2 g hef]
          · rw [Function.update_of_ne hge]; exact (h1 g hge).symm
        · simp [h2]
      · simp [h1]
    · intro h; exact absurd (Finset.mem_univ _) h
  ext m m'
  rw [key e f hef A B, key f e hef.symm B A]
  have hiff : (∀ g, g ≠ e → g ≠ f → m g = m' g) ↔ (∀ g, g ≠ f → g ≠ e → m g = m' g) :=
    ⟨fun h g h1 h2 => h g h2 h1, fun h g h1 h2 => h g h2 h1⟩
  by_cases h : ∀ g, g ≠ e → g ≠ f → m g = m' g
  · rw [ite_eq_left h, ite_eq_left (hiff.1 h), mul_comm]
  · rw [ite_eq_right h, ite_eq_right (fun H => h (hiff.2 H))]

/-- The angular-momentum operator `J_e^a` of the edge `e` on the node Hilbert space. -/
noncomputable def edgeOp (n : Fin k → ℕ) (e : Fin k) (a : Fin 3) : Matrix (Idx n) (Idx n) ℂ :=
  liftOp e (Lightlike.Poincare.spinOp (n e) a)

/-- The edge operators are Hermitian. -/
theorem edgeOp_conjTranspose (e : Fin k) (a : Fin 3) : (edgeOp n e a)ᴴ = edgeOp n e a := by
  rw [edgeOp, liftOp_conjTranspose, spinOp_conjTranspose]

/-- Edge operators of different edges commute. -/
theorem edgeOp_comm_of_ne {e f : Fin k} (hef : e ≠ f) (a b : Fin 3) :
    edgeOp n e a * edgeOp n f b = edgeOp n f b * edgeOp n e a :=
  liftOp_comm hef _ _

/-- `[J_e^x, J_e^y] = i J_e^z`. -/
theorem edgeOp_comm_xy (e : Fin k) :
    edgeOp n e 0 * edgeOp n e 1 - edgeOp n e 1 * edgeOp n e 0 = Complex.I • edgeOp n e 2 := by
  simp only [edgeOp, ← liftOp_mul, ← liftOp_sub, spinOp_comm_xy, liftOp_smul]

/-- `[J_e^y, J_e^z] = i J_e^x`. -/
theorem edgeOp_comm_yz (e : Fin k) :
    edgeOp n e 1 * edgeOp n e 2 - edgeOp n e 2 * edgeOp n e 1 = Complex.I • edgeOp n e 0 := by
  simp only [edgeOp, ← liftOp_mul, ← liftOp_sub, spinOp_comm_yz, liftOp_smul]

/-- `[J_e^z, J_e^x] = i J_e^y`. -/
theorem edgeOp_comm_zx (e : Fin k) :
    edgeOp n e 2 * edgeOp n e 0 - edgeOp n e 0 * edgeOp n e 2 = Complex.I • edgeOp n e 1 := by
  simp only [edgeOp, ← liftOp_mul, ← liftOp_sub, spinOp_comm_zx, liftOp_smul]

end Lightlike.Canonical.VolumeOperator

/-! Deprecated names (kept for one release) -/

@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G2_014.Idx := _root_.Lightlike.Canonical.VolumeOperator.Idx
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G2_014.edgeOp := _root_.Lightlike.Canonical.VolumeOperator.edgeOp
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G2_014.edgeOp_comm_of_ne := _root_.Lightlike.Canonical.VolumeOperator.edgeOp_comm_of_ne
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G2_014.edgeOp_comm_xy := _root_.Lightlike.Canonical.VolumeOperator.edgeOp_comm_xy
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G2_014.edgeOp_comm_yz := _root_.Lightlike.Canonical.VolumeOperator.edgeOp_comm_yz
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G2_014.edgeOp_comm_zx := _root_.Lightlike.Canonical.VolumeOperator.edgeOp_comm_zx
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G2_014.edgeOp_conjTranspose := _root_.Lightlike.Canonical.VolumeOperator.edgeOp_conjTranspose
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G2_014.liftOp := _root_.Lightlike.Canonical.VolumeOperator.liftOp
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G2_014.liftOp_add := _root_.Lightlike.Canonical.VolumeOperator.liftOp_add
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G2_014.liftOp_apply := _root_.Lightlike.Canonical.VolumeOperator.liftOp_apply
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G2_014.liftOp_comm := _root_.Lightlike.Canonical.VolumeOperator.liftOp_comm
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G2_014.liftOp_conjTranspose := _root_.Lightlike.Canonical.VolumeOperator.liftOp_conjTranspose
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G2_014.liftOp_mul := _root_.Lightlike.Canonical.VolumeOperator.liftOp_mul
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G2_014.liftOp_smul := _root_.Lightlike.Canonical.VolumeOperator.liftOp_smul
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G2_014.liftOp_sub := _root_.Lightlike.Canonical.VolumeOperator.liftOp_sub
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G2_014.sum_eq_update := _root_.Lightlike.Canonical.VolumeOperator.sum_eq_update
