import Lightlike.Rows.G2_015.Flux

/-!
# The diffeomorphism action on the holonomy–flux algebra (row G2-015)

The third piece of the diffeomorphism action on the holonomy–flux algebra (`lost-2006`).  Here the algebra is the
**free** unital `ℂ`-algebra on the generators `HFGen n`: the matrix entries `h_e(A)_{ij}` of edge holonomies and the
smeared fluxes `E(S)` through parametrised surfaces.  The Poisson relations of the holonomy–flux algebra are *not*
imposed (they are not formalised in Lightlike), so this is the free algebra on the same generators, not the quotient.

The group `Diff` of `C¹` diffeomorphisms of the chart `ℝ³` acts on the generators by moving edges and surfaces
(`Diff.gen`), hence on the algebra by `ℂ`-algebra homomorphisms (`Diff.act`); this is a left action
(`Diff.act_mul`, `Diff.act_one`), packaged as a `MulSemiringAction` (instance on `FreeAlgebra ℂ (HFGen n)`).

The generators are functions on the phase space `(A, E)` of connections and fluxes (`HFGen.val`, extended to the
algebra by `ev`), and the action is the pullback of phase space: `ev A E (φ • a) = ev (φ*A) (φ*E) a`
(`ev_act`), which combines `Edge.hol_pullConn` and `Surf.flux_pullFlux`.
-/

open Matrix Set
open scoped ContDiff

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

noncomputable section

namespace Lightlike.Canonical

variable {n : ℕ}

/-- The group of **`C¹` diffeomorphisms of the chart `ℝ³`**: a bijection which is `C¹` with `C¹` inverse. -/
@[ext]
structure Diff where
  /-- the underlying bijection -/
  equiv : (Fin 3 → ℝ) ≃ (Fin 3 → ℝ)
  /-- the map is `C¹` -/
  smooth : ContDiff ℝ 1 equiv
  /-- the inverse is `C¹` -/
  smooth_symm : ContDiff ℝ 1 equiv.symm

namespace Diff

instance : CoeFun Diff fun _ => (Fin 3 → ℝ) → Fin 3 → ℝ := ⟨fun φ => φ.equiv⟩

instance : Group Diff where
  mul φ ψ := ⟨ψ.equiv.trans φ.equiv, φ.smooth.comp ψ.smooth, ψ.smooth_symm.comp φ.smooth_symm⟩
  mul_assoc _ _ _ := rfl
  one := ⟨Equiv.refl _, contDiff_id, contDiff_id⟩
  one_mul _ := rfl
  mul_one _ := rfl
  inv φ := ⟨φ.equiv.symm, φ.smooth_symm, φ.smooth⟩
  inv_mul_cancel φ := Diff.ext (Equiv.self_trans_symm φ.equiv)

lemma mul_apply (φ ψ : Diff) (x : Fin 3 → ℝ) : (φ * ψ) x = φ (ψ x) := rfl

lemma one_apply (x : Fin 3 → ℝ) : (1 : Diff) x = x := rfl

end Diff

/-- The **generators** of the holonomy–flux algebra: matrix entries of edge holonomies, and smeared fluxes. -/
inductive HFGen (n : ℕ) : Type
  /-- the `(i, j)` entry of the holonomy along the edge `e` -/
  | hol (e : Edge) (i j : Fin n) : HFGen n
  /-- the flux through the smeared surface `S` -/
  | flux (S : Surf n) : HFGen n

/-- The **holonomy–flux algebra** (free version): the free `ℂ`-algebra on the generators. -/
abbrev HFAlg (n : ℕ) := FreeAlgebra ℂ (HFGen n)

namespace Diff

/-- The action of a diffeomorphism on generators: it moves the edge or the surface. -/
def gen (φ : Diff) : HFGen n → HFGen n
  | .hol e i j => .hol (e.map φ φ.smooth) i j
  | .flux S => .flux (S.map φ φ.smooth)

lemma gen_one (g : HFGen n) : gen (1 : Diff) g = g := by
  cases g with
  | hol e i j => cases e; rfl
  | flux S => cases S; rfl

lemma gen_mul (φ ψ : Diff) (g : HFGen n) : gen (φ * ψ) g = gen φ (gen ψ g) := by
  cases g with
  | hol e i j => cases e; rfl
  | flux S => cases S; rfl

/-- The **diffeomorphism action on the holonomy–flux algebra**, by `ℂ`-algebra endomorphisms. -/
def act (φ : Diff) : HFAlg n →ₐ[ℂ] HFAlg n :=
  FreeAlgebra.lift ℂ fun g => FreeAlgebra.ι ℂ (φ.gen g)

@[simp] lemma act_ι (φ : Diff) (g : HFGen n) : φ.act (FreeAlgebra.ι ℂ g) = FreeAlgebra.ι ℂ (φ.gen g) :=
  FreeAlgebra.lift_ι_apply _ _

lemma act_one : (1 : Diff).act = AlgHom.id ℂ (HFAlg n) := by
  apply FreeAlgebra.hom_ext
  funext g
  simp [gen_one]

lemma act_mul (φ ψ : Diff) : (φ * ψ).act = φ.act.comp ψ.act (R := ℂ) (A := HFAlg n) := by
  apply FreeAlgebra.hom_ext
  funext g
  simp [gen_mul]

instance : MulSemiringAction Diff (HFAlg n) where
  smul φ a := φ.act a
  one_smul a := by
    show (1 : Diff).act a = a
    rw [act_one]; rfl
  mul_smul φ ψ a := by
    show (φ * ψ).act a = φ.act (ψ.act a)
    rw [act_mul]; rfl
  smul_zero φ := map_zero φ.act
  smul_add φ a b := map_add φ.act a b
  smul_one φ := map_one φ.act
  smul_mul φ a b := map_mul φ.act a b

lemma smul_def (φ : Diff) (a : HFAlg n) : φ • a = φ.act a := rfl

end Diff

/-- The value of a generator at the phase-space point `(A, E)`. -/
def HFGen.val (A : MatConn n) (E : Fl n) : HFGen n → ℂ
  | .hol e i j => e.hol A i j
  | .flux S => S.flux E

/-- **Evaluation** of the algebra at the phase-space point `(A, E)`, a `ℂ`-algebra homomorphism. -/
def ev (A : MatConn n) (E : Fl n) : HFAlg n →ₐ[ℂ] ℂ :=
  FreeAlgebra.lift ℂ (HFGen.val A E)

@[simp] lemma ev_ι (A : MatConn n) (E : Fl n) (g : HFGen n) :
    ev A E (FreeAlgebra.ι ℂ g) = HFGen.val A E g :=
  FreeAlgebra.lift_ι_apply _ _

/-- **Covariance of the diffeomorphism action**: evaluating `φ • a` at `(A, E)` is evaluating `a` at the pulled-back
point `(φ*A, φ*E)`.  On generators this is `Edge.hol_pullConn` and `Surf.flux_pullFlux`. -/
theorem ev_smul (φ : Diff) (A : MatConn n) (E : Fl n) (a : HFAlg n) :
    ev A E (φ • a) = ev (pullConn φ A) (pullFlux φ E) a := by
  have h : (ev A E).comp φ.act = ev (pullConn φ A) (pullFlux φ E) := by
    apply FreeAlgebra.hom_ext
    funext g
    cases g with
    | hol e i j =>
      simp only [AlgHom.comp_apply, Function.comp_apply, Diff.act_ι, Diff.gen, ev_ι, HFGen.val]
      rw [Edge.hol_pullConn A φ.smooth]
    | flux S =>
      simp only [AlgHom.comp_apply, Function.comp_apply, Diff.act_ι, Diff.gen, ev_ι, HFGen.val]
      rw [Surf.flux_pullFlux φ.smooth]
  rw [Diff.smul_def, ← AlgHom.comp_apply, h]

end Lightlike.Canonical
