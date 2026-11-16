import Lightlike.Regge.Linear3.TorusBridge
import Lightlike.Regge.Geodesic.DistSymm
import Lightlike.Regge.Conv3.ReggeConvergence

/-!
# The Regge action of the periodic Kuhn complex with geodesic lengths is the lattice hinge sum

Take a metric `g` on `ℝ³` that is invariant under integer translations and give the edge `{z, z + w}` of
the periodic Kuhn complex `torusComplex n` the geodesic length `d (z/n) ((z + w)/n)` of the real lifts
(`lenD`, with `d = Lightlike.Geodesic.dist g univ`). The distance is symmetric and translation invariant
(`Lightlike/Regge/Geodesic/DistSymm.lean`), so the length of the edge between two corners of a Kuhn tetrahedron is
the distance of any two real lifts of the corners that differ by the edge vector (`lenD_corner`), and
the dihedral angle of a tetrahedron is the angle `Dsq` of the squared distances of its corners
(`dihedralAt_inc`). The squared lengths of the star of a hinge used by `reggeAction3` are the same
numbers (`trueLen_eq`). Hence the Regge action of the complex is the lattice hinge sum
`Conv3.reggeAction3 g univ n` (`reggeAction_torus_eq`), with no boundary layer: the cells of the torus
are the cells of `[0, 1)³`.

## Main results

* `lenD`, `lenD_edgeOf`, `lenD_corner`: the lengths and their value on an edge or between corners.
* `dihedralAt_inc`: the dihedral angle of an incidence is `Dsq` of the squared distances.
* `reggeAction_torus_eq`: `reggeAction (torusComplex n) (lenD n (dist g univ)) = reggeAction3 g univ n`.

**Limits.** `g` is invariant under integer translations and `n ≥ 3`; the hypothesis `hpos` (the geodesic
length of each hinge of each tetrahedron is positive) is not derived here (it holds for large `n`,
from the hinge length expansion `hinge_length`).
-/

open Real Finset
namespace Lightlike.Regge.Linear3
open Lightlike.Regge Lightlike.Regge.Conv3
open Lightlike.PR (Complex3)

variable (n : ℕ) [NeZero n]

/-- The point of `ℝ³` with coordinates `val / n` of a grid vertex. -/
noncomputable def liftPt (z : TV n) : Fin 3 → ℝ := fun i => ((z i).val : ℝ) / n

/-- Edge lengths on the periodic complex from a function `d` of two points of `ℝ³`: the edge from `z` in
the direction `k` has length `d (z/n) (z/n + dirs k / n)`; the value `1` for sets that are not edges. -/
noncomputable def lenD (d : (Fin 3 → ℝ) → (Fin 3 → ℝ) → ℝ) (e : Finset (TV n)) : ℝ :=
  if h : ∃ p : TV n × Fin 7, edgeOf n p.1 p.2 = e then
    d (liftPt n h.choose.1) (liftPt n h.choose.1 + fun i => ((dirsN h.choose.2 i : ℕ) : ℝ) / n)
  else 1

theorem lenD_edgeOf (hn : 3 ≤ n) (d : (Fin 3 → ℝ) → (Fin 3 → ℝ) → ℝ) (z : TV n) (k : Fin 7) :
    lenD n d (edgeOf n z k) = d (liftPt n z) (liftPt n z + fun i => ((dirsN k i : ℕ) : ℝ) / n) := by
  have h : ∃ p : TV n × Fin 7, edgeOf n p.1 p.2 = edgeOf n z k := ⟨(z, k), rfl⟩
  unfold lenD
  rw [dif_pos h]
  have := @edgeOf_injective n _ hn h.choose (z, k) h.choose_spec
  rw [this]

theorem koff_mono_all : ∀ a b : Fin 4, a < b → ∀ j : Fin 3, koff a j ≤ koff b j := by decide


/-- The lift of the vertex represented by the integer `m` differs from `m / n` by an integer. -/
theorem liftPt_int (m : Fin 3 → ℤ) (z : TV n) (hz : ∀ i, (m i : ZMod n) = z i) :
    ∃ e : Fin 3 → ℤ, ∀ i, liftPt n z i = ((m i : ℤ) : ℝ) / n - (e i : ℝ) := by
  refine ⟨fun i => m i / n, fun i => ?_⟩
  have hn : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  have h1 : ((z i).val : ℤ) = m i % n := by
    rw [← hz i, ZMod.val_intCast]
  have h2 : ((z i).val : ℝ) = ((m i : ℤ) : ℝ) - n * ((m i / n : ℤ) : ℝ) := by
    have : ((z i).val : ℝ) = (((z i).val : ℤ) : ℝ) := by norm_cast
    rw [this, h1, Int.emod_def]
    push_cast
    ring
  unfold liftPt
  rw [h2]
  field_simp

/-- **The length of the edge between two corners of a Kuhn tetrahedron** with the lengths `lenD d`
for a symmetric `d` that is invariant under integer translations: `d` of the two real lifts of the
corners (`c̃` an integer representative of the cell `c`). -/
theorem lenD_corner (hn : 3 ≤ n) (d : (Fin 3 → ℝ) → (Fin 3 → ℝ) → ℝ)
    (hsym : ∀ x y, d x y = d y x)
    (hper : ∀ x y (e : Fin 3 → ℤ), d (x + fun i => (e i : ℝ)) (y + fun i => (e i : ℝ)) = d x y)
    (c : TV n) (ct : Fin 3 → ℤ) (hc : ∀ i, (ct i : ZMod n) = c i) (σ : Fin 6) {a b : Fin 4} (hab : a ≠ b) :
    lenD n d {c + off n σ a, c + off n σ b} =
      d (fun i => ((ct i + koff a (perms σ i) : ℤ) : ℝ) / n)
        (fun i => ((ct i + koff b (perms σ i) : ℤ) : ℝ) / n) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  -- the case `a < b`
  have main : ∀ {a b : Fin 4}, a < b → lenD n d {c + off n σ a, c + off n σ b} =
      d (fun i => ((ct i + koff a (perms σ i) : ℤ) : ℝ) / n)
        (fun i => ((ct i + koff b (perms σ i) : ℤ) : ℝ) / n) := by
    intro a b hlt
    have hmono := fun j => koff_mono_all a b hlt j
    set w : Fin 3 → ℕ := fun i => koff b (perms σ i) - koff a (perms σ i) with hw
    have hw1 : ∀ i, w i ≤ 1 := fun i => by
      have := koff_le b (perms σ i); have := hmono (perms σ i); simp only [hw]; omega
    have hw0 : ∃ i, w i ≠ 0 := by
      by_contra hcon
      push Not at hcon
      have : off n σ a = off n σ b := by
        funext i
        have h1 := hcon i
        have h2 := hmono (perms σ i)
        have : koff a (perms σ i) = koff b (perms σ i) := by simp only [hw] at h1; omega
        simp only [off, this]
      exact (ne_of_lt hlt) (off_injective n (by omega) σ this)
    obtain ⟨k, hk⟩ := dirsN_surj w hw1 hw0
    have hset : ({c + off n σ a, c + off n σ b} : Finset (TV n)) = edgeOf n (c + off n σ a) k := by
      unfold edgeOf
      congr 2
      funext i
      have h2 := hmono (perms σ i)
      simp only [Pi.add_apply, off, wv, hk, hw]
      rw [Nat.cast_sub h2]
      ring
    rw [hset, lenD_edgeOf n (by omega)]
    obtain ⟨e, he⟩ := liftPt_int n (fun i => ct i + koff a (perms σ i)) (c + off n σ a)
      (fun i => by simp [hc, off])
    have hx : liftPt n (c + off n σ a) = (fun i => ((ct i + koff a (perms σ i) : ℤ) : ℝ) / n) +
        fun i => (((-e) i : ℤ) : ℝ) := by
      funext i; simp [he i]; ring
    rw [hx]
    have hy : ((fun i => ((ct i + koff a (perms σ i) : ℤ) : ℝ) / n) +
        fun i => (((-e) i : ℤ) : ℝ)) + (fun i => ((dirsN k i : ℕ) : ℝ) / n) =
        (fun i => ((ct i + koff b (perms σ i) : ℤ) : ℝ) / n) + fun i => (((-e) i : ℤ) : ℝ) := by
      funext i
      have h2 := hmono (perms σ i)
      have : dirsN k i = w i := congrFun hk i
      simp only [Pi.add_apply, this, hw]
      push_cast
      rw [Nat.cast_sub h2]
      ring
    rw [hy]
    exact hper _ _ (-e)
  rcases lt_or_gt_of_ne hab with h | h
  · exact main h
  · rw [pair_comm, main h, hsym]


/-- The real corner `a` of the tetrahedron with integer cell representative `ct`. -/
noncomputable def cornerPt (ct : Fin 3 → ℤ) (σ : Fin 6) (a : Fin 4) : Fin 3 → ℝ :=
  fun i => ((ct i + koff a (perms σ i) : ℤ) : ℝ) / n

/-- **The true squared lengths of the star are the squares of `d` between the corners.** For the hinge
midpoint `v = (z + w/2)/n`, the point `v + (1/n) k_a` of the corner `a` of the incidence `(σ, h)` is the
corner of the tetrahedron with cell representative `ct = z - koff (hP h)`. -/
theorem trueLen_eq {g : (Fin 3 → ℝ) → Matrix (Fin 3) (Fin 3) ℝ} (σ h : Fin 6) (k : Fin 7) (hc : Cond (dirsN k) σ h)
    (zv : Fin 3 → ℤ) :
    Conv3.trueLen g Set.univ (fun i => ((zv i : ℤ) + dirs k i / 2) / n) (1 / (n : ℝ)) σ h =
      ![Geodesic.dist g Set.univ (cornerPt n (fun i => zv i - koff (hP h) (perms σ i)) σ (hP h))
          (cornerPt n (fun i => zv i - koff (hP h) (perms σ i)) σ (hQ h)) ^ 2,
        Geodesic.dist g Set.univ (cornerPt n (fun i => zv i - koff (hP h) (perms σ i)) σ (hP h))
          (cornerPt n (fun i => zv i - koff (hP h) (perms σ i)) σ (hR h)) ^ 2,
        Geodesic.dist g Set.univ (cornerPt n (fun i => zv i - koff (hP h) (perms σ i)) σ (hQ h))
          (cornerPt n (fun i => zv i - koff (hP h) (perms σ i)) σ (hR h)) ^ 2,
        Geodesic.dist g Set.univ (cornerPt n (fun i => zv i - koff (hP h) (perms σ i)) σ (hP h))
          (cornerPt n (fun i => zv i - koff (hP h) (perms σ i)) σ (hS h)) ^ 2,
        Geodesic.dist g Set.univ (cornerPt n (fun i => zv i - koff (hP h) (perms σ i)) σ (hQ h))
          (cornerPt n (fun i => zv i - koff (hP h) (perms σ i)) σ (hS h)) ^ 2,
        Geodesic.dist g Set.univ (cornerPt n (fun i => zv i - koff (hP h) (perms σ i)) σ (hR h))
          (cornerPt n (fun i => zv i - koff (hP h) (perms σ i)) σ (hS h)) ^ 2] := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  have hd : ∀ i, dirs k i = kv (hQ h) (perms σ i) - kv (hP h) (perms σ i) := fun i => by
    have := (cond_iff_real (dirsN k) σ h).1 hc
    rcases (by fin_cases i <;> simp : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl
    · rw [← dirsN_cast]; exact this.1.symm
    · rw [← dirsN_cast]; exact this.2.1.symm
    · rw [← dirsN_cast]; exact this.2.2.symm
  have hpt : ∀ a : Fin 4, (fun i => ((zv i : ℤ) + dirs k i / 2) / n) + (1 / (n : ℝ)) • (fun i => kpos σ h a i) =
      cornerPt n (fun i => zv i - koff (hP h) (perms σ i)) σ a := by
    intro a
    funext i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, cornerPt, kpos, hd i]
    have : ((koff a (perms σ i) : ℕ) : ℝ) = kv a (perms σ i) := koff_cast a _
    have h2 : ((koff (hP h) (perms σ i) : ℕ) : ℝ) = kv (hP h) (perms σ i) := koff_cast _ _
    push_cast
    rw [this, h2]
    field_simp
    ring
  have e1 : ∀ (a b : Fin 4) (v : Fin 3 → ℝ) (ε : ℝ),
      v + ε • ((fun i => (kpos σ h a i + kpos σ h b i) / 2) - (1 / 2 : ℝ) • (fun i => kpos σ h b i - kpos σ h a i)) =
        v + ε • (fun i => kpos σ h a i) := fun a b v ε => by funext i; simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]; ring
  have e2 : ∀ (a b : Fin 4) (v : Fin 3 → ℝ) (ε : ℝ),
      v + ε • ((fun i => (kpos σ h a i + kpos σ h b i) / 2) + (1 / 2 : ℝ) • (fun i => kpos σ h b i - kpos σ h a i)) =
        v + ε • (fun i => kpos σ h b i) := fun a b v ε => by funext i; simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]; ring
  unfold Conv3.trueLen incVec
  simp only [e1, e2, hpt]


/-- **The dihedral angle of a tetrahedron of the periodic complex with the lengths `lenD d`** at the hinge
`h` is the angle `Dsq` of the squared `d`-distances of the corners. -/
theorem dihedralAt_inc (hn : 3 ≤ n) (d : (Fin 3 → ℝ) → (Fin 3 → ℝ) → ℝ)
    (hsym : ∀ x y, d x y = d y x)
    (hper : ∀ x y (e : Fin 3 → ℤ), d (x + fun i => (e i : ℝ)) (y + fun i => (e i : ℝ)) = d x y)
    (hnn : ∀ x y, 0 ≤ d x y)
    (c : TV n) (ct : Fin 3 → ℤ) (hc : ∀ i, (ct i : ZMod n) = c i) (σ h : Fin 6)
    (hpos : 0 < d (cornerPt n ct σ (hP h)) (cornerPt n ct σ (hQ h))) :
    dihedralAt (lenD n d) (tetV n c σ) (hing n c σ h) =
      Dsq ![d (cornerPt n ct σ (hP h)) (cornerPt n ct σ (hQ h)) ^ 2,
        d (cornerPt n ct σ (hP h)) (cornerPt n ct σ (hR h)) ^ 2,
        d (cornerPt n ct σ (hQ h)) (cornerPt n ct σ (hR h)) ^ 2,
        d (cornerPt n ct σ (hP h)) (cornerPt n ct σ (hS h)) ^ 2,
        d (cornerPt n ct σ (hQ h)) (cornerPt n ct σ (hS h)) ^ 2,
        d (cornerPt n ct σ (hR h)) (cornerPt n ct σ (hS h)) ^ 2] := by
  obtain ⟨d1, d2, d3, d4, d5, d6⟩ := hinge_distinct h
  have inj := fun {a b : Fin 4} (hab : a ≠ b) (e : c + off n σ a = c + off n σ b) =>
    hab (off_injective n (by omega) σ (add_left_cancel e))
  have hlen : ∀ {a b : Fin 4}, a ≠ b → lenD n d {c + off n σ a, c + off n σ b} =
      d (cornerPt n ct σ a) (cornerPt n ct σ b) := fun hab =>
    lenD_corner n hn d hsym hper c ct hc σ hab
  unfold hing
  rw [tetV_eq_hinge n c σ h, dihedralAt_eq _ (fun e => inj d1 e) (fun e => inj d2 e)
    (fun e => inj d3 e) (fun e => inj d4 e) (fun e => inj d5 e) (fun e => inj d6 e)
    (by rw [hlen d1]; exact hpos.ne')]
  rw [hlen d1, hlen d4, hlen d2, hlen d6, hlen d3, hlen d5]
  have := dihedral_sqrt_eq (A := d (cornerPt n ct σ (hP h)) (cornerPt n ct σ (hQ h)) ^ 2)
    (B := d (cornerPt n ct σ (hP h)) (cornerPt n ct σ (hR h)) ^ 2)
    (C := d (cornerPt n ct σ (hQ h)) (cornerPt n ct σ (hR h)) ^ 2)
    (D := d (cornerPt n ct σ (hP h)) (cornerPt n ct σ (hS h)) ^ 2)
    (E := d (cornerPt n ct σ (hQ h)) (cornerPt n ct σ (hS h)) ^ 2)
    (F := d (cornerPt n ct σ (hR h)) (cornerPt n ct σ (hS h)) ^ 2) (by positivity) (by positivity)
    (by positivity) (by positivity) (by positivity) (by positivity)
  simp only [Real.sqrt_sq (hnn _ _)] at this
  exact this


/-- The grid `ZMod n` is `Fin n` through `val`. -/
def valEquiv : ZMod n ≃ Fin n where
  toFun x := ⟨x.val, ZMod.val_lt x⟩
  invFun i := ((i : ℕ) : ZMod n)
  left_inv x := by simp
  right_inv i := by
    apply Fin.ext
    simp [ZMod.val_natCast, Nat.mod_eq_of_lt i.2]

theorem cond_iff_inClass (k : Fin 7) (σ h : Fin 6) : Cond (dirsN k) σ h ↔ InClass (dirs k) σ h := by
  rw [cond_iff_real]
  unfold InClass
  constructor
  · rintro ⟨h0, h1, h2⟩ i
    fin_cases i
    · simpa [dirsN_cast] using h0
    · simpa [dirsN_cast] using h1
    · simpa [dirsN_cast] using h2
  · intro hc
    refine ⟨?_, ?_, ?_⟩
    · simpa [dirsN_cast] using hc 0
    · simpa [dirsN_cast] using hc 1
    · simpa [dirsN_cast] using hc 2


/-- **The Regge action of the periodic Kuhn complex with geodesic lengths is the lattice hinge sum.**
For a metric `g` on `ℝ³` that is invariant under integer translations, and `n ≥ 3` such that the geodesic
length of every hinge of every tetrahedron is positive, the Regge action `reggeAction` of the complex
`torusComplex n` with the lengths `lenD (dist g univ)` equals `reggeAction3 g univ n`. -/
theorem reggeAction_torus_eq (hn : 3 ≤ n) (g : (Fin 3 → ℝ) → Matrix (Fin 3) (Fin 3) ℝ)
    (hg : ∀ (p : Fin 3 → ℝ) (e : Fin 3 → ℤ), g (p + fun i => (e i : ℝ)) = g p)
    (hpos : ∀ (ct : Fin 3 → ℤ) (σ h : Fin 6),
      0 < Geodesic.dist g Set.univ (cornerPt n ct σ (hP h)) (cornerPt n ct σ (hQ h))) :
    reggeAction (torusComplex n (by omega)) (lenD n (Geodesic.dist g Set.univ)) =
      Conv3.reggeAction3 g Set.univ n := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  have hsym := fun x y => Geodesic.dist_comm_univ (g := g) x y
  have hper : ∀ x y (e : Fin 3 → ℤ), Geodesic.dist g Set.univ (x + fun i => (e i : ℝ))
      (y + fun i => (e i : ℝ)) = Geodesic.dist g Set.univ x y := fun x y e =>
    Geodesic.dist_translate_univ _ (hg · e) x y
  have hnn := fun x y => Geodesic.dist_nonneg (g := g) (U := Set.univ) (x := x) (y := y)
  rw [reggeAction_torus n hn]
  let E : (Fin 3 → Fin n) ≃ TV n := Equiv.piCongrRight fun _ => (valEquiv n).symm
  rw [Conv3.reggeAction3]
  refine sum_congr rfl fun k _ => ?_
  rw [← Equiv.sum_comp E]
  refine sum_congr rfl fun z' _ => ?_
  have hval : ∀ i, (E z' i).val = z' i := fun i => by
    simp [E, valEquiv, ZMod.val_natCast, Nat.mod_eq_of_lt (z' i).2]
  -- the length of the hinge
  have hlen : lenD n (Geodesic.dist g Set.univ) (edgeOf n (E z') k) =
      Conv3.hingeLen g Set.univ (Conv3.hingeMid n k z') (1 / (n : ℝ)) k := by
    rw [lenD_edgeOf n hn, Conv3.hingeLen]
    congr 1
    · funext i
      simp only [liftPt, hval, Conv3.hingeMid, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      field_simp
      ring
    · funext i
      simp only [liftPt, hval, Conv3.hingeMid, Pi.add_apply, Pi.smul_apply, smul_eq_mul, dirsN_cast]
      field_simp
      ring
  rw [hlen]
  congr 1
  rw [Conv3.hingeDef]
  congr 1
  unfold Conv3.clsSum
  refine sum_congr rfl fun σ _ => sum_congr rfl fun h _ => ?_
  rw [← cond_iff_inClass]
  by_cases hc : Cond (dirsN k) σ h
  · simp only [hc, if_true]
    have hct : ∀ i, (((z' i : ℕ) : ℤ) - koff (hP h) (perms σ i) : ℤ) = ((z' i : ℕ) : ℤ) - koff (hP h) (perms σ i) :=
      fun _ => rfl
    have hcc : ∀ i, ((((z' i : ℕ) : ℤ) - koff (hP h) (perms σ i) : ℤ) : ZMod n) =
        (E z' - off n σ (hP h)) i := fun i => by
      simp [E, valEquiv, off]
    rw [dihedralAt_inc n hn _ hsym hper hnn (E z' - off n σ (hP h))
      (fun i => ((z' i : ℕ) : ℤ) - koff (hP h) (perms σ i)) hcc σ h (hpos _ σ h)]
    have hv : Conv3.hingeMid n k z' = fun i => ((((z' i : ℕ) : ℤ) : ℝ) + dirs k i / 2) / n := by
      funext i; simp [Conv3.hingeMid]
    rw [hv, trueLen_eq n σ h k hc (fun i => ((z' i : ℕ) : ℤ))]
  · simp [hc]

end Lightlike.Regge.Linear3
