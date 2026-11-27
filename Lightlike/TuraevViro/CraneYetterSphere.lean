import Lightlike.TuraevViro.CraneYetterThreeWeight
import Lightlike.FourD.Tests

/-!
# The Crane–Yetter weight on the boundary of the 5-simplex, in coordinates

On `sphere6 = ∂Δ⁵` (the 4-simplices `univ.erase p`, the tetrahedra `univ \ {p, p.succAbove a}`) the sorted vertices are
`p.succAbove` and `p.succAbove ∘ a.succAbove`. This file rewrites the data of the weight at `r = 3`
(`craneYetterWeight_three`) in these coordinates, free of `orderEmbOfFin`, so that it can be evaluated by kernel `decide`.
-/

open Finset Lightlike.Pentagon Lightlike.FourD Lightlike.FourD.Tests

namespace Lightlike.TV

/-- The sorted embedding of `univ.erase p` is `p.succAbove`. -/
lemma orderEmbOfFin_erase_univ (p : Fin 6) (h : #(univ.erase p) = 5) (a : Fin 5) :
    (univ.erase p).orderEmbOfFin h a = p.succAbove a :=
  (congrFun (Finset.orderEmbOfFin_unique h (f := p.succAbove)
    (fun x => by simp) (Fin.strictMono_succAbove p)) a).symm

lemma succAbove_succAbove_mem : ∀ (p : Fin 6) (a : Fin 5) (x : Fin 4),
    p.succAbove (a.succAbove x) ∈ (univ \ {p, p.succAbove a} : Finset (Fin 6)) := by
  decide +kernel

/-- The sorted vertices of the tetrahedron `univ \ {p, p.succAbove a}` are `p.succAbove (a.succAbove i)`. -/
lemma orderEmbOfFin_tet (p : Fin 6) (a : Fin 5) (h : #(univ \ {p, p.succAbove a} : Finset (Fin 6)) = 4) (i : Fin 4) :
    (univ \ {p, p.succAbove a} : Finset (Fin 6)).orderEmbOfFin h i = p.succAbove (a.succAbove i) :=
  (congrFun (Finset.orderEmbOfFin_unique h (f := fun i => p.succAbove (a.succAbove i))
    (fun x => succAbove_succAbove_mem p a x)
    ((Fin.strictMono_succAbove p).comp (Fin.strictMono_succAbove a))) i).symm


/-- The `i`-th leg (triangle) of the tetrahedron `univ \ {p, p.succAbove a}`. -/
def tetLeg (p : Fin 6) (a : Fin 5) (i : Fin 4) : Finset (Fin 6) :=
  univ \ {p, p.succAbove a, p.succAbove (a.succAbove i)}

lemma card_tet : ∀ (p : Fin 6) (a : Fin 5), #(univ \ {p, p.succAbove a} : Finset (Fin 6)) = 4 := by
  decide +kernel

lemma erase_tet : ∀ (p : Fin 6) (a : Fin 5) (i : Fin 4),
    (univ \ {p, p.succAbove a} : Finset (Fin 6)).erase (p.succAbove (a.succAbove i)) = tetLeg p a i := by
  unfold tetLeg; decide +kernel

/-- The integer weight of the tetrahedron `univ \ {p, p.succAbove a}` at `r = 3`, in coordinates. -/
def tetModel (col : Finset (Fin 6) → ℕ) (p : Fin 6) (a : Fin 5) : ℤ :=
  (-1 : ℤ) ^ col (univ \ {p, p.succAbove a}) *
      theta3Z (col (univ \ {p, p.succAbove a})) (col (tetLeg p a 0)) (col (tetLeg p a 2)) *
    theta3Z (col (univ \ {p, p.succAbove a})) (col (tetLeg p a 1)) (col (tetLeg p a 3))

/-- `tetEps3` of the tetrahedron `univ \ {p, p.succAbove a}` is `tetModel`. -/
lemma tetEps3_tet (col : Finset (Fin 6) → ℕ) (p : Fin 6) (a : Fin 5) :
    tetEps3 col (univ \ {p, p.succAbove a}) = tetModel col p a := by
  unfold tetEps3
  rw [dif_pos (card_tet p a)]
  rw [orderEmbOfFin_tet p a (card_tet p a) 0, orderEmbOfFin_tet p a (card_tet p a) 1,
    orderEmbOfFin_tet p a (card_tet p a) 2, orderEmbOfFin_tet p a (card_tet p a) 3,
    erase_tet, erase_tet, erase_tet, erase_tet]
  rfl

/-- The pairs `(p, a)` with `p ≤ a` parametrise the tetrahedra `univ \ {p, p.succAbove a}` of `sphere6`, once each. -/
def tetIdx : Finset (Fin 6 × Fin 5) := univ.filter fun x => x.1.val ≤ x.2.val

lemma tets_sphere6_image :
    sphere6.tets = tetIdx.image (fun x => (univ \ {x.1, x.1.succAbove x.2} : Finset (Fin 6))) := by
  unfold tetIdx; decide +kernel

lemma tetIdx_inj : Set.InjOn (fun x : Fin 6 × Fin 5 => (univ \ {x.1, x.1.succAbove x.2} : Finset (Fin 6)))
    (tetIdx : Set (Fin 6 × Fin 5)) := by
  unfold tetIdx; intro x hx y hy hxy; revert x y; decide +kernel


/-- The embedding `Fin 5 ↪ Fin 6` omitting `p`. -/
def succAboveEmb (p : Fin 6) : Fin 5 ↪ Fin 6 := ⟨p.succAbove, Fin.succAbove_right_injective⟩

/-- The local triangle colours of the 4-simplex `univ.erase p`, in coordinates. -/
def Jp (col : Finset (Fin 6) → ℕ) (p : Fin 6) : Finset (Fin 5) → ℕ := fun F => col (F.map (succAboveEmb p))

/-- The local tetrahedron colours of the 4-simplex `univ.erase p`, in coordinates. -/
def Ip (col : Finset (Fin 6) → ℕ) (p : Fin 6) : Fin 5 → ℕ := fun m => col ((univ.erase p).erase (p.succAbove m))

lemma card_erase_univ (p : Fin 6) : #(univ.erase p : Finset (Fin 6)) = 5 := by
  simp

lemma emb_erase (p : Fin 6) : ((univ.erase p).orderEmbOfFin (card_erase_univ p)).toEmbedding = succAboveEmb p :=
  Function.Embedding.ext fun i => orderEmbOfFin_erase_univ p (card_erase_univ p) i

lemma locJ_erase (col : Finset (Fin 6) → ℕ) (p : Fin 6) :
    locJ col (univ.erase p) (card_erase_univ p) = Jp col p := by
  funext F
  unfold locJ Jp
  rw [emb_erase]

lemma locI_erase (col : Finset (Fin 6) → ℕ) (p : Fin 6) :
    locI col (univ.erase p) (card_erase_univ p) = Ip col p := by
  funext m
  unfold locI Ip
  rw [orderEmbOfFin_erase_univ]

lemma vertexEps3_erase (col : Finset (Fin 6) → ℕ) (p : Fin 6) :
    vertexEps3 col (univ.erase p) = cy3Eps (Jp col p) (Ip col p) := by
  unfold vertexEps3
  rw [dif_pos (card_erase_univ p), locJ_erase, locI_erase]

lemma vertexExp3_erase (col : Finset (Fin 6) → ℕ) (p : Fin 6) (o : ℤ) :
    vertexExp3 col (univ.erase p) o = (if o = 1 then 1 else -1) * cy3Exp (Jp col p) (Ip col p) := by
  unfold vertexExp3
  rw [dif_pos (card_erase_univ p), locJ_erase, locI_erase]

lemma simps_sphere6_image : sphere6.simps = (univ : Finset (Fin 6)).image (fun p => univ.erase p) := by
  decide +kernel

lemma erase_inj : Function.Injective (fun p : Fin 6 => (univ.erase p : Finset (Fin 6))) := by
  decide +kernel

/-- The integer `M` of the weight of a colouring of `sphere6` at `r = 3`. -/
def sphereM (col : Finset (Fin 6) → ℕ) : ℤ :=
  (∏ f ∈ sphere6.tris, (-1 : ℤ) ^ col f) * (∏ x ∈ tetIdx, tetModel col x.1 x.2) *
    ∏ p : Fin 6, cy3Eps (Jp col p) (Ip col p)

/-- The exponent `E` of `q^{1/2}` in the weight of a colouring of `sphere6` at `r = 3`. -/
def sphereE (col : Finset (Fin 6) → ℕ) : ℤ :=
  ∑ p : Fin 6, (if relSign univ (univ.erase p) = 1 then 1 else -1) * cy3Exp (Jp col p) (Ip col p)

/-- **The weight of a colouring of `∂Δ⁵` at `r = 3`**, in coordinates: an integer times a power of `q^{1/2}`. -/
theorem craneYetterWeight_three_sphere6 (col : Finset (Fin 6) → ℕ) (hc : ∀ f, col f ≤ 1) :
    craneYetterWeight 3 sphere6 (relSign univ) col = (sphereM col : ℂ) * qHalf 3 ^ sphereE col := by
  rw [craneYetterWeight_three sphere6 (relSign univ) col hc]
  have ht : ∏ t ∈ sphere6.tets, tetEps3 col t = ∏ x ∈ tetIdx, tetModel col x.1 x.2 := by
    rw [tets_sphere6_image, Finset.prod_image tetIdx_inj]
    exact Finset.prod_congr rfl fun x _ => tetEps3_tet col x.1 x.2
  have hv : ∏ s ∈ sphere6.simps, vertexEps3 col s = ∏ p : Fin 6, cy3Eps (Jp col p) (Ip col p) := by
    rw [simps_sphere6_image, Finset.prod_image (fun x _ y _ h => erase_inj h)]
    exact Finset.prod_congr rfl fun p _ => vertexEps3_erase col p
  have he : ∑ s ∈ sphere6.simps, vertexExp3 col s (relSign univ s) = sphereE col := by
    rw [simps_sphere6_image, Finset.sum_image (fun x _ y _ h => erase_inj h)]
    exact Finset.sum_congr rfl fun p _ => vertexExp3_erase col p _
  rw [ht, hv, he]
  rfl


/-- The triangles through the vertex `0`, the free data of a `ℤ/2` 2-cocycle of `∂Δ⁵`. -/
def tri0 : Finset (Finset (Fin 6)) := ((univ : Finset (Fin 6)).powersetCard 3).filter fun f => 0 ∈ f

/-- The colour of a triangle: the free datum `γ` on the triangles through `0`, and the cone formula
`γ(abc) = γ(0ab) + γ(0ac) + γ(0bc) (mod 2)` on the others. -/
def triCol (γ : Finset (Fin 6) → ℕ) (f : Finset (Fin 6)) : ℕ :=
  if 0 ∈ f then γ f else (∑ e ∈ f.powersetCard 2, γ (insert 0 e)) % 2

/-- The colour of a tetrahedron: `j_l + j_{t₃} (mod 2)`, the sum of the colours of the faces opposite its lowest and third
vertex (the vertices of even rank). -/
def tetCol (γ : Finset (Fin 6) → ℕ) (t : Finset (Fin 6)) : ℕ :=
  (∑ x ∈ t.filter (fun x => (t.filter (· < x)).card % 2 = 0), triCol γ (t.erase x)) % 2

/-- The colouring of the triangles and tetrahedra of `∂Δ⁵` determined by the cone datum `γ`. -/
def coneCol (γ : Finset (Fin 6) → ℕ) (f : Finset (Fin 6)) : ℕ :=
  if #f = 3 then triCol γ f else if #f = 4 then tetCol γ f else 0

/-- **Every cone cocycle of `∂Δ⁵` has weight `1` at `r = 3`**: for every choice of the colours `0, 1` on the ten triangles
through the vertex `0`, either `sphereM = 1` and `sphereE ≡ 0` or `sphereM = -1` and `sphereE ≡ 6` modulo `12`, i.e.
`sphereM · (q^{1/2})^{sphereE} = 1` (as `(q^{1/2})^{12} = 1`). The check is by kernel evaluation of the 1024 cases. -/
theorem sphere_weight_one :
    ∀ b ∈ tri0.pi (fun _ => range 2),
      (sphereM (coneCol (Lightlike.PR.extS tri0 b)) = 1 ∧ sphereE (coneCol (Lightlike.PR.extS tri0 b)) % 12 = 0) ∨
        (sphereM (coneCol (Lightlike.PR.extS tri0 b)) = -1 ∧
          sphereE (coneCol (Lightlike.PR.extS tri0 b)) % 12 = 6) := by
  unfold sphereM sphereE tetModel cy3Eps cy3Exp cyA cyB cyC cyS cyP pr3 Jp Ip tetLeg tetIdx theta3Z tet3Z
    coneCol triCol tetCol tri0 Lightlike.PR.extS
  decide +kernel

end Lightlike.TV
