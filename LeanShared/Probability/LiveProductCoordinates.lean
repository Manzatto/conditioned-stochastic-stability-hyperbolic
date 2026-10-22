module

public import Mathlib.Topology.Homeomorph.Lemmas

/-! Exact state coordinates for a local system stabilized with a full
auxiliary manifold. The closed live neighborhood uses its literal subtype. -/

@[expose] public noncomputable section
open Set
namespace LeanShared.LiveProductCoordinates
variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- The auxiliary factor is completely live. -/
def liveProduct (K : Set X) : ↥(K ×ˢ (univ : Set Y)) ≃ₜ K × Y :=
  (Homeomorph.Set.prod K univ).trans
    ((Homeomorph.refl K).prodCongr (Homeomorph.Set.univ Y))

@[simp] theorem liveProduct_fst (K : Set X) (z : ↥(K ×ˢ (univ : Set Y))) :
    (liveProduct K z).1.val = z.val.1 := rfl

@[simp] theorem liveProduct_snd (K : Set X) (z : ↥(K ×ˢ (univ : Set Y))) :
    (liveProduct K z).2 = z.val.2 := rfl

/-- Closure of the actual product collar has the expected product live
state, without redefining the manuscript state space. -/
def closedCollar (V : Set X) :
    ↥(closure (V ×ˢ (univ : Set Y))) ≃ₜ (closure V) × Y :=
  (Homeomorph.setCongr (by rw [closure_prod_eq, closure_univ])).trans
    (liveProduct (closure V))

@[simp] theorem closedCollar_fst (V : Set X)
    (z : ↥(closure (V ×ˢ (univ : Set Y)))) :
    (closedCollar V z).1.val = z.val.1 := rfl

@[simp] theorem closedCollar_snd (V : Set X)
    (z : ↥(closure (V ×ˢ (univ : Set Y)))) :
    (closedCollar V z).2 = z.val.2 := rfl

end LeanShared.LiveProductCoordinates
