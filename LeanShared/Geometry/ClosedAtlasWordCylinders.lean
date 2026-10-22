module

public import LeanShared.Dynamics.FiniteWordCylinders
public import Mathlib.Topology.OpenPartialHomeomorph.Basic

/-! Closed genuine atlas itineraries for compact moving distortion fibers.
Only intrinsic weights/Jacobians are evaluated on their boundaries; no
partial chart inverse is assumed valid there. -/

@[expose] public noncomputable section
open Set
namespace LeanShared.ClosedAtlasWordCylinders
open CylinderPrincipalCoefficient
variable {E M Ω J : Type*} [TopologicalSpace E] [TopologicalSpace M] [TopologicalSpace Ω]

/-- The closure of every actual base chart is observed at each prefix. -/
def cylinder (e : J → OpenPartialHomeomorph M E) (F : Ω → M → M)
    (N : ℕ) (labels : Fin (N + 1) → J) : Set ((Fin N → Ω) × M) :=
  {z | ∀ j : Fin (N + 1), prefixOrbit F z.1 j.val z.2 ∈ closure (e (labels j)).source}

theorem cylinder_closed (e : J → OpenPartialHomeomorph M E) (F : Ω → M → M)
    (hF : Continuous (fun z : Ω × M => F z.1 z.2))
    (N : ℕ) (labels : Fin (N + 1) → J) : IsClosed (cylinder e F N labels) := by
  have heq : cylinder e F N labels = ⋂ j : Fin (N + 1),
      (fun z : (Fin N → Ω) × M => prefixOrbit F z.1 j.val z.2) ⁻¹' closure (e (labels j)).source := by
    ext z
    simp only [cylinder, mem_ofPred_eq, mem_iInter, mem_preimage]
  rw [heq]
  exact isClosed_iInter fun j => isClosed_closure.preimage (continuous_prefixOrbit F hF N j.val)

omit [TopologicalSpace Ω] in
theorem open_cylinder_subset (e : J → OpenPartialHomeomorph M E) (F : Ω → M → M)
    (N : ℕ) (labels : Fin (N + 1) → J) :
    FiniteWordCylinders.cylinder F (fun j => (e j).source) N labels ⊆ cylinder e F N labels := by
  intro z hz j
  exact subset_closure (hz j)

end LeanShared.ClosedAtlasWordCylinders
