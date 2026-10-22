module

public import LeanShared.Dynamics.ReindexedInteriorClassifierCoding

/-! The derived finite coding geometry used by the Manning argument.
It applies to the actual pruned full-interior alphabet.  The producer
retains the literal original classifier enumeration and coding map in
its parameters; no Boolean enumeration of the pruned alphabet is assumed.
-/

public noncomputable section
namespace LeanShared.MarkovFinitePathRealization
open Set Function BilateralShadowingCoding
variable {X I : Type*} [MetricSpace X] [TopologicalSpace I] [Fintype I]

structure FiniteCodingGeometry (T : X ≃ₜ X) (rectangles : I → Set X)
    (code : Path (Transition T rectangles) → X) : Prop where
  continuous : Continuous code
  onto : Surjective code
  intertwines : ∀ a, code (shift (Transition T rectangles) a) = T (code a)
  windows : ∀ a radius, code a ∈ closure (itineraryWindow T rectangles a.val radius)
  geometry : HasSymbolicFiberGeometry T rectangles code
  fibers : ∀ x, (code ⁻¹' {x}).Finite ∧ (code ⁻¹' {x}).ncard ≤ (Fintype.card I) ^ 2

variable {T : X ≃ₜ X} {rectangles : I → Set X} {code : Path (Transition T rectangles) → X}

theorem MarkovCodingProperties.finiteGeometry (p : MarkovCodingProperties T rectangles code) :
    FiniteCodingGeometry T rectangles code :=
  ⟨p.continuous, p.onto, p.intertwines, p.windows, p.geometry, p.fibers⟩

theorem FiniteCodingGeometry.finiteFibers (p : FiniteCodingGeometry T rectangles code) (x : X) :
    (code ⁻¹' {x}).Finite := (p.fibers x).1

theorem FiniteCodingGeometry.periodicSymbols (p : FiniteCodingGeometry T rectangles code)
    (x : X) (n : ℕ) (positive : 0 < n) (fixed : (T : X → X)^[n] x = x) (k : ℤ) :
    Injective (fun a : code ⁻¹' {x} => a.val.val k) :=
  periodic_fiber_coordinate_injective T rectangles code p.intertwines p.finiteFibers p.geometry x n positive fixed k

theorem FiniteCodingGeometry.returnPermutation (p : FiniteCodingGeometry T rectangles code)
    (x : X) (n : ℕ) (fixed : (T : X → X)^[n] x = x) :
    ∃ P : (code ⁻¹' {x}) ≃ (code ⁻¹' {x}), ∀ a,
      (P a).val = (shift (Transition T rectangles) : _ → _)^[n] a.val :=
  exists_fiber_return_equiv T rectangles code p.intertwines p.finiteFibers x n fixed

end LeanShared.MarkovFinitePathRealization

namespace LeanShared.FiniteClosedRefinement
open Set Function BilateralShadowingCoding MarkovFinitePathRealization
variable {X J : Type*} [MetricSpace X] [BaireSpace X] [CompactSpace X]
  [TopologicalSpace J] [Fintype J] {d : ℕ}

theorem reindexedInteriorCode_finiteGeometry (T : X ≃ₜ X) (C : Fin d → Set X)
    (rectangles : J → Set X) (statuses : J ≃ (Fin d → Bool))
    (law : ∀ j, rectangles j = atom C (statuses j)) (closed : ∀ i, IsClosed (C i))
    (code : Path (Transition T rectangles) → X) (properties : MarkovCodingProperties T rectangles code) :
    FiniteCodingGeometry T (interiorRectangles C) (reindexedInteriorCode T C rectangles statuses law code) :=
  ⟨reindexedInteriorCode_continuous T C rectangles statuses law code properties.continuous,
    reindexedInteriorCode_surjective T C rectangles statuses law closed code properties,
    reindexedInteriorCode_intertwines T C rectangles statuses law code properties,
    reindexedInteriorCode_windows T C rectangles statuses law code properties,
    reindexedInteriorCode_geometry T C rectangles statuses law code properties,
    reindexedInteriorCode_fiber_card T C rectangles statuses law code properties⟩

end LeanShared.FiniteClosedRefinement
