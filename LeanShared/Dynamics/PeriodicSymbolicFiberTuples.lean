module

public import LeanShared.Dynamics.SymbolicFiberTuples
public import LeanShared.Dynamics.MarkovCodingPeriodicSymbols

/-! Any ordered family of distinct lifts of an actual periodic base point
produces a path in the literal separated affiliated tuple graph.  Symbol
injectivity at every time is proved from finite fibers and no-diamonds.
-/

public noncomputable section
namespace LeanShared.BilateralShadowingCoding
open Set Function MarkovFinitePathRealization
variable {A X : Type*} [MetricSpace X] [TopologicalSpace A]

theorem exists_periodic_fiber_tuple (T : X ≃ₜ X) (rectangles : A → Set X)
    (code : Path (Transition T rectangles) → X)
    (intertwines : ∀ a, code (shift (Transition T rectangles) a) = T (code a))
    (finiteFibers : ∀ x, (code ⁻¹' {x}).Finite)
    (geometry : HasSymbolicFiberGeometry T rectangles code)
    (x : X) (n : ℕ) (positive : 0 < n) (fixed : (T : X → X)^[n] x = x)
    (k : ℕ) (lifts : Fin k → code ⁻¹' {x}) (distinct : Injective lifts) :
    ∃ a : Path (FiberTupleTransition (Transition T rectangles) (Affiliated rectangles) k),
      ∀ i, tupleCoordinate a i = (lifts i).val := by
  let a : ℤ → Fin k → A := fun j i => (lifts i).val.val j
  have admissible (j : ℤ) :
      FiberTupleTransition (Transition T rectangles) (Affiliated rectangles) k (a j) (a (j + 1)) := by
    refine ⟨fun i => (lifts i).val.property j, ?_, ?_, ?_, ?_⟩
    · intro i l
      exact (geometry.1 _ _).mp
        ((show code (lifts i).val = x from (lifts i).property).trans
          (show code (lifts l).val = x from (lifts l).property).symm) j
    · intro i l
      exact (geometry.1 _ _).mp
        ((show code (lifts i).val = x from (lifts i).property).trans
          (show code (lifts l).val = x from (lifts l).property).symm) (j + 1)
    · exact (periodic_fiber_coordinate_injective T rectangles code intertwines finiteFibers geometry x n positive fixed j).comp distinct
    · exact (periodic_fiber_coordinate_injective T rectangles code intertwines finiteFibers geometry x n positive fixed (j + 1)).comp distinct
  exact ⟨⟨a, admissible⟩, fun _ => rfl⟩

end LeanShared.BilateralShadowingCoding
