module

public import LeanShared.Dynamics.ClosedClassifierCodingBoundary
public import LeanShared.Dynamics.MarkovCodingPeriodicSymbols

/-! A retained output packet for an actual finite Markov coding.  It
keeps exact closed-classifier raw-atom origin, all whole-window closures,
finite fibers and the derived affiliation/no-diamonds geometry together.
Boundary and periodic-fiber consequences are proved methods rather than
additional assumed dynamical fields.
-/

public noncomputable section
namespace LeanShared.MarkovFinitePathRealization
open Set Function BilateralShadowingCoding
open scoped Topology
variable {X I : Type*} [MetricSpace X] [TopologicalSpace I] [Fintype I]

structure MarkovCodingProperties (T : X ≃ₜ X) (rectangles : I → Set X)
    (code : Path (Transition T rectangles) → X) : Prop where
  continuous : Continuous code
  onto : Surjective code
  intertwines : ∀ a, code (shift (Transition T rectangles) a) = T (code a)
  windows : ∀ a radius, code a ∈ closure (itineraryWindow T rectangles a.val radius)
  geometry : HasSymbolicFiberGeometry T rectangles code
  fibers : ∀ x, (code ⁻¹' {x}).Finite ∧ (code ⁻¹' {x}).ncard ≤ (Fintype.card I) ^ 2
  classifierOrigin : HasClosedClassifierOrigin rectangles

variable {T : X ≃ₜ X} {rectangles : I → Set X}
  {code : Path (Transition T rectangles) → X}

theorem MarkovCodingProperties.finiteFibers (p : MarkovCodingProperties T rectangles code) (x : X) :
    (code ⁻¹' {x}).Finite := (p.fibers x).1

theorem MarkovCodingProperties.symbolBoundary [BaireSpace X]
    (p : MarkovCodingProperties T rectangles code) :
    ∃ boundary : Set X, IsClosed boundary ∧ interior boundary = ∅ ∧
      ∀ a b, code a = code b → a.val 0 ≠ b.val 0 → code a ∈ boundary :=
  classifier_coding_boundary T rectangles p.classifierOrigin code p.windows

theorem MarkovCodingProperties.periodicLift (p : MarkovCodingProperties T rectangles code)
    (a : Path (Transition T rectangles)) (n : ℕ) (positive : 0 < n)
    (fixed : (T : X → X)^[n] (code a) = code a) :
    ∃ period : ℕ, 0 < period ∧ Function.Periodic a.val (period : ℤ) :=
  periodic_base_lift_periodic T rectangles code p.intertwines p.finiteFibers a n positive fixed

theorem MarkovCodingProperties.periodicSymbols (p : MarkovCodingProperties T rectangles code)
    (x : X) (n : ℕ) (positive : 0 < n) (fixed : (T : X → X)^[n] x = x) (k : ℤ) :
    Injective (fun a : code ⁻¹' {x} => a.val.val k) :=
  periodic_fiber_coordinate_injective T rectangles code p.intertwines p.finiteFibers p.geometry x n positive fixed k

theorem MarkovCodingProperties.returnPermutation (p : MarkovCodingProperties T rectangles code)
    (x : X) (n : ℕ) (fixed : (T : X → X)^[n] x = x) :
    ∃ P : (code ⁻¹' {x}) ≃ (code ⁻¹' {x}), ∀ a,
      (P a).val = (shift (Transition T rectangles) : _ → _)^[n] a.val :=
  exists_fiber_return_equiv T rectangles code p.intertwines p.finiteFibers x n fixed

end LeanShared.MarkovFinitePathRealization
