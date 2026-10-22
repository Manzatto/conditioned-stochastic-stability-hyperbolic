module

public import LeanShared.Dynamics.MarkovCodingPeriodicFibers
public import LeanShared.Dynamics.SymbolicExponentialVariation

/-! Literal finite graphs of ordered separated fiber tuples.  Each tuple
coordinate is an original graph path; affiliation proves that all
coordinates code the same point.  Their pulled-back potentials retain
exponential cylinder variations. -/

public noncomputable section
namespace LeanShared.BilateralShadowingCoding
open Set Function MarkovFinitePathRealization
variable {A X : Type*} [MetricSpace X] {R : A → A → Prop}

@[expose] def FiberTupleTransition (R : A → A → Prop) (E : A → A → Prop) (k : ℕ)
    (u v : Fin k → A) : Prop :=
  (∀ i, R (u i) (v i)) ∧ (∀ i j, E (u i) (u j)) ∧
  (∀ i j, E (v i) (v j)) ∧ Injective u ∧ Injective v

@[expose] def tupleCoordinate {E : A → A → Prop} {k : ℕ}
    (a : Path (FiberTupleTransition R E k)) (i : Fin k) : Path R :=
  ⟨fun n => a.val n i, fun n => (a.property n).1 i⟩

theorem tupleCoordinate_continuous [TopologicalSpace A] {E : A → A → Prop} {k : ℕ} (i : Fin k) :
    Continuous (fun a : Path (FiberTupleTransition R E k) => tupleCoordinate a i) := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro n
  exact (continuous_apply i).comp ((continuous_apply n).comp continuous_subtype_val)

theorem tupleCoordinate_shift [TopologicalSpace A] {E : A → A → Prop} {k : ℕ}
    (a : Path (FiberTupleTransition R E k)) (i : Fin k) :
    tupleCoordinate (shift (FiberTupleTransition R E k) a) i = shift R (tupleCoordinate a i) := by
  rfl

theorem tuple_coordinates_code_eq (T : X ≃ₜ X) (rectangles : A → Set X)
    (code : Path (Transition T rectangles) → X)
    (geometry : HasSymbolicFiberGeometry T rectangles code) {k : ℕ}
    (a : Path (FiberTupleTransition (Transition T rectangles) (Affiliated rectangles) k))
    (i j : Fin k) : code (tupleCoordinate a i) = code (tupleCoordinate a j) := by
  apply (geometry.1 _ _).mpr
  intro n
  exact (a.property n).2.1 i j

theorem tuple_potential_exponential {E : A → A → Prop} {k : ℕ}
    (φ : Path R → ℝ) (variation : HasExponentialVariations φ) (i : Fin k) :
    HasExponentialVariations (fun a : Path (FiberTupleTransition R E k) => φ (tupleCoordinate a i)) := by
  obtain ⟨rate, positive, small, C, nonnegative, bound⟩ := variation
  refine ⟨rate, positive, small, C, nonnegative, fun radius a b matching => ?_⟩
  apply bound radius
  intro n lower upper
  exact congrArg (fun u : Fin k → A => u i) (matching n lower upper)

end LeanShared.BilateralShadowingCoding
