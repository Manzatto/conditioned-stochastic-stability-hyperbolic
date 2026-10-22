module

public import LeanShared.Dynamics.SubsetMatchingPathLift

/-! Actual coding on the finite signed matching graph.  The chosen
bilateral index lift produces an original graph path; affiliation makes
the resulting point independent of coordinate and proves the exact
semiconjugacy, without assuming a coding on the correction graph.
-/

public noncomputable section
namespace LeanShared.BilateralShadowingCoding
open Set Function MarkovFinitePathRealization
variable {A X : Type*} [MetricSpace X] [DecidableEq A] [TopologicalSpace A]

instance matchingEdgeTopology (R E : A → A → Prop) (k : ℕ) :
    TopologicalSpace (SubsetMatchingEdge R E k) := ⊥

instance matchingEdgeDiscrete (R E : A → A → Prop) (k : ℕ) :
    DiscreteTopology (SubsetMatchingEdge R E k) := ⟨rfl⟩

omit [DecidableEq A] [TopologicalSpace A] in
theorem matching_edge_evaluation_continuous {R E : A → A → Prop} {k : ℕ} (n : ℤ) :
    Continuous (fun a : Path (SubsetMatchingEdgeTransition R E k) => a.val n) :=
  (continuous_apply n).comp continuous_subtype_val

omit [DecidableEq A] [TopologicalSpace A] in
theorem forwardIndexTransport_continuous {R E : A → A → Prop} {k : ℕ} (n : ℕ) (i : Fin k) :
    Continuous (fun a : Path (SubsetMatchingEdgeTransition R E k) =>
      forwardIndexTransport (matchingPathPermutation a) n i) := by
  induction n with
  | zero => exact continuous_const
  | succ n induction =>
    let localMap : SubsetMatchingEdge R E k × Fin k → Fin k := fun p => p.1.val.2.2.symm p.2
    exact (continuous_of_discreteTopology : Continuous localMap).comp
      ((matching_edge_evaluation_continuous (n : ℤ)).prodMk induction)

omit [DecidableEq A] [TopologicalSpace A] in
theorem backwardIndexTransport_continuous {R E : A → A → Prop} {k : ℕ} (n : ℕ) (i : Fin k) :
    Continuous (fun a : Path (SubsetMatchingEdgeTransition R E k) =>
      backwardIndexTransport (matchingPathPermutation a) n i) := by
  induction n with
  | zero => exact continuous_const
  | succ n induction =>
    let localMap : SubsetMatchingEdge R E k × Fin k → Fin k := fun p => p.1.val.2.2 p.2
    exact (continuous_of_discreteTopology : Continuous localMap).comp
      ((matching_edge_evaluation_continuous (-(n : ℤ) - 1)).prodMk induction)

omit [DecidableEq A] [TopologicalSpace A] in
theorem indexTransport_continuous {R E : A → A → Prop} {k : ℕ} (n : ℤ) (i : Fin k) :
    Continuous (fun a : Path (SubsetMatchingEdgeTransition R E k) =>
      indexTransport (matchingPathPermutation a) n i) := by
  cases n with
  | ofNat n => exact forwardIndexTransport_continuous n i
  | negSucc n => exact backwardIndexTransport_continuous (n + 1) i

set_option maxHeartbeats 1000000 in
omit [DecidableEq A] in
theorem liftMatchingPath_continuous {R E : A → A → Prop} {k : ℕ} :
    Continuous (fun a : Path (SubsetMatchingEdgeTransition R E k) => liftMatchingPath a) := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro n
  apply continuous_pi
  intro i
  change Continuous (fun a : Path (SubsetMatchingEdgeTransition R E k) =>
    subsetSymbol (a.val n).val.1 (indexTransport (matchingPathPermutation a) n i))
  let localMap : SubsetMatchingEdge R E k × Fin k → A := fun p => subsetSymbol p.1.val.1 p.2
  have localContinuous : Continuous localMap := continuous_of_discreteTopology
  have inputs : Continuous (fun a : Path (SubsetMatchingEdgeTransition R E k) =>
      (a.val n, indexTransport (matchingPathPermutation a) n i)) :=
    (matching_edge_evaluation_continuous (R := R) (E := E) (k := k) n).prodMk
      (indexTransport_continuous (R := R) (E := E) (k := k) n i)
  exact localContinuous.comp inputs

@[expose] def matchingCode (T : X ≃ₜ X) (rectangles : A → Set X)
    (code : Path (Transition T rectangles) → X) (k : ℕ)
    (a : Path (SubsetMatchingEdgeTransition (Transition T rectangles) (Affiliated rectangles) (k + 1))) : X :=
  code (tupleCoordinate (liftMatchingPath a) 0)

omit [DecidableEq A] in
theorem matchingCode_continuous (T : X ≃ₜ X) (rectangles : A → Set X)
    (code : Path (Transition T rectangles) → X) (continuousCode : Continuous code) (k : ℕ) :
    Continuous (matchingCode T rectangles code k) :=
  continuousCode.comp ((tupleCoordinate_continuous 0).comp liftMatchingPath_continuous)

omit [DecidableEq A] in
theorem matchingCode_intertwines (T : X ≃ₜ X) (rectangles : A → Set X)
    (code : Path (Transition T rectangles) → X)
    (geometry : HasSymbolicFiberGeometry T rectangles code)
    (intertwines : ∀ a, code (shift (Transition T rectangles) a) = T (code a)) (k : ℕ)
    (a : Path (SubsetMatchingEdgeTransition (Transition T rectangles) (Affiliated rectangles) (k + 1))) :
    matchingCode T rectangles code k
      (shift (SubsetMatchingEdgeTransition (Transition T rectangles) (Affiliated rectangles) (k + 1)) a) =
      T (matchingCode T rectangles code k a) := by
  rw [matchingCode, matchingCode, ← intertwines]
  apply (geometry.1 _ _).mpr
  intro n
  exact subsetSymbol_related (a.val (n + 1)).val.1 _ _

end LeanShared.BilateralShadowingCoding
