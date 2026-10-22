module

public import LeanShared.Geometry.SmoothHolderTestSpaces

/-! Its norm and all operations are unchanged. This prevents class resolution from repeatedly
expanding the nested graph/closed-core subtype when an ordinary source record is specialized to
the concrete test space. -/

public noncomputable section
open Set
namespace LeanShared.SmoothHolderTestSpaces
open SmoothSupportedManifoldCore
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MetricSpace M] [ChartedSpace E M] [CompactSpace M]
  (u : ℝ) (holder : ∀ c : core (E := E) (univ : Set M), ∃ C : ℝ,
    ∀ x y, ‖c.val x - c.val y‖ ≤ C * dist x y ^ u) (V : Set M)

instance holderSpaceSeminormed : SeminormedAddCommGroup (space u holder V) :=
  (inferInstance : NormedAddCommGroup (space u holder V)).toSeminormedAddCommGroup

end LeanShared.SmoothHolderTestSpaces
