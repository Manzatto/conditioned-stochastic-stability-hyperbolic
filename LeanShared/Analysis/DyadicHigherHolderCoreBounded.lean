module
public import LeanShared.Analysis.DyadicHigherHolderBlockBound
public import LeanShared.Analysis.DyadicHolderCoreBounded
public import LeanShared.Geometry.EuclideanHigherHolderCore

/-! Smooth-core boundedness at arbitrary finite anisotropic orders follows
from the genuine complete higher Holder graph norm. -/
public noncomputable section
open Set Filter MeasureTheory
open scoped SchwartzMap Topology
namespace LeanShared.DyadicHigherHolderCoreBounded
variable {E : Type} {U A S : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
  [MeasurableSpace U] [BorelSpace U] [Fintype S]
  {ι:Type} [Fintype ι] (basis:OrthonormalBasis ι ℝ E)
  (μ:Measure U) [μ.IsAddHaarMeasure] {J:ℝ} (hJ:0≤J)
  (leaves:A→GraphLeafNorm.GraphLeaf U E J)

include basis in
theorem smoothCoreBounded (low high:S→𝓢(E,ℂ))
    (zero:∀s,∀ᶠ ξ in 𝓝 (0:E),high s ξ=0)
    {K:Set E} (compact:IsCompact K) {a:ℝ} (ha:0<a) (ha1:a<1) (n:ℕ)
    (t:S→ℝ) (margin:∀s,t s≤a+(n+1:ℕ)) :
    SchwartzAmbientBlocks.SmoothCoreBounded μ hJ leaves K (DyadicSymbols.symbol low high) t := by
  have compactClosure : IsCompact (closure K) := by
    rw [compact.isClosed.closure_eq]
    exact compact
  obtain ⟨C,_,estimate⟩ := DyadicHigherHolderBlockBound.exists_bound basis μ hJ leaves
    low high zero compact ha ha1 n t margin
  intro f
  let c := DyadicHolderCoreBounded.smoothCore compact f
  let v := EuclideanHigherHolderCore.smooth compactClosure ha ha1 (n+1) c
  refine ⟨C*‖v.val‖,?_⟩
  intro j
  apply estimate f.val v.val ?_ (DyadicHolderCoreBounded.supported_tsupport compact f) j
  intro x
  exact EuclideanHigherHolderCore.physical_smooth compactClosure ha ha1 (n+1) c x
end LeanShared.DyadicHigherHolderCoreBounded
