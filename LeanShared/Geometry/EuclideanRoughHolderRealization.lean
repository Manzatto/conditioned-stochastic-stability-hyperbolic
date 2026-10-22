module
public import LeanShared.Geometry.EuclideanSmoothHolderCore
public import LeanShared.Geometry.SupportedFractionalApproximation
public import Mathlib.Topology.Sequences
import all LeanShared.Analysis.BumpSupportedHolderDensity

/-! Actual rough functions in the constructed supported little Hölder
space. Membership follows from the proved exact-support smoothing theorem;
neither lower-space representation nor smooth approximation is an input. -/
public noncomputable section
open Set Filter MeasureTheory
open scoped Topology BoundedContinuousFunction Manifold ContDiff
namespace LeanShared.EuclideanSmoothHolderCore
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [μ.IsAddHaarMeasure]
  {V : Set E} (hV : IsCompact (closure V)) {b : ℝ} (hb : 0 < b) (hb1 : b < 1)

omit [MeasurableSpace E] [BorelSpace E] in
theorem smoothGraph_mem (v : BoundedHolderSpace.graph E b)
    (hv : BumpSupportedHolderDensity.SmoothGraph V v) :
    v ∈ space hV hb hb1 := by
  let c : SmoothSupportedManifoldCore.core (E := E) V :=
    ⟨fun x => BoundedHolderSpace.physical E b v x, hv.1.contMDiff, hv.2.2⟩
  have identity : core hV hb hb1 c = v := by
    apply BoundedHolderSpace.physical_injective E b
    ext x
    rfl
  exact (core hV hb hb1).range.le_topologicalClosure ⟨c, identity⟩

include μ in
theorem lower_mem (f : E →ᵇ ℂ) (openV : IsOpen V) (support : tsupport f ⊆ V)
    (compact : HasCompactSupport f) {a C : ℝ} (hab : b < a) (hC : 0 ≤ C)
    (hf : ∀ x y, ‖f x - f y‖ ≤ C * ‖x - y‖ ^ a) :
    BumpLowerHolderConvergence.lift f hb.le hab hC hf ∈ space hV hb hb1 := by
  obtain ⟨v, smooth, limit⟩ := BumpSupportedHolderDensity.exists_sequence
    μ f openV support compact hb.le hab hC hf
  exact (core hV hb hb1).range.isClosed_topologicalClosure.mem_of_tendsto limit
    (Eventually.of_forall fun n => smoothGraph_mem hV hb hb1 (v n) (smooth n))

include μ in
theorem exists_lower_of_regular (f : E →ᵇ ℂ) (openV : IsOpen V)
    (support : tsupport f ⊆ V) (compact : HasCompactSupport f)
    {a : ℝ} (ha : 0 < a) (ha1 : a < 1) (hab : b < a)
    (regular : FractionalManifoldRegularity.Regular (E := E) (F := ℂ) a (fun x => f x)) :
    ∃ v : space hV hb hb1, physical hV hb hb1 v = f := by
  obtain ⟨C, hC, hf⟩ := FractionalManifoldRegularity.global_holder_of_regular
    f compact ha ha1 regular
  exact ⟨⟨BumpLowerHolderConvergence.lift f hb.le hab hC hf,
    lower_mem μ hV hb hb1 f openV support compact hab hC hf⟩, rfl⟩

omit [MeasurableSpace E] [BorelSpace E] in
theorem exists_smooth_sequence (v : space hV hb hb1) :
    ∃ c : ℕ → SmoothSupportedManifoldCore.core (E := E) V,
      Tendsto (fun n => smooth hV hb hb1 (c n)) atTop (𝓝 v) := by
  have dense := smooth_dense hV hb hb1
  have member : v ∈ closure (range (smooth hV hb hb1)) := dense.closure_range ▸ mem_univ v
  obtain ⟨s, hs, limit⟩ := mem_closure_iff_seq_limit.mp member
  choose c hc using hs
  exact ⟨c, by simpa only [hc] using limit⟩
end LeanShared.EuclideanSmoothHolderCore
