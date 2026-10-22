module
public import LeanShared.Analysis.DyadicHolderBlockBound
public import LeanShared.Geometry.EuclideanSmoothHolderCore

/-! The cited smooth-core boundedness input is proved for literal compact
support and dyadic Schwartz bases whenever the exponents admit a lower
Hölder order between zero and one. -/
public noncomputable section
open Set MeasureTheory
open scoped SchwartzMap Manifold ContDiff
namespace LeanShared.DyadicHolderCoreBounded
variable {E U A S : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
  [MeasurableSpace U] [BorelSpace U] [Fintype S]
  (μ : Measure U) [μ.IsAddHaarMeasure] {J : ℝ} (hJ : 0≤J)
  (leaves : A → GraphLeafNorm.GraphLeaf U E J)
  (low high : S → 𝓢(E,ℂ)) (zero : ∀s,high s 0=0)
  {K : Set E} (compact : IsCompact K) {a : ℝ} (ha : 0<a) (ha1 : a<1)
  (t : S → ℝ) (margin : ∀s,t s≤a)

include compact in
omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem supported_tsupport (f : SchwartzJetSpace.supportedCore K) : tsupport f.val⊆K :=
  closure_minimal (fun x hx => by
    by_contra outside
    exact hx (f.property x outside)) compact.isClosed

@[expose] def smoothCore (f : SchwartzJetSpace.supportedCore K) :
    SmoothSupportedManifoldCore.core (E:=E) K :=
  ⟨f.val,(f.val.smooth ⊤).contMDiff,supported_tsupport compact f⟩

include μ hJ leaves compact zero ha ha1 margin in
theorem smoothCoreBounded : SchwartzAmbientBlocks.SmoothCoreBounded μ hJ leaves K
    (DyadicSymbols.symbol low high) t := by
  have compactClosure : IsCompact (closure K) := by
    rw [compact.isClosed.closure_eq]
    exact compact
  obtain ⟨C,_,estimate⟩ := DyadicHolderBlockBound.exists_bound μ hJ leaves low high zero compact ha ha1.le t margin
  intro f
  let c := smoothCore compact f
  let v := EuclideanSmoothHolderCore.core compactClosure ha ha1 c
  refine ⟨C*‖v‖,?_⟩
  intro j
  have result := estimate f.val v (fun _ => rfl) (supported_tsupport compact f) j
  exact result
end LeanShared.DyadicHolderCoreBounded
