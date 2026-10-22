module
public import LeanShared.Analysis.DyadicHolderCoreBounded

/-! Quantitative control of the actual completed-core norm by the literal
lower Hölder graph norm. The bound holds for every boundedness witness. -/
public noncomputable section
open Set MeasureTheory
open scoped SchwartzMap
namespace LeanShared.DyadicHolderNormEstimate
variable {E U A S : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
  [MeasurableSpace U] [BorelSpace U] [Fintype S]
  (μ : Measure U) [μ.IsAddHaarMeasure] {J : ℝ} (hJ : 0≤J)
  (leaves : A → GraphLeafNorm.GraphLeaf U E J)

theorem exists_bound (low high : S → 𝓢(E,ℂ)) (zero : ∀s,high s 0=0)
    {K : Set E} (compact : IsCompact K) {a : ℝ} (ha : 0<a) (ha1 : a≤1)
    (t : S → ℝ) (margin : ∀s,t s≤a) :
    ∃ C : ℝ, 0≤C ∧ ∀ bounded : SchwartzAmbientBlocks.SmoothCoreBounded μ hJ leaves K
      (DyadicSymbols.symbol low high) t,
      ∀ (f : SchwartzJetSpace.supportedCore K) (v : BoundedHolderSpace.graph E a),
      (∀x,BoundedHolderSpace.physical E a v x=f.val x) →
      ‖SchwartzAmbientBlocks.coreMap μ hJ leaves K (DyadicSymbols.symbol low high) t bounded f‖ ≤ C*‖v‖ := by
  obtain ⟨C,hC,estimate⟩ := DyadicHolderBlockBound.exists_bound μ hJ leaves low high zero compact ha ha1 t margin
  refine ⟨C,hC,?_⟩
  intro bounded f v physical
  apply lp.norm_le_of_forall_le (mul_nonneg hC (norm_nonneg v))
  intro j
  have support := DyadicHolderCoreBounded.supported_tsupport compact f
  exact estimate f.val v physical support j
end LeanShared.DyadicHolderNormEstimate
