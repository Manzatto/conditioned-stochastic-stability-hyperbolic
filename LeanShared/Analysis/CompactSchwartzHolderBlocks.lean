module
public import LeanShared.Geometry.CompactSchwartzHolderCore
public import LeanShared.Analysis.ConeHolderAnisotropicEmbedding
public import LeanShared.Analysis.ConeDyadicHolderCoreBounded

/-! The local physical block bound is derived on the literal compact chart
support before constructing a manifold transfer Data record. -/
public noncomputable section
open Set MeasureTheory
open scoped SchwartzMap
namespace LeanShared.CompactSchwartzHolderBlocks
open ConeDyadicSymbols
variable {E U A : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
  [MeasurableSpace U] [BorelSpace U]
  (μ:Measure U) [μ.IsAddHaarMeasure] {J:ℝ} (hJ:0≤J)
  (leaves:A→GraphLeafNorm.GraphLeaf U E J)
  {Cplus Cminus:Set E} (χ:RadialCutoff) (Φ:AngularCutoff Cplus Cminus)
  {K:Set E} (compact:IsCompact K) {b:ℝ} (hb:0<b) (hb1:b<1)
  (t:Bool→ℝ) (margin:∀s,t s≤b)

include compact hb hb1 margin in
theorem bounded : SchwartzAmbientBlocks.SmoothCoreBounded μ hJ leaves K (symbols χ Φ) t :=
  ConeDyadicHolderCoreBounded.smoothCoreBounded μ hJ leaves χ Φ compact hb hb1 t margin

include hb hb1 margin in
theorem bound : ∃C:ℝ,0≤C ∧ ∀bd:SchwartzAmbientBlocks.SmoothCoreBounded μ hJ leaves K (symbols χ Φ) t,
    ∀f:SchwartzJetSpace.supportedCore K,
      ‖SchwartzAmbientBlocks.coreMap μ hJ leaves K (symbols χ Φ) t bd f‖ ≤
        C*‖CompactSchwartzHolderCore.core compact hb hb1 f‖ := by
  obtain ⟨C,hC,estimate⟩ := DyadicHolderNormEstimate.exists_bound μ hJ leaves
    (ConeHolderAnisotropicEmbedding.lowBase χ) (ConeHolderAnisotropicEmbedding.highBase χ Φ)
    (ConeHolderAnisotropicEmbedding.high_zero χ Φ) compact hb hb1.le t margin
  refine ⟨C,hC,?_⟩
  intro bd f
  exact estimate bd f
    (EuclideanSmoothHolderCore.core compact.closure hb hb1 (CompactSchwartzHolderCore.toSmooth compact f))
    (fun _=>rfl)
end LeanShared.CompactSchwartzHolderBlocks
