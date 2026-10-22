module
public import LeanShared.Analysis.EuclideanHolderAnisotropicEmbedding
public import LeanShared.Analysis.ConeDyadicHolderCoreBounded

/-! A constructed C^a-to-anisotropic operator for the exact manuscript cone
symbols. All symbol, frequency, leaf and norm estimates are derived. -/
public noncomputable section
open Set MeasureTheory
open scoped SchwartzMap Manifold ContDiff
namespace LeanShared.ConeHolderAnisotropicEmbedding
open ConeDyadicSymbols
variable {E U A : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
  [MeasurableSpace U] [BorelSpace U]
  (μ : Measure U) [μ.IsAddHaarMeasure] {J : ℝ} (hJ : 0≤J)
  (leaves : A → GraphLeafNorm.GraphLeaf U E J)
  {Cplus Cminus : Set E} (χ : RadialCutoff) (Φ : AngularCutoff Cplus Cminus)
  {V : Set E} (compact : IsCompact (closure V)) {a : ℝ} (ha : 0<a) (ha1 : a<1)
  (t : Bool → ℝ) (margin : ∀s,t s≤a)

@[expose] def lowBase : Bool → 𝓢(E,ℂ) := fun _ =>
  FourierSchwartzKernel.symbol (low χ) (low_hasCompactSupport χ) (low_smooth χ)
@[expose] def highBase : Bool → 𝓢(E,ℂ) := fun s =>
  FourierSchwartzKernel.symbol (high χ Φ.toFun s)
    (high_hasCompactSupport χ Φ.toFun s) (high_smooth χ Φ s)

omit [MeasurableSpace E] [BorelSpace E] in
theorem high_zero (s : Bool) : highBase χ Φ s 0=0 := by
  change (high χ Φ.toFun s) 0=0
  rw [high,highReal,annular_zero_near_origin χ (by simp),mul_zero,Complex.ofReal_zero]

include compact ha ha1 margin in
theorem bounded : SchwartzAmbientBlocks.SmoothCoreBounded μ hJ leaves (closure V)
    (symbols χ Φ) t :=
  ConeDyadicHolderCoreBounded.smoothCoreBounded μ hJ leaves χ Φ compact ha ha1 t margin

@[expose] def realization : EuclideanSmoothHolderCore.space compact ha ha1 →L[ℂ]
    DyadicCompletion.BlockSpace (F:=GraphLeafNorm.AmbientFamilySpace μ leaves) (S:=Bool) :=
  EuclideanHolderAnisotropicEmbedding.realization μ hJ leaves compact ha ha1
    (lowBase χ) (highBase χ Φ) t (bounded μ hJ leaves χ Φ compact ha ha1 t margin)

theorem realization_smooth (c : SmoothSupportedManifoldCore.core (E:=E) V) :
    realization μ hJ leaves χ Φ compact ha ha1 t margin
      (EuclideanSmoothHolderCore.smooth compact ha ha1 c) =
      SchwartzAmbientBlocks.coreMap μ hJ leaves (closure V) (symbols χ Φ) t
        (bounded μ hJ leaves χ Φ compact ha ha1 t margin)
        (EuclideanHolderAnisotropicEmbedding.schwartzCore compact c) :=
  EuclideanHolderAnisotropicEmbedding.realization_smooth μ hJ leaves compact ha ha1
    (lowBase χ) (highBase χ Φ) (high_zero χ Φ) t margin
    (bounded μ hJ leaves χ Φ compact ha ha1 t margin) c
end LeanShared.ConeHolderAnisotropicEmbedding
