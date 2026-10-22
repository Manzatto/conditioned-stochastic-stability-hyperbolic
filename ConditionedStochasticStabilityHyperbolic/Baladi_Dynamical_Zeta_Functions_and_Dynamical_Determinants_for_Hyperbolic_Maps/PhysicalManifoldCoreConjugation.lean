module

public import LeanShared.Geometry.SupportedCoreConjugation
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.ManifoldPhysicalCore
public import ConditionedStochasticStabilityHyperbolic.Spectral.CoreConjugation

/-! The actual finite maximum of physical chart norms is invariant under
conjugation for real chart cutoffs and even angular symbols. -/

@[expose] public noncomputable section
open MeasureTheory Set IsManifold
open scoped Manifold ContDiff SchwartzMap NNReal ComplexConjugate
namespace ConditionedStochasticStabilityHyperbolic.PhysicalManifoldCoreConjugation
open LeanShared
variable {E U M AtlasIndex A : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
  [MeasurableSpace U] [BorelSpace U]
  [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold (𝓘(ℝ, E)) ∞ M] [T2Space M] [CompactSpace M]
  (e : AtlasIndex → OpenPartialHomeomorph M E) {S : Set M}
  (D : ConstructedManifoldLocalization.Data e S)
  (he : ∀ j, e j ∈ maximalAtlas (𝓘(ℝ, E)) ∞ M)
  (V : Set M)
  (μ : Measure U) [μ.IsAddHaarMeasure] {L : ℝ} (hL : 0 ≤ L)
  (leaves : D.indices → A → GraphLeafNorm.GraphLeaf U E L)
  {Cplus Cminus : D.indices → Set E}
  (radial : D.indices → ConeDyadicSymbols.RadialCutoff)
  (angle : ∀ i, ConeDyadicSymbols.AngularCutoff (Cplus i) (Cminus i))
  (exponent : D.indices → Bool → ℝ)
  (bounded : ∀ i, SchwartzAmbientBlocks.SmoothCoreBounded μ hL (leaves i)
    (ConstructedManifoldLocalization.support e D i)
    (ConeDyadicSymbols.symbols (radial i) (angle i)) (exponent i))


omit [IsManifold (𝓘(ℝ, E)) ∞ M] [T2Space M] [CompactSpace M] in
theorem norm_conjugate
    (hcutoff : ∀ i x, conj (D.cutoff i x) = D.cutoff i x)
    (hangle : ∀ i ξ, (angle i).toFun (-ξ) = (angle i).toFun ξ)
    (f : SmoothSupportedManifoldCore.core (E := E) V) :
    ‖DyadicCompletion.coreLift
      (ManifoldPhysicalCore.coreMap e D he (SmoothSupportedManifoldCore.functions V)
        (SmoothSupportedManifoldCore.smooth V) μ hL leaves radial angle exponent bounded)
      (SmoothSupportedManifoldCore.conjugate V f)‖ =
    ‖DyadicCompletion.coreLift
      (ManifoldPhysicalCore.coreMap e D he (SmoothSupportedManifoldCore.functions V)
        (SmoothSupportedManifoldCore.smooth V) μ hL leaves radial angle exponent bounded) f‖ := by
  rw [ManifoldPhysicalCore.norm_core, ManifoldPhysicalCore.norm_core]
  apply congrArg (fun t : ℝ≥0 => (t : ℝ))
  apply Finset.sup_congr rfl
  intro i _
  apply NNReal.eq
  change ‖ManifoldPhysicalCore.localBlocks e D μ hL leaves radial angle exponent bounded i
      (ConstructedManifoldLocalization.localize e D he
        (SmoothSupportedManifoldCore.functions V) (SmoothSupportedManifoldCore.smooth V) i
        (SmoothSupportedManifoldCore.conjugate V f))‖ = _
  rw [ConstructedManifoldLocalization.localize_conjugate e D he V hcutoff]
  exact RealEvenFourierBlocks.coreMap_conjugate_norm μ hL (leaves i) _ _ _ (bounded i)
    (RealEvenFourierBlocks.symbols_real (radial i) (angle i))
    (RealEvenFourierBlocks.symbols_even (radial i) (angle i) (hangle i)) _

def coreData
    (hcutoff : ∀ i x, conj (D.cutoff i x) = D.cutoff i x)
    (hangle : ∀ i ξ, (angle i).toFun (-ξ) = (angle i).toFun ξ) :
    CoreConjugation.CoreData (DyadicCompletion.coreLift
      (ManifoldPhysicalCore.coreMap e D he (SmoothSupportedManifoldCore.functions V)
        (SmoothSupportedManifoldCore.smooth V) μ hL leaves radial angle exponent bounded)) where
  conjugate := SmoothSupportedManifoldCore.conjugate V
  involutive := SmoothSupportedManifoldCore.conjugate_involutive V
  smul := SmoothSupportedManifoldCore.conjugate_smul V
  norm := norm_conjugate e D he V μ hL leaves radial angle exponent bounded hcutoff hangle

end ConditionedStochasticStabilityHyperbolic.PhysicalManifoldCoreConjugation
