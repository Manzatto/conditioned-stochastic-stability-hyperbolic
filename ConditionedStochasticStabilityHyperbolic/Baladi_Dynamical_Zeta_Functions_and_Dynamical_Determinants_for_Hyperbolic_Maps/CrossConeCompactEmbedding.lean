module

public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.LocalCompactEmbedding
public import LeanShared.Analysis.NormCompletionComparison

/-!
# Constructed cross-cone local compact embeddings

A cited smooth-core comparison constructs the completed comparison map.
Common continuous distribution realizations and separation in the source
prove its injectivity by density, allowing a nonnormable Hausdorff distribution
target. Composition with the actual physical same-cone compact weakening
then gives the cross-cone compact injection, with exact physical core values.

The source core map is explicit and may be instantiated by the actual
physical blocks for another cone and leaf family. No completed comparison,
compactness certificate, or core smoothing identity is supplied.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped SchwartzMap BoundedContinuousFunction

namespace ConditionedStochasticStabilityHyperbolic.CrossConeCompactEmbedding

open LeanShared

namespace Canonical

variable {Core B F S : Type*} [AddCommGroup Core] [Module ℂ Core]
  [NormedAddCommGroup B] [NormedSpace ℂ B]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
  (qPrime : Core →ₗ[ℂ] B)
  (q : Core →ₗ[ℂ] DyadicCompletion.BlockSpace (F := F) (S := S))
  {η : ℝ} (hη : 0 < η) (δ : S → ℝ) (hδ : ∀ s, 0 ≤ δ s)

/-- Canonical completed comparison followed by actual coordinate weakening. -/
def embedding : DyadicCompletion.closedCore qPrime →L[ℂ]
    DyadicCompletion.closedCore (DyadicCompletion.finalCore q η hη δ hδ) :=
  (DyadicCompletion.exactInclusion q η hη δ hδ).comp
    (NormCompletionComparison.comparison qPrime q)

theorem embedding_core (C : ℝ) (hbound : ∀ c, ‖q c‖ ≤ C * ‖qPrime c‖) (c : Core) :
    embedding qPrime q hη δ hδ (DyadicCompletion.coreLift qPrime c) =
      DyadicCompletion.coreLift (DyadicCompletion.finalCore q η hη δ hδ) c := by
  change DyadicCompletion.exactInclusion q η hη δ hδ
    (NormCompletionComparison.comparison qPrime q (DyadicCompletion.coreLift qPrime c)) = _
  rw [NormCompletionComparison.comparison_core qPrime q C hbound]
  rfl

variable {Z : Type*} [AddCommGroup Z] [Module ℂ Z] [TopologicalSpace Z] [T2Space Z]
  (pPrime : DyadicCompletion.closedCore qPrime →L[ℂ] Z)
  (p : DyadicCompletion.closedCore q →L[ℂ] Z)
  (hcommon : ∀ c, p (DyadicCompletion.coreLift q c) = pPrime (DyadicCompletion.coreLift qPrime c))

include hcommon in
/-- Density identifies completed realizations without requiring a norm on
the common distribution space. -/
theorem comparison_realization (C : ℝ) (hbound : ∀ c, ‖q c‖ ≤ C * ‖qPrime c‖)
    (z : DyadicCompletion.closedCore qPrime) :
    p (NormCompletionComparison.comparison qPrime q z) = pPrime z := by
  refine (DyadicCompletion.coreLift_dense qPrime).induction_on
    (p := fun x => p (NormCompletionComparison.comparison qPrime q x) = pPrime x) z
    (isClosed_eq (p.continuous.comp (NormCompletionComparison.comparison qPrime q).continuous)
      pPrime.continuous) ?_
  intro c
  rw [NormCompletionComparison.comparison_core qPrime q C hbound, hcommon]

include hcommon in
theorem embedding_injective (C : ℝ) (hbound : ∀ c, ‖q c‖ ≤ C * ‖qPrime c‖)
    (hpPrime : Function.Injective pPrime) : Function.Injective (embedding qPrime q hη δ hδ) := by
  intro x y hxy
  have he : NormCompletionComparison.comparison qPrime q x =
      NormCompletionComparison.comparison qPrime q y :=
    DyadicCompletion.exactInclusion_injective q η hη δ hδ hxy
  apply hpPrime
  rw [← comparison_realization qPrime q pPrime p hcommon C hbound x,
    ← comparison_realization qPrime q pPrime p hcommon C hbound y, he]

end Canonical

section PhysicalTarget

variable {E U A I BPrime : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
  [MeasurableSpace U] [BorelSpace U]
  (μ : Measure U) [μ.IsAddHaarMeasure] {J : ℝ} (hJ : 0 ≤ J)
  (leaves : A → GraphLeafNorm.GraphLeaf U E J)
  (D : Set E) {Cplus Cminus : Set E} (radial : ConeDyadicSymbols.RadialCutoff)
  (angle : ConeDyadicSymbols.AngularCutoff Cplus Cminus) (t : Bool → ℝ)
  (hbounded : SchwartzAmbientBlocks.SmoothCoreBounded μ hJ leaves D
    (ConeDyadicSymbols.symbols radial angle) t)
  [NormedAddCommGroup BPrime] [NormedSpace ℂ BPrime]
  (qPrime : SchwartzJetSpace.supportedCore D →ₗ[ℂ] BPrime)
  (Ccompare : ℝ)
  (hcompare : ∀ f, ‖LocalCompactEmbedding.coreMap μ hJ leaves D radial angle t hbounded f‖ ≤
    Ccompare * ‖qPrime f‖)
  {η : ℝ} (hη : 0 < η) (δ : Bool → ℝ) (hδ : ∀ s, 0 ≤ δ s)

/-- Cross-cone embedding into the actual weakened physical target completion. -/
abbrev embedding := Canonical.embedding qPrime
  (LocalCompactEmbedding.coreMap μ hJ leaves D radial angle t hbounded) hη δ hδ

include hcompare in
/-- Exact core agreement uses the literal weak physical exponents, not a
postulated completed comparison or a supplied smoothing formula. -/
theorem embedding_core_block (f : SchwartzJetSpace.supportedCore D) (j : ℕ × Bool) :
    (embedding μ hJ leaves D radial angle t hbounded qPrime hη δ hδ
      (DyadicCompletion.coreLift qPrime f) :
        DyadicCompletion.BlockSpace (F := GraphLeafNorm.AmbientFamilySpace μ leaves) (S := Bool)) j =
      SchwartzAmbientBlocks.weightedBlock μ hJ leaves D (ConeDyadicSymbols.symbols radial angle)
        (fun s => t s - η - δ s) j f := by
  rw [Canonical.embedding_core qPrime
    (LocalCompactEmbedding.coreMap μ hJ leaves D radial angle t hbounded) hη δ hδ Ccompare hcompare]
  exact LocalCompactEmbedding.canonicalWeakCore_apply μ hJ leaves D radial angle t hbounded hη δ hδ f j

variable [Fintype I] (w : I → List E)
  {K : Set E} (hK : IsCompact K) (cutoff : 𝓢(E, ℂ))
  (hcutoff : ∀ y ∉ K, cutoff y = 0) (hone : ∀ y ∈ D, cutoff y = 1)
  (pairing : LocalCompactEmbedding.StrongSpace μ hJ leaves D radial angle t hbounded →ₗ[ℂ]
    (𝓢(E, ℂ) →ₗ[ℂ] ℂ)) (Corder : ℝ) (hCorder : 0 ≤ Corder)
  (horder : ∀ b (f : 𝓢(E, ℂ)), (∀ x ∉ K, f x = 0) →
    ‖pairing b f‖ ≤ Corder * ‖b‖ * ‖SchwartzJetSpace.jetMap K w f‖)
  (hpairing : ∀ (f : SchwartzJetSpace.supportedCore D) (test : 𝓢(E, ℂ)),
    pairing (DyadicCompletion.coreLift (LocalCompactEmbedding.coreMap μ hJ leaves D radial angle t hbounded) f)
      test = ConeFourierBlocks.integralPairing f.val test)

include hK hcutoff hone hCorder horder hpairing in
/-- Compactness is derived by composing the actual physical local producer
with the constructed continuous comparison. -/
theorem embedding_isCompact :
    IsCompactOperator (embedding μ hJ leaves D radial angle t hbounded qPrime hη δ hδ) :=
  (LocalCompactEmbedding.compact_injective_exactInclusion μ hJ leaves D radial angle t hbounded
    w hK cutoff hcutoff hone pairing Corder hCorder horder hpairing hη δ hδ).1.comp_clm
      (NormCompletionComparison.comparison qPrime
        (LocalCompactEmbedding.coreMap μ hJ leaves D radial angle t hbounded))

variable {Z : Type*} [AddCommGroup Z] [Module ℂ Z] [TopologicalSpace Z] [T2Space Z]
  (pPrime : DyadicCompletion.closedCore qPrime →L[ℂ] Z)
  (p : LocalCompactEmbedding.StrongSpace μ hJ leaves D radial angle t hbounded →L[ℂ] Z)
  (hcommon : ∀ f, p (DyadicCompletion.coreLift
      (LocalCompactEmbedding.coreMap μ hJ leaves D radial angle t hbounded) f) =
    pPrime (DyadicCompletion.coreLift qPrime f))
  (hpPrime : Function.Injective pPrime)

include hcompare hcommon hpPrime in
theorem embedding_injective :
    Function.Injective (embedding μ hJ leaves D radial angle t hbounded qPrime hη δ hδ) :=
  Canonical.embedding_injective qPrime
    (LocalCompactEmbedding.coreMap μ hJ leaves D radial angle t hbounded) hη δ hδ
    pPrime p hcommon Ccompare hcompare hpPrime

include hK hcutoff hone hCorder horder hpairing hcompare hcommon hpPrime in
/-- The actual cross-cone compact injection, with the cited comparison and
distribution separation inputs and no assumed completed map or compactness. -/
theorem compact_injective_embedding :
    IsCompactOperator (embedding μ hJ leaves D radial angle t hbounded qPrime hη δ hδ) ∧
      Function.Injective (embedding μ hJ leaves D radial angle t hbounded qPrime hη δ hδ) :=
  ⟨embedding_isCompact μ hJ leaves D radial angle t hbounded qPrime hη δ hδ w hK cutoff hcutoff hone
      pairing Corder hCorder horder hpairing,
    embedding_injective μ hJ leaves D radial angle t hbounded qPrime Ccompare hcompare hη δ hδ
      pPrime p hcommon hpPrime⟩

end PhysicalTarget

end ConditionedStochasticStabilityHyperbolic.CrossConeCompactEmbedding
