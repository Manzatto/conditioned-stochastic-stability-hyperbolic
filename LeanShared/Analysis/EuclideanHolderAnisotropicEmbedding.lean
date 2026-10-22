module
public import LeanShared.Analysis.DyadicHolderNormEstimate
public import LeanShared.Geometry.EuclideanSmoothHolderCore

/-! A constructed continuous map from the actual Euclidean little C^a
space to the literal physical anisotropic block space. The norm estimate
and extension are proved; no Cv-to-anisotropic source is supplied. -/
public noncomputable section
open Set MeasureTheory
open scoped SchwartzMap Manifold ContDiff
namespace LeanShared.EuclideanHolderAnisotropicEmbedding
variable {E U A S : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
  [MeasurableSpace U] [BorelSpace U] [Fintype S]
  (μ : Measure U) [μ.IsAddHaarMeasure] {J : ℝ} (hJ : 0≤J)
  (leaves : A → GraphLeafNorm.GraphLeaf U E J)
  {V : Set E} (compact : IsCompact (closure V))
  {a : ℝ} (ha : 0<a) (ha1 : a<1)

local instance lowerNormed : NormedAddCommGroup (EuclideanSmoothHolderCore.space compact ha ha1) := inferInstance
local instance lowerSemi : SeminormedAddCommGroup (EuclideanSmoothHolderCore.space compact ha ha1) :=
  (lowerNormed compact ha ha1).toSeminormedAddCommGroup
local instance lowerScalar : NormedSpace ℂ (EuclideanSmoothHolderCore.space compact ha ha1) := inferInstance
local instance blocksNormed : NormedAddCommGroup
    (DyadicCompletion.BlockSpace (F:=GraphLeafNorm.AmbientFamilySpace μ leaves) (S:=S)) := inferInstance
local instance blocksSemi : SeminormedAddCommGroup
    (DyadicCompletion.BlockSpace (F:=GraphLeafNorm.AmbientFamilySpace μ leaves) (S:=S)) :=
  (blocksNormed μ leaves).toSeminormedAddCommGroup
local instance blocksScalar : NormedSpace ℂ
    (DyadicCompletion.BlockSpace (F:=GraphLeafNorm.AmbientFamilySpace μ leaves) (S:=S)) := inferInstance

@[expose] def schwartzCore : SmoothSupportedManifoldCore.core (E:=E) V →ₗ[ℂ]
    SchwartzJetSpace.supportedCore (closure V) where
  toFun c := ⟨(EuclideanSmoothHolderCore.compact_support compact c).toSchwartzMap
    c.property.1.contDiff, fun x hx => image_eq_zero_of_notMem_tsupport
      (fun hs => hx (subset_closure (c.property.2 hs)))⟩
  map_add' f g := by apply Subtype.ext; ext x; rfl
  map_smul' z f := by apply Subtype.ext; ext x; rfl

variable (low high : S → 𝓢(E,ℂ)) (zero : ∀s,high s 0=0)
  (t : S → ℝ) (margin : ∀s,t s≤a)
  (bounded : SchwartzAmbientBlocks.SmoothCoreBounded μ hJ leaves (closure V)
    (DyadicSymbols.symbol low high) t)

@[expose] def blocks : SmoothSupportedManifoldCore.core (E:=E) V →ₗ[ℂ]
    DyadicCompletion.BlockSpace (F:=GraphLeafNorm.AmbientFamilySpace μ leaves) (S:=S) :=
  (SchwartzAmbientBlocks.coreMap μ hJ leaves (closure V) (DyadicSymbols.symbol low high) t bounded).comp
    (schwartzCore compact)

include zero ha ha1 margin in
theorem bound : ∃ C : ℝ, ∀ c : SmoothSupportedManifoldCore.core (E:=E) V,
    ‖blocks μ hJ leaves compact low high t bounded c‖ ≤
      C*‖EuclideanSmoothHolderCore.smooth compact ha ha1 c‖ := by
  obtain ⟨C,_,estimate⟩ := DyadicHolderNormEstimate.exists_bound μ hJ leaves low high zero compact ha ha1.le t margin
  refine ⟨C,?_⟩
  intro c
  exact estimate bounded (schwartzCore compact c) (EuclideanSmoothHolderCore.core compact ha ha1 c) (fun _ => rfl)

@[expose] def realization : EuclideanSmoothHolderCore.space compact ha ha1 →L[ℂ]
    DyadicCompletion.BlockSpace (F:=GraphLeafNorm.AmbientFamilySpace μ leaves) (S:=S) :=
  (blocks μ hJ leaves compact low high t bounded).extendOfNorm
    (EuclideanSmoothHolderCore.smooth compact ha ha1)

include zero margin in
theorem realization_smooth (c : SmoothSupportedManifoldCore.core (E:=E) V) :
    realization μ hJ leaves compact ha ha1 low high t bounded
      (EuclideanSmoothHolderCore.smooth compact ha ha1 c) =
      blocks μ hJ leaves compact low high t bounded c :=
  LinearMap.extendOfNorm_eq (EuclideanSmoothHolderCore.smooth_dense compact ha ha1)
    (bound μ hJ leaves compact ha ha1 low high zero t margin bounded) c
end LeanShared.EuclideanHolderAnisotropicEmbedding
