module
public import LeanShared.Analysis.SchwartzJetSpace
public import LeanShared.Geometry.EuclideanSmoothHolderCore

/-! Literal compact-supported Schwartz generators for the actual little
Hölder space on a closed chart support. No boundary smoothing assertion is
needed: both generating sets consist of precisely the same smooth functions. -/
public noncomputable section
open Set
open scoped SchwartzMap Manifold ContDiff BoundedContinuousFunction
namespace LeanShared.CompactSchwartzHolderNormedCore
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {K : Set E} (compact : IsCompact K)
  {b : ℝ} (hb : 0<b) (hb1 : b<1)

include compact in
omit [FiniteDimensional ℝ E] in
theorem supported_tsupport (f : SchwartzJetSpace.supportedCore K) : tsupport f.val ⊆ K :=
  closure_minimal (fun x hx => by
    by_contra outside
    exact hx (f.property x outside)) compact.isClosed

@[expose] def toSmooth : SchwartzJetSpace.supportedCore K →ₗ[ℂ]
    SmoothSupportedManifoldCore.core (E:=E) K where
  toFun f := ⟨f.val,(f.val.smooth ⊤).contMDiff,
    supported_tsupport compact f⟩
  map_add' f g := by apply Subtype.ext; ext x; rfl
  map_smul' z f := by apply Subtype.ext; ext x; rfl

omit [FiniteDimensional ℝ E] in
theorem toSmooth_surjective : Function.Surjective (toSmooth compact) := by
  intro c
  have hs : HasCompactSupport c.val := compact.of_isClosed_subset (isClosed_tsupport _) c.property.2
  refine ⟨⟨hs.toSchwartzMap c.property.1.contDiff,?_⟩,?_⟩
  · intro x hx
    exact image_eq_zero_of_notMem_tsupport (fun hy=>hx (c.property.2 hy))
  · apply Subtype.ext
    rfl

@[expose] def core : SchwartzJetSpace.supportedCore K →ₗ[ℂ]
    EuclideanSmoothHolderCore.space compact.closure hb hb1 :=
  (EuclideanSmoothHolderCore.smooth compact.closure hb hb1).comp (toSmooth compact)

theorem core_dense : DenseRange (core compact hb hb1) :=
  by
    intro z
    apply closure_mono (s := Set.range (EuclideanSmoothHolderCore.smooth compact.closure hb hb1)) ?_
      ((EuclideanSmoothHolderCore.smooth_dense compact.closure hb hb1) z)
    rintro _ ⟨c,rfl⟩
    obtain ⟨f,rfl⟩ := toSmooth_surjective compact c
    exact ⟨f,rfl⟩

theorem physical_core (f : SchwartzJetSpace.supportedCore K) (x:E) :
    EuclideanSmoothHolderCore.physical compact.closure hb hb1 (core compact hb hb1 f) x=f.val x := rfl
end LeanShared.CompactSchwartzHolderNormedCore
