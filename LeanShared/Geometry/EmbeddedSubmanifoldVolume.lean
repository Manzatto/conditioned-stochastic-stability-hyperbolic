module
public import LeanShared.Geometry.ImmersionVolumeAtlas
public import LeanShared.MeasureTheory.ImmersionAtlasExtraChart
public import Mathlib.Geometry.Manifold.MFDeriv.Defs

/-! Independent induced volume on an actual embedded C¹ submanifold.
The construction chooses ordinary manifold charts and glues the intrinsic
ambient derivative densities; it does not choose a graph parametrization. -/
public noncomputable section
open Set MeasureTheory IsManifold
open scoped Manifold ContDiff
namespace LeanShared.EmbeddedSubmanifoldVolume
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

@[expose] def Embedded (U : Submodule ℝ E) (Γ : Set E) : Prop :=
  ∃ atlas : ChartedSpace U Γ, letI := atlas
    IsManifold (𝓘(ℝ, U)) 1 Γ ∧
      ContMDiff (𝓘(ℝ, U)) (𝓘(ℝ, E)) 1 (Subtype.val : Γ → E) ∧
      ∀ x : Γ, Function.Injective
        (mfderiv (𝓘(ℝ, U)) (𝓘(ℝ, E)) (Subtype.val : Γ → E) x)

structure Data (U : Submodule ℝ E) (Γ : Set E) where
  charted : ChartedSpace U Γ
  manifold : letI := charted; IsManifold (𝓘(ℝ, U)) 1 Γ
  smooth : letI := charted
    ContMDiff (𝓘(ℝ, U)) (𝓘(ℝ, E)) 1 (Subtype.val : Γ → E)
  immersion : letI := charted
    ∀ x : Γ, Function.Injective
      (mfderiv (𝓘(ℝ, U)) (𝓘(ℝ, E)) (Subtype.val : Γ → E) x)
  model : ImmersionAtlasVolume.Atlas (U := U) (Subtype.val : Γ → E)
  compatible : letI := charted
    ∀ n, model.chart n ∈ maximalAtlas (𝓘(ℝ, U)) 1 Γ

@[expose] def data {U : Submodule ℝ E} {Γ : Set E}
    (embedded : Embedded U Γ) [Nonempty Γ] : Data U Γ := by
  let atlas := Classical.choose embedded
  let : ChartedSpace U Γ := atlas
  have facts := Classical.choose_spec embedded
  let : IsManifold (𝓘(ℝ, U)) 1 Γ := facts.1
  have possible := ImmersionVolumeAtlas.exists_atlas (Subtype.val : Γ → E) facts.2.1
  exact ⟨atlas, facts.1, facts.2.1, facts.2.2, Classical.choose possible,
    Classical.choose_spec possible⟩

@[expose] def intrinsic {U : Submodule ℝ E} {Γ : Set E}
    (embedded : Embedded U Γ) (μ : Measure U) : Measure Γ := by
  classical
  exact if nonempty : Nonempty Γ then
    letI := nonempty
    ImmersionAtlasVolume.volume (data embedded).model μ else 0

@[expose] def volume (U : Submodule ℝ E) (μ : Measure U) (Γ : Set E) : Measure E := by
  classical
  exact if embedded : Embedded U Γ then (intrinsic embedded μ).map Subtype.val else 0

omit [BorelSpace E] in
theorem volume_eq_map_data {U : Submodule ℝ E} {Γ : Set E}
    (embedded : Embedded U Γ) [Nonempty Γ] (μ : Measure U) :
    volume U μ Γ = (ImmersionAtlasVolume.volume (data embedded).model μ).map Subtype.val := by
  simp only [volume, dite_eq_left embedded, intrinsic, dite_eq_left ‹Nonempty Γ›]
end LeanShared.EmbeddedSubmanifoldVolume
