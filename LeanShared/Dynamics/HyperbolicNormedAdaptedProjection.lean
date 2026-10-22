module
public import LeanShared.Geometry.TangentProjectionExtensionNormedModel
public import LeanShared.Dynamics.HyperbolicBasicSet
public import LeanShared.Geometry.BundleEndomorphismCoordinates
public import LeanShared.Topology.CompactNearDiagonalContinuity
public noncomputable section
namespace LeanShared.HyperbolicBasicSet
open Set IsManifold Bundle
open scoped Manifold ContDiff Bundle
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MetricSpace M] [CompactSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ,E)) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ,E)) x)]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace (𝓘(ℝ,E)) x)]
  {T : M ≃ₜ M} {Λ : Set M}

structure HyperbolicData.NormedAdaptedProjection (h : HyperbolicData (E := E) T Λ) where
  collar : Set M
  open_collar : IsOpen collar
  core_subset : Λ ⊆ collar
  projection : ∀ x : M, TangentSpace (𝓘(ℝ,E)) x →L[ℝ] TangentSpace (𝓘(ℝ,E)) x
  continuous_action : ContinuousOn
    (fun v : TotalSpace E (TangentSpace (𝓘(ℝ,E))) =>
      (⟨v.proj,projection v.proj v.2⟩ : TotalSpace E (TangentSpace (𝓘(ℝ,E))))) {v | v.proj∈collar}
  idempotent : ∀ x∈collar, IsIdempotentElem (projection x)
  core_eq : ∀ x∈Λ, projection x=h.projection x

namespace HyperbolicData.NormedAdaptedProjection
variable {h : HyperbolicData (E := E) T Λ}
@[expose] def stable (a : h.NormedAdaptedProjection) (x : M) := (a.projection x).range
@[expose] def unstable (a : h.NormedAdaptedProjection) (x : M) := (a.projection x).ker

omit [FiniteDimensional ℝ E] [CompactSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace (𝓘(ℝ,E)) x)] in
theorem complementary (a : h.NormedAdaptedProjection) (x : M) (hx : x∈a.collar) :
    IsCompl (a.stable x) (a.unstable x) := by
  have idem : IsIdempotentElem (a.projection x).toLinearMap := by
    change (a.projection x).toLinearMap*(a.projection x).toLinearMap=(a.projection x).toLinearMap
    exact congrArg ContinuousLinearMap.toLinearMap (a.idempotent x hx).eq
  exact LinearMap.IsIdempotentElem.isCompl idem

omit [FiniteDimensional ℝ E] [CompactSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace (𝓘(ℝ,E)) x)] in
theorem stable_core (a : h.NormedAdaptedProjection) (x : M) (hx : x∈Λ) : a.stable x=h.stable x := by
  change (a.projection x).range=h.stable x
  rw [a.core_eq x hx]
  exact h.projection_range x hx

omit [FiniteDimensional ℝ E] [CompactSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace (𝓘(ℝ,E)) x)] in
theorem unstable_core (a : h.NormedAdaptedProjection) (x : M) (hx : x∈Λ) : a.unstable x=h.unstable x := by
  change (a.projection x).ker=h.unstable x
  rw [a.core_eq x hx]
  exact h.projection_kernel x hx
omit [CompactSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace (𝓘(ℝ,E)) x)] in
theorem exists_ambient_projection_radius (a : h.NormedAdaptedProjection)
    (e : Trivialization E (Bundle.TotalSpace.proj (E := TangentSpace (𝓘(ℝ,E))))) [e.IsLinear ℝ]
    (K : Set M) (compact : IsCompact K) (core : K ⊆ Λ) (chart : K ⊆ e.baseSet)
    (ε : ℝ) (positive : 0<ε) : ∃ δ : ℝ, 0<δ ∧
      ∀ x∈K, ∀ y : M, dist x y<δ → y∈a.collar∩e.baseSet ∧
      ‖BundleEndomorphismCoordinates.coordinates (TangentSpace (𝓘(ℝ,E))) e a.projection y-
        BundleEndomorphismCoordinates.coordinates (TangentSpace (𝓘(ℝ,E))) e h.projection x‖<ε := by
  let P := BundleEndomorphismCoordinates.coordinates (TangentSpace (𝓘(ℝ,E))) e a.projection
  have continuous : ContinuousOn P (a.collar∩e.baseSet) :=
    BundleEndomorphismCoordinates.continuousOn_coordinates
      (TangentSpace (𝓘(ℝ,E))) e a.projection a.collar a.continuous_action
  obtain ⟨δ,positiveδ,near⟩ := CompactNearDiagonalContinuity.exists_radius K
    (a.collar∩e.baseSet) compact (a.open_collar.inter e.open_baseSet)
    (fun x hx => ⟨a.core_subset (core hx),chart hx⟩) P continuous ε positive
  refine ⟨δ,positiveδ,fun x hx y hxy => ?_⟩
  have result := near x hx y hxy
  refine ⟨result.1,?_⟩
  have same : P x=BundleEndomorphismCoordinates.coordinates (TangentSpace (𝓘(ℝ,E))) e h.projection x := by
    unfold P BundleEndomorphismCoordinates.coordinates
    rw [a.core_eq x (core hx)]
  rw [dist_eq_norm,same,norm_sub_rev] at result
  exact result.2
end HyperbolicData.NormedAdaptedProjection

def HyperbolicData.normedAdaptedProjection (h : HyperbolicData (E := E) T Λ) : h.NormedAdaptedProjection := by
  apply Classical.choice
  have idem (x : M) (hx : x∈Λ) : IsIdempotentElem (h.projection x) := h.projection_idempotent x hx
  obtain ⟨U,openU,inside,Q,continuousQ,agreesQ,idemQ⟩ :=
    TangentProjectionExtensionNormedModel.exists_extension Λ h.compact h.projection h.continuous_splitting idem
  exact ⟨⟨U,openU,inside,Q,continuousQ,idemQ,agreesQ⟩⟩
end LeanShared.HyperbolicBasicSet
