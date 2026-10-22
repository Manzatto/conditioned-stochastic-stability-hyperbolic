module
public import LeanShared.Geometry.NormalizedRegularChartAffineExtension

/-! The actual open coordinate-validity domain is constructed internally.
Only validity on the common closed ball is required from the application. -/
@[expose] public noncomputable section
open Set Filter Function IsManifold Metric
open scoped NNReal Manifold ContDiff Topology
namespace LeanShared.CenteredManifoldCoordinates
open FractionalManifoldRegularity
universe u v
variable {E F : Type u} {P Q : Type v} {M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup P] [NormedSpace ℝ P] [CompleteSpace P] [FiniteDimensional ℝ P]
  [NormedAddCommGroup Q] [NormedSpace ℝ Q]
  [TopologicalSpace M] [ChartedSpace E M]
  [TopologicalSpace N] [ChartedSpace F N]

theorem exists_uniform_scaled_chart_extension_of_ball {r η K : ℝ}
    (hr : 1 ≤ r) (positiveη : 0 < η) (nonnegativeK : 0 ≤ K) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ ρ : ℝ → P → ℝ, ∀ radius : ℝ, 0 < radius →
      ContDiff ℝ ∞ (ρ radius) ∧ HasCompactSupport (ρ radius) ∧
      tsupport (ρ radius) ⊆ closedBall 0 radius ∧
      (∀ z ∈ closedBall 0 (radius/2), ρ radius z = 1) ∧
      ∀ A : P ≃L[ℝ] Q, ‖A.symm.toContinuousLinearMap‖ ≤ K → ∀ β : Q,
      ∀ (L : P ≃L[ℝ] E) (R : Q ≃L[ℝ] F) (a : E) (b : F),
      ∀ (c : OpenPartialHomeomorph M E) (d : OpenPartialHomeomorph N F),
        c ∈ maximalAtlas (𝓘(ℝ, E)) ∞ M → d ∈ maximalAtlas (𝓘(ℝ, F)) ∞ N →
          ∀ f : M → N, Regular (E := E) (F := F) r f →
            (∀ z ∈ closedBall 0 radius, a+L z ∈ c.target ∧ f (c.symm (a+L z)) ∈ d.source) →
            let h := centered L R a b (d ∘ f ∘ c.symm)
            ‖h 0-β‖ ≤ δ*radius →
            (∀ z ∈ closedBall 0 radius, ‖fderiv ℝ h z-A.toContinuousLinearMap‖ ≤ δ) →
            ∃ H : P ≃ₜ Q, (∀ z, H z = A z+β+ρ radius z • (h z-(A z+β))) ∧
              Regular (E := P) (F := Q) r H ∧ Regular (E := Q) (F := P) r H.symm ∧
              (∀ z, ‖fderiv ℝ H z-A.toContinuousLinearMap‖ < η) ∧
              (∀ z ∈ closedBall 0 (radius/2), H z = h z) ∧
              ∀ z, z ∉ closedBall 0 radius → H z = A z+β := by
  obtain ⟨δ, positiveδ, ρ, extensions⟩ :=
    exists_uniform_scaled_chart_extension (E := E) (F := F) (P := P) (Q := Q)
      (M := M) (N := N) hr positiveη nonnegativeK
  refine ⟨δ, positiveδ, ρ, ?_⟩
  intro radius positiveRadius
  obtain ⟨smoothρ, compactρ, supportρ, oneρ, extend⟩ := extensions radius positiveRadius
  refine ⟨smoothρ, compactρ, supportρ, oneρ, ?_⟩
  intro A inverseBound β L R a b c d hc hd f regular domain
  dsimp only
  intro center derivative
  let U : Set P := {z | a+L z ∈ c.target ∧ f (c.symm (a+L z)) ∈ d.source}
  have rawOpen : IsOpen (c.target ∩ c.symm ⁻¹' (f ⁻¹' d.source)) :=
    c.isOpen_inter_preimage_symm (d.open_source.preimage regular.differentiable.continuous)
  have openU : IsOpen U := rawOpen.preimage (continuous_const.add L.continuous)
  exact extend A inverseBound β L R a b c d hc hd U openU domain f regular
    (fun _ hz => hz) center derivative

end LeanShared.CenteredManifoldCoordinates
