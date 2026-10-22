module
public import LeanShared.Geometry.ScaledLocalAffineExtension
public import LeanShared.Geometry.HigherFractionalMapCharts
public import LeanShared.Geometry.CenteredManifoldCoordinates
public import LeanShared.Geometry.LocalFractionalJetLinear
public import LeanShared.Geometry.LocalFractionalJetPostlinear

/-! Global regular affine extensions in the literal normalized coordinates
of genuine manifold charts. The normalized model may differ from the
original manifold model; no new manifold atlas is assumed. -/
@[expose] public noncomputable section
open Set Filter Function IsManifold Metric
open scoped NNReal Manifold ContDiff Topology
namespace LeanShared.CenteredManifoldCoordinates
open FractionalManifoldRegularity
universe u v
variable {E F : Type u} {P Q : Type v} {M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup Q] [NormedSpace ℝ Q]
  [TopologicalSpace M] [ChartedSpace E M]
  [TopologicalSpace N] [ChartedSpace F N]

theorem contDiffAt_centered_charts {r : ℝ} {f : M → N}
    (regular : Regular (E := E) (F := F) r f)
    (c : OpenPartialHomeomorph M E) (d : OpenPartialHomeomorph N F)
    (hc : c ∈ maximalAtlas (𝓘(ℝ, E)) ∞ M) (hd : d ∈ maximalAtlas (𝓘(ℝ, F)) ∞ N)
    (L : P ≃L[ℝ] E) (R : Q ≃L[ℝ] F) (a : E) (b : F) (z : P)
    (source : a+L z ∈ c.target) (target : f (c.symm (a+L z)) ∈ d.source) :
    ContDiffAt ℝ (⌊r⌋₊ : ℕ) (centered L R a b (d ∘ f ∘ c.symm)) z := by
  have pre : ContDiff ℝ ∞ (fun y : P => a+L y) := contDiff_const.add L.contDiff
  have post : ContDiff ℝ ∞ (fun y : F => R.symm (y-b)) :=
    R.symm.contDiff.comp (contDiff_id.sub contDiff_const)
  have raw := regular.contDiffAt_in_charts c d hc hd (a+L z) source target
  have first := raw.comp z (pre.of_le (show (⌊r⌋₊ : ℕ) ≤ (∞ : ℕ∞ω) by simp)).contDiffAt
  have result := (post.of_le (show (⌊r⌋₊ : ℕ) ≤ (∞ : ℕ∞ω) by simp)).contDiffAt.comp z first
  exact result

theorem holder_jet_centered_charts {r : ℝ} {f : M → N}
    (regular : Regular (E := E) (F := F) r f) (unequal : r ≠ (⌊r⌋₊ : ℝ))
    (c : OpenPartialHomeomorph M E) (d : OpenPartialHomeomorph N F)
    (hc : c ∈ maximalAtlas (𝓘(ℝ, E)) ∞ M) (hd : d ∈ maximalAtlas (𝓘(ℝ, F)) ∞ N)
    (L : P ≃L[ℝ] E) (R : Q ≃L[ℝ] F) (a : E) (b : F) (z : P)
    (source : a+L z ∈ c.target) (target : f (c.symm (a+L z)) ∈ d.source) :
    JetAt ⌊r⌋₊ (r-(⌊r⌋₊ : ℝ)) (centered L R a b (d ∘ f ∘ c.symm)) z := by
  have shift : ContDiff ℝ ∞ (fun y : E => a+y) := contDiff_const.add contDiff_id
  have nonnegative : 0 ≤ r-(⌊r⌋₊ : ℝ) := sub_nonneg.mpr (Nat.floor_le regular.nonnegative)
  have subunit : r-(⌊r⌋₊ : ℝ) ≤ 1 := by linarith [Nat.lt_floor_add_one r]
  have raw := regular.holder_jet_in_charts unequal c d hc hd (a+L z) source target
  have shifted := JetAt.comp_smooth ⌊r⌋₊ nonnegative subunit
    (g := fun y : E => a+y) (x := L z) raw shift.contDiffAt
  have negative : JetAt ⌊r⌋₊ (r-(⌊r⌋₊ : ℝ)) (fun _ : E => -b) (L z) :=
    JetAt.of_contDiff_succ subunit contDiffAt_const
  have subtracted := shifted.add negative
  have precomposed := subtracted.comp_linear nonnegative L.toContinuousLinearMap (x := z)
  have result := precomposed.linear_comp R.symm.toContinuousLinearMap
  change JetAt ⌊r⌋₊ (r-(⌊r⌋₊ : ℝ)) (fun y : P => R.symm (d (f (c.symm (a+L y)))-b)) z
  simpa only [Function.comp_def, sub_eq_add_neg, ContinuousLinearEquiv.coe_coe] using result

variable [CompleteSpace P] [FiniteDimensional ℝ P]

/-- One common inverse-prototype bound determines the derivative budget
before the radius, actual frames, original charts, and regular map. -/
theorem exists_uniform_scaled_chart_extension {r η K : ℝ}
    (hr : 1 ≤ r) (positiveη : 0 < η) (nonnegativeK : 0 ≤ K) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ ρ : ℝ → P → ℝ, ∀ radius : ℝ, 0 < radius →
      ContDiff ℝ ∞ (ρ radius) ∧ HasCompactSupport (ρ radius) ∧
      tsupport (ρ radius) ⊆ closedBall 0 radius ∧
      (∀ z ∈ closedBall 0 (radius/2), ρ radius z = 1) ∧
      ∀ A : P ≃L[ℝ] Q, ‖A.symm.toContinuousLinearMap‖ ≤ K → ∀ β : Q,
      ∀ (L : P ≃L[ℝ] E) (R : Q ≃L[ℝ] F) (a : E) (b : F),
      ∀ (c : OpenPartialHomeomorph M E) (d : OpenPartialHomeomorph N F),
        c ∈ maximalAtlas (𝓘(ℝ, E)) ∞ M → d ∈ maximalAtlas (𝓘(ℝ, F)) ∞ N →
        ∀ U : Set P, IsOpen U → closedBall 0 radius ⊆ U →
          ∀ f : M → N, Regular (E := E) (F := F) r f →
            (∀ z ∈ U, a+L z ∈ c.target ∧ f (c.symm (a+L z)) ∈ d.source) →
            let h := centered L R a b (d ∘ f ∘ c.symm)
            ‖h 0-β‖ ≤ δ*radius →
            (∀ z ∈ closedBall 0 radius, ‖fderiv ℝ h z-A.toContinuousLinearMap‖ ≤ δ) →
            ∃ H : P ≃ₜ Q, (∀ z, H z = A z+β+ρ radius z • (h z-(A z+β))) ∧
              Regular (E := P) (F := Q) r H ∧ Regular (E := Q) (F := P) r H.symm ∧
              (∀ z, ‖fderiv ℝ H z-A.toContinuousLinearMap‖ < η) ∧
              (∀ z ∈ closedBall 0 (radius/2), H z = h z) ∧
              ∀ z, z ∉ closedBall 0 radius → H z = A z+β := by
  obtain ⟨δ, positiveδ, ρ, extensions⟩ :=
    ScaledLocalAffineExtension.exists_uniform_scaled_tolerance (E := P) (F := Q) hr positiveη nonnegativeK
  refine ⟨δ, positiveδ, ρ, ?_⟩
  intro radius positiveRadius
  obtain ⟨smoothρ, compactρ, supportρ, oneρ, extend⟩ := extensions radius positiveRadius
  refine ⟨smoothρ, compactρ, supportρ, oneρ, ?_⟩
  intro A inverseBound β L R a b c d hc hd U openU inside f regular domain
  dsimp only
  intro center derivative
  have smooth : ContDiffOn ℝ (⌊r⌋₊ : ℕ) (centered L R a b (d ∘ f ∘ c.symm)) U := by
    intro z hz
    exact (contDiffAt_centered_charts regular c d hc hd L R a b z
      (domain z hz).1 (domain z hz).2).contDiffWithinAt
  have holder (unequal : r ≠ (⌊r⌋₊ : ℝ)) (z : P) (hz : z ∈ U) :
      JetAt ⌊r⌋₊ (r-(⌊r⌋₊ : ℝ)) (centered L R a b (d ∘ f ∘ c.symm)) z :=
    holder_jet_centered_charts regular unequal c d hc hd L R a b z (domain z hz).1 (domain z hz).2
  exact extend A inverseBound β U openU inside _ smooth holder center derivative

end LeanShared.CenteredManifoldCoordinates
