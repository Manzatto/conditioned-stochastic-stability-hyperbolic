module

public import LeanShared.Analysis.FiniteRegularCoreNoiseContinuity

/-!
# Lower regularity continuity of actual noisy weighted smooth-core outputs

The joint function-valued perturbation is continuous. No continuity of the
noise parameter as a map into the highest fractional C^r operator topology
is required. The standard interpolation inequality, with a uniform higher
regularity bound, gives continuity of the constructed ordinary core output.
-/

@[expose] public noncomputable section

namespace LeanShared.ActualRegularNoiseContinuity

open Set
open FiniteRegularTransferRealization

variable {X G P Core R : Type*} [TopologicalSpace X] [TopologicalSpace P]
  [AddCommGroup Core] [Module ℂ Core] [NormedAddCommGroup R] [NormedSpace ℂ R]

/-- Source-exact measurability producer: continuity follows from the joint
physical maps and classical lower-Hölder interpolation, independently of
continuity in the top fractional regularity norm. -/
theorem continuous_noisy_core
    (smooth : Core →ₗ[ℂ] (X → ℂ)) (view : R →ₗ[ℂ] (X → ℂ))
    (inj : Function.Injective view) (F : G → X → X) (g : X → ℝ)
    (regular : ∀ a c, weightedComposition (F a) g (smooth c) ∈ view.range)
    (noise : P → G)
    (joint : Continuous (fun z : P × X => F (noise z.1) z.2))
    (hg : Continuous g) (hsmooth : ∀ c, Continuous (smooth c))
    (K : Set X) (hK : IsCompact K) (support : ∀ x ∉ K, g x = 0)
    (θ : ℝ) (hθ : 0 < θ) (C : Core → P → ℝ)
    (interpolation : ∀ c a₀ a ε, 0 ≤ ε →
      (∀ x, ‖view (regularAction smooth R view inj F g regular (noise a) c) x -
        view (regularAction smooth R view inj F g regular (noise a₀) c) x‖ ≤ ε) →
      dist (regularAction smooth R view inj F g regular (noise a) c)
        (regularAction smooth R view inj F g regular (noise a₀) c) ≤ C c a₀ * ε ^ θ)
    (c : Core) : Continuous (fun a => regularAction smooth R view inj F g regular (noise a) c) := by
  apply FiniteRegularCoreNoiseContinuity.continuous_regularFunction_of_interpolation
    (fun a => F (noise a)) g (smooth c) joint hg (hsmooth c) K hK support
    R (fun f => view f) (fun a => regularAction smooth R view inj F g regular (noise a) c)
    (fun a x => regularAction_apply smooth R view inj F g regular (noise a) c x) θ hθ (C c)
  exact interpolation c

end LeanShared.ActualRegularNoiseContinuity
