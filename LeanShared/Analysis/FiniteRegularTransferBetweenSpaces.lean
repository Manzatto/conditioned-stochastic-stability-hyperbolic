module

public import LeanShared.Analysis.FiniteRegularTransferRealization
public import LeanShared.Analysis.FiniteRegularCoreNoiseContinuity

/-!
# Actual finite-regularity transfer between distinct completed norms

The input completion may be the intermediate anisotropic space `H` and
the target the weaker space `W`. Literal weighted core outputs are realized
in `W`; the cited one-step anisotropic bound constructs a uniformly bounded
`H→W` family. Continuous finite-regularity core noise orbits then give the
pointwise core convergence used by compact finite-net perturbation.
No input truncation or core-preserving smooth weighted composition is used.
-/

@[expose] public noncomputable section

open Filter
open scoped Topology

namespace LeanShared.FiniteRegularTransferBetweenSpaces

open DyadicCompletion FiniteRegularTransferRealization

variable {X Ω Core V W : Type*} [AddCommGroup Core] [Module ℂ Core]
  [NormedAddCommGroup V] [NormedSpace ℂ V]
  [NormedAddCommGroup W] [NormedSpace ℂ W] [CompleteSpace W]
  (q : Core →ₗ[ℂ] V) (smooth : Core →ₗ[ℂ] (X → ℂ))
  (R : Type*) [NormedAddCommGroup R] [NormedSpace ℂ R]
  (view : R →ₗ[ℂ] (X → ℂ)) (hview : Function.Injective view)
  (realize : R →L[ℂ] W) (F : Ω → X → X) (g : X → ℝ)
  (hregular : ∀ a c, weightedComposition (F a) g (smooth c) ∈ view.range)

def targetCore (a : Ω) : Core →ₗ[ℂ] W :=
  realize.toLinearMap.comp (regularAction smooth R view hview F g hregular a)

def operator (a : Ω) : closedCore q →L[ℂ] W :=
  (targetCore smooth R view hview realize F g hregular a).extendOfNorm (coreLift q)

variable (L : ℝ)
  (hbound : ∀ a c, ‖targetCore smooth R view hview realize F g hregular a c‖ ≤ L * ‖q c‖)

include hbound in
@[simp] theorem operator_core (a : Ω) (c : Core) :
    operator q smooth R view hview realize F g hregular a (coreLift q c) =
      realize (regularAction smooth R view hview F g hregular a c) :=
  LinearMap.extendOfNorm_eq (f := targetCore smooth R view hview realize F g hregular a)
    (e := coreLift q) (coreLift_dense q) ⟨L, hbound a⟩ c

include hbound in
theorem operator_norm_le (hL : 0 ≤ L) (a : Ω) :
    ‖operator q smooth R view hview realize F g hregular a‖ ≤ L :=
  LinearMap.opNorm_extendOfNorm_le (coreLift_dense q) hL (hbound a)

include hbound in
theorem continuous_core_orbit [TopologicalSpace Ω]
    (horbit : ∀ c, Continuous (fun a => regularAction smooth R view hview F g hregular a c)) (c : Core) :
    Continuous (fun a => operator q smooth R view hview realize F g hregular a (coreLift q c)) := by
  exact (realize.continuous.comp (horbit c)).congr
    (fun a => (operator_core q smooth R view hview realize F g hregular L hbound a c).symm)

include hbound in
theorem core_tendsto [TopologicalSpace Ω]
    (horbit : ∀ c, Continuous (fun a => regularAction smooth R view hview F g hregular a c))
    (a₀ : Ω) (c : Core) :
    Tendsto (fun a => operator q smooth R view hview realize F g hregular a (coreLift q c)) (𝓝 a₀)
      (𝓝 (operator q smooth R view hview realize F g hregular a₀ (coreLift q c))) :=
  (continuous_core_orbit q smooth R view hview realize F g hregular L hbound horbit c).tendsto a₀

include hbound in
/-- The core convergence comes from literal weighted-function uniform
errors and the cited ordinary lower-Hölder interpolation estimate. -/
theorem core_tendsto_of_interpolation [TopologicalSpace Ω] [TopologicalSpace X]
    (hF : Continuous (fun z : Ω × X => F z.1 z.2)) (hg : Continuous g)
    (hsmooth : ∀ c, Continuous (smooth c)) (K : Set X) (hK : IsCompact K)
    (hsupport : ∀ x ∉ K, g x = 0) (θ : ℝ) (hθ : 0 < θ) (C : Core → Ω → ℝ)
    (hinterpolation : ∀ c a₀ a ε, 0 ≤ ε →
      (∀ x, ‖view (regularAction smooth R view hview F g hregular a c) x -
        view (regularAction smooth R view hview F g hregular a₀ c) x‖ ≤ ε) →
      dist (regularAction smooth R view hview F g hregular a c)
        (regularAction smooth R view hview F g hregular a₀ c) ≤ C c a₀ * ε ^ θ)
    (a₀ : Ω) (c : Core) :
    Tendsto (fun a => operator q smooth R view hview realize F g hregular a (coreLift q c)) (𝓝 a₀)
      (𝓝 (operator q smooth R view hview realize F g hregular a₀ (coreLift q c))) := by
  apply core_tendsto q smooth R view hview realize F g hregular L hbound _ a₀ c
  intro f
  exact FiniteRegularCoreNoiseContinuity.continuous_regularFunction_of_interpolation
    F g (smooth f) hF hg (hsmooth f) K hK hsupport R view
    (fun a => regularAction smooth R view hview F g hregular a f)
    (fun a x => regularAction_apply smooth R view hview F g hregular a f x)
    θ hθ (C f) (hinterpolation f)

end LeanShared.FiniteRegularTransferBetweenSpaces
