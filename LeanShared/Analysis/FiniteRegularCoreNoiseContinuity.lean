module

public import LeanShared.Analysis.CylinderPrincipalCoefficient
public import LeanShared.Analysis.FiniteRegularTransferRealization
public import Mathlib.Analysis.Normed.Group.Continuity

/-!
# Continuous noisy finite-regularity outputs from actual uniform errors

Jointly continuous maps and a fixed compactly supported weight give
uniform convergence of the literal functions `g(x)*h(F_a(x))`. The
classical Hölder interpolation estimate, with a common higher-regularity
bound, turns that uniform error into continuity in a lower Hölder norm.
This derives the core orbit continuity needed for strong measurability
without assuming continuity in the highest fractional regularity norm.
-/

@[expose] public noncomputable section

open Set Filter
open scoped Topology

namespace LeanShared.FiniteRegularCoreNoiseContinuity

open CylinderPrincipalCoefficient

variable {X P : Type*} [TopologicalSpace X] [TopologicalSpace P]

def rawFunction (F : P → X → X) (g : X → ℝ) (h : X → ℂ) (a : P) (x : X) : ℂ :=
  (g x : ℂ) * h (F a x)

def uniformError (F : P → X → X) (g : X → ℝ) (h : X → ℂ) (K : Set X) (a₀ a : P) : ℝ :=
  coefficient K Set.univ (fun z => ‖rawFunction F g h z.1 z.2 - rawFunction F g h a₀ z.2‖) a

theorem continuous_rawFunction (F : P → X → X) (g : X → ℝ) (h : X → ℂ)
    (hF : Continuous (fun z : P × X => F z.1 z.2)) (hg : Continuous g) (hh : Continuous h) :
    Continuous (fun z : P × X => rawFunction F g h z.1 z.2) :=
  ((Complex.continuous_ofReal.comp (hg.comp continuous_snd)).mul (hh.comp hF))

theorem tendsto_uniformError (F : P → X → X) (g : X → ℝ) (h : X → ℂ)
    (hF : Continuous (fun z : P × X => F z.1 z.2)) (hg : Continuous g) (hh : Continuous h)
    (K : Set X) (hK : IsCompact K) (a₀ : P) :
    Tendsto (uniformError F g h K a₀) (𝓝 a₀) (𝓝 0) := by
  let f : P × X → ℝ := fun z => ‖rawFunction F g h z.1 z.2 - rawFunction F g h a₀ z.2‖
  have hf : Continuous f := ((continuous_rawFunction F g h hF hg hh).sub
    ((continuous_rawFunction F g h hF hg hh).comp (continuous_const.prodMk continuous_snd))).norm
  have hzero : coefficient K Set.univ f a₀ = 0 := by
    apply le_antisymm
    · apply csSup_le (s := values K Set.univ f a₀) (values_nonempty K Set.univ f a₀)
      intro y hy
      rcases hy with hy | ⟨x, _, rfl⟩
      · obtain rfl := mem_singleton_iff.mp hy
        exact le_rfl
      · simp [f]
    · exact coefficient_nonneg hK isClosed_univ hf a₀
  have husc := upperSemicontinuous_coefficient hK isClosed_univ hf
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hev := husc a₀ ε (by simpa only [hzero] using hε)
  filter_upwards [hev] with a ha
  change dist (coefficient K Set.univ f a) 0 < ε
  simpa only [Real.dist_eq, sub_zero, abs_of_nonneg (coefficient_nonneg hK isClosed_univ hf a)] using ha

theorem raw_difference_le_uniformError (F : P → X → X) (g : X → ℝ) (h : X → ℂ)
    (hF : Continuous (fun z : P × X => F z.1 z.2)) (hg : Continuous g) (hh : Continuous h)
    (K : Set X) (hK : IsCompact K) (hsupport : ∀ x ∉ K, g x = 0) (a₀ a : P) (x : X) :
    ‖rawFunction F g h a x - rawFunction F g h a₀ x‖ ≤ uniformError F g h K a₀ a := by
  have hf : Continuous (fun z : P × X => ‖rawFunction F g h z.1 z.2 - rawFunction F g h a₀ z.2‖) :=
    ((continuous_rawFunction F g h hF hg hh).sub
    ((continuous_rawFunction F g h hF hg hh).comp (continuous_const.prodMk continuous_snd))).norm
  by_cases hx : x ∈ K
  · exact density_le_coefficient hK isClosed_univ hf a x ⟨hx, mem_univ _⟩
  · have hz : rawFunction F g h a x = 0 := by simp [rawFunction, hsupport x hx]
    have hz₀ : rawFunction F g h a₀ x = 0 := by simp [rawFunction, hsupport x hx]
    rw [hz, hz₀, sub_self, norm_zero]
    exact coefficient_nonneg hK isClosed_univ hf a

theorem continuous_regularFunction_of_interpolation
    (F : P → X → X) (g : X → ℝ) (h : X → ℂ)
    (hF : Continuous (fun z : P × X => F z.1 z.2)) (hg : Continuous g) (hh : Continuous h)
    (K : Set X) (hK : IsCompact K) (hsupport : ∀ x ∉ K, g x = 0)
    (R : Type*) [NormedAddCommGroup R] (view : R → X → ℂ) (regular : P → R)
    (hview : ∀ a x, view (regular a) x = rawFunction F g h a x)
    (θ : ℝ) (hθ : 0 < θ) (C : P → ℝ)
    (hinterpolation : ∀ a₀ a ε, 0 ≤ ε →
      (∀ x, ‖view (regular a) x - view (regular a₀) x‖ ≤ ε) →
      dist (regular a) (regular a₀) ≤ C a₀ * ε ^ θ) :
    Continuous regular := by
  apply continuous_iff_continuousAt.mpr
  intro a₀
  have he := tendsto_uniformError F g h hF hg hh K hK a₀
  have hb : Tendsto (fun a => C a₀ * uniformError F g h K a₀ a ^ θ) (𝓝 a₀) (𝓝 0) := by
    simpa only [Real.zero_rpow hθ.ne', mul_zero] using
      (tendsto_const_nhds.mul (he.rpow_const (Or.inr hθ.le)))
  have hd : Tendsto (fun a => dist (regular a) (regular a₀)) (𝓝 a₀) (𝓝 0) := by
    apply squeeze_zero (fun _ => dist_nonneg) _ hb
    intro a
    apply hinterpolation a₀ a (uniformError F g h K a₀ a)
    · have hf : Continuous (fun z : P × X => ‖rawFunction F g h z.1 z.2 - rawFunction F g h a₀ z.2‖) :=
        ((continuous_rawFunction F g h hF hg hh).sub
        ((continuous_rawFunction F g h hF hg hh).comp (continuous_const.prodMk continuous_snd))).norm
      exact coefficient_nonneg hK isClosed_univ hf a
    · intro x
      rw [hview, hview]
      exact raw_difference_le_uniformError F g h hF hg hh K hK hsupport a₀ a x
  change Tendsto regular (𝓝 a₀) (𝓝 (regular a₀))
  exact tendsto_iff_dist_tendsto_zero.mpr hd

end LeanShared.FiniteRegularCoreNoiseContinuity
