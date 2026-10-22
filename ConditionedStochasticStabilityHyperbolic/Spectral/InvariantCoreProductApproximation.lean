module

public import ConditionedStochasticStabilityHyperbolic.Spectral.PhysicalProjectorPairing
public import Mathlib.Topology.Algebra.Algebra

/-! # Simultaneous product approximation from invariant common-core powers

No noisy eigenfunction regularity upgrade is used. A core seed's normalized
transfer powers remain in the invariant finite-regular common core and
converge in both the analytic and physical spaces. Literal core multiplication
then gives the simultaneous product approximants needed for physical pairing.
-/

@[expose] public noncomputable section
open Filter
open scoped Topology BoundedContinuousFunction
namespace ConditionedStochasticStabilityHyperbolic.InvariantCoreProductApproximation

variable {Core A X : Type*}
  [NormedAddCommGroup Core] [NormedSpace ℂ Core]
  [NormedAddCommGroup A] [NormedSpace ℂ A] [TopologicalSpace X]

/-- Iterates of an actual core operator intertwine with its completed
realization; independent approximation sequences are unnecessary. -/
theorem map_power
    (T : Core →L[ℂ] Core) (P : A →L[ℂ] A) (I : Core →L[ℂ] A)
    (hI : I.comp T = P.comp I) :
    ∀ n : ℕ, ∀ u, I ((T ^ n) u) = (P ^ n) (I u) := by
  intro n
  induction n with
  | zero => intro u; simp
  | succ n ih =>
      intro u
      have he := congrArg (fun B : Core →L[ℂ] A => B ((T ^ n) u)) hI
      simp only [ContinuousLinearMap.comp_apply] at he
      rw [pow_succ', mul_apply_eq_comp, he, ih, ← mul_apply_eq_comp, ← pow_succ']

/-- A normalized common-core seed and the two actual power gaps supply
simultaneous harmonic-product approximants. The core is allowed to be finite
regular; neither the noisy harmonic vector nor its product is assumed smooth. -/
theorem exists_product_approximants_of_invariant_core
    (T : Core →L[ℂ] Core) (Pa : A →L[ℂ] A)
    (Pp : (X →ᵇ ℂ) →L[ℂ] (X →ᵇ ℂ))
    (Ia : Core →L[ℂ] A) (Ip : Core →L[ℂ] (X →ᵇ ℂ))
    (ha : Ia.comp T = Pa.comp Ia) (hp : Ip.comp T = Pp.comp Ip)
    (z : ℂ) (seed : Core) (γ : A) (g : X →ᵇ ℝ) (c : ℂ)
    (hlimA : Tendsto (fun n : ℕ => ((z⁻¹ • Pa) ^ n) (Ia seed)) atTop (𝓝 (c • γ)))
    (hlimP : Tendsto (fun n : ℕ => ((z⁻¹ • Pp) ^ n) (Ip seed)) atTop
      (𝓝 (AbsorbingMarkovChains.ComplexKernel.ofReal g)))
    (Mt : Core →L[ℂ] Core) (Ma : A →L[ℂ] A) (h : X →ᵇ ℝ)
    (hMa : Ia.comp Mt = Ma.comp Ia)
    (hMp : ∀ u, Ip (Mt u) = Ip u * AbsorbingMarkovChains.ComplexKernel.ofReal h) :
    ∃ u : ℕ → Core,
      Tendsto (fun n => Ip (u n)) atTop
        (𝓝 (AbsorbingMarkovChains.ComplexKernel.ofReal (g * h))) ∧
      Tendsto (fun n => Ia (u n)) atTop (𝓝 (c • Ma γ)) := by
  let v := fun n : ℕ => ((z⁻¹ • T) ^ n) seed
  have hmapA (n : ℕ) : Ia (v n) = ((z⁻¹ • Pa) ^ n) (Ia seed) := by
    apply map_power (z⁻¹ • T) (z⁻¹ • Pa) Ia _ n seed
    ext u
    simp only [ContinuousLinearMap.comp_apply, smul_apply, map_smul]
    exact congrArg (fun v => z⁻¹ • v) (congrArg (fun B : Core →L[ℂ] A => B u) ha)
  have hmapP (n : ℕ) : Ip (v n) = ((z⁻¹ • Pp) ^ n) (Ip seed) := by
    apply map_power (z⁻¹ • T) (z⁻¹ • Pp) Ip _ n seed
    ext u x
    have he := congrArg (fun B : Core →L[ℂ] (X →ᵇ ℂ) => B u) hp
    simp only [ContinuousLinearMap.comp_apply] at he
    simpa only [ContinuousLinearMap.comp_apply, smul_apply, map_smul] using
      congrArg (fun v : X →ᵇ ℂ => (z⁻¹ • v) x) he
  have hvA : Tendsto (fun n => Ia (v n)) atTop (𝓝 (c • γ)) :=
    hlimA.congr' (Eventually.of_forall (fun n => (hmapA n).symm))
  have hvP : Tendsto (fun n => Ip (v n)) atTop
      (𝓝 (AbsorbingMarkovChains.ComplexKernel.ofReal g)) :=
    hlimP.congr' (Eventually.of_forall (fun n => (hmapP n).symm))
  refine ⟨fun n => Mt (v n), ?_, ?_⟩
  · have he : AbsorbingMarkovChains.ComplexKernel.ofReal g *
        AbsorbingMarkovChains.ComplexKernel.ofReal h =
        AbsorbingMarkovChains.ComplexKernel.ofReal (g * h) := by
      ext x
      simp [AbsorbingMarkovChains.ComplexKernel.ofReal_apply]
    rw [← he]
    exact (hvP.mul_const _).congr' (Eventually.of_forall (fun n => (hMp (v n)).symm))
  · have hl := Ma.continuous.continuousAt.tendsto.comp hvA
    rw [map_smul] at hl
    apply hl.congr'
    exact Eventually.of_forall (fun n => (congrArg
      (fun B : Core →L[ℂ] A => B (v n)) hMa).symm)

end ConditionedStochasticStabilityHyperbolic.InvariantCoreProductApproximation
