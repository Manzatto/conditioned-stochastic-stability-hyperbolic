module

public import ConditionedStochasticStabilityHyperbolic.Spectral.InvariantCoreProductApproximation

/-! # A normalized common-core seed from Riesz projector agreement

Density provides a seed with nonzero analytic projection. The exact
same-cutoff common-core Riesz identity forces its physical projection to be
nonzero too. Normalization then fixes both limiting right vectors, without
assuming that either noisy right vector belongs to the finite-regular core.
-/

@[expose] public noncomputable section
open Set
namespace ConditionedStochasticStabilityHyperbolic.CommonCoreSeed

variable {Core A F Z : Type*}
  [NormedAddCommGroup Core] [NormedSpace ℂ Core]
  [NormedAddCommGroup A] [NormedSpace ℂ A]
  [NormedAddCommGroup F] [NormedSpace ℂ F]
  [NormedAddCommGroup Z] [NormedSpace ℂ Z]

/-- Both rank-one projections can be normalized using a single actual core
seed. No independent physical matching vector or regularity witness is needed. -/
theorem exists_normalized_seed
    (Ia : Core →L[ℂ] A) (Ip : Core →L[ℂ] F) (hdense : DenseRange Ia)
    (Pa : A →L[ℂ] A) (Pp : F →L[ℂ] F)
    (ma : A →L[ℂ] ℂ) (mp : F →L[ℂ] ℂ) (γ : A) (g : F)
    (hPa : Pa = ma.smulRight γ) (hPp : Pp = mp.smulRight g)
    (hnorm : ma γ = 1)
    (a : A →L[ℂ] Z) (b : F →L[ℂ] Z)
    (hcore : ∀ u, b (Pp (Ip u)) = a (Pa (Ia u)))
    (c : ℂ) (hmatch : b g = c • a γ) (hγ : a γ ≠ 0) :
    ∃ seed : Core, Pp (Ip seed) = g ∧ Pa (Ia seed) = c • γ := by
  have hma : ma γ ≠ 0 := by rw [hnorm]; exact one_ne_zero
  obtain ⟨u, hu⟩ := hdense.exists_mem_open (isOpen_ne_fun ma.continuous continuous_const)
    ⟨γ, hma⟩
  have he := hcore u
  rw [hPa, hPp, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.smulRight_apply, map_smul, hmatch, map_smul, smul_smul] at he
  have hs : mp (Ip u) * c = ma (Ia u) := (smul_left_injective ℂ hγ) he
  have hmp : mp (Ip u) ≠ 0 := by
    intro hz
    rw [hz, zero_mul] at hs
    exact hu hs.symm
  let seed := (mp (Ip u))⁻¹ • u
  refine ⟨seed, ?_, ?_⟩
  · rw [show seed = (mp (Ip u))⁻¹ • u from rfl, map_smul, hPp,
      ContinuousLinearMap.smulRight_apply, map_smul, smul_eq_mul,
      inv_mul_cancel₀ hmp, one_smul]
  · rw [show seed = (mp (Ip u))⁻¹ • u from rfl, map_smul, hPa,
      ContinuousLinearMap.smulRight_apply, map_smul, smul_eq_mul,
      ← hs, ← mul_assoc, inv_mul_cancel₀ hmp, one_mul]

/-- Exact same-cutoff core projector agreement derives the scalar ambient
right-vector matching itself. It does not need to be supplied separately. -/
theorem exists_ambient_scalar
    (Ia : Core →L[ℂ] A) (Ip : Core →L[ℂ] F) (hdense : DenseRange Ip)
    (Pa : A →L[ℂ] A) (Pp : F →L[ℂ] F)
    (ma : A →L[ℂ] ℂ) (mp : F →L[ℂ] ℂ) (γ : A) (g : F)
    (hPa : Pa = ma.smulRight γ) (hPp : Pp = mp.smulRight g)
    (hnorm : mp g = 1)
    (a : A →L[ℂ] Z) (b : F →L[ℂ] Z) (hg : b g ≠ 0)
    (hcore : ∀ u, b (Pp (Ip u)) = a (Pa (Ia u))) :
    ∃ c : ℂ, c ≠ 0 ∧ b g = c • a γ ∧ a γ ≠ 0 := by
  have hmp : mp g ≠ 0 := by rw [hnorm]; exact one_ne_zero
  obtain ⟨u, hu⟩ := hdense.exists_mem_open (isOpen_ne_fun mp.continuous continuous_const)
    ⟨g, hmp⟩
  have he := hcore u
  rw [hPa, hPp, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.smulRight_apply, map_smul, map_smul] at he
  have hma : ma (Ia u) ≠ 0 := by
    intro hz
    rw [hz, zero_smul] at he
    exact hg ((smul_eq_zero.mp he).resolve_left hu)
  let c := (mp (Ip u))⁻¹ * ma (Ia u)
  have heq : b g = c • a γ := by
    have h := congrArg (fun v : Z => (mp (Ip u))⁻¹ • v) he
    simpa only [smul_smul, inv_mul_cancel₀ hu, one_smul] using h
  refine ⟨c, mul_ne_zero (inv_ne_zero hu) hma, heq, ?_⟩
  intro hz
  rw [hz, smul_zero] at heq
  exact hg heq

end ConditionedStochasticStabilityHyperbolic.CommonCoreSeed
