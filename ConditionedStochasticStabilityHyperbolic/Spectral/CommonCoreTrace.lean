module

public import ConditionedStochasticStabilityHyperbolic.Spectral.CommonCoreSeed

/-! Ambient projector matching needs approximation of the supported leading
vector, not density of the supported common core in boundary-valued C0. -/

@[expose] public noncomputable section
open Set Filter
open scoped Topology

namespace ConditionedStochasticStabilityHyperbolic.CommonCoreSeed

variable {A F Z Core : Type*}
  [NormedAddCommGroup A] [NormedSpace ℂ A]
  [NormedAddCommGroup F] [NormedSpace ℂ F]
  [NormedAddCommGroup Z] [NormedSpace ℂ Z]
  [NormedAddCommGroup Core] [NormedSpace ℂ Core]

theorem exists_nonzero_core_trace_of_closure
    (Ip : Core →L[ℂ] F) (mp : F →L[ℂ] ℂ) (g : F)
    (hg : g ∈ closure (range Ip)) (hmg : mp g ≠ 0) :
    ∃ u : Core, mp (Ip u) ≠ 0 := by
  obtain ⟨y, hyp, hy⟩ := mem_closure_iff.1 hg {v | mp v ≠ 0}
    (isOpen_ne_fun mp.continuous continuous_const) hmg
  obtain ⟨u, rfl⟩ := hy
  exact ⟨u, hyp⟩

theorem exists_ambient_scalar_of_nonzero_core_trace
    (Ia : Core →L[ℂ] A) (Ip : Core →L[ℂ] F)
    (Pa : A →L[ℂ] A) (Pp : F →L[ℂ] F)
    (ma : A →L[ℂ] ℂ) (mp : F →L[ℂ] ℂ) (γ : A) (g : F)
    (hPa : Pa = ma.smulRight γ) (hPp : Pp = mp.smulRight g)
    (htrace : ∃ u : Core, mp (Ip u) ≠ 0)
    (a : A →L[ℂ] Z) (b : F →L[ℂ] Z) (hg : b g ≠ 0)
    (hcore : ∀ u, b (Pp (Ip u)) = a (Pa (Ia u))) :
    ∃ c : ℂ, c ≠ 0 ∧ b g = c • a γ ∧ a γ ≠ 0 := by
  obtain ⟨u, hu⟩ := htrace
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
