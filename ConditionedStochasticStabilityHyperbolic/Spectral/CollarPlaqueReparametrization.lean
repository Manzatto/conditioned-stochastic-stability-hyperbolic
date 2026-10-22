module

public import ConditionedStochasticStabilityHyperbolic.Spectral.LocalPositiveCollar

/-! Ordinary random-plaque data are invariant under a homeomorphic change of
control coordinates. This transfers literal shrinking-cube plaque sources to
the fixed cube without making any noise-law assumption. -/

@[expose] public noncomputable section
open Set Filter
open scoped Topology
namespace ConditionedStochasticStabilityHyperbolic.LocalPositiveCollar
open LeanShared.ControlledPlaqueClosure
variable {X Ω Ω' : Type*} [MetricSpace X] [TopologicalSpace Ω] [TopologicalSpace Ω']

namespace ForwardCollarPlaqueInputs
variable {T : X ≃ₜ X} {F : X × Ω → X} {V K G : Set X}

def reparametrize (h : ForwardCollarPlaqueInputs T F V K G) (e : Ω' ≃ₜ Ω) :
    ForwardCollarPlaqueInputs T (fun z : X × Ω' => F (z.1, e z.2)) V K G where
  zero := e.symm h.zero
  continuous_noise := h.continuous_noise.comp (continuous_fst.prodMk (e.continuous.comp continuous_snd))
  zero_noise := fun x => by simpa only [e.apply_symm_apply] using h.zero_noise x
  local_cover := by
    intro p hp
    obtain ⟨W, ho, hpw, hWG, hc⟩ := h.local_cover p hp
    refine ⟨W, ho, hpw, hWG, ?_⟩
    intro y hy
    obtain ⟨z, hz⟩ := hc y hy
    exact ⟨e.symm z, by simpa only [e.apply_symm_apply] using hz⟩
  plaque := fun ω => h.plaque (fun i => e (ω i))
  lower_semicontinuous := by
    intro ω ωn hn z hz
    apply h.lower_semicontinuous (fun i => e (ω i)) (fun n i => e (ωn n i)) _ z hz
    exact tendsto_pi_nhds.mpr (fun i => e.continuous.continuousAt.tendsto.comp
      ((tendsto_pi_nhds.mp hn) i))
  backward_orbit := by
    intro ω z hz
    exact h.backward_orbit (fun i => e (ω i)) z hz
  capture := by
    intro ω b hb hs he
    exact h.capture (fun i => e (ω i)) b hb hs he

end ForwardCollarPlaqueInputs
end ConditionedStochasticStabilityHyperbolic.LocalPositiveCollar
