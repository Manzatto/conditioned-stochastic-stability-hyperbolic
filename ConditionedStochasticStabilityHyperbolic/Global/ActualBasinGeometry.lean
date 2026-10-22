module

public import ConditionedStochasticStabilityHyperbolic.Global.HeteroclinicAccessibility
public import LeanShared.Dynamics.AbsorbingBasinSeparation

/-! # Actual live stable and heteroclinic orbits from classical basin data

Ordinary stable/unstable approach and the adapted filtration imply the live
orbit conditions needed for noise controls. Strict trapping is stated
explicitly; it excludes absorbing-boundary starts from a retained stable basin.
No noisy path or eigenfunction positivity conclusion is assumed.
-/
@[expose] public section
open Set Function Metric
namespace ConditionedStochasticStabilityHyperbolic.Global.ActualBasinGeometry
open LeanShared AbsorbingBasinSeparation HeteroclinicAccessibility
variable {X : Type*} [MetricSpace X]

/-- Compact metric orbit approach implies the ordinary neighborhood form. -/
theorem approaches_of_metric (T : X → X) (Γ : Set X) (hΓ : IsCompact Γ) (x : X)
    (hmetric : ∀ r : ℝ, 0 < r → ∃ n : ℕ, ∃ y ∈ Γ, dist (T^[n] x) y < r) :
    Approaches T Γ x := by
  intro U hU hΓU
  obtain ⟨r, hr, hthick⟩ := hΓ.exists_thickening_subset_open hU hΓU
  obtain ⟨n, y, hy, hdist⟩ := hmetric r hr
  exact ⟨n, hthick (mem_thickening_iff.mpr ⟨y, hy, hdist⟩)⟩

/-- Commuting invariant maps preserve approach to the same basic set. -/
theorem approaches_of_commuting_map (T H : X → X) (Γ : Set X)
    (hH : Continuous H) (hΓ : MapsTo H Γ Γ) (hcomm : Function.Commute T H) (x : X)
    (happ : Approaches T Γ x) : Approaches T Γ (H x) := by
  intro U hU hΓU
  obtain ⟨n, hn⟩ := happ (H ⁻¹' U) (hU.preimage hH) (fun y hy => hΓU (hΓ hy))
  exact ⟨n, (hcomm.iterate_left n x).symm ▸ hn⟩

theorem commute_inverse (T : X ≃ₜ X) : Function.Commute (T : X → X) T.symm := by
  intro x
  rw [T.apply_symm_apply, T.symm_apply_apply]

/-- A retained stable point lies in the interior of the live region. This
also holds after any orbit shift preserving its stable approach. -/
theorem retained_stable_point_live_interior
    (T : X ≃ₜ X) (A Γ : Set X) (hstrict : MapsTo T (closure A) A)
    (hΓA : Γ ⊆ interior Aᶜ) (hΓT : MapsTo T Γ Γ) (x : X)
    (happ : Approaches T Γ x) : x ∈ interior Aᶜ := by
  have hAfwd : MapsTo T A A := fun y hy => hstrict (subset_closure hy)
  have hnext := approaches_of_commuting_map T T Γ T.continuous hΓT (Function.Commute.refl _) x happ
  have hnot : T x ∉ A := forward_approach_not_mem_absorbing T A Γ hAfwd hΓA (T x) hnext
  have hx : x ∉ closure A := fun h => hnot (hstrict h)
  rw [interior_compl]
  exact hx

/-- Actual stable starting states already in a selected prefix have all
forward iterates in the prefix and the open live control region. -/
theorem stable_orbit_in_selected_live_prefix
    (T : X ≃ₜ X) (A P Γ : Set X) (hstrict : MapsTo T (closure A) A)
    (hP : MapsTo T P (interior P)) (hΓA : Γ ⊆ interior Aᶜ)
    (hΓT : MapsTo T Γ Γ) (x : X) (hx : x ∈ P) (happ : Approaches T Γ x) :
    ∀ n : ℕ, (T : X → X)^[n] x ∈ P ∩ interior Aᶜ := by
  intro n
  have hn := approaches_of_commuting_map T ((T : X → X)^[n]) Γ
    (T.continuous.iterate n) (hΓT.iterate n) (Function.Commute.self_iterate _ n) x happ
  exact ⟨(show MapsTo T P P from fun y hy => interior_subset (hP hy)).iterate n hx,
    retained_stable_point_live_interior T A Γ hstrict hΓA hΓT _ hn⟩

/-- Standard heteroclinic orbit data produces the full actual live witness
used by stochastic accessibility; no forward/backward live premise remains. -/
def actual_heteroclinic_witness
    (T : X ≃ₜ X) (A P Γsource Γtarget : Set X)
    (hstrict : MapsTo T (closure A) A) (hP : MapsTo T P (interior P))
    (hsource : Γsource ⊆ interior P) (htarget : Γtarget ⊆ interior Aᶜ)
    (hsourceCompact : IsCompact Γsource) (htargetCompact : IsCompact Γtarget)
    (hsourceT : MapsTo T Γsource Γsource) (hsourceInv : MapsTo T.symm Γsource Γsource)
    (htargetT : MapsTo T Γtarget Γtarget) (htargetInv : MapsTo T.symm Γtarget Γtarget)
    (x : X)
    (hfuture : ∀ r : ℝ, 0 < r → ∃ n : ℕ, ∃ y ∈ Γtarget,
      dist ((T : X → X)^[n + 1] x) y < r)
    (hpast : ∀ r : ℝ, 0 < r → ∃ n : ℕ, ∃ y ∈ Γsource,
      dist ((T.symm : X → X)^[n] x) y < r) :
    HeteroclinicWitness T (P ∩ interior Aᶜ) Γsource Γtarget := by
  have hf : Approaches T Γtarget x := approaches_of_metric T Γtarget htargetCompact x (by
    intro r hr
    obtain ⟨n, y, hy, hd⟩ := hfuture r hr
    exact ⟨n + 1, y, hy, hd⟩)
  have hb : Approaches T.symm Γsource x := approaches_of_metric T.symm Γsource hsourceCompact x hpast
  have hPint : MapsTo T (interior P) (interior P) := fun y hy => hP (interior_subset hy)
  have hpoint : ∀ z, Approaches T.symm Γsource z → Approaches T Γtarget z → z ∈ P ∩ interior Aᶜ := by
    intro z hzpast hzfuture
    exact ⟨interior_subset (backward_approach_mem_absorbing T (interior P) Γsource isOpen_interior
      hPint hsource z hzpast), retained_stable_point_live_interior T A Γtarget hstrict htarget htargetT z hzfuture⟩
  refine ⟨x, ?_, ?_, hfuture, hpast⟩
  · intro n
    exact hpoint _
      (approaches_of_commuting_map T.symm ((T : X → X)^[n]) Γsource
        (T.continuous.iterate n) (hsourceT.iterate n) ((commute_inverse T).symm.iterate_right n) x hb)
      (approaches_of_commuting_map T ((T : X → X)^[n]) Γtarget
        (T.continuous.iterate n) (htargetT.iterate n) (Function.Commute.self_iterate _ n) x hf)
  · intro n
    exact hpoint _
      (approaches_of_commuting_map T.symm ((T.symm : X → X)^[n]) Γsource
        (T.symm.continuous.iterate n) (hsourceInv.iterate n) (Function.Commute.self_iterate _ n) x hb)
      (approaches_of_commuting_map T ((T.symm : X → X)^[n]) Γtarget
        (T.symm.continuous.iterate n) (htargetInv.iterate n) ((commute_inverse T).iterate_right n) x hf)

end ConditionedStochasticStabilityHyperbolic.Global.ActualBasinGeometry
