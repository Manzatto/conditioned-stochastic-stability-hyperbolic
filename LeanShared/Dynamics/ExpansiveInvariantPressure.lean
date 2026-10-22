module

public import LeanShared.Dynamics.ExpansiveFinitePressure
public import LeanShared.Dynamics.PressureInvariantSubtype
public import Mathlib.Topology.Homeomorph.Lemmas

/-! Actual finite pressure on a compact invariant expansive subset, using
the original ambient separated sets and potential. -/
public noncomputable section
open Set Function
namespace LeanShared.ThermodynamicDefinitions
variable {X : Type*} [MetricSpace X]

theorem finite_pressure_on_compact_expansive (T : X ≃ₜ X) (K : Set X)
    (compact : IsCompact K) (nonempty : K.Nonempty) (invariant : T '' K=K)
    (c : ℝ) (hc : 0 < c)
    (expansive : ∀ x ∈ K, ∀ y ∈ K, (∀ j : ℕ,
      dist ((T : X → X)^[j] x) ((T : X → X)^[j] y) ≤ c ∧
      dist ((T.symm : X → X)^[j] x) ((T.symm : X → X)^[j] y) ≤ c) → x=y)
    (φ : X → ℝ) (continuous : ContinuousOn φ K) :
    ∃ P : ℝ, pressure T φ K=(P : EReal) := by
  have iff_mem (x : X) : x ∈ K ↔ T x ∈ K := by
    constructor
    · intro hx
      rw [←invariant]
      exact ⟨x,hx,rfl⟩
    · intro hx
      rw [←invariant] at hx
      obtain ⟨y,hy,equal⟩ := hx
      exact (T.injective equal) ▸ hy
  let TK : K ≃ₜ K := T.subtype iff_mem
  let : CompactSpace K := isCompact_iff_compactSpace.mp compact
  let : Nonempty K := nonempty.to_subtype
  have forward (x : K) : (TK x).val=T x.val := rfl
  have backward (x : K) : (TK.symm x).val=T.symm x.val := rfl
  have restricted_expansive : ∀ x y : K, (∀ j : ℕ,
      dist ((TK : K → K)^[j] x) ((TK : K → K)^[j] y) ≤ c ∧
      dist ((TK.symm : K → K)^[j] x) ((TK.symm : K → K)^[j] y) ≤ c) → x=y := by
    intro x y small
    apply Subtype.ext
    apply expansive x.val x.property y.val y.property
    intro j
    have h := small j
    change dist (((TK : K → K)^[j] x).val) (((TK : K → K)^[j] y).val) ≤ c ∧
      dist (((TK.symm : K → K)^[j] x).val) (((TK.symm : K → K)^[j] y).val) ≤ c at h
    simpa only [iterate_coe_restriction TK forward,iterate_coe_restriction TK.symm backward] using h
  obtain ⟨P,identity⟩ := finite_pressure_of_expansive TK c hc restricted_expansive
    (fun x => φ x.val) continuous.domRestrict
  refine ⟨P,?_⟩
  rw [←pressure_restriction TK forward φ]
  exact identity

end LeanShared.ThermodynamicDefinitions
