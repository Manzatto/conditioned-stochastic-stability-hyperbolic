module

public import LeanShared.Dynamics.CompactExpansivePeriodicGrowth
public import LeanShared.Dynamics.InvariantCoreHomeomorphism
public import LeanShared.Dynamics.PressureInvariantSubtype

/-! The original ambient periodic weighted sums on any compact invariant
expansive subset satisfy the bound at THAT subset's actual pressure.
The metric, periodic points, potential and energies are transported
literally through the invariant subtype.
-/

public noncomputable section
open Set Function MeasureTheory
open scoped BoundedContinuousFunction
namespace LeanShared.ThermodynamicDefinitions
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

theorem actual_periodic_weight_growth_on_invariant (T : X ≃ₜ X) (K : Set X)
    (compactK : IsCompact K) (nonemptyK : K.Nonempty) (invariantK : T '' K = K)
    (c : ℝ) (positiveC : 0 < c)
    (expansive : ∀ x ∈ K, ∀ y ∈ K, (∀ j : ℕ,
      dist ((T : X → X)^[j] x) ((T : X → X)^[j] y) ≤ c ∧
      dist ((T.symm : X → X)^[j] x) ((T.symm : X → X)^[j] y) ≤ c) → x = y)
    (φ : X → ℝ) (continuous : ContinuousOn φ K) :
    ∃ P : ℝ, pressure T φ K = (P : EReal) ∧ ∀ η : ℝ, 0 < η →
      ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 0 < n → ∀ s : Finset X,
        (∀ x ∈ s, x ∈ K) → (∀ x ∈ s, (T : X → X)^[n] x = x) →
        (∑ x ∈ s, Real.exp (orbitSum T φ n x)) ≤ C * Real.exp (P + η) ^ n := by
  classical
  let S := LeanShared.invariantCoreHomeomorphism T K invariantK
  let : CompactSpace K := isCompact_iff_compactSpace.mp compactK
  let : Nonempty K := nonemptyK.to_subtype
  have forward (x : K) : (S x).val = T x.val := rfl
  have backward (x : K) : (S.symm x).val = T.symm x.val := rfl
  have expansiveK : ∀ x y : K, (∀ j : ℕ,
      dist ((S : K → K)^[j] x) ((S : K → K)^[j] y) ≤ c ∧
      dist ((S.symm : K → K)^[j] x) ((S.symm : K → K)^[j] y) ≤ c) → x = y := by
    intro x y close
    apply Subtype.ext
    apply expansive x.val x.property y.val y.property
    intro j
    have small := close j
    change dist (((S : K → K)^[j] x).val) (((S : K → K)^[j] y).val) ≤ c ∧
      dist (((S.symm : K → K)^[j] x).val) (((S.symm : K → K)^[j] y).val) ≤ c at small
    simpa only [iterate_coe_restriction S forward, iterate_coe_restriction S.symm backward] using small
  let φK : K →ᵇ ℝ := BoundedContinuousFunction.mkOfCompact
    ⟨fun x => φ x.val, continuous.domRestrict⟩
  obtain ⟨P, pressureP, growth⟩ := actual_periodic_weight_growth S c positiveC expansiveK φK
  have ambientP : pressure T φ K = (P : EReal) := by
    rw [← pressure_restriction S forward φ]
    exact pressureP
  refine ⟨P, ambientP, ?_⟩
  intro η positiveη
  obtain ⟨C, positive, bound⟩ := growth η positiveη
  refine ⟨C, positive, ?_⟩
  intro n positiveN s inside fixed
  have fixedK : ∀ x ∈ s.subtype (fun x => x ∈ K), (S : K → K)^[n] x = x := by
    intro x hx
    apply Subtype.ext
    exact (iterate_coe_restriction S forward n x).trans (fixed x.val (Finset.mem_subtype.mp hx))
  have result := bound n positiveN (s.subtype (fun x => x ∈ K)) fixedK
  have energies (x : K) : orbitSum S φK n x = orbitSum T φ n x.val :=
    orbitSum_restriction S forward φ n x
  simp_rw [energies] at result
  rw [Finset.sum_subtype_of_mem (p := fun x => x ∈ K)
    (fun x : X => Real.exp (orbitSum T φ n x)) inside] at result
  exact result

end LeanShared.ThermodynamicDefinitions
