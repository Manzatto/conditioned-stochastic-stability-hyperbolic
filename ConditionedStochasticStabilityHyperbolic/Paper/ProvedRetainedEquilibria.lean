module

public import ConditionedStochasticStabilityHyperbolic.Paper.GlobalHypotheses
public import ConditionedStochasticStabilityHyperbolic.Paper.ProvedHyperbolicEquilibrium
public import LeanShared.Dynamics.EquilibriumExponentialWeight
public import LeanShared.Dynamics.HyperbolicPotentialContinuity
public import LeanShared.Dynamics.ExpansiveInvariantPressure

/-! Every retained mixing basic set of HG2 has a constructed equilibrium
package at its literal geometric potential. No support of the global weight
in an individual collar is required. Finite real pressure is a consequence. -/

@[expose] public noncomputable section
open Set MeasureTheory Bundle
open scoped Manifold ContDiff
namespace ConditionedStochasticStabilityHyperbolic.Paper
open LeanShared HyperbolicBasicSet

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MetricSpace M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] [ChartedSpace E M]
  [IsManifold (𝓘(ℝ, E)) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
  {T : M ≃ₜ M} {D : SpectralDecomposition (E := E) T} {g : M → ℝ} {A : Set M}

omit [BorelSpace M] in
/-- Subordinate HG1 components need not mix: compact hyperbolicity and the
actual potential already imply finite real pressure. -/
theorem HG1.exists_retained_real_pressure (h : HG1 D g A) (i : Fin D.count)
    (retained : D.core i ⊆ Aᶜ) : ∃ p : ℝ, D.pressure g i = (p : EReal) := by
  have hn : (1 : ℕ) ≤ ⌊h.r⌋₊ :=
    Nat.le_floor (by simpa only [Nat.cast_one] using h.regularity_gt_one.le)
  have forward : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, E)) 1 T :=
    h.map_regular.differentiable.of_le (by exact_mod_cast hn)
  have inverse : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, E)) 1 T.symm :=
    h.inverse_regular.differentiable.of_le (by exact_mod_cast hn)
  obtain ⟨c, positive, expansive⟩ := (D.basic i).exists_expansivity_radius forward inverse
  exact ThermodynamicDefinitions.finite_pressure_on_compact_expansive T (D.core i)
    (D.basic i).hyperbolic.compact (D.basic i).nonempty (D.basic i).hyperbolic.invariant
    c positive expansive ((D.basic i).hyperbolic.potential g)
    ((D.basic i).hyperbolic.continuousOn_potential forward
      (inverse.mdifferentiable (by norm_num)) g
      h.weight_regular.differentiable.continuous.continuousOn (h.weight_positive i retained))

omit [BorelSpace M] in
theorem HG1.retained_real_pressure_identity (h : HG1 D g A) (i : Fin D.count)
    (retained : D.core i ⊆ Aᶜ) : D.pressure g i = ((D.pressure g i).toReal : EReal) := by
  obtain ⟨p, identity⟩ := h.exists_retained_real_pressure i retained
  rw [identity, EReal.toReal_coe]

def HG2.proved_retained_equilibriumPackage (h : HG2 D g A) (i : Fin D.count)
    (retained : D.core i ⊆ Aᶜ) : EquilibriumPackage (D.basic i).hyperbolic g :=
  Classical.choice ((D.basic i).exists_proved_equilibriumPackage
    h.regularity_gt_one (by linarith [h.regularity_gt_one])
    h.map_regular h.inverse_regular (h.retained_mixing i retained) g h.weight_regular
    (h.weight_positive i retained))

theorem HG2.retained_pressure_finite (h : HG2 D g A) (i : Fin D.count)
    (retained : D.core i ⊆ Aᶜ) : D.pressure g i ≠ ⊤ ∧ D.pressure g i ≠ ⊥ := by
  have identity := (h.proved_retained_equilibriumPackage i retained).pressure_identity
  change D.pressure g i = _ at identity
  rw [identity]
  exact ⟨EReal.coe_ne_top _, EReal.coe_ne_bot _⟩

/-- A named proof of the whole finite-pressure premise. -/
theorem HG2.proved_retained_pressure_finiteness (h : HG2 D g A) :
    ∀ i : {i : Fin D.count // D.core i ⊆ Aᶜ},
      D.pressure g i.val ≠ ⊤ ∧ D.pressure g i.val ≠ ⊥ :=
  fun i => h.retained_pressure_finite i.val i.property

theorem HG2.retained_equilibrium_actual_phi (h : HG2 D g A) (i : Fin D.count)
    (retained : D.core i ⊆ Aᶜ) (φ : M → ℝ)
    (agreement : EqOn g (fun x => Real.exp (φ x)) (D.core i)) :
    ThermodynamicDefinitions.IsEquilibriumState T
      (fun x => φ x - Real.log ((D.basic i).hyperbolic.unstableJacobian x))
      (D.core i) (h.proved_retained_equilibriumPackage i retained).state :=
  (h.proved_retained_equilibriumPackage i retained).equilibrium_actual_phi φ agreement

theorem HG2.retained_unique_actual_phi (h : HG2 D g A) (i : Fin D.count)
    (retained : D.core i ⊆ Aᶜ) (φ : M → ℝ)
    (agreement : EqOn g (fun x => Real.exp (φ x)) (D.core i))
    (ν : ProbabilityMeasure M)
    (equilibrium : ThermodynamicDefinitions.IsEquilibriumState T
      (fun x => φ x - Real.log ((D.basic i).hyperbolic.unstableJacobian x)) (D.core i) ν) :
    ν = (h.proved_retained_equilibriumPackage i retained).state :=
  (h.proved_retained_equilibriumPackage i retained).unique_actual_phi φ agreement ν equilibrium

end ConditionedStochasticStabilityHyperbolic.Paper
