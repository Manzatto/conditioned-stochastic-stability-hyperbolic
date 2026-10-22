module

public import LeanShared.Dynamics.ComplexOneSidedPeripheralPhase
public import LeanShared.Dynamics.ComplexOneSidedUnitalLasota

/-! Literal mixing graph connections force every nonzero peripheral
continuous eigenfunction to be a constant, at eigenvalue one.  The same
conclusion transfers faithfully to the actual complex Banach operator.
-/

public noncomputable section
namespace LeanShared.BilateralShadowingCoding
open Set Function Filter Topology
variable {A : Type*} [TopologicalSpace A] [DiscreteTopology A] [CompactSpace A] [Fintype A]
  {R : A → A → Prop} [Nonempty (FuturePath R)]

theorem complex_unital_peripheral_eigenfunction_constant (ψ : C(FuturePath R, ℝ)) (f : C(FuturePath R, ℂ))
    (eigenvalue : ℂ) (unit : ‖eigenvalue‖ = 1) (nonzero : f ≠ 0)
    (unital : weightedTransferOperator ψ 1 = 1)
    (eigen : complexWeightedTransferOperator ψ f = eigenvalue • f)
    (N : ℕ)
    (connections : ∀ i j : A, ∃ p : Path R, p.val 0 = i ∧ p.val N = j)
    (nextConnections : ∀ i j : A, ∃ p : Path R, p.val 0 = i ∧ p.val (N + 1) = j) :
    eigenvalue = 1 ∧ ∃ c : ℂ, ∀ a, f a = c := by
  have eigenvalueOne := complex_unital_peripheral_eigenvalue_eq_one ψ f eigenvalue unit nonzero
    unital eigen N connections nextConnections
  obtain ⟨M, _, modulus⟩ := complex_unital_eigenfunction_constant_modulus ψ f eigenvalue unit unital eigen N connections
  have phase := complex_unital_eigenfunction_predecessor_phase ψ f eigenvalue unit unital eigen M modulus
  obtain ⟨b⟩ := ‹Nonempty (FuturePath R)›
  refine ⟨eigenvalueOne, f b, ?_⟩
  intro a
  obtain ⟨c, convergence, preimages⟩ := exists_convergent_future_prehistories N connections a b
  have values (m : ℕ) : f (c m) = f b := by
    have identity := future_phase_prehistory f eigenvalue phase (m + N) (c m)
    simpa only [preimages m, eigenvalueOne, one_pow, one_mul] using identity
  have firstLimit := f.continuous.continuousAt.tendsto.comp convergence
  have secondLimit : Tendsto (fun m => f (c m)) atTop (𝓝 (f b)) := by
    simpa only [values] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => f b) atTop (𝓝 (f b)))
  exact tendsto_nhds_unique firstLimit secondLimit

theorem complexUnitalVariation_peripheral_simple (ψ : C(FuturePath R, ℝ)) (θ : ℝ)
    (positiveθ : 0 < θ) (smallθ : θ < 1) (Cψ : ℝ) (nonnegativeψ : 0 ≤ Cψ)
    (potential : ∀ n a b, PrefixAgreement a b n → |ψ b - ψ a| ≤ Cψ * θ ^ n)
    (unital : weightedTransferOperator ψ 1 = 1)
    (v : complexVariationGraph R θ) (nonzero : v ≠ 0) (eigenvalue : ℂ) (unit : ‖eigenvalue‖ = 1)
    (eigen : complexUnitalVariationOperator ψ θ positiveθ smallθ Cψ nonnegativeψ potential unital v = eigenvalue • v)
    (N : ℕ)
    (connections : ∀ i j : A, ∃ p : Path R, p.val 0 = i ∧ p.val N = j)
    (nextConnections : ∀ i j : A, ∃ p : Path R, p.val 0 = i ∧ p.val (N + 1) = j) :
    eigenvalue = 1 ∧ ∃ c : ℂ, ∀ a, complexVariationPhysical θ v a = c := by
  have physicalNonzero : complexVariationPhysical θ v ≠ 0 := by
    intro zero
    apply nonzero
    apply complexVariationPhysical_injective θ positiveθ
    simpa only [map_zero] using zero
  have physicalEigen := congrArg (complexVariationPhysical θ) eigen
  change complexVariationPhysical θ
    (complexUnitalVariationTransfer ψ θ positiveθ smallθ Cψ nonnegativeψ potential unital v) = _ at physicalEigen
  rw [complexUnitalVariationTransfer_physical, map_smul] at physicalEigen
  exact complex_unital_peripheral_eigenfunction_constant ψ (complexVariationPhysical θ v) eigenvalue unit
    physicalNonzero unital physicalEigen N connections nextConnections

end LeanShared.BilateralShadowingCoding
