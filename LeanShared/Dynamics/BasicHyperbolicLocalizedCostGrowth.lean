module
public import LeanShared.Dynamics.HyperbolicLocalizedNativeCost
public import LeanShared.Dynamics.BasicHyperbolicCorePartitionUpper

/-! The actual ambient pressure bounds the total localized native costs
over every finite separated family of core orbit tubes. The cutoffs and
endpoint observation add no exponential combinatorial loss. -/
@[expose] public noncomputable section
namespace LeanShared.HyperbolicBasicSet
open Set IsManifold Bundle ThermodynamicDefinitions FiniteSmoothCapturePartition PressureCoverRefinement Filter
open scoped Manifold ContDiff BigOperators Topology ENNReal
attribute [local instance] Classical.propDecidable
variable {E M I : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MetricSpace M] [CompactSpace M] [ChartedSpace E M]
  [IsManifold (𝓘(ℝ,E)) ∞ M] [Fintype I]
  [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ,E)) x)]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace (𝓘(ℝ,E)) x)]
  {T : M ≃ₜ M} {Λ V : Set M} {v : I → Set M}

theorem BasicData.eventual_localized_native_cost_growth (b : BasicData (E := E) T Λ V)
    (forward : ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 T)
    (inverse : ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 T.symm)
    (g : M → ℝ) (continuous : ContinuousOn g Λ) (positive : ∀ x ∈ Λ, 0 < g x)
    (d : FiniteSmoothCapturePartition.Data (E := E) Λ v) (capture : Λ ⊆ d.capture) :
    ∃ P : ℝ, pressure T (b.hyperbolic.potential g) Λ = (P : EReal) ∧
      ∀ ε : ℝ, 0 < ε → ∃ ρ C : ℝ, 0 < ρ ∧ 0 < C ∧
        ∀ᶠ N : ℕ in atTop, ∀ centers : Finset M, Separated T Λ (N+1) ρ centers →
          (∑ x ∈ centers, ∑ labels : Fin (N+1) → I,
            domainCoefficient Λ (BowenOpenCoverCoefficient.orbitBall T (N+1) ρ x)
              (b.hyperbolic.localizedNativeCost d g N labels)) ≤
            C * Real.exp ((N : ℝ) * (P+ε)) := by
  have potential := b.hyperbolic.continuousOn_potential forward
    (inverse.mdifferentiable one_ne_zero) g continuous positive
  obtain ⟨P,pressureP,upper⟩ := b.eventual_core_partition_exponential_upper forward inverse
    (b.hyperbolic.potential g) potential
  obtain ⟨B,boundPotential⟩ := b.hyperbolic.compact.exists_bound_of_continuousOn potential
  have invariant : MapsTo T Λ Λ := image_subset_iff.mp b.hyperbolic.invariant.subset
  refine ⟨P,pressureP,fun ε positiveε => ?_⟩
  let δ := ε/3
  have positiveδ : 0 < δ := div_pos positiveε (by norm_num)
  obtain ⟨ρ,positiveρ,localCost⟩ := b.hyperbolic.exists_localized_native_cost_radius forward
    (inverse.mdifferentiable one_ne_zero) g continuous positive d capture positiveδ
  let C := Real.exp (B+P+2*δ)
  refine ⟨ρ,C,positiveρ,Real.exp_pos _,?_⟩
  filter_upwards [upper ρ positiveρ δ positiveδ] with N partitionBound
  intro centers separated
  have energy (x : M) (hx : x ∈ centers) :
      Real.exp (orbitSum T (b.hyperbolic.potential g) N x) ≤
        Real.exp B * Real.exp (orbitSum T (b.hyperbolic.potential g) (N+1) x) := by
    have bounded := boundPotential ((T : M → M)^[N] x) (invariant.iterate N (separated.1 x hx))
    rw [Real.norm_eq_abs] at bounded
    have lower := neg_abs_le (b.hyperbolic.potential g ((T : M → M)^[N] x))
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have next : orbitSum T (b.hyperbolic.potential g) (N+1) x =
        orbitSum T (b.hyperbolic.potential g) N x +
          b.hyperbolic.potential g ((T : M → M)^[N] x) := Finset.sum_range_succ _ _
    rw [next]
    linarith
  have energyPartition : ENNReal.ofReal
      (∑ x ∈ centers, Real.exp (orbitSum T (b.hyperbolic.potential g) (N+1) x)) ≤
        separatedPartitionSum T (b.hyperbolic.potential g) Λ (N+1) ρ := by
    rw [ENNReal.ofReal_sum_of_nonneg (fun _ _ => Real.exp_nonneg _)]
    exact le_iSup_of_le centers (le_iSup_of_le separated le_rfl)
  have realPartition := (ENNReal.ofReal_le_ofReal_iff (Real.exp_nonneg _)).mp
    (energyPartition.trans partitionBound)
  let Q := Real.exp (δ * ((N : ℝ)+1)) * Real.exp ((N : ℝ)*δ)
  have nonnegativeQ : 0 ≤ Q := mul_nonneg (Real.exp_nonneg _) (Real.exp_nonneg _)
  calc
    _ ≤ ∑ x ∈ centers, Q * Real.exp (orbitSum T (b.hyperbolic.potential g) N x) := by
      apply Finset.sum_le_sum
      intro x hx
      exact localCost N x (separated.1 x hx)
    _ = Q * ∑ x ∈ centers, Real.exp (orbitSum T (b.hyperbolic.potential g) N x) :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ Q * ∑ x ∈ centers,
        (Real.exp B * Real.exp (orbitSum T (b.hyperbolic.potential g) (N+1) x)) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum energy) nonnegativeQ
    _ = Q * Real.exp B *
        (∑ x ∈ centers, Real.exp (orbitSum T (b.hyperbolic.potential g) (N+1) x)) := by
      rw [← Finset.mul_sum]
      exact (mul_assoc Q _ _).symm
    _ ≤ Q * Real.exp B * Real.exp ((((N+1 : ℕ) : ℝ))*(P+δ)) :=
      mul_le_mul_of_nonneg_left realPartition (mul_nonneg nonnegativeQ (Real.exp_nonneg _))
    _ = C * Real.exp ((N : ℝ)*(P+ε)) := by
      dsimp only [Q,C,δ]
      simp only [Nat.cast_add,Nat.cast_one]
      rw [← Real.exp_add,← Real.exp_add,← Real.exp_add,← Real.exp_add]
      congr 1
      ring

end LeanShared.HyperbolicBasicSet
