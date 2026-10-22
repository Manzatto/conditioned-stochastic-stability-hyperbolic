module
public import LeanShared.Dynamics.BasicHyperbolicNormedWeightedPeriodicAsymptotic
public import LeanShared.Dynamics.BasicHyperbolicLefschetzAsymptotics

/-! The periodic Lefschetz sum normalized by the exponential of the pressure tends to one. -/
public noncomputable section
namespace LeanShared.HyperbolicBasicSet
open Set Bundle IsManifold Filter FractionalManifoldRegularity ThermodynamicDefinitions
open scoped Topology Manifold ContDiff
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MetricSpace M] [CompactSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ,E)) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ,E)) x)]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace (𝓘(ℝ,E)) x)]
  {T : M ≃ₜ M} {Λ V : Set M}

theorem BasicData.lefschetz_ratio_tendsto
    (b : BasicData (E := E) T Λ V)
    {r q : ℝ} (regularity : 1 < r) (weightOrder : 0 < q)
    (forwardRegular : Regular (E := E) (F := E) r T)
    (inverseRegular : Regular (E := E) (F := E) r T.symm)
    (mixing : MixingOn T Λ) (g : M → ℝ)
    (weightRegular : Regular (E := E) (F := ℝ) q g)
    (weightPositive : ∀ x ∈ Λ, 0 < g x)
    (forward : ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 T)
    (inverse : ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 T.symm) :
    ∃ P : ℝ, pressure T (b.hyperbolic.potential g) Λ = (P : EReal) ∧
      Tendsto (fun p : ℕ => b.periodicLefschetzSum forward inverse g p / Real.exp P ^ p) atTop
        (𝓝 1) := by
  obtain ⟨P, hP, τ, D, τ0, τ1, _, asym⟩ := b.actual_normed_weighted_periodic_asymptotic
    regularity weightOrder forwardRegular inverseRegular mixing g weightRegular weightPositive
    forward inverse
  refine ⟨P, hP, ?_⟩
  have partLim : Tendsto (fun p : ℕ =>
      b.periodicPartitionSum forward inverse (b.hyperbolic.potential g) p / Real.exp P ^ p)
      atTop (𝓝 1) := by
    rw [← tendsto_add_atTop_iff_nat 1, tendsto_iff_norm_sub_tendsto_zero]
    have small : Tendsto (fun n : ℕ => D * τ ^ (n + 1)) atTop (𝓝 0) := by
      have := ((tendsto_pow_atTop_nhds_zero_of_lt_one τ0.le τ1).comp
        (tendsto_add_atTop_nat 1)).const_mul D
      simpa using this
    refine squeeze_zero (fun _ => norm_nonneg _) (fun n => ?_) small
    rw [Real.norm_eq_abs, div_eq_inv_mul]
    exact asym n
  obtain ⟨C, _, err⟩ := b.normalized_lefschetz_partition_error forward inverse g weightPositive
    (Real.exp P) (Real.exp_pos P)
  have errLim : Tendsto (fun p : ℕ => C * b.hyperbolic.contraction ^ p *
      (b.periodicPartitionSum forward inverse (b.hyperbolic.potential g) p / Real.exp P ^ p))
      atTop (𝓝 0) := by
    have := ((tendsto_pow_atTop_nhds_zero_of_lt_one b.hyperbolic.contraction_pos.le
      b.hyperbolic.contraction_lt_one).const_mul C).mul partLim
    simpa using this
  have diff : Tendsto (fun p : ℕ => b.periodicLefschetzSum forward inverse g p / Real.exp P ^ p -
      b.periodicPartitionSum forward inverse (b.hyperbolic.potential g) p / Real.exp P ^ p)
      atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    exact squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _)
      (err.mono fun p hp => by rw [Real.norm_eq_abs]; exact hp) errLim
  simpa using diff.add partLim

end LeanShared.HyperbolicBasicSet
