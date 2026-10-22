module
public import LeanShared.Dynamics.BasicHyperbolicWeightedBowenUpper
public import LeanShared.Dynamics.BasicHyperbolicSeparatedSpanning
public import LeanShared.Dynamics.HyperbolicPotentialContinuity
public import LeanShared.MeasureTheory.FiniteWeightedCoverIntegral

/-! Integrals over arbitrary sets of core-shadowed finite orbits are bounded
by the literal separated partition sum of the basic set. -/
public noncomputable section
namespace LeanShared.HyperbolicBasicSet
open Set IsManifold Bundle MeasureTheory ThermodynamicDefinitions
open scoped Manifold ContDiff NNReal ENNReal BigOperators

theorem BasicData.exists_shadowed_integral_upper
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    [MetricSpace M] [CompactSpace M] [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace E M] [IsManifold (𝓘(ℝ, E)) ∞ M]
    [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
    {T : M ≃ₜ M} {Λ V : Set M} (b : BasicData (E := E) T Λ V)
    (forward : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, E)) 1 T)
    (inverse : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, E)) 1 T.symm)
    (g : M → ℝ) (continuous : Continuous g) (positive : ∀ x ∈ Λ, 0 < g x)
    (γ : ℝ) (hγ : 1 < γ) (ε : ℝ) (hε : 0 < ε)
    (referenceMeasure : FiniteSmoothReferenceCharts.Data (E := E) (M := M))
    (μ : Measure E) [Measure.IsAddHaarMeasure μ] :
    ∃ N : ℕ, 0 < N ∧ ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∃ η : ℝ, 0 < η ∧
      ∀ p : ℕ, 0 < p → ∀ S : Set M,
        (∀ y ∈ S, ∃ x : Λ, ∀ j ≤ N*p,
          dist ((T : M → M)^[j] y) ((T : M → M)^[j] x.val) < η) →
        (∫⁻ y in S, ENNReal.ofReal (∏ j ∈ Finset.range (N*p), g ((T : M → M)^[j] y))
          ∂(referenceMeasure.measure μ)) ≤
        C * ENNReal.ofReal (γ^p) * ENNReal.ofReal (Real.exp (ε*(N*p))) *
          separatedPartitionSum T (b.hyperbolic.potential g) Λ (N*p+1) η := by
  classical
  obtain ⟨N, positiveN, C, finiteC, r, positiveR, localBound⟩ :=
    b.exists_weighted_bowen_integral_upper forward inverse g continuous positive γ hγ ε hε
      referenceMeasure μ
  have cont := b.hyperbolic.continuousOn_potential forward
    (inverse.mdifferentiable (by norm_num)) g continuous.continuousOn positive
  obtain ⟨m, lower⟩ := b.hyperbolic.compact.bddBelow_image cont
  have finiteExp : ENNReal.ofReal (Real.exp (-m)) ≠ ⊤ := ENNReal.ofReal_ne_top
  refine ⟨N, positiveN, C*ENNReal.ofReal (Real.exp (-m)),
    ENNReal.mul_ne_top finiteC finiteExp, r/2, half_pos positiveR, fun p hp S shadow => ?_⟩
  let n := N*p
  let φ := b.hyperbolic.potential g
  obtain ⟨s, separated, spans⟩ := b.exists_separated_spanning forward inverse
    (n+1) (r/2) (half_pos positiveR)
  let W := fun x : M => {y | ∀ j ≤ n,
    dist ((T : M → M)^[j] y) ((T : M → M)^[j] x) < r}
  have cover : ∀ y ∈ S, ∃ x ∈ s, y ∈ W x := by
    intro y hy
    obtain ⟨z, close⟩ := shadow y hy
    obtain ⟨x, hx, traces⟩ := spans z.val z.property
    refine ⟨x,hx,fun j hj => ?_⟩
    have first := close j hj
    have second := traces j (by omega)
    exact (dist_triangle _ _ _).trans_lt (by linarith)
  have invariant : MapsTo (T : M → M) Λ Λ := image_subset_iff.mp b.hyperbolic.invariant.subset
  have endpoint (x : M) (hx : x ∈ s) :
      ENNReal.ofReal (Real.exp (orbitSum T φ n x)) ≤
      ENNReal.ofReal (Real.exp (-m)) * ENNReal.ofReal (Real.exp (orbitSum T φ (n+1) x)) := by
    have low : m ≤ φ ((T : M → M)^[n] x) :=
      lower ⟨(T : M → M)^[n] x, invariant.iterate n (separated.1 x hx), rfl⟩
    have sum : orbitSum T φ (n+1) x = orbitSum T φ n x + φ ((T : M → M)^[n] x) := by
      exact Finset.sum_range_succ _ _
    have energy : orbitSum T φ n x ≤ -m + orbitSum T φ (n+1) x := by rw [sum]; linarith
    have expBound := ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr energy)
    rw [Real.exp_add, ENNReal.ofReal_mul (Real.exp_pos _).le] at expBound
    exact expBound
  have partition : (∑ x ∈ s, ENNReal.ofReal (Real.exp (orbitSum T φ n x))) ≤
      ENNReal.ofReal (Real.exp (-m)) * separatedPartitionSum T φ Λ (n+1) (r/2) := by
    calc
      _ ≤ ∑ x ∈ s, ENNReal.ofReal (Real.exp (-m)) *
        ENNReal.ofReal (Real.exp (orbitSum T φ (n+1) x)) := Finset.sum_le_sum endpoint
      _ = ENNReal.ofReal (Real.exp (-m)) *
        ∑ x ∈ s, ENNReal.ofReal (Real.exp (orbitSum T φ (n+1) x)) := (Finset.mul_sum _ _ _).symm
      _ ≤ _ := mul_le_mul le_rfl
        (le_iSup_of_le s (by simp only [iSup_pos separated]; exact le_rfl)) bot_le bot_le
  let K := C * ENNReal.ofReal (γ^p) * ENNReal.ofReal (Real.exp (ε*n))
  calc
    _ ≤ ∑ x ∈ s, ∫⁻ y in W x,
        ENNReal.ofReal (∏ j ∈ Finset.range n, g ((T : M → M)^[j] y))
        ∂(referenceMeasure.measure μ) :=
      FiniteWeightedCoverIntegral.set_integral_le_sum _ s W S _ cover
    _ ≤ ∑ x ∈ s, K*ENNReal.ofReal (Real.exp (orbitSum T φ n x)) := by
      apply Finset.sum_le_sum
      intro x hx
      have upper := localBound p hp ⟨x,separated.1 x hx⟩
      simpa only [W,K,φ,n,Nat.cast_mul] using upper
    _ = K * ∑ x ∈ s, ENNReal.ofReal (Real.exp (orbitSum T φ n x)) := (Finset.mul_sum _ _ _).symm
    _ ≤ K * (ENNReal.ofReal (Real.exp (-m)) * separatedPartitionSum T φ Λ (n+1) (r/2)) :=
      mul_le_mul le_rfl partition bot_le bot_le
    _ = _ := by dsimp [K,n,φ]; simp only [Nat.cast_mul]; ac_rfl

end LeanShared.HyperbolicBasicSet
