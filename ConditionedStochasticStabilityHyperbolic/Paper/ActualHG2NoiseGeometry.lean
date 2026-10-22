module
public import ConditionedStochasticStabilityHyperbolic.Paper.ActualHG2BasinGeometry
public import ConditionedStochasticStabilityHyperbolic.Paper.ActualOriginalFixedGlobalChain
public import ConditionedStochasticStabilityHyperbolic.Paper.RegularNoiseUniformControl

/-! Literal regular perturbations and HG2 construct the full stochastic basin
geometry, including the actual graph assignment. No representation/model on
the original factor and no supplied noisy geometric certificate are needed. -/
public noncomputable section
open Set MeasureTheory Filter Bundle
open scoped Manifold ContDiff Topology NNReal Bundle
namespace ConditionedStochasticStabilityHyperbolic.Paper.ActualHG2BasinGeometry
open LeanShared Global ShiftedFiltrationGeometry RegularNoise
open ActualOriginalGlobalChain PaperHG2GreedySelection PressureFiltrationSource

/-- The only filtration input is an ordinary adapted filtration in the
computed pressure-compatible order. Strict trapping remains explicit. -/
def windowed
    {E M ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MetricSpace M] [CompactSpace M] [ChartedSpace E M]
    [IsManifold (𝓘(ℝ, E)) ∞ M]
    [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
    [MeasurableSpace M] [BorelSpace M] [Fintype ι]
    {T : M ≃ₜ M} (D0 : SpectralDecomposition (E := E) T) (g : M → ℝ) (A : Set M)
    (h : HG2 D0 g A)
    (finitePressure : ∀ i : Retained D0 A, D0.pressure g i.val ≠ ⊤ ∧ D0.pressure g i.val ≠ ⊥)
    (D : AdaptedSource T A (retainedCore D0 A) (greedy D0 g A h finitePressure).order.length)
    (index_eq : D.index = reversedVertex (greedy D0 g A h finitePressure).order)
    (strict : MapsTo T (closure A) A)
    (F : Maps (E := E) (ι := ι) T h.r) (L : Laws (ι := ι))
    (openEndpoint : OpenCubeEndpointContract (E := E) (M := M) (ι := ι))
    (φ : M → ℝ) (hφ : Measurable φ) (R : ℝ) (hR : 0 < R)
    (bound : ∀ x, Real.exp (φ x) ≤ R) :
    PositiveNoiseContinuation.WindowedGeometry (Ω := FixedControl (ι := ι))
      T A h.absorbing_open (retainedCore D0 A) (greedy D0 g A h finitePressure).order.length D
      (greedy D0 g A h finitePressure).number (greedy D0 g A h finitePressure).terminal
      (greedy D0 g A h finitePressure).selectedRoot
      (rawChain F L Aᶜ h.absorbing_open.measurableSet.compl
        (fun x => Real.exp (φ x)) (Real.measurable_exp.comp hφ) R hR bound) F.window := by
  classical
  have radii : ∀ ε : ℝ≥0, ∃ δ : ℝ, 0 < δ ∧
      (0 < ε → ε ≤ F.window → ∀ x y : M, dist (T x) y < δ →
        ∃ z : FixedControl (ι := ι), F.fixedMap ε x z = y) := by
    intro ε
    by_cases small : 0 < ε ∧ ε ≤ F.window
    · obtain ⟨δ, positive, cover⟩ := F.exists_uniform_fixed_control_radius openEndpoint ε small.1 small.2
      exact ⟨δ, positive, fun _ _ => cover⟩
    · exact ⟨1, zero_lt_one, fun he hw => (small ⟨he, hw⟩).elim⟩
  choose δ positive cover using radii
  exact {
    strict_trapping := strict
    separation := retained_separation D0 A strict
    transitive := adapted_transitive D0 g A h _ D
    noise := L.fixedLaw
    probability := fun _ => inferInstance
    open_positive := fun ε he _ => L.fixedLaw_full_support ε he
    maps := fixedRawMap F
    measurable := fixedRawMap_measurable F
    continuous := fun ε he hw => by
      simpa only [fixedRawMap, dite_eq_left (show 0 < ε ∧ ε ≤ F.window from ⟨he, hw⟩)] using
        F.fixedMap_continuous ε he hw
    potential := φ
    potential_measurable := hφ
    R := R
    R_positive := hR
    weight_bound := bound
    actual_model := fun ε => congrArg (fun C => C.killedTransition)
      (rawChain_fixed F L Aᶜ h.absorbing_open.measurableSet.compl
        (fun x => Real.exp (φ x)) (Real.measurable_exp.comp hφ) R hR bound ε)
    zero_control := zeroFixed
    zero_map := fun ε he hw x => by
      simp only [fixedRawMap, dite_eq_left (show 0 < ε ∧ ε ≤ F.window from ⟨he, hw⟩),
        Maps.fixedMap, dite_eq_left he]
      change F.family ε (fun _ => (ε : ℝ) * 0) x = T x
      have zero : (fun _ : ι => (ε : ℝ) * 0) = (0 : Control (ι := ι)) :=
        funext (fun _ => mul_zero _)
      rw [zero]
      exact F.zero_control ε he hw x
    radius := δ
    radius_positive := fun ε _ _ => positive ε
    image_ball := fun ε he hw x _ y _ near => by
      obtain ⟨z, same⟩ := cover ε he hw x y near
      exact ⟨z, by simpa only [fixedRawMap,
        dite_eq_left (show 0 < ε ∧ ε ≤ F.window from ⟨he, hw⟩)] using same⟩
    edge := fun i j => D0.edge (D.index i).val (D.index j).val
    connections := adapted_connections D0 A _ D
    assignment := adapted_assignment D0 g A h finitePressure D index_eq }

theorem continued_noise_bound
    {E M ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MetricSpace M] [CompactSpace M] [ChartedSpace E M]
    [IsManifold (𝓘(ℝ, E)) ∞ M]
    [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
    [MeasurableSpace M] [BorelSpace M] [Fintype ι]
    {T : M ≃ₜ M} (D0 : SpectralDecomposition (E := E) T) (g : M → ℝ) (A : Set M)
    (h : HG2 D0 g A)
    (finitePressure : ∀ i : Retained D0 A, D0.pressure g i.val ≠ ⊤ ∧ D0.pressure g i.val ≠ ⊥)
    (D : AdaptedSource T A (retainedCore D0 A) (greedy D0 g A h finitePressure).order.length)
    (index_eq : D.index = reversedVertex (greedy D0 g A h finitePressure).order)
    (strict : MapsTo T (closure A) A)
    (F : Maps (E := E) (ι := ι) T h.r) (L : Laws (ι := ι))
    (openEndpoint : OpenCubeEndpointContract (E := E) (M := M) (ι := ι))
    (φ : M → ℝ) (hφ : Measurable φ) (R : ℝ) (hR : 0 < R)
    (bound : ∀ x, Real.exp (φ x) ≤ R) :
    ∀ ε, 0 < ε → ∀ x z,
      dist (((windowed D0 g A h finitePressure D index_eq strict F L openEndpoint φ hφ R hR bound).continued F.window_positive).maps ε (x, z)) (T x) ≤
        F.constant * (ε : ℝ) := by
  apply PositiveNoiseContinuation.WindowedGeometry.continued_noise_bound
    (windowed D0 g A h finitePressure D index_eq strict F L openEndpoint φ hφ R hR bound) F.window_positive F.constant F.constant_positive.le
  intro ε he hw x z
  change dist (fixedRawMap F ε (x, z)) (T x) ≤ _
  simpa only [fixedRawMap, dite_eq_left (show 0 < ε ∧ ε ≤ F.window from ⟨he, hw⟩)] using
    F.fixedMap_uniform_close ε he hw x z

end ConditionedStochasticStabilityHyperbolic.Paper.ActualHG2BasinGeometry
