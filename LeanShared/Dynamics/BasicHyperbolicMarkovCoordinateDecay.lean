module

public import LeanShared.Dynamics.BasicHyperbolicFiniteToOneMarkovCoding
public import LeanShared.Dynamics.BasicHyperbolicFiniteWindowCoordinates
public import LeanShared.Dynamics.MarkovCodingMatchingWindow
public import LeanShared.Geometry.CoherentChartSourceRadius

/-! Matching refined symbolic windows give exponentially small actual
normalized hyperbolic coordinates.  The rate comes from the proved
finite-window nonlinear contraction.  No Lipschitz comparison with an
arbitrary supplied compatible metric is asserted.
-/

public noncomputable section
namespace LeanShared.HyperbolicBasicSet
open Set IsManifold Bundle Function ThermodynamicDefinitions
open BilateralShadowingCoding ExpansiveLocalProduct FiniteClosedRefinement MarkovFinitePathRealization
open BilateralHomeomorphismOrbit CoherentCenteredCoordinateMaps
open scoped Topology Manifold ContDiff

theorem BasicData.exists_markov_coordinate_decay
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MetricSpace M] [CompactSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ,E)) ∞ M]
    [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ,E)) x)]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace (𝓘(ℝ,E)) x)]
    {T : M ≃ₜ M} {Λ V : Set M} (b : BasicData (E := E) T Λ V)
    (forward : ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 T)
    (inverse : ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 T.symm) :
    let S := invariantCoreHomeomorphism T Λ b.hyperbolic.invariant
    ∃ frame : IsometricFraming b.hyperbolic, ∃ block : ℕ, 0 < block ∧
      ∃ B : ℝ, ∃ d : CompactCoherentCenteredCharts.Data (E := E)
        (P := EuclideanSpace ℝ (Fin frame.unstableDimension) × EuclideanSpace ℝ (Fin frame.stableDimension))
        (Q := EuclideanSpace ℝ (Fin frame.unstableDimension) × EuclideanSpace ℝ (Fin frame.stableDimension))
        ((T ^ block : M ≃ₜ M) : M → M) Λ B (1 / 16),
      ∃ N : ℕ, ∃ rectangles : ((Fin N ⊕ ((Fin N × Fin N) × Bool)) → Bool) → Set Λ,
      ∃ code : Path (Transition S rectangles) → Λ,
        MarkovCodingProperties S rectangles code ∧
        ∀ n : ℕ, ∀ a a' : Path (Transition S rectangles),
          (∀ k : ℤ, -((block * n : ℕ) : ℤ) ≤ k → k ≤ (block * n : ℕ) → a.val k = a'.val k) →
          (code a').val ∈ (chart d (code a)).source ∧
          ‖coordinate d frame.whole (code a) (code a').val‖ ≤ (3 / 8 : ℝ) ^ n * (2 * d.radius) := by
  let S := invariantCoreHomeomorphism T Λ b.hyperbolic.invariant
  have forwardS (x : Λ) : (S x).val = T x.val := rfl
  obtain ⟨frame, block, positiveBlock, B, d, η, positiveη, decay⟩ :=
    b.exists_finite_window_coordinates forward inverse
  obtain ⟨ρ, positiveρ, chartSource⟩ := exists_chart_source_radius d
  let scale := min η ρ / 4
  have positiveScale : 0 < scale := div_pos (lt_min positiveη positiveρ) (by norm_num)
  have smallEta : scale < η := by have bound := min_le_left η ρ; dsimp only [scale]; linarith
  have smallRho : scale < ρ := by have bound := min_le_right η ρ; dsimp only [scale]; linarith
  obtain ⟨N, rectangles, smallRectangles, code, properties⟩ :=
    b.exists_finite_to_one_markov_coding forward inverse scale positiveScale
  have windows := properties.windows
  have diameter : ∀ i, ∀ x ∈ rectangles i, ∀ y ∈ rectangles i, dist x y ≤ scale :=
    fun i x hx y hy => (smallRectangles i x hx y hy).le
  have forwardBlock (x : Λ) : ((S ^ block) x).val = (T ^ block) x.val := by
    rw [DiffeomorphismIterates.coe_pow, DiffeomorphismIterates.coe_pow]
    exact iterate_coe_restriction S forwardS block x
  refine ⟨frame, block, positiveBlock, B, d, N, rectangles, code, properties, ?_⟩
  intro n a a' matching
  have closeZero := coding_matching_window_close S rectangles scale diameter code windows a a'
    (block * n) matching 0 (by omega) (by omega)
  simp only [zpow_zero, Homeomorph.one_apply] at closeZero
  refine ⟨chartSource (code a) (code a').val (closeZero.trans_lt smallRho), ?_⟩
  let reference : ℤ → Λ := fun j => BilateralHomeomorphismOrbit.orbit (S ^ block) (code a) (j - n)
  let actualOrbit : ℤ → M := fun j => (BilateralHomeomorphismOrbit.orbit (S ^ block) (code a') (j - n)).val
  have sampledStep (p : Λ) (j : ℤ) :
      (T ^ block) (BilateralHomeomorphismOrbit.orbit (S ^ block) p (j + 1 - n)).val = (BilateralHomeomorphismOrbit.orbit (S ^ block) p (j - n)).val := by
    rw [← forwardBlock]
    have index : j + 1 - (n : ℤ) = (j - (n : ℤ)) + 1 := by omega
    exact congrArg Subtype.val (by simpa only [index] using step (S ^ block) p (j - n))
  have referenceStep (j : ℤ) : (T ^ block) (reference (j + 1)).val = (reference j).val :=
    sampledStep (code a) j
  have actualStep (j : ℕ) (_ : j < 2 * n) :
      (T ^ block) (actualOrbit (j + 1)) = actualOrbit j := by
    simpa only [actualOrbit, Nat.cast_add, Nat.cast_one] using sampledStep (code a') j
  have sampledTime (p : Λ) (j : ℤ) :
      BilateralHomeomorphismOrbit.orbit (S ^ block) p (j - n) = (S ^ ((block : ℤ) * ((n : ℤ) - j))) p := by
    change ((S ^ block) ^ (-(j - n))) p = _
    rw [← zpow_natCast, ← zpow_mul]
    exact congrArg (fun k : ℤ => (S ^ k) p) (by ring)
  have close (j : ℕ) (bound : j ≤ 2 * n) : dist (reference j).val (actualOrbit j) < η := by
    let k : ℤ := (block : ℤ) * ((n : ℤ) - j)
    have lower : -((block * n : ℕ) : ℤ) ≤ k := by
      have result := mul_le_mul_of_nonneg_left (by omega : -(n : ℤ) ≤ (n : ℤ) - j) (Nat.cast_nonneg block)
      simpa only [Nat.cast_mul, mul_neg] using result
    have upper : k ≤ ((block * n : ℕ) : ℤ) := by
      have result := mul_le_mul_of_nonneg_left (by omega : (n : ℤ) - j ≤ n) (Nat.cast_nonneg block)
      simpa only [Nat.cast_mul] using result
    have estimate := coding_matching_window_close S rectangles scale diameter code windows a a'
      (block * n) matching k lower upper
    change dist (BilateralHomeomorphismOrbit.orbit (S ^ block) (code a) ((j : ℤ) - n))
      (BilateralHomeomorphismOrbit.orbit (S ^ block) (code a') ((j : ℤ) - n)) < η
    rw [sampledTime, sampledTime]
    exact estimate.trans_lt smallEta
  have estimate := decay reference referenceStep actualOrbit (2 * n) actualStep close n (by omega)
  have exponent : min n (2 * n - n) = n := by omega
  simpa only [reference, actualOrbit, sub_self, BilateralHomeomorphismOrbit.zero, exponent] using estimate

end LeanShared.HyperbolicBasicSet
