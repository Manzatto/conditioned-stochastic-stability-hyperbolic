module

public import LeanShared.Dynamics.BasicHyperbolicOrbitIntegralGrowth
public import LeanShared.Dynamics.BasicHyperbolicSpectralRadiusLower
public import LeanShared.Geometry.FiniteSmoothReferenceSupport
public import Mathlib.Analysis.SpecificLimits.Basic

/-! For a full-manifold mixing hyperbolic basic set the literal geometric
potential -log Jᵘ has pressure zero. Its weighted orbit integrals for g=1
are the same finite positive smooth-reference mass at every length. The
proved geometric upper and lower growth bounds therefore fix the pressure. -/

public noncomputable section
namespace LeanShared.HyperbolicBasicSet
open Set IsManifold Bundle MeasureTheory Filter
open ThermodynamicDefinitions FractionalManifoldRegularity
open scoped Manifold ContDiff BigOperators ENNReal Topology

set_option maxHeartbeats 3200000 in
theorem BasicData.full_core_pressure_one_eq_zero
    {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    [MetricSpace M] [CompactSpace M] [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace E M] [IsManifold (𝓘(ℝ, E)) ∞ M]
    [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
    {T : M ≃ₜ M} {V : Set M} (b : BasicData (E := E) T univ V)
    {r : ℝ} (regularity : 1 < r)
    (forwardRegular : Regular (E := E) (F := E) r T)
    (inverseRegular : Regular (E := E) (F := E) r T.symm)
    (mixing : MixingOn T univ)
    (reference : FiniteSmoothReferenceCharts.Data (E := E) (M := M))
    (μ : Measure E) [Measure.IsAddHaarMeasure μ] :
    pressure T (b.hyperbolic.potential (fun _ => 1)) univ = (0 : EReal) := by
  classical
  have oneFloor : (1 : ℕ) ≤ ⌊r⌋₊ :=
    Nat.le_floor (by simpa only [Nat.cast_one] using regularity.le)
  have forward : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, E)) 1 T :=
    forwardRegular.differentiable.of_le (by exact_mod_cast oneFloor)
  have inverse : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, E)) 1 T.symm :=
    inverseRegular.differentiable.of_le (by exact_mod_cast oneFloor)
  have supported : Function.support (fun _ : M => (1 : ℝ)) ⊆ closure V := by
    intro x _
    exact subset_closure (b.subset_neighborhood (mem_univ x))
  obtain ⟨P, pressureP, upper⟩ := b.exists_orbit_integral_growth forward inverse
    (fun _ => 1) continuous_const (by intro _ _; exact zero_lt_one)
    (by intro _; exact zero_le_one) supported reference μ
  let mass := (reference.measure μ) univ
  have finiteMass : mass ≠ ⊤ := measure_ne_top _ _
  have positiveMass : 0 < mass := isOpen_univ.measure_pos (reference.measure μ) b.nonempty
  have positiveRealMass : 0 < mass.toReal := ENNReal.toReal_pos positiveMass.ne' finiteMass
  have unitRegular : Regular (E := E) (F := ℝ) 1 (fun _ : M => (1 : ℝ)) := {
    nonnegative := zero_le_one
    differentiable := by simpa using (contMDiff_const :
      ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, ℝ)) 1 (fun _ : M => (1 : ℝ)))
    holder := by norm_num }
  let pairing : ℂ →L[ℂ] ℂ := (mass.toReal : ℂ) • (1 : ℂ →L[ℂ] ℂ)
  have lower := b.exp_pressure_le_spectralRadius_from_coefficients regularity
    (show (0 : ℝ) < 1 from zero_lt_one) forwardRegular inverseRegular mixing reference μ
    (fun _ => 1) unitRegular (by intro _ _; exact zero_lt_one) P pressureP
    (1 : ℂ →L[ℂ] ℂ) pairing (1 : ℂ) (fun n => by
      simp [pairing, mass, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg ENNReal.toReal_nonneg, ENNReal.ofReal_toReal finiteMass])
  have nonpositive : P ≤ 0 := by
    have exponential : Real.exp P ≤ 1 := ENNReal.ofReal_le_one.mp (by simpa using lower)
    exact Real.exp_le_one_iff.mp exponential
  have nonnegative : 0 ≤ P := by
    by_contra contrary
    have negative : P < 0 := lt_of_not_ge contrary
    have small : Real.exp P < 1 := Real.exp_lt_one_iff.mpr negative
    let R := (Real.exp P + 1) / 2
    have above : Real.exp P < R := by dsimp only [R]; linarith
    have positiveR : 0 < R := (Real.exp_pos P).trans above
    have smallR : R < 1 := by dsimp only [R]; linarith
    obtain ⟨C, nonnegativeC, bound⟩ := upper R above
    have realBound (n : ℕ) : mass.toReal ≤ C * R ^ n := by
      have raw := bound n
      simp only [Finset.prod_const_one, ENNReal.ofReal_one, lintegral_const, one_mul] at raw
      have toReal := ENNReal.toReal_mono ENNReal.ofReal_ne_top raw
      simpa only [ENNReal.toReal_ofReal (mul_nonneg nonnegativeC (pow_nonneg positiveR.le n))]
        using toReal
    have vanish : Tendsto (fun n : ℕ => C * R ^ n) atTop (𝓝 0) := by
      simpa only [mul_zero] using
        (tendsto_const_nhds (x := C)).mul
          (tendsto_pow_atTop_nhds_zero_of_lt_one positiveR.le smallR)
    have impossible : mass.toReal ≤ 0 := le_of_tendsto_of_tendsto
      (tendsto_const_nhds (x := mass.toReal)) vanish (Eventually.of_forall realBound)
    exact positiveRealMass.not_ge impossible
  have zero : P = 0 := le_antisymm nonpositive nonnegative
  simpa only [zero, EReal.coe_zero] using pressureP

end LeanShared.HyperbolicBasicSet
