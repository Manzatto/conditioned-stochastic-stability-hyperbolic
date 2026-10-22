module

public import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
public import Mathlib.Basic.Real.Basic
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Dynamics.FixedPoints.Basic

/-! Nonnegative bounded orbit products have genuine finite real integrals.
Appending j departure weights costs at most G^j, uniformly in the preceding
length. These facts also identify the extended-real geometric integrals. -/
public noncomputable section
namespace LeanShared.BoundedWeightedOrbitIntegrals
open Set MeasureTheory
open scoped BigOperators

variable {X : Type*} [TopologicalSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X] (σ : Measure X) [IsFiniteMeasure σ]
  (T : X → X) (continuousT : Continuous T) (g : X → ℝ) (continuousG : Continuous g)

omit [TopologicalSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X] in
@[expose] def product (n : ℕ) (x : X) : ℝ := ∏ j ∈ Finset.range n, g (T^[j] x)

omit [TopologicalSpace X] [CompactSpace X] [BorelSpace X] [IsFiniteMeasure σ] in
@[expose] def integral (n : ℕ) : ℝ := ∫ x, product T g n x ∂σ

include continuousT continuousG in
omit [CompactSpace X] [MeasurableSpace X] [BorelSpace X] in
theorem continuous_product (n : ℕ) : Continuous (product T g n) :=
  continuous_finsetProd _ (fun j _ => continuousG.comp (continuousT.iterate j))

include continuousT continuousG in
theorem integrable_product (n : ℕ) : Integrable (product T g n) σ :=
  (continuous_product T continuousT g continuousG n).integrable_of_hasCompactSupport
    (isClosed_tsupport _).isCompact

omit [TopologicalSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X] in
theorem product_nonnegative (nonnegative : ∀ x, 0 ≤ g x) (n : ℕ) (x : X) :
    0 ≤ product T g n x := Finset.prod_nonneg (fun _j _ => nonnegative _)

omit [TopologicalSpace X] [CompactSpace X] [BorelSpace X] [IsFiniteMeasure σ] in
theorem integral_nonnegative (nonnegative : ∀ x, 0 ≤ g x) (n : ℕ) :
    0 ≤ integral σ T g n :=
  MeasureTheory.integral_nonneg (product_nonnegative T g nonnegative n)

include continuousT continuousG in
theorem lintegral_eq (nonnegative : ∀ x, 0 ≤ g x) (n : ℕ) :
    (∫⁻ x, ENNReal.ofReal (product T g n x) ∂σ) =
      ENNReal.ofReal (integral σ T g n) :=
  (ofReal_integral_eq_lintegral_ofReal
    (integrable_product σ T continuousT g continuousG n)
    (Filter.Eventually.of_forall (product_nonnegative T g nonnegative n))).symm

omit [TopologicalSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X] in
theorem product_append_le (nonnegative : ∀ x, 0 ≤ g x)
    (G : ℝ) (_nonnegativeG : 0 ≤ G) (bounded : ∀ x, g x ≤ G)
    (m j : ℕ) (x : X) :
    product T g (m + j) x ≤ G ^ j * product T g m x := by
  classical
  unfold product
  rw [Finset.prod_range_add]
  have tail : (∏ k ∈ Finset.range j, g (T^[m + k] x)) ≤ G ^ j := by
    simpa using Finset.prod_le_prod₀ (s := Finset.range j)
      (fun k _ => nonnegative _) (fun k _ => bounded _)
  have first : 0 ≤ ∏ k ∈ Finset.range m, g (T^[k] x) :=
    Finset.prod_nonneg (fun k _ => nonnegative _)
  simpa only [mul_comm] using mul_le_mul_of_nonneg_left tail first

include continuousT continuousG in
theorem integral_append_le (nonnegative : ∀ x, 0 ≤ g x)
    (G : ℝ) (nonnegativeG : 0 ≤ G) (bounded : ∀ x, g x ≤ G) (m j : ℕ) :
    integral σ T g (m + j) ≤ G ^ j * integral σ T g m := by
  calc
    integral σ T g (m + j) ≤ ∫ x, G ^ j * product T g m x ∂σ :=
      integral_mono (integrable_product σ T continuousT g continuousG (m + j))
        ((integrable_product σ T continuousT g continuousG m).const_mul (G ^ j))
        (product_append_le T g nonnegative G nonnegativeG bounded m j)
    _ = G ^ j * integral σ T g m := integral_const_mul _ _

end LeanShared.BoundedWeightedOrbitIntegrals
