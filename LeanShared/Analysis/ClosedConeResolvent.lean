module

public import LeanShared.Analysis.SpectralRadiusNeumannSeries
public import LeanShared.Analysis.AnalyticResolvent
public import LeanShared.Analysis.PositiveRealizedTransferCone
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NoncommRing

/-! Real exterior resolvents preserve a closed positive cone in the actual
Banach norm. If a positive boundary value is regular, this positivity
continues slightly to its left by a second positive Neumann expansion. -/

public noncomputable section
open Set Filter
open scoped Topology

namespace LeanShared.ClosedConeResolvent
variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H] [CompleteSpace H]
  (C : Set H) (closed : IsClosed C) (zero : (0 : H) ∈ C)
  (add : ∀ {x y}, x ∈ C → y ∈ C → x + y ∈ C)
  (smul : ∀ (r : ℝ), 0 ≤ r → ∀ {x}, x ∈ C → (r : ℂ) • x ∈ C)

omit [NormedSpace ℂ H] [CompleteSpace H] in
include zero add in
theorem sum_mem {I : Type*} (s : Finset I) (f : I → H)
    (mem : ∀ i ∈ s, f i ∈ C) : (∑ i ∈ s, f i) ∈ C := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using zero
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact add (mem i (Finset.mem_insert_self i s))
      (ih (fun j hj => mem j (Finset.mem_insert_of_mem hj)))

omit [CompleteSpace H] in
theorem pow_mem (P : H →L[ℂ] H) (positive : MapsTo P C C)
    {x : H} (mem : x ∈ C) (n : ℕ) : (P ^ n) x ∈ C := by
  induction n with
  | zero => simpa only [pow_zero, one_apply_eq_self] using mem
  | succ n ih =>
    simpa only [pow_succ', mul_apply_eq_comp] using positive ih

include closed zero add smul in
/-- Norm convergence of the actual Neumann expansion preserves the cone. -/
theorem mapsTo_of_radius_lt (P : H →L[ℂ] H) (positive : MapsTo P C C)
    (r : ℝ) (positiveR : 0 < r)
    (outside : spectralRadius ℂ P < ENNReal.ofReal r) :
    MapsTo (resolvent P (r : ℂ) : H →L[ℂ] H) C C := by
  have outside' : spectralRadius ℂ P < (‖(r : ℂ)‖₊ : ENNReal) := by
    rw [← ENNReal.ofReal_coe_nnreal]
    change spectralRadius ℂ P < ENNReal.ofReal ‖(r : ℂ)‖
    simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos positiveR] using outside
  intro x hx
  have sum := (SpectralRadiusNeumannSeries.hasSum P (r : ℂ) outside').mapL
    (ContinuousLinearMap.apply ℂ H x)
  apply closed.mem_of_tendsto sum.tendsto_sum_nat
  apply Eventually.of_forall
  intro n
  apply sum_mem C zero add
  intro k _
  change ((r : ℂ)⁻¹ • ((r : ℂ)⁻¹ • P) ^ k) x ∈ C
  rw [smul_pow, smul_smul, smul_apply]
  rw [show (r : ℂ)⁻¹ = (r⁻¹ : ℝ) from (Complex.ofReal_inv r).symm,
    ← Complex.ofReal_pow, ← Complex.ofReal_mul]
  exact smul _ (mul_nonneg (inv_nonneg.mpr positiveR.le)
    (pow_nonneg (inv_nonneg.mpr positiveR.le) k)) (pow_mem C P positive hx k)

include closed zero add smul in
/-- At a regular positive boundary point, continuity retains cone positivity. -/
theorem mapsTo_at_regular_boundary (P : H →L[ℂ] H) (positive : MapsTo P C C)
    (R : ℝ) (positiveR : 0 < R) (radius : spectralRadius ℂ P ≤ ENNReal.ofReal R)
    (regular : (R : ℂ) ∈ resolventSet ℂ P) :
    MapsTo (resolvent P (R : ℂ) : H →L[ℂ] H) C C := by
  intro x hx
  have continuous := ((ContinuousLinearMap.apply ℂ H x).continuous.continuousAt.comp
    (AnalyticResolvent.analyticAt P regular).continuousAt).comp
      Complex.continuous_ofReal.continuousAt
  apply closed.mem_of_tendsto (continuous.tendsto.mono_left
    (show 𝓝[>] R ≤ 𝓝 R from nhdsWithin_le_nhds))
  filter_upwards [self_mem_nhdsWithin] with r hr
  exact mapsTo_of_radius_lt C closed zero add smul P positive r (positiveR.trans hr)
    (radius.trans_lt (ENNReal.ofReal_lt_ofReal_iff (positiveR.trans hr) |>.mpr hr)) hx

include closed zero add in
theorem inverse_one_sub_mapsTo (Q : H →L[ℂ] H) (positive : MapsTo Q C C)
    (small : ‖Q‖ < 1) : MapsTo (Ring.inverse (1 - Q) : H →L[ℂ] H) C C := by
  intro x hx
  have sum := (hasSum_geom_series_inverse Q small).mapL (ContinuousLinearMap.apply ℂ H x)
  apply closed.mem_of_tendsto sum.tendsto_sum_nat
  apply Eventually.of_forall
  intro n
  apply sum_mem C zero add
  intro k _
  exact pow_mem C Q positive hx k

include closed zero add smul in
/-- Positivity of a regular real resolvent persists at some strictly smaller
positive real parameter, by the local norm-convergent positive expansion. -/
theorem exists_lower_positive_resolvent (P : H →L[ℂ] H) (R : ℝ) (positiveR : 0 < R)
    (regular : (R : ℂ) ∈ resolventSet ℂ P)
    (positive : MapsTo (resolvent P (R : ℂ) : H →L[ℂ] H) C C) :
    ∃ r : ℝ, 0 < r ∧ r < R ∧ (r : ℂ) ∈ resolventSet ℂ P ∧
      MapsTo (resolvent P (r : ℂ) : H →L[ℂ] H) C C := by
  let L := resolvent P (R : ℂ)
  have normPositive : 0 < ‖L‖ + 1 := by linarith [norm_nonneg L]
  obtain ⟨δ, positiveD, smallD⟩ := exists_between
    (lt_min positiveR (inv_pos.mpr normPositive))
  have belowR : δ < R := smallD.trans_le (min_le_left _ _)
  have product : δ * (‖L‖ + 1) < 1 :=
    (lt_div_iff₀ normPositive).mp (by
      simpa only [one_div] using smallD.trans_le (min_le_right _ _))
  let Q : H →L[ℂ] H := (δ : ℂ) • L
  have smallQ : ‖Q‖ < 1 := by
    rw [show Q = (δ : ℂ) • L from rfl, norm_smul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos positiveD]
    nlinarith
  have positiveQ : MapsTo Q C C := by
    intro x hx
    exact smul δ positiveD.le (positive hx)
  have positiveInverse := inverse_one_sub_mapsTo C closed zero add Q positiveQ smallQ
  have unit := isUnit_one_sub_of_norm_lt_one smallQ
  let S := algebraMap ℂ (H →L[ℂ] H) (R : ℂ) - P
  have SL : S * L = 1 := Ring.mul_inverse_cancel _ regular
  have LS : L * S = 1 := Ring.inverse_mul_cancel _ regular
  have factor : algebraMap ℂ (H →L[ℂ] H) ((R - δ : ℝ) : ℂ) - P = S * (1 - Q) := by
    rw [mul_sub, mul_one]
    dsimp only [Q]
    rw [mul_smul_comm, SL]
    dsimp only [S]
    simp only [Complex.ofReal_sub, map_sub, Algebra.algebraMap_eq_smul_one]
    abel
  let B := Ring.inverse (1 - Q) * L
  have left : (algebraMap ℂ (H →L[ℂ] H) ((R - δ : ℝ) : ℂ) - P) * B = 1 := by
    rw [factor]
    dsimp only [B]
    calc
      _ = S * ((1 - Q) * Ring.inverse (1 - Q)) * L := by noncomm_ring
      _ = 1 := by rw [Ring.mul_inverse_cancel _ unit, mul_one, SL]
  have right : B * (algebraMap ℂ (H →L[ℂ] H) ((R - δ : ℝ) : ℂ) - P) = 1 := by
    rw [factor]
    dsimp only [B]
    calc
      _ = Ring.inverse (1 - Q) * (L * S) * (1 - Q) := by noncomm_ring
      _ = 1 := by rw [LS, mul_one, Ring.inverse_mul_cancel _ unit]
  have regularLower := spectrum.mem_resolventSet_of_left_right_inverse left right
  have formula : resolvent P ((R - δ : ℝ) : ℂ) = B :=
    left_inv_eq_right_inv (Ring.inverse_mul_cancel _ regularLower) left
  refine ⟨R - δ, sub_pos.mpr belowR, by linarith, regularLower, ?_⟩
  rw [formula]
  intro x hx
  exact positiveInverse (positive hx)

end LeanShared.ClosedConeResolvent
