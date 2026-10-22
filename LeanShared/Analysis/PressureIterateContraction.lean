module
public import LeanShared.Dynamics.ThermodynamicDefinitions
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Topology.Instances.NNReal.Lemmas

/-! Deduction of the strict pressure contraction from the precise fixed-map
iterate-pressure formula of Baladi--Tsujii (2008), Lemma 3.3. The formula,
ordinary pressure order and pressure-of-iterate identity are cited inputs;
the desired gamma times exp(P) bound is proved here. -/
@[expose] public noncomputable section
open Set Filter Function
open scoped Topology
namespace LeanShared.PressureIterateContraction
open ThermodynamicDefinitions
variable {X : Type*} [MetricSpace X]

theorem bound (T : X → X) (K : Set X) (ψ : X → ℝ)
    (φ : ℕ → X → ℝ) (P Q C γ : ℝ) (_hC : 0 < C) (hγ : 0 < γ)
    (PN : ℕ → ℝ)
    (finitePressure : ∀ N, 0 < N → pressure (T^[N]) (φ N) K = (PN N : EReal))
    (iteratePressure : ∀ N, 0 < N → pressure (T^[N]) (orbitSum T ψ N) K = ((N : ℝ) * P : ℝ))
    (order : ∀ N, 0 < N → ∀ (f g : X → ℝ) (Pf Pg c : ℝ),
      pressure (T^[N]) f K = (Pf : EReal) → pressure (T^[N]) g K = (Pg : EReal) →
      (∀ x ∈ K, f x ≤ g x + c) → Pf ≤ Pg + c)
    (comparison : ∀ N, 0 < N → ∀ x ∈ K,
      φ N x ≤ orbitSum T ψ N x + (Real.log C + (N : ℝ) * Real.log γ))
    (BT : Tendsto (fun N : ℕ => Real.exp ((N : ℝ)⁻¹ * PN N)) atTop (𝓝 Q)) :
    Q ≤ γ * Real.exp P := by
  have hinv : Tendsto (fun N : ℕ => (N : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hup : Tendsto (fun N : ℕ => Real.exp (P + Real.log γ + (N : ℝ)⁻¹ * Real.log C))
      atTop (𝓝 (γ * Real.exp P)) := by
    have hh0 : Tendsto (fun N : ℕ => P + Real.log γ + (N : ℝ)⁻¹ * Real.log C)
        atTop (𝓝 (P + Real.log γ)) := by
      simpa only [zero_mul, add_zero] using
        (tendsto_const_nhds.add (hinv.mul_const (Real.log C)))
    have hh := Real.continuous_exp.continuousAt.tendsto.comp hh0
    have hlim : Real.exp (P + Real.log γ) = γ * Real.exp P := by
      rw [Real.exp_add, Real.exp_log hγ, mul_comm]
    simpa only [Function.comp_def, hlim] using hh
  apply le_of_tendsto_of_tendsto BT hup
  filter_upwards [eventually_gt_atTop 0] with N hN
  have hPN := order N hN (φ N) (orbitSum T ψ N) (PN N) ((N : ℝ) * P)
    (Real.log C + (N : ℝ) * Real.log γ) (finitePressure N hN)
    (iteratePressure N hN) (comparison N hN)
  apply Real.exp_le_exp.mpr
  have hNR : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  calc
    (N : ℝ)⁻¹ * PN N ≤ (N : ℝ)⁻¹ * ((N : ℝ) * P +
        (Real.log C + (N : ℝ) * Real.log γ)) := mul_le_mul_of_nonneg_left hPN (inv_nonneg.mpr hNR.le)
    _ = P + Real.log γ + (N : ℝ)⁻¹ * Real.log C := by field_simp; ring

end LeanShared.PressureIterateContraction
