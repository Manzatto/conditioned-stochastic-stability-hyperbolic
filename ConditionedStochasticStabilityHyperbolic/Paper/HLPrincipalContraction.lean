module

public import ConditionedStochasticStabilityHyperbolic.Paper.HLDifferential
public import LeanShared.Analysis.IntrinsicSplittingFactors
public import LeanShared.Geometry.IntrinsicWordInverseDifferential

/-! The stable principal factor for the actual deterministic HL tangent
word, derived from the literal hyperbolicity hypothesis. -/

@[expose] public noncomputable section
open Set Bundle
open scoped Manifold ContDiff Bundle
namespace ConditionedStochasticStabilityHyperbolic.Paper.HL
open LeanShared
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MetricSpace M] [ChartedSpace E M]
  [IsManifold (𝓘(ℝ, E)) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
  {T : M ≃ₜ M} {g : M → ℝ} {Λ V : Set M} (h : HL (E := E) T g Λ V)

private theorem reference_orbit (N : ℕ) :
    IntrinsicPrincipalDensity.orbit (fun _ : Unit => (T : M → M)) (List.replicate N ()) =
      (T : M → M)^[N] := by
  funext x
  induction N generalizing x with
  | zero => rfl
  | succ N ih =>
    simpa only [List.replicate_succ, IntrinsicPrincipalDensity.orbit,
      Function.iterate_succ_apply] using ih (T x)

omit [FiniteDimensional ℝ E] in
private theorem reference_stable_invariant (word : List Unit) (x : M) (hx : x ∈ Λ) :
    (h.basic.hyperbolic.stable x).map
      (IntrinsicPrincipalDensity.derivative (fun _ : Unit => (T : M → M))
        (fun x => TangentSpace (𝓘(ℝ, E)) x) (fun _ => h.differential) word x).toLinearMap =
      h.basic.hyperbolic.stable
        (IntrinsicPrincipalDensity.orbit (fun _ : Unit => (T : M → M)) word x) := by
  apply IntrinsicPrincipalDensity.derivative_map_invariant
    (fun _ : Unit => (T : M → M)) (fun x => TangentSpace (𝓘(ℝ, E)) x)
    (fun _ => h.differential) Λ
  · intro _ y hy
    exact h.basic.hyperbolic.invariant ▸ Set.mem_image_of_mem T hy
  · intro _ y hy
    exact h.basic.hyperbolic.stable_invariant y hy
  · exact hx

omit [FiniteDimensional ℝ E] in
/-- The actual stable restriction in the intrinsic coefficient contracts at
the HL rate. The coefficient is not supplied as an independent scalar. -/
theorem principal_stableFactor_bound (N : ℕ) (x : M) (hx : x ∈ Λ) :
    IntrinsicPrincipalDensity.stableFactor (fun _ : Unit => (T : M → M))
      (fun x => TangentSpace (𝓘(ℝ, E)) x) (fun _ => h.differential)
      (List.replicate N ()) x
      (h.basic.hyperbolic.stable
        (IntrinsicPrincipalDensity.orbit (fun _ : Unit => (T : M → M)) (List.replicate N ()) x)) ≤
      h.basic.hyperbolic.constant * h.basic.hyperbolic.contraction ^ N := by
  apply IntrinsicPrincipalDensity.stableFactor_le_of_invariant
    (fun _ : Unit => (T : M → M)) (fun x => TangentSpace (𝓘(ℝ, E)) x)
    (fun _ => h.differential) (List.replicate N ()) x
    (h.basic.hyperbolic.stable x) _ (reference_stable_invariant h _ x hx)
  · exact mul_nonneg h.basic.hyperbolic.constant_pos.le
      (pow_nonneg h.basic.hyperbolic.contraction_pos.le N)
  · intro v hv
    have hd := IntrinsicWordDifferential.derivative_apply (fun _ : Unit => T)
      (fun _ => h.map_regular.mdifferentiable h.regularity_gt_one.le)
      (fun _ => h.inverse_regular.mdifferentiable h.regularity_gt_one.le)
      (List.replicate N ()) x v
    change IntrinsicPrincipalDensity.derivative (fun _ : Unit => (T : M → M))
      (fun x => TangentSpace (𝓘(ℝ, E)) x) (fun _ => h.differential)
      (List.replicate N ()) x v = _ at hd
    rw [hd, reference_orbit]
    exact h.basic.hyperbolic.stable_bound N x hx v hv

private theorem reference_backward (N : ℕ) :
    ((IntrinsicWordDifferential.wordHomeomorph (fun _ : Unit => T) (List.replicate N ())).symm : M → M) =
      (T.symm : M → M)^[N] := by
  funext x
  induction N generalizing x with
  | zero => rfl
  | succ N ih =>
    change T.symm ((IntrinsicWordDifferential.wordHomeomorph
      (fun _ : Unit => T) (List.replicate N ())).symm x) = _
    rw [ih, Function.iterate_succ_apply']

omit [FiniteDimensional ℝ E] in
private theorem reference_unstable_invariant (word : List Unit) (x : M) (hx : x ∈ Λ) :
    (h.basic.hyperbolic.unstable x).map
      (IntrinsicPrincipalDensity.derivative (fun _ : Unit => (T : M → M))
        (fun x => TangentSpace (𝓘(ℝ, E)) x) (fun _ => h.differential) word x).toLinearMap =
      h.basic.hyperbolic.unstable
        (IntrinsicPrincipalDensity.orbit (fun _ : Unit => (T : M → M)) word x) := by
  apply IntrinsicPrincipalDensity.derivative_map_invariant
    (fun _ : Unit => (T : M → M)) (fun x => TangentSpace (𝓘(ℝ, E)) x)
    (fun _ => h.differential) Λ
  · intro _ y hy
    exact h.basic.hyperbolic.invariant ▸ Set.mem_image_of_mem T hy
  · intro _ y hy
    exact h.basic.hyperbolic.unstable_invariant y hy
  · exact hx

include h in
omit [FiniteDimensional ℝ E] in
private theorem reference_orbit_mem (word : List Unit) (x : M) (hx : x ∈ Λ) :
    IntrinsicPrincipalDensity.orbit (fun _ : Unit => (T : M → M)) word x ∈ Λ := by
  induction word generalizing x with
  | nil => exact hx
  | cons a word ih =>
    exact ih (T x) (h.basic.hyperbolic.invariant ▸ Set.mem_image_of_mem T hx)

omit [FiniteDimensional ℝ E] in
/-- The actual inverse unstable restriction in the principal coefficient
contracts at the HL rate in the Riemannian norms at the correct basepoints. -/
theorem principal_inverseFactor_bound (N : ℕ) (x : M) (hx : x ∈ Λ) :
    IntrinsicPrincipalDensity.inverseFactor (fun _ : Unit => (T : M → M))
      (fun x => TangentSpace (𝓘(ℝ, E)) x) (fun _ => h.differential)
      (List.replicate N ()) x (h.basic.hyperbolic.unstable x) ≤
      h.basic.hyperbolic.constant * h.basic.hyperbolic.contraction ^ N := by
  apply IntrinsicPrincipalDensity.inverseFactor_le_of_invariant
    (fun _ : Unit => (T : M → M)) (fun x => TangentSpace (𝓘(ℝ, E)) x)
    (fun _ => h.differential) (List.replicate N ()) x
    (h.basic.hyperbolic.unstable x) _ (reference_unstable_invariant h _ x hx)
  · exact mul_nonneg h.basic.hyperbolic.constant_pos.le
      (pow_nonneg h.basic.hyperbolic.contraction_pos.le N)
  · intro v hv
    have hd := IntrinsicWordDifferential.norm_inverse_derivative (fun _ : Unit => T)
      (fun _ => h.map_regular.mdifferentiable h.regularity_gt_one.le)
      (fun _ => h.inverse_regular.mdifferentiable h.regularity_gt_one.le)
      (List.replicate N ()) x v
    change ‖(IntrinsicPrincipalDensity.derivative (fun _ : Unit => (T : M → M))
      (fun x => TangentSpace (𝓘(ℝ, E)) x) (fun _ => h.differential)
      (List.replicate N ()) x).symm v‖ = _ at hd
    rw [hd, reference_backward]
    exact h.basic.hyperbolic.unstable_bound N _
      (reference_orbit_mem h _ x hx) v hv

end ConditionedStochasticStabilityHyperbolic.Paper.HL
