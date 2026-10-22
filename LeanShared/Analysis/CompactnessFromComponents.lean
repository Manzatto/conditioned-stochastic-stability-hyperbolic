module

public import Mathlib.Analysis.Normed.Operator.Compact.Basic
public import Mathlib.Analysis.Normed.Group.Constructions
public import Mathlib.Topology.MetricSpace.Pseudo.Pi
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Compactness from finite components and small tails

Finite compact component images and arbitrarily fine control of the target
distance imply total boundedness. This finite-cover argument does not select
a different subsequence for each error tolerance. The final theorem applies
the criterion to a norm estimate with an arbitrarily small strong-norm tail.
It does not assume or construct any concrete anisotropic function space.
-/

@[expose] public noncomputable section

open Set Metric

namespace LeanShared.CompactnessFromComponents

variable {A B I : Type*} [PseudoMetricSpace B]
  {Z : I → Type*} [∀ i, PseudoMetricSpace (Z i)]

/-- Totally bounded control images at each tolerance give a totally bounded
target image, provided sufficiently close controls force close target values. -/
theorem totallyBounded_image_of_controls (s : Set A) (f : A → B)
    (q : ∀ i, A → Z i)
    (hcontrol : ∀ ε > 0, ∃ i, ∃ δ > 0,
      TotallyBounded (q i '' s) ∧
      ∀ x ∈ s, ∀ y ∈ s, dist (q i x) (q i y) < δ → dist (f x) (f y) < ε) :
    TotallyBounded (f '' s) := by
  classical
  refine Metric.totallyBounded_iff.mpr fun ε hε => ?_
  obtain ⟨i, δ, hδ, hq, hclose⟩ := hcontrol ε hε
  obtain ⟨t, hts, ht, hcover⟩ := Metric.finite_approx_of_totallyBounded hq δ hδ
  choose r hr hqr using fun z : t => hts z.property
  let : Fintype t := ht.fintype
  refine ⟨Set.range (fun z : t => f (r z)), Set.finite_range _, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨z, hz⟩ := Set.mem_iUnion.mp (hcover ⟨x, hx, rfl⟩)
  obtain ⟨hzt, hzdist⟩ := Set.mem_iUnion.mp hz
  have hclose' : dist (f x) (f (r ⟨z, hzt⟩)) < ε :=
    hclose x hx (r ⟨z, hzt⟩) (hr ⟨z, hzt⟩) (by
      simpa only [hqr ⟨z, hzt⟩, Metric.mem_ball] using hzdist)
  exact Set.mem_iUnion.mpr ⟨f (r ⟨z, hzt⟩),
    Set.mem_iUnion.mpr ⟨⟨⟨z, hzt⟩, rfl⟩, hclose'⟩⟩

/-- In a complete target, the preceding criterion gives relatively compact
images. No completeness of the control spaces is required. -/
theorem isCompact_closure_image_of_controls [CompleteSpace B]
    (s : Set A) (f : A → B) (q : ∀ i, A → Z i)
    (hcontrol : ∀ ε > 0, ∃ i, ∃ δ > 0,
      TotallyBounded (q i '' s) ∧
      ∀ x ∈ s, ∀ y ∈ s, dist (q i x) (q i y) < δ → dist (f x) (f y) < ε) :
    IsCompact (closure (f '' s)) :=
  (totallyBounded_image_of_controls s f q hcontrol).closure.isCompact_of_isComplete
    isClosed_closure.isComplete

/-- A finite family of relatively compact components can be used at each
tolerance. Different tolerances may use different finite families. -/
theorem isCompact_closure_image_of_finite_components [CompleteSpace B]
    (s : Set A) (f : A → B) (component : ∀ i, A → Z i)
    (hcompact : ∀ i, IsCompact (closure (component i '' s)))
    (hcontrol : ∀ ε > 0, ∃ J : Finset I, ∃ δ > 0,
      ∀ x ∈ s, ∀ y ∈ s,
        (∀ i ∈ J, dist (component i x) (component i y) < δ) →
          dist (f x) (f y) < ε) :
    IsCompact (closure (f '' s)) := by
  classical
  let q : ∀ J : Finset I, A → ((i : J) → Z i) :=
    fun _ x i => component i x
  apply isCompact_closure_image_of_controls s f q
  intro ε hε
  obtain ⟨J, δ, hδ, hclose⟩ := hcontrol ε hε
  refine ⟨J, δ, hδ, ?_, ?_⟩
  · apply (isCompact_pi_infinite (fun i : J => hcompact i)).totallyBounded.subset
    rintro _ ⟨x, hx, rfl⟩ i
    exact subset_closure ⟨x, hx, rfl⟩
  · intro x hx y hy hxy
    apply hclose x hx y hy
    intro i hi
    exact (dist_pi_lt_iff hδ).mp hxy ⟨i, hi⟩

section Operators

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]
  {G : I → Type*} [∀ i, NormedAddCommGroup (G i)] [∀ i, NormedSpace 𝕜 (G i)]

/-- Operator form of finite component control on the closed unit ball. -/
theorem isCompactOperator_of_finite_components (T : E →L[𝕜] F)
    (component : ∀ i, E →L[𝕜] G i)
    (hcompact : ∀ i, IsCompactOperator (component i))
    (hcontrol : ∀ ε > 0, ∃ J : Finset I, ∃ δ > 0,
      ∀ x ∈ Metric.closedBall (0 : E) 1, ∀ y ∈ Metric.closedBall (0 : E) 1,
        (∀ i ∈ J, dist (component i x) (component i y) < δ) →
          dist (T x) (T y) < ε) :
    IsCompactOperator T := by
  apply (isCompactOperator_iff_exists_mem_nhds_isCompact_closure_image T).mpr
  refine ⟨Metric.closedBall (0 : E) 1, Metric.closedBall_mem_nhds _ zero_lt_one, ?_⟩
  exact isCompact_closure_image_of_finite_components _ T (fun i => component i)
    (fun i => (hcompact i).isCompact_closure_image_closedBall (f := (component i).toLinearMap) 1)
    hcontrol

/-- A finite-component estimate plus an arbitrarily small strong-norm tail
proves compactness. The component term is the maximum norm of the selected
finite family (zero if the family is empty). -/
theorem isCompactOperator_of_small_tails (T : E →L[𝕜] F)
    (component : ∀ i, E →L[𝕜] G i)
    (hcompact : ∀ i, IsCompactOperator (component i))
    (htail : ∀ η > 0, ∃ J : Finset I, ∃ C ≥ 0,
      ∀ z : E, ‖T z‖ ≤ C * ‖fun i : J => component i z‖ + η * ‖z‖) :
    IsCompactOperator T := by
  classical
  apply isCompactOperator_of_finite_components T component hcompact
  intro ε hε
  obtain ⟨J, C, hC, hestimate⟩ := htail (ε / 4) (by positivity)
  let δ : ℝ := (ε / 4) / (C + 1)
  have hC1 : 0 < C + 1 := by positivity
  have hδ : 0 < δ := by dsimp [δ]; positivity
  refine ⟨J, δ, hδ, ?_⟩
  intro x hx y hy hxy
  have hnorm : ‖fun i : J => component i (x - y)‖ < δ := by
    apply (pi_norm_lt_iff hδ).mpr
    intro i
    simpa only [map_sub, dist_eq_norm] using hxy i i.property
  have hprod : C * ‖fun i : J => component i (x - y)‖ < ε / 4 := by
    have hlt := mul_lt_mul_of_pos_left hnorm hC1
    have hcancel : (C + 1) * δ = ε / 4 := by
      exact mul_div_cancel₀ (ε / 4) hC1.ne'
    rw [hcancel] at hlt
    have hn := norm_nonneg (fun i : J => component i (x - y))
    nlinarith
  have hxnorm : ‖x‖ ≤ 1 := by simpa only [Metric.mem_closedBall, dist_zero_right] using hx
  have hynorm : ‖y‖ ≤ 1 := by simpa only [Metric.mem_closedBall, dist_zero_right] using hy
  have hdiff : ‖x - y‖ ≤ 2 := (norm_sub_le x y).trans (by linarith)
  have hbound := hestimate (x - y)
  rw [dist_eq_norm, ← map_sub]
  nlinarith

end Operators

end LeanShared.CompactnessFromComponents
