module
public import LeanShared.Dynamics.HyperbolicLinearRechartPotential
public import LeanShared.Dynamics.BasicHyperbolicPeriodicPartition

/-! The original and recharted BasicData have exactly the same finite
periodic point sets and literal weighted periodic partition sums. -/
public noncomputable section
open Set IsManifold Bundle
open scoped Manifold ContDiff Topology
namespace LeanShared.HyperbolicLinearRechart
open HyperbolicBasicSet LinearRechartedManifold

section Smooth
variable {E F M : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace M] [ChartedSpace E M]

theorem contMDiff_one_rechart (e : E ≃L[ℝ] F) {f : M → M}
    (hf : ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 f) :
    letI := charts (M := M) e;
    ContMDiff (𝓘(ℝ,F)) (𝓘(ℝ,F)) 1 f := by
  let := charts (M := M) e
  exact ((identity_forward (M := M) e).of_le (by simp)).comp
    (hf.comp ((identity_backward (M := M) e).of_le (by simp)))
end Smooth

variable {E F M : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [MetricSpace M] [CompactSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ,E)) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ,E)) x)]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace (𝓘(ℝ,E)) x)]
  (e : E ≃L[ℝ] F) {T : M ≃ₜ M} {Λ V : Set M}

theorem periodicPoints_eq (b : BasicData (E := E) T Λ V)
    (forward : ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 T)
    (inverse : ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 T.symm) (n : ℕ) (positive : 0 < n) :
    let oldPoints := b.periodicPoints forward inverse n positive;
    let transported := transportBasic e b (forward.mdifferentiable (by simp))
      (inverse.mdifferentiable (by simp));
    let original := RiemannianBundle.g (E := fun x : M => TangentSpace (𝓘(ℝ,E)) x);
    letI := charts (M := M) e;
    letI := manifold (M := M) e;
    letI : RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ,F)) x) :=
      ⟨transportMetric e original⟩;
    letI := continuous_metric (M := M) e;
    transported.periodicPoints (contMDiff_one_rechart e forward)
      (contMDiff_one_rechart e inverse) n positive = oldPoints := by
  classical
  let oldPoints := b.periodicPoints forward inverse n positive
  let transported := transportBasic e b (forward.mdifferentiable (by simp))
    (inverse.mdifferentiable (by simp))
  let original := RiemannianBundle.g (E := fun x : M => TangentSpace (𝓘(ℝ,E)) x)
  let := charts (M := M) e
  let := manifold (M := M) e
  let : RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ,F)) x) :=
    ⟨transportMetric e original⟩
  let := continuous_metric (M := M) e
  ext x
  exact (transported.mem_periodicPoints _ _ n positive x).trans
    (b.mem_periodicPoints forward inverse n positive x).symm

theorem periodicPartitionSum_eq (b : BasicData (E := E) T Λ V)
    (forward : ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 T)
    (inverse : ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 T.symm) (φ : M → ℝ) (n : ℕ) :
    let oldSum := b.periodicPartitionSum forward inverse φ n;
    let transported := transportBasic e b (forward.mdifferentiable (by simp))
      (inverse.mdifferentiable (by simp));
    let original := RiemannianBundle.g (E := fun x : M => TangentSpace (𝓘(ℝ,E)) x);
    letI := charts (M := M) e;
    letI := manifold (M := M) e;
    letI : RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ,F)) x) :=
      ⟨transportMetric e original⟩;
    letI := continuous_metric (M := M) e;
    transported.periodicPartitionSum (contMDiff_one_rechart e forward)
      (contMDiff_one_rechart e inverse) φ n = oldSum := by
  let oldSum := b.periodicPartitionSum forward inverse φ n
  let transported := transportBasic e b (forward.mdifferentiable (by simp))
    (inverse.mdifferentiable (by simp))
  let original := RiemannianBundle.g (E := fun x : M => TangentSpace (𝓘(ℝ,E)) x)
  let := charts (M := M) e
  let := manifold (M := M) e
  let : RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ,F)) x) :=
    ⟨transportMetric e original⟩
  let := continuous_metric (M := M) e
  change transported.periodicPartitionSum (contMDiff_one_rechart e forward)
    (contMDiff_one_rechart e inverse) φ n = b.periodicPartitionSum forward inverse φ n
  by_cases positive : 0 < n
  · rw [transported.periodicPartitionSum_eq _ _ φ n positive,
      b.periodicPartitionSum_eq forward inverse φ n positive,
      periodicPoints_eq e b forward inverse n positive]
  · simp only [BasicData.periodicPartitionSum, dite_eq_right positive]

end LeanShared.HyperbolicLinearRechart
