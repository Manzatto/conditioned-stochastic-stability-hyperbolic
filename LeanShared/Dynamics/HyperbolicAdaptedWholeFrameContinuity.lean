module
public import LeanShared.Dynamics.HyperbolicAdaptedFrameContinuity
import Mathlib.Tactic.FinCases

/-! Actual whole adapted frames vary jointly continuously on each local
patch. There is no continuous choice across different cover patches. -/
public noncomputable section
open Set IsManifold Bundle
open scoped Manifold ContDiff BigOperators
namespace LeanShared.HyperbolicAdaptedFramePatches
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MetricSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ, E)) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
  {T : M ≃ₜ M} {Λ : Set M} {h : HyperbolicBasicSet.HyperbolicData (E := E) T Λ}
  {du ds : ℕ} {a : ℝ} {N : ℕ} {x : Λ}

theorem wholeFrame_joint (Fu : LocalFrame h h.unstable du a N x)
    (Fs : LocalFrame h h.stable ds a N x) :
    Continuous (fun p : ↥(Λ ∩ (Fu.neighborhood ∩ Fs.neighborhood)) ×
        (EuclideanSpace ℝ (Fin du) × EuclideanSpace ℝ (Fin ds)) =>
      (⟨p.1.val, wholeFrame Fu Fs p.1 p.2⟩ : TangentBundle (𝓘(ℝ, E)) M)) := by
  let X := ↥(Λ ∩ (Fu.neighborhood ∩ Fs.neighborhood)) ×
    (EuclideanSpace ℝ (Fin du) × EuclideanSpace ℝ (Fin ds))
  let sourceU (p : X) : ↥(Λ ∩ Fu.neighborhood) :=
    ⟨p.1.val, p.1.property.1, p.1.property.2.1⟩
  let sourceS (p : X) : ↥(Λ ∩ Fs.neighborhood) :=
    ⟨p.1.val, p.1.property.1, p.1.property.2.2⟩
  have continuousU : Continuous sourceU :=
    (continuous_subtype_val.comp continuous_fst).subtype_mk _
  have continuousS : Continuous sourceS :=
    (continuous_subtype_val.comp continuous_fst).subtype_mk _
  let u (p : X) := (Fu.euclideanCoordinates (sourceU p) p.2.1).val
  let s (p : X) := (Fs.euclideanCoordinates (sourceS p) p.2.2).val
  have cu : Continuous (fun p : X => (⟨p.1.val, u p⟩ : TangentBundle (𝓘(ℝ, E)) M)) :=
    Fu.joint_euclidean.comp (continuousU.prodMk (continuous_fst.comp continuous_snd))
  have cs : Continuous (fun p : X => (⟨p.1.val, s p⟩ : TangentBundle (𝓘(ℝ, E)) M)) :=
    Fs.joint_euclidean.comp (continuousS.prodMk (continuous_snd.comp continuous_snd))
  let vector (p : X) (i : Fin 2) := if i = 0 then u p else s p
  have cv (i : Fin 2) : Continuous (fun p : X =>
      (⟨p.1.val, vector p i⟩ : TangentBundle (𝓘(ℝ, E)) M)) := by
    fin_cases i
    · exact cu
    · exact cs
  have combined := FiniteBundleSectionCombination.continuous_combination
    (fun y : M => TangentSpace (𝓘(ℝ, E)) y) (fun p : X => p.1.val)
    (continuous_subtype_val.comp continuous_fst) vector cv
    (fun (_ : X) (_ : Fin 2) => (1 : ℝ)) (fun _ => continuous_const)
  apply combined.congr
  intro p
  congr 1
  simp only [Fin.sum_univ_two, vector, ↓reduceIte, Fin.one_eq_zero_iff,
    Nat.reduceEqDiff, one_smul, wholeFrame_apply, u, s, sourceU, sourceS]

end LeanShared.HyperbolicAdaptedFramePatches
