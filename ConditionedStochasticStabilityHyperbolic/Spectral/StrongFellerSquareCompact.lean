module

public import ConditionedStochasticStabilityHyperbolic.Spectral.ComplexStrongFeller
public import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
public import Mathlib.Analysis.Normed.Operator.Compact.Basic

/-! # The classical ultra-Feller theorem gives actual square compactness

Dobrick--Hölz--Kunze, *Ultra Feller operators from a functional analytic
perspective*, Theorems 3.10--3.11, compact-space case:
https://arxiv.org/html/2312.13266v2
Two strong-Feller kernel operators have ultra-Feller composition. The named
classical input below records its unit-ball equicontinuity consequence.
Arzelà--Ascoli then proves compactness of the actual squared transfer.
Bounded measurable noise densities need no pointwise continuity or higher
regularity upgrade. The input is universal and contains no spectral gap.
-/

@[expose] public noncomputable section
open Set Metric
open scoped BoundedContinuousFunction
namespace ConditionedStochasticStabilityHyperbolic.StrongFellerSquareCompact
variable {X : Type*} [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]

def UltraFellerContract : Prop :=
  ∀ (C : AbsorbingMarkovChains.CanonicalChain X) (hSF : HasStrongFellerKernel C),
    Equicontinuous (fun f : {f : X →ᵇ ℂ // ‖f‖ ≤ 1} =>
      fun x => (ComplexStrongFeller.transferOperator (𝕜 := ℂ) C hSF ^ 2) f.val x)

/-- Relative compactness is derived with the actual transfer norm bound. -/
theorem square_compact (source : UltraFellerContract (X := X))
    (C : AbsorbingMarkovChains.CanonicalChain X) (hSF : HasStrongFellerKernel C) :
    IsCompactOperator (ComplexStrongFeller.transferOperator (𝕜 := ℂ) C hSF ^ 2 :
      (X →ᵇ ℂ) →L[ℂ] (X →ᵇ ℂ)) := by
  let P : (X →ᵇ ℂ) →L[ℂ] (X →ᵇ ℂ) := ComplexStrongFeller.transferOperator (𝕜 := ℂ) C hSF ^ 2
  let A := P '' closedBall (0 : X →ᵇ ℂ) 1
  have he : Equicontinuous (fun u : A => fun x => u.val x) := by
    have hsrc := source C hSF
    have hw (u : A) : ∃ f : X →ᵇ ℂ, ‖f‖ ≤ 1 ∧ P f = u.val := by
      have hu : u.val ∈ P '' closedBall (0 : X →ᵇ ℂ) 1 := u.property
      obtain ⟨f, hf, hfu⟩ := hu
      exact ⟨f, mem_closedBall_zero_iff.mp hf, hfu⟩
    let lift : A → {f : X →ᵇ ℂ // ‖f‖ ≤ 1} := fun u =>
      ⟨Classical.choose (hw u), (Classical.choose_spec (hw u)).1⟩
    have hl (u : A) : P (lift u).val = u.val := (Classical.choose_spec (hw u)).2
    have h := hsrc.comp lift
    have hh : (fun u : A => fun x => P (lift u).val x) = (fun u : A => fun x => u.val x) := by
      funext u x
      rw [hl u]
    exact hh ▸ h
  have hc : IsCompact (closure A) := by
    apply BoundedContinuousFunction.arzela_ascoli (closedBall (0 : ℂ) ‖P‖)
      (isCompact_closedBall (0 : ℂ) ‖P‖)
    · intro u x hu
      change u ∈ P '' closedBall (0 : X →ᵇ ℂ) 1 at hu
      obtain ⟨f, hf, rfl⟩ := hu
      apply mem_closedBall_zero_iff.mpr
      exact ((P f).norm_coe_le_norm x).trans ((P.le_opNorm f).trans
        (mul_le_of_le_one_right (norm_nonneg P) (mem_closedBall_zero_iff.mp hf)))
    · exact he
  exact (isCompactOperator_iff_image_closedBall_subset_compact P.toLinearMap
    (r := 1) (by norm_num)).mpr ⟨closure A, hc, subset_closure⟩

end ConditionedStochasticStabilityHyperbolic.StrongFellerSquareCompact
