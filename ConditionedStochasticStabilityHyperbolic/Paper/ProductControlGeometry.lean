module

public import ConditionedStochasticStabilityHyperbolic.Paper.ProductRegularNoiseLaws
public import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions
public import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
public import Mathlib.Topology.Algebra.Module.Equiv.Basic
public import Mathlib.Topology.Algebra.Module.Equiv.Pi
public import Mathlib.Topology.Algebra.Module.Equiv.Prod
public import Mathlib.Topology.Algebra.Module.Equiv.Submodule

/-! The derivative of the actual independent control map is block diagonal
in the sum-coordinate control cube. Surjectivity is derived from the two
original control derivatives. -/

@[expose] public noncomputable section
open Set IsManifold
open scoped Manifold ContDiff NNReal
namespace ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

def splitControl : Control (ι := ι ⊕ κ) ≃L[ℝ] Control (ι := ι) × Control (ι := κ) :=
  ContinuousLinearEquiv.sumPiEquivProdPi ℝ ι κ (fun _ => ℝ)

private theorem splitControl_hasMFDerivAt (v : Control (ι := ι ⊕ κ)) :
    HasMFDerivAt (𝓘(ℝ, Control (ι := ι ⊕ κ)))
      ((𝓘(ℝ, Control (ι := ι))).prod (𝓘(ℝ, Control (ι := κ))))
      (splitControl (ι := ι) (κ := κ)) v (splitControl (ι := ι) (κ := κ)).toContinuousLinearMap := by
  have hm := (hasMFDerivAt_iff_hasFDerivAt).mpr
    ((splitControl (ι := ι) (κ := κ)).toContinuousLinearMap.hasFDerivAt (x := v))
  rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod] at hm
  exact hm

variable {E F M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace M] [ChartedSpace E M]
  [TopologicalSpace N] [ChartedSpace F N]

/-- Actual independent controls, before restricting to their compact cube. -/
def independentControlMap (f : Control (ι := ι) → M) (g : Control (ι := κ) → N) :
    Control (ι := ι ⊕ κ) → M × N :=
  fun v => (f (fun i => v (.inl i)), g (fun j => v (.inr j)))

theorem independentControlMap_mfderiv
    (f : Control (ι := ι) → M) (g : Control (ι := κ) → N)
    (v : Control (ι := ι ⊕ κ))
    (hf : MDifferentiableAt (𝓘(ℝ, Control (ι := ι))) (𝓘(ℝ, E))
      f (fun i => v (.inl i)))
    (hg : MDifferentiableAt (𝓘(ℝ, Control (ι := κ))) (𝓘(ℝ, F))
      g (fun j => v (.inr j))) :
    mfderiv (𝓘(ℝ, Control (ι := ι ⊕ κ))) ((𝓘(ℝ, E)).prod (𝓘(ℝ, F)))
      (independentControlMap f g) v =
      ((mfderiv (𝓘(ℝ, Control (ι := ι))) (𝓘(ℝ, E)) f (fun i => v (.inl i))).prodMap
        (mfderiv (𝓘(ℝ, Control (ι := κ))) (𝓘(ℝ, F)) g (fun j => v (.inr j)))).comp
          (splitControl (ι := ι) (κ := κ)).toContinuousLinearMap := by
  have hfg : MDifferentiableAt
      ((𝓘(ℝ, Control (ι := ι))).prod (𝓘(ℝ, Control (ι := κ))))
      ((𝓘(ℝ, E)).prod (𝓘(ℝ, F))) (Prod.map f g)
      (splitControl (ι := ι) (κ := κ) v) := hf.prodMap hg
  have h := mfderiv_comp (f := splitControl (ι := ι) (κ := κ)) (g := Prod.map f g)
    v hfg (splitControl_hasMFDerivAt v).mdifferentiableAt
  rw [mfderiv_prodMap hf hg, (splitControl_hasMFDerivAt v).mfderiv] at h
  exact h

/-- No extra rank assumption appears in the stabilized noise family. -/
theorem independentControlMap_surjective
    (f : Control (ι := ι) → M) (g : Control (ι := κ) → N)
    (v : Control (ι := ι ⊕ κ))
    (hf : MDifferentiableAt (𝓘(ℝ, Control (ι := ι))) (𝓘(ℝ, E))
      f (fun i => v (.inl i)))
    (hg : MDifferentiableAt (𝓘(ℝ, Control (ι := κ))) (𝓘(ℝ, F))
      g (fun j => v (.inr j)))
    (hsf : Function.Surjective (mfderiv (𝓘(ℝ, Control (ι := ι))) (𝓘(ℝ, E)) f
      (fun i => v (.inl i))))
    (hsg : Function.Surjective (mfderiv (𝓘(ℝ, Control (ι := κ))) (𝓘(ℝ, F)) g
      (fun j => v (.inr j)))) :
    Function.Surjective (mfderiv (𝓘(ℝ, Control (ι := ι ⊕ κ)))
      ((𝓘(ℝ, E)).prod (𝓘(ℝ, F))) (independentControlMap f g) v) := by
  rw [independentControlMap_mfderiv f g v hf hg]
  intro z
  obtain ⟨a, ha⟩ := hsf z.1
  obtain ⟨b, hb⟩ := hsg z.2
  refine ⟨(splitControl (ι := ι) (κ := κ)).symm (a, b), ?_⟩
  change ((mfderiv (𝓘(ℝ, Control (ι := ι))) (𝓘(ℝ, E)) f (fun i => v (.inl i))).prodMap
    (mfderiv (𝓘(ℝ, Control (ι := κ))) (𝓘(ℝ, F)) g (fun j => v (.inr j))))
      (splitControl (ι := ι) (κ := κ) ((splitControl (ι := ι) (κ := κ)).symm (a, b))) = z
  rw [ContinuousLinearEquiv.apply_symm_apply]
  exact Prod.ext ha hb


section ActualMaps
variable {X Y : Type*} [MetricSpace X] [ChartedSpace E X]
  [MetricSpace Y] [ChartedSpace F Y]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
  {T : X ≃ₜ X} {T' : Y ≃ₜ Y} {r : ℝ}

omit [FiniteDimensional ℝ E] in
/-- Literal joint C¹ regularity implies the control differentiability needed
for the block derivative computation, including boundary controls. -/
theorem Maps.control_mdifferentiableAt
    (P : Maps (E := E) (ι := ι) T r) (ε : ℝ≥0) (hε : 0 < ε)
    (hw : ε ≤ P.window) (v : cube (ι := ι) ε) (x : X) :
    MDifferentiableAt (𝓘(ℝ, Control (ι := ι))) (𝓘(ℝ, E))
      (fun a => P.family ε a x) v.val := by
  obtain ⟨O, hO, hc, hC⟩ := P.joint_C1 ε hε hw
  have hx : (v.val, x) ∈ O ×ˢ (univ : Set X) := ⟨hc v.property, mem_univ x⟩
  have hAt := hC.contMDiffAt ((hO.prod isOpen_univ).mem_nhds hx)
  have hIn : ContMDiff (𝓘(ℝ, Control (ι := ι)))
      ((𝓘(ℝ, Control (ι := ι))).prod (𝓘(ℝ, E))) 1
      (fun a : Control (ι := ι) => (a, x)) := contMDiff_id.prodMk contMDiff_const
  exact (hAt.comp v.val hIn.contMDiffAt).mdifferentiableAt (by decide)

def independentFamily (P : Maps (E := E) (ι := ι) T r)
    (Q : Maps (E := F) (ι := κ) T' r) :
    ℝ≥0 → Control (ι := ι ⊕ κ) → X × Y → X × Y :=
  fun ε a z => (P.family ε (fun i => a (.inl i)) z.1,
    Q.family ε (fun j => a (.inr j)) z.2)

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
/-- The actual stabilized family retains full control rank on its entire
closed cube; neither an averaged rank nor a new source is used. -/
theorem independentFamily_control_surjective
    (P : Maps (E := E) (ι := ι) T r) (Q : Maps (E := F) (ι := κ) T' r)
    (ε : ℝ≥0) (hε : 0 < ε) (hw : ε ≤ min P.window Q.window)
    (v : cube (ι := ι ⊕ κ) ε) (z : X × Y) :
    Function.Surjective (mfderiv (𝓘(ℝ, Control (ι := ι ⊕ κ)))
      ((𝓘(ℝ, E)).prod (𝓘(ℝ, F))) (fun a => independentFamily P Q ε a z) v.val) := by
  let vl : cube (ι := ι) ε := (LeanShared.NoiseCubeRescaling.splitCube (ε : ℝ) v).1
  let vr : cube (ι := κ) ε := (LeanShared.NoiseCubeRescaling.splitCube (ε : ℝ) v).2
  exact independentControlMap_surjective
    (fun a => P.family ε a z.1) (fun a => Q.family ε a z.2) v.val
    (P.control_mdifferentiableAt ε hε (le_min_iff.mp hw).1 vl z.1)
    (Q.control_mdifferentiableAt ε hε (le_min_iff.mp hw).2 vr z.2)
    (P.control_surjective ε hε (le_min_iff.mp hw).1 vl z.1)
    (Q.control_surjective ε hε (le_min_iff.mp hw).2 vr z.2)

end ActualMaps

end ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
