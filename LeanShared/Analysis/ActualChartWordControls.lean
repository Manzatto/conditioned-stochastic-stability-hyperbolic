module

public import LeanShared.Analysis.MovingChartWordPhase
public import LeanShared.Analysis.MicrolocalBlockParameters

/-! Uniform microscopic parameters for actual endpoint-chart manifold words.
The only norm input is the ordinary finite C^r composition/weight calculus
on valid coordinate supports. Robust phase denominators are proved here from
relative continuity of the literal word derivatives, including moving fibers.
These statements assert no transfer norm or Lasota--Yorke estimate. -/

@[expose] public noncomputable section
open Set Filter
open scoped Topology
namespace LeanShared.ActualChartWordControls
open CylinderPrincipalCoefficient MicrolocalBlockParameters
variable {E M Ω : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [TopologicalSpace M] [TopologicalSpace Ω]
  (out inp : OpenPartialHomeomorph M E) (F : Ω → M ≃ₜ M)

/-- Ordinary local finite fractional derivative data. Partial chart formulas
need only be regular on their actual domains. -/
structure LocalBounds {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (f : E → Y) (K : Set E) (m : ℕ) (δ B : ℝ) : Prop where
  regularity : ContDiffOn ℝ m f K
  derivatives : ∀ k ≤ m, ∀ x ∈ K, ‖iteratedFDeriv ℝ k f x‖ ≤ B
  highest : ∀ x ∈ K, ∀ y ∈ K,
    ‖iteratedFDeriv ℝ m f x - iteratedFDeriv ℝ m f y‖ ≤ B * ‖x - y‖ ^ δ

/-- Actual complex chart-row weight, including the output partition cutoff. -/
def weight (θ : M → ℂ) (g : M → ℝ) (word : List Ω) (y : E) : ℂ :=
  θ (out.symm y) * (ActualWordMicrolocalBound.realWeight (fun a => F a) g word (out.symm y) : ℂ)

structure Controls (θ : M → ℂ) (g : M → ℝ) (K L : Set E)
    {N : ℕ} (R Rback : Set ((Fin N → Ω) × E)) (m : ℕ) (δ : ℝ)
    (word : Fin N → Ω) (nonlinked : E → E → ℝ → Prop) (p : Parameters) : Prop where
  order_positive : 0 < m
  fraction_nonnegative : 0 ≤ δ
  fraction_lt_one : δ < 1
  forward : LocalBounds (ActualChartWordFields.forward out inp F (List.ofFn word))
    (fiber K R word) m δ p.mapBound
  inverse : LocalBounds (ActualChartWordFields.backward out inp F (List.ofFn word))
    (fiber L Rback word) m δ p.inverseBound
  weighted : LocalBounds (weight out F θ g (List.ofFn word))
    (fiber K R word) (m - 1) δ p.weightBound
  phase : ∀ x ∈ fiber K R word, ∀ ξ η Λ, nonlinked ξ η Λ → 0 ≤ Λ →
    p.phaseGap * Λ ≤ ‖ξ - ContinuousLinearMap.adjoint
      (MovingChartWordPhase.derivative out inp F N (word, x)) η‖

/-- One common generator neighborhood for the actual finite manifold word.
Classical composition calculus supplies MF/MB/MG only for this fixed N;
no uniformity in N is required of the weak microscopic remainder. -/
theorem exists_uniform_controls (N m : ℕ) (δ : ℝ) (hm : 0 < m)
    (hδ : 0 ≤ δ) (hδ1 : δ < 1) (reference : Ω)
    (θ : M → ℂ) (g : M → ℝ) (K L : Set E) (hK : IsCompact K)
    (R Rback : Set ((Fin N → Ω) × E)) (hR : IsClosed R)
    (U : Set Ω) (hU : IsOpen U) (href : reference ∈ U)
    (MF MB MG σ : ℝ) (hMF : 0 ≤ MF) (hMB : 0 ≤ MB) (hMG : 0 ≤ MG) (hσ : 0 < σ)
    (hcomposition : ∀ word : Fin N → Ω, (∀ i, word i ∈ U) →
      LocalBounds (ActualChartWordFields.forward out inp F (List.ofFn word))
        (fiber K R word) m δ MF ∧
      LocalBounds (ActualChartWordFields.backward out inp F (List.ofFn word))
        (fiber L Rback word) m δ MB ∧
      LocalBounds (weight out F θ g (List.ofFn word))
        (fiber K R word) (m - 1) δ MG)
    (hd : ContinuousOn (MovingChartWordPhase.derivative out inp F N)
      (((⋂ i : Fin N, (fun word => word i) ⁻¹' U) ×ˢ univ) ∩ R))
    (hbase : ContinuousOn (fun z : (Fin N → Ω) × E =>
      MovingChartWordPhase.derivative out inp F N ((fun _ => reference), z.2))
      (((⋂ i : Fin N, (fun word => word i) ⁻¹' U) ×ˢ univ) ∩ R))
    (nonlinked : E → E → ℝ → Prop)
    (hfrequency : ∀ ξ η Λ, nonlinked ξ η Λ → ‖η‖ ≤ 2 * Λ)
    (hdeterministic : ∀ x ∈ K, ∀ ξ η Λ, nonlinked ξ η Λ → 0 ≤ Λ →
      σ * Λ ≤ ‖ξ - ContinuousLinearMap.adjoint
        (MovingChartWordPhase.derivative out inp F N ((fun _ => reference), x)) η‖) :
    ∃ p : Parameters, ∃ V : Set Ω, IsOpen V ∧ reference ∈ V ∧
      ∀ word : Fin N → Ω, (∀ i, word i ∈ V) →
        Controls out inp F θ g K L R Rback m δ word nonlinked p := by
  have hbox : IsOpen (⋂ i : Fin N, (fun word : Fin N → Ω => word i) ⁻¹' U) :=
    isOpen_iInter_of_finite fun i => hU.preimage (continuous_apply i)
  have hrefbox : (fun _ : Fin N => reference) ∈
      ⋂ i : Fin N, (fun word : Fin N → Ω => word i) ⁻¹' U := mem_iInter.mpr fun _ => href
  obtain ⟨W, hW, hrefW, hphase⟩ := MovingChartWordPhase.exists_uniform_phase
    out inp F N reference K hK R hR _ hbox hrefbox hd hbase σ hσ
  let p : Parameters := ⟨MF, MB, MG, σ / 2, hMF, hMB, hMG, by positivity⟩
  refine ⟨p, U ∩ W, hU.inter hW, ⟨href, hrefW⟩, ?_⟩
  intro word hw
  have hwu : ∀ i, word i ∈ U := fun i => (hw i).1
  have hww : ∀ i, word i ∈ W := fun i => (hw i).2
  obtain ⟨hf, hb, hg⟩ := hcomposition word hwu
  refine ⟨hm, hδ, hδ1, hf, hb, hg, ?_⟩
  intro x hx ξ η Λ hnl hΛ
  exact hphase word hww x hx.1 hx.2 ξ η Λ hΛ (hfrequency ξ η Λ hnl)
    (hdeterministic x hx.1 ξ η Λ hnl hΛ)

end LeanShared.ActualChartWordControls
