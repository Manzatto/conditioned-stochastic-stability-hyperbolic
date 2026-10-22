module

public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.DomainPressureStrictBlock
public import LeanShared.Analysis.DomainCylinderCoefficient
public import LeanShared.Analysis.RobustPressureCover

/-!
# Robust intrinsic pressure block on the actual manifold state space

The density is an actual intrinsic scalar on word × manifold. It is not a
single global Euclidean conjugacy, and continuity is required only in the
valid chart cylinders. Primary minimum-open-cover pressure asymptotics
select the strict block. Inner/outer shrinking, moving survivor cover
persistence, finite chart validity and local closed-supremum robustness are
proved here. No global word operator inequality is a parameter.

The constructed block is consumed by local chart-pair microscopic estimates,
whose global completed estimate is derived by CompletedMicrolocalEstimate.
-/

@[expose] public noncomputable section

open Set Filter
open scoped Topology BigOperators

namespace ConditionedStochasticStabilityHyperbolic.IntrinsicPressureBlock

open LeanShared.CylinderPrincipalCoefficient LeanShared.PressureCoverRefinement
open LeanShared.RobustPressureCover

private theorem outer_coefficient {P M : Type*} [TopologicalSpace P] [TopologicalSpace M]
    (K V : Set M) (f : P × M → ℝ) (p : P) :
    coefficient K (Set.univ ×ˢ V) f p = domainCoefficient K V (fun x => f (p, x)) := by
  unfold coefficient values fiber domainCoefficient
  congr 2
  ext x
  simp

private theorem coefficient_nonneg_on_fiber {P M : Type*}
    [TopologicalSpace P] [TopologicalSpace M]
    {K : Set M} {R : Set (P × M)} {f : P × M → ℝ}
    (hK : IsCompact K) (hR : IsClosed R) (p : P)
    (hf : ContinuousOn (fun x => f (p, x)) (fiber K R p)) : 0 ≤ coefficient K R f p := by
  have hc : IsCompact (values K R f p) :=
    isCompact_singleton.union ((fiber_isCompact hK hR p).image_of_continuousOn hf)
  exact le_csSup hc.bddAbove (Or.inl (mem_singleton 0))

private theorem exists_chart_neighborhood {P M I : Type*}
    [TopologicalSpace P] [TopologicalSpace M] [Fintype I]
    (p : P) (chart : I → Set (P × M)) (hchart : ∀ i, IsOpen (chart i))
    (v : I → Set M) (hcompact : ∀ i, IsCompact (closure (v i)))
    (hsub : ∀ i x, x ∈ closure (v i) → (p, x) ∈ chart i) :
    ∃ W : Set P, IsOpen W ∧ p ∈ W ∧
      ∀ q ∈ W, ∀ i x, x ∈ closure (v i) → (q, x) ∈ chart i := by
  classical
  have hh : ∀ i, ∃ W : Set P, IsOpen W ∧ p ∈ W ∧
      ∀ q ∈ W, ∀ x ∈ closure (v i), (q, x) ∈ chart i := by
    intro i
    obtain ⟨W, V, hW, _, hpW, hKV, hWV⟩ := generalized_tube_lemma
      isCompact_singleton (hcompact i) (hchart i) (by
        rintro ⟨q, x⟩ ⟨hq, hx⟩
        obtain rfl := mem_singleton_iff.mp hq
        exact hsub i x hx)
    exact ⟨W, hW, singleton_subset_iff.mp hpW,
      fun q hq x hx => hWV (mk_mem_prod hq (hKV hx))⟩
  choose W hW hpW hvalid using hh
  exact ⟨⋂ i, W i, isOpen_iInter_of_finite hW, mem_iInter.mpr hpW,
    fun q hq i x hx => hvalid i q (mem_iInter.mp hq i) x hx⟩

theorem exists_robust_strict_block
    {G M Params : Type*} [TopologicalSpace G] [TopologicalSpace M]
    [T2Space M] [LocallyCompactSpace M]
    (T : G) (K : Set M) (hK : IsCompact K)
    (d : (N : ℕ) → (Fin N → G) × M → ℝ)
    {I : ℕ → Type*} (chart : (N : ℕ) → I N → Set ((Fin N → G) × M))
    (hchart : ∀ N i, IsOpen (chart N i))
    (surviving : (N : ℕ) → Set ((Fin N → G) × M))
    (closed : ∀ N, IsClosed (surviving N))
    (cover : ∀ N, ∃ c : Finset (I N),
      fiber K (surviving N) (fun _ => T) ⊆
        ⋃ i ∈ c, (fun x => ((fun _ : Fin N => T), x)) ⁻¹' chart N i)
    (continuous : ∀ N i, ContinuousOn (d N) (chart N i))
    (bounded : ∀ N i, BddAbove ({0} ∪
      (fun x => d N ((fun _ => T), x)) ''
      (K ∩ (fun x => ((fun _ : Fin N => T), x)) ⁻¹' chart N i)))
    (parameters : (N : ℕ) → Params → (Fin N → G) → Prop)
    (parameterControl : ∀ N, ∃ p : Params, ∃ V : Set (Fin N → G),
      V ∈ 𝓝 (fun _ => T) ∧ ∀ word ∈ V, parameters N p word)
    (valid : (N : ℕ) → Set (Fin N → G))
    (validNeighborhood : ∀ N, valid N ∈ 𝓝 (fun _ => T))
    (Q Cmic ρ : ℝ) (positive : 0 < Cmic) (slack : Q < ρ)
    (pressure : Tendsto (fun N =>
      (coverCoefficient K (fiber K (surviving N) (fun _ => T))
        (fun i => (fun x => ((fun _ : Fin N => T), x)) ⁻¹' chart N i)
        (fun x => d N ((fun _ => T), x))) ^ ((N : ℝ)⁻¹)) atTop (𝓝 Q)) :
    ∃ N : ℕ, 0 < N ∧ ∃ (c : Finset (I N)) (v : c → Set M) (p : Params)
      (O : Set (Fin N → G)), O ∈ 𝓝 (fun _ => T) ∧
      (∀ i, IsOpen (v i)) ∧ (∀ i, IsCompact (closure (v i))) ∧
      ∀ word ∈ O, word ∈ valid N ∧ parameters N p word ∧
        (∀ i x, x ∈ closure (v i) → (word, x) ∈ chart N i) ∧
        (fiber K (surviving N) word ⊆ ⋃ i, v i) ∧
        0 ≤ (∑ i, coefficient K (Set.univ ×ˢ closure (v i)) (d N) word) ∧
        Cmic * (∑ i, coefficient K (Set.univ ×ˢ closure (v i)) (d N) word) < ρ ^ N := by
  classical
  let u := fun N (i : I N) => (fun x => ((fun _ : Fin N => T), x)) ⁻¹' chart N i
  have hu : ∀ N i, IsOpen (u N i) := fun N i =>
    (hchart N i).preimage (continuous_const.prodMk continuous_id)
  obtain ⟨N, hN, c, v, hvc, hvo, hvk, hvs, hstrict⟩ :=
    DomainPressureStrictBlock.exists_strict_refined_block K
      (fun N => fiber K (surviving N) (fun _ => T))
      (fun N => fiber_isCompact hK (closed N) _) u hu cover
      (fun N x => d N ((fun _ => T), x)) bounded Q Cmic ρ positive slack pressure
  obtain ⟨Vinner, hvinner, htinner, hinner⟩ := exists_robust_subcover hK (closed N)
    (Prod.snd ⁻¹' (⋃ i, v i)) ((isOpen_iUnion hvo).preimage continuous_snd)
    (fun _ => T) (fun _ hx => hvc hx)
  obtain ⟨Vchart, hvchart, htchart, hvalid⟩ := exists_chart_neighborhood (fun _ : Fin N => T)
    (fun i : c => chart N i) (fun i => hchart N i) v hvk (fun i _ hx => hvs i hx)
  obtain ⟨p, Vparams, hvparams, hparams⟩ := parameterControl N
  let outer := fun i : c => (Set.univ : Set (Fin N → G)) ×ˢ closure (v i)
  have hclosed : ∀ i : c, IsClosed (outer i) := fun _ => isClosed_univ.prod isClosed_closure
  have hsum : UpperSemicontinuousAt
      (fun word => ∑ i : c, coefficient K (outer i) (d N) word) (fun _ => T) := by
    apply LeanShared.DomainCylinderCoefficient.upperSemicontinuousAt_coverSum_on_neighborhood
      Finset.univ outer (fun _ => d N) hK (fun i _ => hclosed i)
      Vchart hvchart (fun _ => T) htchart
    intro i _
    apply (continuous N i).mono
    rintro ⟨word, x⟩ ⟨⟨hw, _⟩, hx⟩
    exact hvalid word hw i x hx.2
  have ha : UpperSemicontinuousAt
      (fun word => Cmic * ∑ i : c, coefficient K (outer i) (d N) word) (fun _ => T) :=
    (continuous_const.mul continuous_id).continuousAt.comp_upperSemicontinuousAt hsum
      (fun _ _ h => mul_le_mul_of_nonneg_left h positive.le)
  have hstrict' : Cmic * (∑ i : c, coefficient K (outer i) (d N) (fun _ => T)) < ρ ^ N := by
    simp only [outer, outer_coefficient]
    exact hstrict
  let threshold := {word | Cmic * ∑ i : c, coefficient K (outer i) (d N) word < ρ ^ N}
  have hthreshold : threshold ∈ 𝓝 (fun _ => T) := ha (ρ ^ N) hstrict'
  let O := valid N ∩ Vparams ∩ Vinner ∩ Vchart ∩ threshold
  have hO : O ∈ 𝓝 (fun _ => T) :=
    inter_mem (inter_mem (inter_mem (inter_mem (validNeighborhood N) hvparams)
      (hvinner.mem_nhds htinner)) (hvchart.mem_nhds htchart)) hthreshold
  refine ⟨N, hN, c, v, p, O, hO, hvo, hvk, ?_⟩
  intro word hw
  refine ⟨hw.1.1.1.1, hparams word hw.1.1.1.2, hvalid word hw.1.2,
    fun x hx => hinner word hw.1.1.2 x hx, ?_, hw.2⟩
  apply Finset.sum_nonneg
  intro i _
  apply coefficient_nonneg_on_fiber hK (hclosed i) word
  apply (continuous N i).comp (continuous_const.prodMk continuous_id).continuousOn
  intro x hx
  exact hvalid word hw.1.2 i x hx.2.2

end ConditionedStochasticStabilityHyperbolic.IntrinsicPressureBlock
