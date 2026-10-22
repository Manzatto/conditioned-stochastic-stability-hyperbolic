module
public import LeanShared.Analysis.CompactC1UniformDomains
public import LeanShared.Analysis.CompactSupportedHolderExtension
public import LeanShared.Analysis.UniformBilinearHolder
public import LeanShared.Analysis.BoundedHolderLowering
public import Mathlib.Analysis.Normed.Operator.Mul
public import Mathlib.Analysis.Normed.Operator.NormedSpace

/-! Uniform C^(1+a) globalization by a fixed smooth cutoff. Only the
actual value and first-derivative controls on a common convex valid
neighborhood are used. No parameter topology is required. -/
public noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace LeanShared.CompactOneHolderGlobalization
variable {E F P:Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem fixed_controls {G:Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (f:E→G) (smooth:ContDiff ℝ 1 f) (compact:HasCompactSupport f)
    {a:ℝ} (ha:0≤a) (ha1:a≤1) :
    ∃B H:ℝ,0≤B ∧ 0≤H ∧ (∀x,‖f x‖≤B) ∧
      ∀x y,‖f x-f y‖≤H*‖x-y‖^a :=by
  obtain ⟨B,hB,bound⟩:=compact.isCompact_range smooth.continuous |>.isBounded.exists_pos_norm_le
  obtain ⟨L,lip⟩:=CompactC1Lipschitz.exists_lipschitz f smooth compact
  refine ⟨B,(L:ℝ)+2*B,hB.le,by positivity,(fun x=>bound _ (mem_range_self x)),?_⟩
  intro x y
  apply BoundedHolderLowering.bound ha ha1 hB.le L.coe_nonneg
    (K:=univ) (f:=f) (fun z _=>bound _ (mem_range_self z)) ?_ x (mem_univ x) y (mem_univ y)
  intro z _ w _
  simpa only [Real.rpow_one] using lip.norm_sub_le z w

theorem exists_controls (ρ:E→ℝ) (smoothρ:ContDiff ℝ 2 ρ)
    (compact:HasCompactSupport ρ) {K U:Set E} (convex:Convex ℝ K)
    (openU:IsOpen U) (valid:K⊆U) (inside:tsupport ρ⊆interior K)
    (g:P→E→F) (regular:∀p,ContDiffOn ℝ 1 (g p) U)
    {a B D H:ℝ} (ha:0≤a) (ha1:a≤1) (hB:0≤B) (hD:0≤D) (hH:0≤H)
    (value:∀p x,x∈K→‖g p x‖≤B)
    (derivative:∀p x,x∈K→‖fderiv ℝ (g p) x‖≤D)
    (holder:∀p x,x∈K→∀y,y∈K→
      ‖fderiv ℝ (g p) x-fderiv ℝ (g p) y‖≤H*‖x-y‖^a) :
    ∃L:NNReal,∃C:ℝ,0≤C ∧ ∀p,
      ContDiff ℝ 1 (fun x=>ρ x • g p x) ∧
      HasCompactSupport (fun x=>ρ x • g p x) ∧
      LipschitzWith L (fun x=>ρ x • g p x) ∧
      (∀x,‖fderiv ℝ (fun x=>ρ x • g p x) x‖≤L) ∧
      ∀x y,‖fderiv ℝ (fun x=>ρ x • g p x) x-
        fderiv ℝ (fun x=>ρ x • g p x) y‖≤C*‖x-y‖^a :=by
  have smooth1:ContDiff ℝ 1 ρ:=smoothρ.of_le (by norm_num)
  have smoothD:ContDiff ℝ 1 (fderiv ℝ ρ):=
    (contDiff_succ_iff_fderiv.mp (show ContDiff ℝ (1+1) ρ from smoothρ)).2.2
  obtain ⟨R,HR,hR,hHR,rvalue,rholder⟩:=fixed_controls ρ smooth1 compact ha ha1
  obtain ⟨S,HS,hS,hHS,svalue,sholder⟩:=
    fixed_controls (fderiv ℝ ρ) smoothD (compact.fderiv ℝ) ha ha1
  have diff (p:P) (x:E) (hx:x∈K):DifferentiableAt ℝ (g p) x:=
    (((regular p x (valid hx)).contDiffAt (openU.mem_nhds (valid hx))).differentiableAt (by norm_num))
  have gholder (p:P):∀x∈K,∀y∈K,‖g p x-g p y‖≤(D+2*B)*‖x-y‖^a:=by
    apply BoundedHolderLowering.bound ha ha1 hB hD (value p)
    intro x hx y hy
    simpa only [Real.rpow_one] using
      Convex.norm_image_sub_le_of_norm_fderiv_le (diff p) (derivative p) convex hy hx
  have formula (p:P) (x:E) (hx:x∈K):
      fderiv ℝ (fun x=>ρ x • g p x) x=
        ρ x • fderiv ℝ (g p) x+(fderiv ℝ ρ x).smulRight (g p x):=
    ((smooth1.differentiable (by norm_num) x).hasFDerivAt.smul (diff p x hx).hasFDerivAt).fderiv
  let LS:ℝ→L[ℝ](E→L[ℝ]F)→L[ℝ](E→L[ℝ]F):=ContinuousLinearMap.lsmul ℝ ℝ
  let LR:(E→L[ℝ]ℝ)→L[ℝ]F→L[ℝ](E→L[ℝ]F):=ContinuousLinearMap.smulRightL ℝ E F
  let A:ℝ:=(R*H+HR*D)+(S*(D+2*B)+HS*B)
  have hA:0≤A:=by dsimp [A]; positivity
  have localD (p:P):∀x∈K,∀y∈K,
      ‖fderiv ℝ (fun x=>ρ x • g p x) x-fderiv ℝ (fun x=>ρ x • g p x) y‖≤A*‖x-y‖^a:=by
    intro x hx y hy
    have first:=UniformBilinearHolder.bound LS (show (0:ℝ)≤1 by norm_num)
      (fun u v=>by change ‖u • v‖≤1*‖u‖*‖v‖; rw [norm_smul,one_mul]) hR hHR hH hD
      (fun z _=>rvalue z) (derivative p) (fun z _ w _=>rholder z w) (holder p) x hx y hy
    have second:=UniformBilinearHolder.bound LR (show (0:ℝ)≤1 by norm_num)
      (fun u v=>by change ‖u.smulRight v‖≤1*‖u‖*‖v‖; rw [ContinuousLinearMap.norm_smulRight_apply,one_mul]) hS hHS (show 0≤D+2*B by positivity) hB
      (fun z _=>svalue z) (value p) (fun z _ w _=>sholder z w) (gholder p) x hx y hy
    rw [formula p x hx,formula p y hy]
    have split:ρ x • fderiv ℝ (g p) x+(fderiv ℝ ρ x).smulRight (g p x)-
        (ρ y • fderiv ℝ (g p) y+(fderiv ℝ ρ y).smulRight (g p y))=
      (LS (ρ x) (fderiv ℝ (g p) x)-LS (ρ y) (fderiv ℝ (g p) y))+
        (LR (fderiv ℝ ρ x) (g p x)-LR (fderiv ℝ ρ y) (g p y)):=by
      change _ = (ρ x • fderiv ℝ (g p) x-ρ y • fderiv ℝ (g p) y)+
        ((fderiv ℝ ρ x).smulRight (g p x)-(fderiv ℝ ρ y).smulRight (g p y))
      abel
    rw [split]
    exact (norm_add_le _ _).trans ((add_le_add first second).trans_eq (by dsimp [A];ring))
  have supportK:tsupport ρ⊆K:=inside.trans interior_subset
  obtain ⟨L,lip⟩:=CompactC1UniformDomains.exists_uniform_lipschitz ρ smooth1 compact
    (fun _ : P=>U) (fun _=>openU) (fun _=>supportK.trans valid) g regular hB hD
    (fun p x hx=>⟨value p x (supportK hx),derivative p x (supportK hx)⟩)
  have zeroD (p:P) (x:E) (hx:x∉tsupport ρ):
      fderiv ℝ (fun x=>ρ x • g p x) x=0:=
    fderiv_of_notMem_tsupport ℝ (fun hy=>hx (tsupport_smul_subset_left ρ (g p) hy))
  have globalD (p:P) (x:E):‖fderiv ℝ (fun x=>ρ x • g p x) x‖≤L:=
    norm_fderiv_le_of_lipschitz ℝ (lip p)
  obtain ⟨C,hC,globalH⟩:=CompactSupportedHolderExtension.exists_bound compact inside ha
    L.coe_nonneg hA (fun p=>fderiv ℝ (fun x=>ρ x • g p x)) zeroD globalD localD
  refine ⟨L,C,hC,fun p=>⟨?_,compact.smul_right,lip p,globalD p,globalH p⟩⟩
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx:x∈tsupport ρ
  · exact smooth1.contDiffAt.smul
      ((regular p x (valid (supportK hx))).contDiffAt (openU.mem_nhds (valid (supportK hx))))
  · apply (contDiffAt_const (c:=(0:F))).congr_of_eventuallyEq
    filter_upwards [isClosed_tsupport ρ |>.isOpen_compl.mem_nhds hx] with y hy
    rw [image_eq_zero_of_notMem_tsupport hy,zero_smul]
end LeanShared.CompactOneHolderGlobalization
