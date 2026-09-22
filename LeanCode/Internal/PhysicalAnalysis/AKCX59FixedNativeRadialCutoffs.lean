import AKCX58ActualOriginalSourceAllSpatialGrades

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option maxRecDepth 3000
open Set Filter MeasureTheory
open scoped ContDiff Topology
namespace Grad.CartesianStartup
open Grad.ClosedJets Grad.CartesianState Grad.PDEBootstrap Grad.SpatialDilation

private def nativeRadialBump (bump : ContDiffBump (0 : ℝ)) (point : Spatial) : ℝ := bump (‖point‖ ^ 2)

private theorem nativeRadialBump_smooth (bump : ContDiffBump (0 : ℝ)) : ContDiff ℝ ∞ (nativeRadialBump bump) :=
  bump.contDiff.comp (contDiff_norm_sq ℝ)

private theorem nativeRadialBump_one (bump : ContDiffBump (0 : ℝ)) (point : Spatial)
    (bound : ‖point‖ ^ 2 ≤ bump.rIn) : nativeRadialBump bump point = 1 := by
  apply bump.one_of_mem_closedBall
  simpa only [Metric.mem_closedBall,Real.dist_eq,sub_zero,abs_of_nonneg (sq_nonneg ‖point‖)] using bound

private theorem nativeRadialBump_supported (bump : ContDiffBump (0 : ℝ)) :
    tsupport (nativeRadialBump bump) ⊆ {point : Spatial | ‖point‖ ^ 2 ≤ bump.rOut} := by
  apply closure_minimal _ (isClosed_le (continuous_norm.pow 2) continuous_const)
  intro point present
  by_contra outside
  have zero : nativeRadialBump bump point = 0 := by
    apply bump.zero_of_le_dist
    simpa only [Real.dist_eq,sub_zero,abs_of_nonneg (sq_nonneg ‖point‖)] using (le_of_lt (lt_of_not_ge outside))
  exact present zero

private theorem nativeRadialBump_compact (bump : ContDiffBump (0 : ℝ)) (radius : ℝ)
    (positive : 0 ≤ radius) (bound : bump.rOut ≤ radius^2) : HasCompactSupport (nativeRadialBump bump) := by
  apply (isCompact_closedBall (0 : Spatial) radius).of_isClosed_subset (isClosed_tsupport _)
  intro point present
  have squared := (nativeRadialBump_supported bump present).trans bound
  rw [Metric.mem_closedBall,dist_zero_right]
  nlinarith [norm_nonneg point]

private def nativeInsideBump : ContDiffBump (0 : ℝ) := ⟨1/16,1/4,by norm_num,by norm_num⟩
private def nativeOuterBump : ContDiffBump (0 : ℝ) := ⟨1/4,9/16,by norm_num,by norm_num⟩
private def nativeCapBump : ContDiffBump (0 : ℝ) := ⟨1,4,by norm_num,by norm_num⟩

def actualNativeInsideCutoff : Spatial → ℝ := nativeRadialBump nativeInsideBump
def actualNativeOuterCutoff : Spatial → ℝ := nativeRadialBump nativeOuterBump
def actualNativeAnnularCutoff (point : Spatial) : ℝ := nativeRadialBump nativeCapBump point * (1-actualNativeInsideCutoff point)

theorem actualNativeInsideCutoff_smooth : ContDiff ℝ ∞ actualNativeInsideCutoff := nativeRadialBump_smooth _
theorem actualNativeOuterCutoff_smooth : ContDiff ℝ ∞ actualNativeOuterCutoff := nativeRadialBump_smooth _
theorem actualNativeAnnularCutoff_smooth : ContDiff ℝ ∞ actualNativeAnnularCutoff :=
  (nativeRadialBump_smooth _).mul (contDiff_const.sub actualNativeInsideCutoff_smooth)

theorem actualNativeInsideCutoff_compact : HasCompactSupport actualNativeInsideCutoff :=
  nativeRadialBump_compact nativeInsideBump (1/2) (by norm_num) (by norm_num [nativeInsideBump])
theorem actualNativeOuterCutoff_compact : HasCompactSupport actualNativeOuterCutoff :=
  nativeRadialBump_compact nativeOuterBump (3/4) (by norm_num) (by norm_num [nativeOuterBump])

theorem actualNativeOuterCutoff_inside : tsupport actualNativeOuterCutoff ⊆ openUnitDisk := by
  intro point present
  have squared := nativeRadialBump_supported nativeOuterBump present
  change ‖point‖^2 ≤ 9/16 at squared
  change ‖point‖ < 1
  nlinarith [norm_nonneg point]

theorem actualNativeCutoff_plateau : Set.EqOn actualNativeOuterCutoff (fun _ => 1) (tsupport actualNativeInsideCutoff) := by
  intro point present
  exact nativeRadialBump_one nativeOuterBump point (nativeRadialBump_supported nativeInsideBump present)

theorem actualNativeInsideCutoff_radial (first second : Spatial) (same : ‖first‖ = ‖second‖) :
    actualNativeInsideCutoff first = actualNativeInsideCutoff second := by
  simp only [actualNativeInsideCutoff,nativeRadialBump,same]

theorem actualNativeAnnularCutoff_radial (first second : Spatial) (same : ‖first‖ = ‖second‖) :
    actualNativeAnnularCutoff first = actualNativeAnnularCutoff second := by
  simp only [actualNativeAnnularCutoff,actualNativeInsideCutoff,nativeRadialBump,same]

theorem actualNativeCutoff_partition (point : Spatial) (inside : point ∈ openUnitDisk) :
    actualNativeAnnularCutoff point = 1-actualNativeInsideCutoff point := by
  have cap : nativeRadialBump nativeCapBump point = 1 := by
    apply nativeRadialBump_one
    change ‖point‖^2 ≤ 1
    change ‖point‖ < 1 at inside
    nlinarith [norm_nonneg point]
  rw [actualNativeAnnularCutoff,cap,one_mul]

theorem actualNativeAnnularCutoff_support : tsupport actualNativeAnnularCutoff ⊆
    {point : Spatial | (1/16 : ℝ) ≤ ‖point‖^2 ∧ ‖point‖^2 ≤ 4} := by
  apply closure_minimal _ ((isClosed_le continuous_const (continuous_norm.pow 2)).inter
    (isClosed_le (continuous_norm.pow 2) continuous_const))
  intro point present
  have capNonzero : nativeRadialBump nativeCapBump point ≠ 0 := by
    intro zero
    apply present
    simp only [actualNativeAnnularCutoff,zero,zero_mul]
  have capSupport : point ∈ tsupport (nativeRadialBump nativeCapBump) :=
    subset_tsupport (nativeRadialBump nativeCapBump) capNonzero
  refine ⟨?_,nativeRadialBump_supported nativeCapBump capSupport⟩
  by_contra below
  have one : actualNativeInsideCutoff point = 1 :=
    nativeRadialBump_one nativeInsideBump point (le_of_lt (lt_of_not_ge below))
  apply present
  simp only [actualNativeAnnularCutoff,one,sub_self,mul_zero]

theorem actualNativeAnnularCutoff_compact : HasCompactSupport actualNativeAnnularCutoff := by
  apply (isCompact_closedBall (0 : Spatial) 2).of_isClosed_subset (isClosed_tsupport _)
  intro point present
  have squared := (actualNativeAnnularCutoff_support present).2
  rw [Metric.mem_closedBall,dist_zero_right]
  nlinarith [norm_nonneg point]

theorem actualNativeAnnularCutoff_punctured (length : ℝ) (positive : 0 < length) :
    tsupport actualNativeAnnularCutoff ⊆ {point : Spatial |
      0 < ‖(originalStartupScale length positive).val • point‖ ∧ ‖(originalStartupScale length positive).val • point‖ < 1} := by
  intro point present
  have bounds := actualNativeAnnularCutoff_support present
  change (1/16 : ℝ) ≤ ‖point‖^2 ∧ ‖point‖^2 ≤ 4 at bounds
  have pointPositive : 0 < ‖point‖ := by nlinarith [bounds.1, norm_nonneg point]
  have pointBound : ‖point‖ ≤ 2 := by nlinarith [bounds.2, norm_nonneg point]
  have scalePositive := (originalStartupScale length positive).property.1
  have scaleBound : (originalStartupScale length positive).val ≤ 1/4 := by
    change min 1 length / 4 ≤ 1/4
    exact div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)
  change 0 < ‖(originalStartupScale length positive).val • point‖ ∧
    ‖(originalStartupScale length positive).val • point‖ < 1
  rw [norm_smul,Real.norm_eq_abs,abs_of_pos scalePositive]
  exact ⟨mul_pos scalePositive pointPositive,
    (mul_le_mul scaleBound pointBound (norm_nonneg _) (by norm_num)).trans_lt (by norm_num)⟩

def actualNativeAllOrderRadius (parameters : PhaseParameters) (length compact : ℝ)
    (positive : 0 < length) (nonnegative : 0 ≤ compact) : ℝ :=
  actualNativeSpatialRadius parameters length compact positive nonnegative actualNativeOuterCutoff
    actualNativeOuterCutoff_smooth actualNativeOuterCutoff_compact actualNativeOuterCutoff_inside

theorem actualNativeAllOrderRadius_positive (parameters : PhaseParameters) (length compact : ℝ)
    (positive : 0 < length) (nonnegative : 0 ≤ compact) :
    0 < actualNativeAllOrderRadius parameters length compact positive nonnegative :=
  actualNativeSpatialRadius_positive parameters length compact positive nonnegative actualNativeOuterCutoff
    actualNativeOuterCutoff_smooth actualNativeOuterCutoff_compact actualNativeOuterCutoff_inside

end Grad.CartesianStartup
