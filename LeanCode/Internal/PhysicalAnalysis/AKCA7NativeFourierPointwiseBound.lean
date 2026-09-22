import AKCA6ActualGlobalCriticalEnergy

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
open Set Filter MeasureTheory
open scoped Topology ENNReal BigOperators
namespace Grad.OriginalCoreRealization
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace Grad.SourceCollarCoefficients
open Grad.ActualSmoothPhysicalField Grad.AnnularPhysicalFourier Grad.AnnularCurrentLow Grad.AnnularJointRegularity
open Grad.BoundaryTrace Grad.BoundaryLift Grad.AnnularGeneralSourceRegularity
open Grad.AnnularSourceGraph
open Grad.AnnularClosedJointRegularity Grad.AnnularRegularity Grad.GaugeCoefficients.Physical.Ledger

def angularReadoutConstant : ℝ := ∑' mode : ℤ × ℤ, (annularFrequency mode.1 mode.2 ^ 4)⁻¹

theorem angularReadoutConstant_nonnegative : 0 ≤ angularReadoutConstant := by
  apply tsum_nonneg
  intro mode
  positivity

theorem physicalCharacterSeries_fourth_bound (field reserve : CellL2 1)
    (same : ∀ mode : ℤ × ℤ, reserve mode = ((annularFrequency mode.1 mode.2 ^ 4 : ℝ) : ℂ) • field mode)
    (angles : ℝ × ℝ) : ‖physicalCharacterSeries (fun mode => field mode) angles‖ ≤ angularReadoutConstant * ‖reserve‖ := by
  have coefficientBound (mode : ℤ × ℤ) : ‖field mode‖ ≤ ‖reserve‖ * (annularFrequency mode.1 mode.2 ^ 4)⁻¹ := by
    rw [← div_eq_mul_inv]
    apply (le_div_iff₀ (pow_pos (annularFrequency_pos mode) _)).mpr
    have coordinate := lp.norm_apply_le_norm (by norm_num : (2 : ENNReal) ≠ 0) reserve mode
    rw [same mode,norm_smul,Complex.norm_real,Real.norm_of_nonneg (pow_nonneg (annularFrequency_pos mode).le _)] at coordinate
    nlinarith only [coordinate]
  have majorant := annularLattice_inverse_four_summable.mul_left ‖reserve‖
  have summable : Summable (fun mode : ℤ × ℤ => ‖field mode‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) coefficientBound majorant
  have termNorm : Summable (fun mode : ℤ × ℤ =>
      ‖(cellExponential mode.1 angles.1 * cellExponential mode.2 angles.2) • field mode‖) := by
    simpa only [norm_smul,norm_mul,cellExponential_norm,one_mul] using summable
  calc
    _ ≤ ∑' mode : ℤ × ℤ, ‖field mode‖ := by
      simpa only [norm_smul,norm_mul,cellExponential_norm,one_mul,physicalCharacterSeries] using norm_tsum_le_tsum_norm termNorm
    _ ≤ ∑' mode : ℤ × ℤ, ‖reserve‖ * (annularFrequency mode.1 mode.2 ^ 4)⁻¹ :=
      summable.tsum_le_tsum coefficientBound majorant
    _ = _ := by rw [tsum_mul_left]; exact mul_comm _ _

variable {dimension : ℕ} {parameters : PhaseParameters} {lower : ℝ} {positive : 0 < lower}
    {row : DivisionRow dimension lower} (curves : SmoothLowPhysicalRow parameters lower positive row)
    (bounded : lower < 1)

include bounded in
theorem nativePhysicalCurve_norm_le (grade : ℕ) (radius : ℝ) (inside : radius ∈ Icc lower 1) :
    ‖curves.physicalCurve grade radius‖ ≤ ‖curves.curve grade radius‖ := by
  apply lp.norm_mono (by norm_num)
  intro mode
  rw [curves.physicalCurve_coefficient bounded grade radius inside mode,norm_smul,Complex.norm_real,
    Real.norm_of_nonneg (Real.exp_pos _).le]
  exact mul_le_of_le_one_left (norm_nonneg _) (by
    change inversePhaseCurve parameters mode.2 radius ≤ 1
    exact inversePhaseCurve_le_one parameters mode.2 radius (positive.le.trans inside.1) inside.2)

theorem nativeComponentField_fourth_bound (component : Fin dimension) (radius : ℝ)
    (inside : radius ∈ Icc lower 1) (angles : ℝ × ℝ) :
    ‖curves.componentField bounded component (radius,angles)‖ ≤
      angularReadoutConstant * ‖physicalHilbertComponent parameters dimension component‖ * ‖curves.curve 4 radius‖ := by
  change ‖physicalCharacterSeries (fun mode => curves.componentCurve component 0 (radialClamp lower bounded.le radius) mode) angles‖ ≤ _
  rw [radialClamp_eq lower bounded.le radius inside]
  have series := physicalCharacterSeries_fourth_bound (curves.componentCurve component 0 radius)
    (curves.componentCurve component 4 radius) (curves.componentCurve_grade bounded component 4 radius inside) angles
  apply series.trans
  calc
    _ ≤ angularReadoutConstant * (‖physicalHilbertComponent parameters dimension component‖ * ‖curves.physicalCurve 4 radius‖) :=
      mul_le_mul_of_nonneg_left ((physicalHilbertComponent parameters dimension component).le_opNorm _) angularReadoutConstant_nonnegative
    _ ≤ angularReadoutConstant * (‖physicalHilbertComponent parameters dimension component‖ * ‖curves.curve 4 radius‖) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (nativePhysicalCurve_norm_le curves bounded 4 radius inside) (norm_nonneg _)) angularReadoutConstant_nonnegative
    _ = _ := by ring

def nativeFieldReadoutConstant (parameters : PhaseParameters) (dimension : ℕ) : ℝ :=
  ∑ component : Fin dimension, ‖matrixUnit (input := 1) (output := dimension) component 0‖ *
    (angularReadoutConstant * ‖physicalHilbertComponent parameters dimension component‖)

theorem nativeFieldReadoutConstant_nonnegative (parameters : PhaseParameters) (dimension : ℕ) :
    0 ≤ nativeFieldReadoutConstant parameters dimension := by
  unfold nativeFieldReadoutConstant
  exact Finset.sum_nonneg (fun _ _ => mul_nonneg (norm_nonneg _) (mul_nonneg angularReadoutConstant_nonnegative (norm_nonneg _)))

theorem nativeFullField_fourth_bound (radius : ℝ) (inside : radius ∈ Icc lower 1) (angles : ℝ × ℝ) :
    ‖curves.fullField bounded (radius,angles)‖ ≤ nativeFieldReadoutConstant parameters dimension * ‖curves.curve 4 radius‖ := by
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ component : Fin dimension,
        (‖matrixUnit (input := 1) (output := dimension) component 0‖ *
          (angularReadoutConstant * ‖physicalHilbertComponent parameters dimension component‖)) * ‖curves.curve 4 radius‖ := by
      apply Finset.sum_le_sum
      intro component _
      apply ((matrixUnit component 0).le_opNorm _).trans
      exact (mul_le_mul_of_nonneg_left (nativeComponentField_fourth_bound curves bounded component radius inside angles) (norm_nonneg _)).trans_eq (by ring)
    _ = _ := by rw [← Finset.sum_mul]; rfl

end Grad.OriginalCoreRealization
