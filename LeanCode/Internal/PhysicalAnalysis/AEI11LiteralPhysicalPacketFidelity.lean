import AEI10OriginalPhysicalLowMultipliers

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
open Set MeasureTheory Filter
open scoped Topology BigOperators ENNReal
namespace Grad.AnnularCurrentLow
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.AnnularVariational
open Grad.AnnularLowEnergy Grad.AnnularLowReference Grad.AnnularLowCompletion
open Grad.AnnularCurrentEnergy Grad.AnnularReconstruction Grad.BoundaryKernelAction Grad.GaugeCoefficients.Physical.Ledger

/-- The literal homogeneous normalized physical packet, without phase or
storage weights. Its second derivative slot is xi_zeta, not xi_zeta/L. -/
def lowPhysicalSevenSymbol (radius : ℝ) (mode : LowAnnularMode) (xi x : ℂ) : ComplexEuclidean 7 :=
  x • operatorBasis 0 +
    (Complex.I * ((mode.val.1 : ℝ) / radius : ℝ) * xi) • operatorBasis 1 +
    (Complex.I * (mode.val.2 : ℂ) * xi) • operatorBasis 2 +
    ((radius⁻¹ : ℝ) * xi) • operatorBasis 3

theorem lowSevenInputSymbol_physical (parameters : PhaseParameters) (lower length : ℝ)
    (lengthPositive : 0 < length) (positive : 0 < lower) (mode : LowAnnularMode)
    (radius : ℝ) (inside : lower ≤ radius) (weight xi x : ℂ) :
    lowSevenInputSymbol parameters lower length positive mode radius
      (scalarOne (weight * ((lowAmplitude length parameters.gamma mode * lowMu length radius mode.val.2 : ℝ) : ℂ) * xi))
      (scalarOne (weight * x)) = weight • lowPhysicalSevenSymbol radius mode xi x := by
  have angular : (lowInputAngularCurve parameters lower length positive mode radius : ℂ) *
      ((lowAmplitude length parameters.gamma mode * lowMu length radius mode.val.2 : ℝ) : ℂ) =
        (((mode.val.1 : ℝ) / radius : ℝ) : ℂ) := by
    exact_mod_cast lowInputAngularCurve_decode parameters lower length positive mode radius inside
  have cell : (lowInputCellCurve parameters lower length positive mode radius : ℂ) *
      ((lowAmplitude length parameters.gamma mode * lowMu length radius mode.val.2 : ℝ) : ℂ) = (mode.val.2 : ℂ) := by
    exact_mod_cast lowInputCellCurve_decode parameters lower length lengthPositive positive mode radius inside
  have radial : (lowInputRadiusCurve parameters lower length positive mode radius : ℂ) *
      ((lowAmplitude length parameters.gamma mode * lowMu length radius mode.val.2 : ℝ) : ℂ) = ((radius⁻¹ : ℝ) : ℂ) := by
    exact_mod_cast lowInputRadiusCurve_decode parameters lower length positive mode radius inside
  push_cast at angular cell radial
  apply PiLp.ext
  intro slot
  fin_cases slot <;> simp [lowSevenInputSymbol, lowPhysicalSevenSymbol, operatorBasis,
    scalarOne_apply_zero, Complex.real_smul]
  · linear_combination (Complex.I * weight * xi) * angular
  · linear_combination (Complex.I * weight * xi) * cell
  · linear_combination (weight * xi) * radial

end Grad.AnnularCurrentLow
