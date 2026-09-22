import AKCK2OriginalSourceCurveCollarEnergy

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open Set Filter MeasureTheory
open scoped Topology BigOperators ENNReal
namespace Grad.OriginalCartesianTameEstimate
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.SourceCollarCoefficients Grad.SourceCollarFullSource Grad.SourceCollarBulk
open Grad.AxisCore Grad.QuotientProjection Grad.FlatSourceProjection Grad.ConstrainedGrades
open Grad.GaugeCoefficients.Physical.Allocation Grad.ExhaustionSourceAllocation
open Grad.AnnularGeneralSourceRegularity Grad.AnnularStrongData

/-- The actual AKV G3 curve is represented by the sharp SCS q+4 row.
This identifies existing realizations of the same source; no new G3 is chosen. -/
theorem actualG3SourceCurve_fourRow (parameters : PhaseParameters) (length rho epsilon : ℝ)
    (field : ACore parameters 3)
    (small : physicalBudget parameters field rho epsilon 6 ≤ originalCoefficientLowRadius parameters length)
    (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1) (grade : ℕ)
    (source : SmoothQuotient parameters) (flat : IsFlat source) :
    ∀ᵐ radius ∂volume.restrict (Icc lower 1), ∀ mode : ℤ × ℤ,
      (actualOriginalG3RadialCurves parameters length rho epsilon field small lower positive bounded source flat).curve (grade+1) radius mode =
      (annularFrequency mode.1 mode.2 : ℂ)^(grade+1) •
        ((Real.exp (Grad.PhaseAlgebra.radialPhase parameters radius mode.2) : ℂ) •
          originalRowCoefficient parameters (grade+1) lower
            (fullG3Row (power := grade+1) parameters length rho epsilon field small lower positive bounded.le
              (by omega : grade+1+3 ≤ grade+4) (quotientEta parameters (grade+4) source)) radius mode) := by
  filter_upwards [(actualOriginalG3RadialCurves parameters length rho epsilon field small lower positive bounded source flat).same (grade+1),
    actualFullG3_fourPayment_physical parameters length rho epsilon field small lower positive bounded.le grade source flat,
    actualG3Value_same_physical parameters length rho epsilon field small lower positive bounded.le 0 source flat,
    ae_restrict_mem measurableSet_Icc] with radius curve high low inside
  intro mode
  rw [curve mode]
  congr 2
  rw [(actualOriginalG3Row_decode parameters length rho epsilon field small lower positive bounded.le 0 source).1]
  exact (low inside mode).trans (high inside mode).symm

/-- The same all-cell G3 curve at q+1 has a genuine fixed-collar L2 bound
using original source q+4 and its independent source3 coefficient branch. -/
theorem actualG3SourceCurve_fourEnergy (parameters : PhaseParameters) (length rho epsilon : ℝ)
    (field : ACore parameters 3)
    (small : physicalBudget parameters field rho epsilon 6 ≤ originalCoefficientLowRadius parameters length)
    (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1) (grade : ℕ)
    (source : SmoothQuotient parameters) (flat : IsFlat source) :
    (∫⁻ radius in Icc lower 1, ENNReal.ofReal
      (‖(actualOriginalG3RadialCurves parameters length rho epsilon field small lower positive bounded source flat).curve (grade+1) radius‖^2)) ≤
      ENNReal.ofReal ((lower⁻¹ *
        (g3HighConstant parameters length grade * ‖quotientEta parameters (grade+4) source‖ +
          g3LowConstant parameters length grade * physicalBudget parameters field rho epsilon (grade+6) *
            ‖quotientEta parameters 3 source‖))^2) := by
  have energy := originalSourceCurve_collarEnergy parameters lower positive (grade+1) _ _
    (actualG3SourceCurve_fourRow parameters length rho epsilon field small lower positive bounded grade source flat)
  have payment := actualFullG3_fourPayment parameters length rho epsilon field small lower positive bounded.le grade source
  have paid := mul_le_mul_of_nonneg_left payment (inv_nonneg.mpr positive.le)
  have leftNonnegative := mul_nonneg (inv_nonneg.mpr positive.le) (norm_nonneg
    (fullG3Row (power := grade+1) parameters length rho epsilon field small lower positive bounded.le
      (by omega : grade+1+3 ≤ grade+4) (quotientEta parameters (grade+4) source)))
  exact energy.trans (ENNReal.ofReal_le_ofReal ((sq_le_sq₀ leftNonnegative (leftNonnegative.trans paid)).mpr paid))

end Grad.OriginalCartesianTameEstimate
