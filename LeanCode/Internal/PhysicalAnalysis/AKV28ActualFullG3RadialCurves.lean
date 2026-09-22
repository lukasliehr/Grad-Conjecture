import AKV27ActualDividedCartesianRowCurves
import AKN32SameFullG3Grades

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open Set Filter MeasureTheory
open scoped ContDiff
namespace Grad.AnnularGeneralSourceRegularity
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarCoefficients
open Grad.SourceCollarRestriction Grad.SourceCollarFullSource Grad.SourceBoundaryTrace Grad.SourceCollarBulk
open Grad.AxisCore Grad.QuotientProjection Grad.FlatSourceProjection
open Grad.GaugeCoefficients.Physical.Allocation Grad.ExhaustionSourceAllocation Grad.AnnularStrongData

variable (parameters : PhaseParameters) (length rho epsilon : ℝ) (field : ACore parameters 3)
    (small : physicalBudget parameters field rho epsilon 6 ≤ originalCoefficientLowRadius parameters length)
    (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (source : SmoothQuotient parameters) (flat : IsFlat source)

/-- Every term of the original full G3, including all three actual kappa
products, the circle correction and its original projection, has actual
all-grade radial Hilbert smoothness. -/
def actualFullG3RadialCurves {grade : ℕ} (large : 3 ≤ grade) :
    OriginalRowRadialCurves parameters lower
      (fullG3Row (power := 0) parameters length rho epsilon field small lower positive bounded.le large
        (quotientEta parameters grade source)) := by
  let divided := actualDividedSourceRadialCurves parameters length lower positive bounded large source flat
  let product := fun component : Fin 3 => actualKappaProductRadialCurves parameters length rho epsilon field small
    lower positive bounded component (divided component)
    (coefficientSourceProduct_literal (power := 0) parameters length rho epsilon field small lower positive bounded.le
      large (quotientEta parameters grade source) component)
  let scalar := (actualRestrictedCoreRadialCurves (grade := grade) parameters lower positive bounded (source 2)).smul ((length : ℂ)⁻¹)
  exact scalar.add ((((product 0).add (product 1)).sub (product 2)).sub (divided 1)).meanFree

/-- The strengthened original datum decodes to the same full G3 value.
This transports actual source regularity, without treating RG3 as free. -/
def actualOriginalG3RadialCurves :
    OriginalRowRadialCurves parameters lower
      (originalAngularDecode lower (actualOriginalG3Row parameters length rho epsilon field small lower positive bounded.le 0 source)) := by
  rw [(actualOriginalG3Row_decode parameters length rho epsilon field small lower positive bounded.le 0 source).1]
  apply (actualFullG3RadialCurves parameters length rho epsilon field small lower positive bounded source flat (by norm_num : 3 ≤ 6)).of_ae
  have inputs := originalFlatSource_division_inputs parameters (by norm_num : 3 ≤ 6) source flat
  filter_upwards [g3Rows_actual_coefficients parameters length rho epsilon field small
      (by norm_num : 0+4 ≤ 6) lower positive bounded.le (quotientEta parameters 6 source) inputs.1 inputs.2,
    fullG3Row_actual_coefficient parameters length rho epsilon field small (by norm_num : 3 ≤ 6)
      (quotientEta parameters 6 source) (power := 0) (by norm_num) lower positive bounded.le inputs.1 inputs.2,
    ae_restrict_mem measurableSet_Icc] with radius value full inside
  intro mode
  exact (value inside mode).1.trans (full inside mode).symm

end Grad.AnnularGeneralSourceRegularity
