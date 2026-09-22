import AIA16CompletedCircularPairing
import AED1CompletedEnergyPairing

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open Set Filter MeasureTheory
open scoped Topology BigOperators ENNReal
namespace Grad.AnnularCircularForm
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularReconstruction Grad.BoundaryKernelAction Grad.AnnularCurrentEnergy Grad.AnnularVariational
open Grad.AnnularTiltedReference

/-- Exact BF base circular high form is the accepted tilted reference form on the original inner-zero test space. -/
theorem circularHighBulkFormValue_eq_reference (parameters : PhaseParameters) (lower L : ℝ)
    (positive : 0 < lower) (bounded : lower < 1) (lengthPositive : 0 < L)
    (widthHalf : parameters.gamma ≤ 1 / 2) (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * L))
    (field test : annularEnergySpace lower L positive)
    (zero : annularEnergyTrace lower L positive bounded lengthPositive 0 test = 0) :
    circularHighBulkFormValue parameters L lower positive bounded.le lengthPositive widthHalf widthLength 0 field test =
      annularTiltFormValue parameters lower L positive lengthPositive widthHalf widthLength field test := by
  rw [circularHighBulkFormValue_radial, annularTiltForm_factorized,
    annularEnergy_cross_innerZero lower L positive bounded lengthPositive test field zero]
  abel

/-- Immediate exact weak-test consumer on the SAME accepted V carrier. -/
theorem circularHighBulkFormValue_innerZero (parameters : PhaseParameters) (lower L : ℝ)
    (positive : 0 < lower) (bounded : lower < 1) (lengthPositive : 0 < L)
    (widthHalf : parameters.gamma ≤ 1 / 2) (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * L))
    (field : annularEnergySpace lower L positive) (test : annularInnerZero lower L positive bounded lengthPositive) :
    circularHighBulkFormValue parameters L lower positive bounded.le lengthPositive widthHalf widthLength 0 field test.val =
      annularTiltFormValue parameters lower L positive lengthPositive widthHalf widthLength field test.val :=
  circularHighBulkFormValue_eq_reference parameters lower L positive bounded lengthPositive widthHalf widthLength field test.val test.property

end Grad.AnnularCircularForm
