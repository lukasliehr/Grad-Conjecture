import AKAC26ExactOriginalPhysicalRecovery

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set Filter MeasureTheory
open scoped Topology ENNReal
namespace Grad.ActualSmoothPhysicalField
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularRestriction Grad.ActualPuncturedReconstruction Grad.ActualPhysicalField
open Grad.GaugeCoefficients.Physical.Allocation Grad.SourceCollarCoefficients

variable (parameters : PhaseParameters) (length rho epsilon : ℝ) (base : ACore parameters 3)
    (small : physicalBudget parameters base rho epsilon 6 ≤ originalCoefficientLowRadius parameters length)
    (collars : ℕ → ℝ) (positive : ∀ index,0 < collars index) (bounded : ∀ index,collars index ≤ 1)
    (polar : ∀ index,DivisionRow 3 (collars index)) (xi : ∀ index,DivisionRow 1 (collars index))

def correctedPhysicalVectorFamily (index : ℕ) : DivisionRow 3 (collars index) :=
  physicalUFromPolar parameters length rho epsilon base small (collars index) (positive index) (bounded index) (polar index)

def correctedPhysicalScalarOverRadiusFamily (index : ℕ) : DivisionRow 1 (collars index) :=
  polarScalarOverRadiusRow (collars index) (xi index) (polar index)

variable (decreasing : Antitone collars)
    (polarCompatible : ∀ first second (ordered : first ≤ second),
      originalBulkRestriction 3 (collars second) (collars first) (decreasing ordered) (polar second) = polar first)
    (xiCompatible : ∀ first second (ordered : first ≤ second),
      originalBulkRestriction 1 (collars second) (collars first) (decreasing ordered) (xi second) = xi first)

include polarCompatible in
theorem correctedPhysicalVectorFamily_compatible (first second : ℕ) (ordered : first ≤ second) :
    originalBulkRestriction 3 (collars second) (collars first) (decreasing ordered)
      (correctedPhysicalVectorFamily parameters length rho epsilon base small collars positive bounded polar second) =
      correctedPhysicalVectorFamily parameters length rho epsilon base small collars positive bounded polar first := by
  have same := physicalUFromPolar_restriction (collars second) (collars first) (decreasing ordered)
    parameters length rho epsilon base small (positive second) (positive first) (bounded first) (polar second)
  rw [polarCompatible first second ordered] at same
  exact same

include polarCompatible xiCompatible in
theorem correctedPhysicalScalarOverRadiusFamily_compatible (first second : ℕ) (ordered : first ≤ second) :
    originalBulkRestriction 1 (collars second) (collars first) (decreasing ordered)
      (correctedPhysicalScalarOverRadiusFamily collars polar xi second) =
      correctedPhysicalScalarOverRadiusFamily collars polar xi first := by
  have same := polarScalarOverRadiusRow_restriction (collars second) (collars first) (decreasing ordered) (xi second) (polar second)
  rw [polarCompatible first second ordered,xiCompatible first second ordered] at same
  exact same

include polarCompatible in
theorem correctedPhysicalVectorFamily_globalBound (cofinal : Tendsto collars atTop (𝓝 0))
    (constant : ℝ) (estimate : ∀ index,‖polar index‖ ≤ constant) :
    globalPhysicalBulkEnergy 3 collars (correctedPhysicalVectorFamily parameters length rho epsilon base small collars positive bounded polar) ≤
      ENNReal.ofReal ((5 * physicalUActionConstant parameters length 0 *
        (1+physicalBudget parameters base rho epsilon 5) * constant)^2) := by
  apply globalPhysicalBulkEnergy_bound 3 collars _ decreasing
    (correctedPhysicalVectorFamily_compatible parameters length rho epsilon base small collars positive bounded polar decreasing polarCompatible)
    positive cofinal
  intro index
  exact (physicalUFromPolar_bound parameters length rho epsilon base small (collars index) (positive index) (bounded index) (polar index)).trans
    (mul_le_mul_of_nonneg_left (estimate index) (mul_nonneg
      (mul_nonneg (by norm_num) (physicalUActionConstant_nonnegative parameters length rho epsilon base small 0))
      (by linarith [physicalBudget_nonnegative parameters base rho epsilon 5])))

include positive polarCompatible xiCompatible in
theorem correctedPhysicalScalarOverRadiusFamily_globalBound (cofinal : Tendsto collars atTop (𝓝 0))
    (polarConstant xiConstant : ℝ) (polarEstimate : ∀ index,‖polar index‖ ≤ polarConstant)
    (xiEstimate : ∀ index,‖xi index‖ ≤ xiConstant) :
    globalPhysicalBulkEnergy 1 collars (correctedPhysicalScalarOverRadiusFamily collars polar xi) ≤
      ENNReal.ofReal ((xiConstant+polarConstant)^2) := by
  apply globalPhysicalBulkEnergy_bound 1 collars _ decreasing
    (correctedPhysicalScalarOverRadiusFamily_compatible collars polar xi decreasing polarCompatible xiCompatible)
    positive cofinal
  intro index
  exact (polarScalarOverRadiusRow_bound (collars index) (xi index) (polar index)).trans
    (add_le_add (xiEstimate index) (polarEstimate index))

end Grad.ActualSmoothPhysicalField
