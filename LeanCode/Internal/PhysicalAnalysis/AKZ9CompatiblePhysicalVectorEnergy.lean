import AKZ6SamePhysicalVectorRecovery

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set Filter MeasureTheory
open scoped Topology BigOperators ENNReal
namespace Grad.ActualPhysicalField
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarCoefficients Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularReconstruction Grad.AnnularRestriction Grad.ActualPuncturedReconstruction
open Grad.GaugeCoefficients.Physical.Allocation

variable (parameters : PhaseParameters) (length rho epsilon : ℝ) (base : ACore parameters 3)
    (small : physicalBudget parameters base rho epsilon 6 ≤ originalCoefficientLowRadius parameters length)
include small

theorem physicalUActionConstant_nonnegative (power : ℕ) :
    0 ≤ physicalUActionConstant parameters length power := by
  have actual := originalInverseTransposeFamily_estimate parameters length rho epsilon base small
  exact mul_nonneg (physicalMatrixKernelConstant_nonnegative parameters 3 3 power)
    (add_nonneg (actual.fixedNonnegative (power + 1)) (actual.deviationNonnegative (power + 1)))

variable (collars : ℕ → ℝ) (positive : ∀ index, 0 < collars index) (bounded : ∀ index, collars index ≤ 1)
    (covariants : ∀ index, DivisionRow 3 (collars index))

def actualPhysicalVectorFamily (index : ℕ) : DivisionRow 3 (collars index) :=
  physicalUFromCovariant parameters length rho epsilon base small 0 (collars index) (positive index) (bounded index) (covariants index)

variable (decreasing : Antitone collars)
    (compatible : ∀ first second (ordered : first ≤ second),
      originalBulkRestriction 3 (collars second) (collars first) (decreasing ordered) (covariants second) = covariants first)
include compatible

theorem actualPhysicalVectorFamily_compatible (first second : ℕ) (ordered : first ≤ second) :
    originalBulkRestriction 3 (collars second) (collars first) (decreasing ordered)
      (actualPhysicalVectorFamily parameters length rho epsilon base small collars positive bounded covariants second) =
      actualPhysicalVectorFamily parameters length rho epsilon base small collars positive bounded covariants first := by
  have actual := physicalUFromCovariant_restriction parameters length rho epsilon base small 0 (collars second) (collars first)
    (positive second) (positive first) (bounded first) (decreasing ordered) (covariants second)
  rw [compatible first second ordered] at actual
  exact actual

theorem actualPhysicalVectorFamily_globalBound (cofinal : Tendsto collars atTop (𝓝 0)) (M constant : ℝ)
    (stateBound : physicalBudget parameters base rho epsilon 5 ≤ M)
    (estimate : ∀ index, ‖covariants index‖ ≤ constant) :
    globalPhysicalBulkEnergy 3 collars (actualPhysicalVectorFamily parameters length rho epsilon base small collars positive bounded covariants) ≤
      ENNReal.ofReal ((physicalUActionConstant parameters length 0 * (1 + M) * constant) ^ 2) := by
  apply globalPhysicalBulkEnergy_bound 3 collars _ decreasing
    (actualPhysicalVectorFamily_compatible parameters length rho epsilon base small collars positive bounded covariants decreasing compatible)
    positive cofinal
  intro index
  have actual := physicalUFromCovariant_bound parameters length rho epsilon base small 0 (collars index) (positive index)
    (bounded index) (covariants index)
  have coefficientNonnegative := physicalUActionConstant_nonnegative parameters length rho epsilon base small 0
  have Mnonnegative := (physicalBudget_nonnegative parameters base rho epsilon 5).trans stateBound
  have coefficientBound := mul_le_mul_of_nonneg_left (add_le_add (show (1 : ℝ) ≤ 1 from le_rfl) stateBound) coefficientNonnegative
  have baseBound := mul_le_mul_of_nonneg_right coefficientBound (norm_nonneg (covariants index))
  have payment := mul_le_mul_of_nonneg_left (estimate index) (mul_nonneg coefficientNonnegative (by positivity : 0 ≤ 1 + M))
  exact actual.trans (baseBound.trans payment)

end Grad.ActualPhysicalField
