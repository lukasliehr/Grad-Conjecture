import AJG8SameFullCompletedCovariants

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
open Set MeasureTheory Filter
open scoped Topology ENNReal
namespace Grad.AnnularPhysicalReconstruction
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.AnnularReconstruction
open Grad.SourceCollarCoefficients Grad.BoundaryKernelAction Grad.AnnularKernelL2
open Grad.AnnularCurrentLow Grad.AnnularLowEnergy

/-- Remove the original common rho^(1/2) storage factor, at the actual radius.
The phase conversion is the exact AJG1 map, not an identification of weights. -/
def physicalBulkLift (parameters : PhaseParameters) (lower : ℝ) (positive : 0 < lower)
    (radius : RadialPoint) (dimension : ℕ) :
    CellL2 dimension →L[ℂ] NegativeTrace (radialKernelParameters parameters radius) 0 0 dimension :=
  (lowStorageWeight lower positive radius.val : ℂ)⁻¹ • bulkNegativeLift parameters radius dimension

theorem physicalBulkLift_coefficient (parameters : PhaseParameters) (lower : ℝ) (positive : 0 < lower)
    (radius : RadialPoint) (dimension : ℕ) (field : CellL2 dimension) (mode : ℤ × ℤ) :
    negativeTraceCoefficient (radialKernelParameters parameters radius) 0 0
      (physicalBulkLift parameters lower positive radius dimension field) mode =
      (lowRhoPhysicalWeight parameters lower positive radius.val mode : ℂ)⁻¹ • field mode := by
  change negativeTraceCoefficient _ 0 0
    ((lowStorageWeight lower positive radius.val : ℂ)⁻¹ • bulkNegativeLift parameters radius dimension field) mode = _
  rw [negativeTraceCoefficient_smul, bulkNegativeLift_coefficient, smul_smul]
  congr 1
  simp only [lowRhoPhysicalWeight, Complex.ofReal_mul, mul_inv_rev]
  exact mul_comm _ _

def originalPhysicalSlice {dimension : ℕ} (parameters : PhaseParameters) (lower : ℝ)
    (positive : 0 < lower) (bounded : lower ≤ 1) (field : DivisionRow dimension lower) (radius : ℝ) :
    NegativeTrace (radialKernelParameters parameters (collarRadius lower positive bounded radius)) 0 0 dimension :=
  physicalBulkLift parameters lower positive (collarRadius lower positive bounded radius) dimension
    (collectRadial lower field radius)

/-- Literal fidelity to the original Fourier field; the same r^(-7/4)
weight and same original radial analytic phase are removed exactly once. -/
theorem originalPhysicalSlice_coefficient {dimension : ℕ} (parameters : PhaseParameters) (lower : ℝ)
    (positive : 0 < lower) (bounded : lower ≤ 1) (field : DivisionRow dimension lower) :
    ∀ᵐ radius ∂volume.restrict (Icc lower 1), ∀ mode,
      negativeTraceCoefficient (radialKernelParameters parameters (collarRadius lower positive bounded radius)) 0 0
        (originalPhysicalSlice parameters lower positive bounded field radius) mode =
        lowRhoPhysicalCoefficient parameters lower positive field radius mode := by
  filter_upwards [collectRadial_ae lower field, ae_restrict_mem measurableSet_Icc] with radius collected inside
  intro mode
  rw [originalPhysicalSlice, physicalBulkLift_coefficient, collected mode,
    collarRadius_literal lower positive bounded radius inside]
  rfl

theorem BulkSevenCompatibility.smul (field : CellL2 7) (compatible : BulkSevenCompatibility field)
    (scalar : ℂ) : BulkSevenCompatibility (scalar • field) := by
  constructor
  · intro cell; change scalar * field (0,cell) 0 = 0; rw [compatible.massMean, mul_zero]
  · intro cell; change scalar * field (0,cell) 3 = 0; rw [compatible.scalarMean, mul_zero]
  · intro mode
    change scalar * field mode 1 = (Complex.I * (mode.1 : ℂ)) * (scalar * field mode 3)
    rw [compatible.scalarDerivative]; ring
  · intro mode
    change scalar * field mode 5 = (Complex.I * (mode.1 : ℂ)) * (scalar * field mode 4)
    rw [compatible.sourceDerivative]; ring
  · intro cell; change scalar * field (0,cell) 2 = 0; rw [compatible.cellMean, mul_zero]
  · intro cell; change scalar * field (0,cell) 6 = 0; rw [compatible.sourceTwoMean, mul_zero]

/-- The scalar radial unweight commutes with the SAME completed reconstruction. -/
theorem physicalBulkLift_action {source target : ℕ} (parameters : PhaseParameters) (lower : ℝ)
    (positive : 0 < lower) (radius : RadialPoint) (action : CellL2 source →L[ℂ] CellL2 target)
    (field : CellL2 source) :
    physicalBulkLift parameters lower positive radius target (action field) =
      bulkNegativeLift parameters radius target
        (action ((lowStorageWeight lower positive radius.val : ℂ)⁻¹ • field)) := by
  rw [map_smul, map_smul]
  rfl

end Grad.AnnularPhysicalReconstruction
