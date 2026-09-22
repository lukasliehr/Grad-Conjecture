import BCT1OriginalBoundaryFamily

noncomputable section

set_option maxHeartbeats 1000000

namespace Grad.ActualBoundaryPrimitives

open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarCoefficients Grad.SourceCollar
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.Allocation Grad.GaugeCoefficients.Physical.Frame
open Grad.GaugeCoefficients.Physical.InverseAllocation Grad.GaugeCoefficients.Physical.Ledger

/-- AD19's actual boundary covector, with algebraic (not Hermitian)
transpose and the physical seed inverse. -/
def originalPhysicalBoundaryMatrix (parameters : PhaseParameters)
    (L rho alpha delta parameter epsilon : ℝ) (field : ACore parameters 3)
    (axialAngle : ℝ) (point : ClosedDisk) : Matrix (Fin 1) (Fin 3) ℂ :=
  (spatialColumn point).transpose * (physicalSeedMatrix rho alpha delta parameter axialAngle)⁻¹ *
    planarPhysicalInclusion.transpose *
      (originalPhysicalFrameMatrix parameters L epsilon field axialAngle point)⁻¹.transpose

theorem originalBoundaryFamily_matrix (parameters : PhaseParameters)
    (L rho alpha delta parameter epsilon compact : ℝ) (field : ACore parameters 3)
    (compactNonnegative : 0 ≤ compact) (alphaSmall : |alpha| ≤ compact)
    (deltaSmall : |delta| ≤ compact) (parameterSmall : |parameter| ≤ compact)
    (low : physicalBudget parameters field rho epsilon 6 ≤ boundaryCoefficientLowRadius parameters L compact)
    (grade : ℕ) (axialAngle : ℝ) (point : ClosedDisk) :
    familyMatrix (originalBoundaryFamily parameters L rho alpha delta parameter epsilon field)
      grade axialAngle point =
      originalPhysicalBoundaryMatrix parameters L rho alpha delta parameter epsilon field axialAngle point := by
  have margin := boundaryCoefficient_seed_margin parameters L rho alpha delta parameter epsilon compact
    field compactNonnegative alphaSmall deltaSmall parameterSmall low
  have originalLow := low.trans (boundaryCoefficientLowRadius_le_original parameters L compact)
  have seedCoherent := actualSeedInverse_coherent (unitDiskAdmissible parameters)
    rho alpha delta parameter margin.2.2
  have inverseCoherent := (originalInverseFamily_estimate parameters L rho epsilon field originalLow).actualCoherent
  have seedInverse : familyMatrix (actualSeedInverse (unitDiskAdmissible parameters)
      rho alpha delta parameter) grade axialAngle point =
      (physicalSeedMatrix rho alpha delta parameter axialAngle)⁻¹ :=
    (Matrix.inv_eq_right_inv (actualSeedInverse_matrix_identity (unitDiskAdmissible parameters)
      rho alpha delta parameter margin.2.2 grade axialAngle point).1).symm
  rw [originalBoundaryFamily, traceFamily_matrix (unitDiskAdmissible parameters) _ _
    seedCoherent inverseCoherent, seedInverse,
    originalInverseFamily_eq_matrixInverse parameters L rho epsilon field originalLow]
  rfl

theorem referenceBoundaryFamily_matrix (parameters : PhaseParameters)
    (grade : ℕ) (axialAngle : ℝ) (point : ClosedDisk) :
    familyMatrix (referenceBoundaryFamily parameters) grade axialAngle point = circleTraceCovector point :=
  traceFamily_circle (unitDiskAdmissible parameters) grade axialAngle point

/-- Literal AD19 substitution U=F^-T a_c, before the fixed high projection. -/
theorem originalPhysicalBoundaryMatrix_apply (parameters : PhaseParameters)
    (L rho alpha delta parameter epsilon : ℝ) (field : ACore parameters 3)
    (axialAngle : ℝ) (point : ClosedDisk) (covariant : Fin 3 → ℂ) :
    (originalPhysicalBoundaryMatrix parameters L rho alpha delta parameter epsilon field
      axialAngle point).mulVec covariant =
      ((spatialColumn point).transpose * (physicalSeedMatrix rho alpha delta parameter axialAngle)⁻¹ *
        planarPhysicalInclusion.transpose).mulVec
        ((originalPhysicalFrameMatrix parameters L epsilon field axialAngle point)⁻¹.transpose.mulVec covariant) := by
  unfold originalPhysicalBoundaryMatrix
  rw [Matrix.mulVec_mulVec]

end Grad.ActualBoundaryPrimitives
