import APR3FourierRetraction

noncomputable section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000
open scoped BigOperators
namespace Grad.OrdinaryDiskReconstruction
open Grad.ClosedJets Grad.CartesianState Grad.CircularHighWeak
open Grad.FourierGrade Grad.COR12Extension Grad.COR13Completion Grad.DiskExtension.Operator
open Grad.GaugeCoefficients.Algebra

/-- Same-field Sobolev reconstruction at each fixed grade, in the literal
ordinary disk norm. The higher Fourier input is supplied, not assumed to be
the result of an elliptic regularity theorem. -/
theorem ordinarySobolevReconstruction_consumer (parameters : PhaseParameters) (grade : ℕ)
    (values : JGrade (ComplexEuclidean 1) grade) (original : AGrade parameters 1 0)
    (same : inclusion grade 0 (Nat.zero_le grade) values = completedExtension parameters original) :
    ∃ ordinary : unitDiskSobolev grade,
      unitDiskBulk grade ordinary = unitDiskBulk 0 (originalDisk parameters 0 original) ∧
      ‖ordinary‖ ≤ sameGradeConstant grade * ‖values‖ ∧
      ‖ordinary‖ ^ 2 = ∑ index : DerivativeIndex grade, ‖unitDiskDerivative grade index ordinary‖ ^ 2 :=
  ⟨fourierDisk parameters grade values, fourierDisk_reconstructs parameters grade values original same,
    fourierDisk_bound parameters grade values, unitDiskSobolev_norm_sq grade (fourierDisk parameters grade values)⟩

/-- Every smooth-core Cartesian derivative is the literal derivative of the
zero cell coefficient of the original physical-torus restriction. -/
theorem fourierDisk_core_derivative (parameters : PhaseParameters) (grade : ℕ)
    (values : JCore (ComplexEuclidean 1)) (index : DerivativeIndex grade) :
    unitDiskDerivative grade index (fourierDisk parameters grade (coreToGrade grade values)) =
      closedDerivativeL2 (derivativeMultiIndex index) (diskCellFourierCoefficientJet
        (ordinaryExtensionRetraction.restriction 1 (reconstructedTorusSmoothField values)) 0) :=
  (congrArg (unitDiskDerivative grade index) (fourierDisk_core parameters grade values)).trans
    (unitDiskDerivative_core grade index _)

theorem fourierDisk_core_norm (parameters : PhaseParameters) (grade : ℕ)
    (values : JCore (ComplexEuclidean 1)) :
    ‖unitSobolevRow grade (diskCellFourierCoefficientJet
      (ordinaryExtensionRetraction.restriction 1 (reconstructedTorusSmoothField values)) 0)‖ ≤
      sameGradeConstant grade * ‖coreToGrade grade values‖ := by
  have norm := (congrArg (fun value : unitDiskSobolev grade => ‖value‖)
    (fourierDisk_core parameters grade values)).trans (unitDiskCore_norm grade _)
  exact norm.symm.le.trans (fourierDisk_bound parameters grade (coreToGrade grade values))

end Grad.OrdinaryDiskReconstruction
