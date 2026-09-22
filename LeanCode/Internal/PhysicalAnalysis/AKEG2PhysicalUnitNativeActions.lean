import AKEG1PhysicalUnitNativeMatrices

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 4000
namespace Grad.OriginalCoreRealization.OriginalUnitRankState
open Grad.ClosedJets Grad.CartesianState Grad.GenericCarriers Grad.SourceCollar Grad.SourceCollarCoefficients
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical Grad.GaugeCoefficients.Physical.Frame Grad.GaugeCoefficients.Physical.Allocation
open Grad.GaugeCoefficients.Physical.Ledger Grad.ActualCurrentPrimitives Grad.Constraints.Gauges
open Grad.ActualScaledNativeCoefficients
variable {parameters : PhaseParameters} {length radius : ℝ}
    (state : OriginalUnitRankState parameters length radius)

/-- Actual physical-length planar coefficient product, with the original full native matrix action retained. -/
theorem planarForce_action (grade : ℕ) (angle : ℝ) (point : ClosedDisk) (value : ComplexEuclidean 3) :
    coefficientPhysicalValue (state.data.rotatedPlanarProduct grade) angle point value =
      planarPartMap (coefficientPhysicalValue (forceMatrixFamily parameters length state.epsilon state.field grade) angle
        point value) := by
  rw [operatorMatrix_action]
  have matrix := congrArg (fun matrix : Matrix (Fin 2) (Fin 3) ℂ => WithLp.toLp 2 (matrix.mulVec value))
    (state.planarForce_matrix grade angle point)
  exact matrix.trans ((nativePlanarSelection _ value).trans
    (congrArg planarPartMap (operatorMatrix_action _ value).symm))

/-- Actual physical-length third coefficient product; its -2L force normalization may be applied after this equality. -/
theorem thirdForce_action (grade : ℕ) (angle : ℝ) (point : ClosedDisk) (value : ComplexEuclidean 3) :
    coefficientPhysicalValue (state.data.rotatedThirdProduct grade) angle point value =
      toroidalPartMap (coefficientPhysicalValue (forceMatrixFamily parameters length state.epsilon state.field grade) angle
        point value) := by
  rw [operatorMatrix_action]
  have matrix := congrArg (fun matrix : Matrix (Fin 1) (Fin 3) ℂ => WithLp.toLp 2 (matrix.mulVec value))
    (state.thirdForce_matrix grade angle point)
  exact matrix.trans ((nativeThirdSelection _ value).trans
    (congrArg toroidalPartMap (operatorMatrix_action _ value).symm))

/-- Actual physical-length h product is the full signed native cofactor action plus the same covariant itself. -/
theorem cofactorFlux_action (grade : ℕ) (angle : ℝ) (point : ClosedDisk) (value : ComplexEuclidean 3) :
    coefficientPhysicalValue (state.data.fluxDeviation grade) angle point value =
      coefficientPhysicalValue (originalCofactorFamily parameters length state.epsilon state.field grade) angle
        point value + value := by
  rw [operatorMatrix_action]
  have matrix := congrArg (fun matrix : Matrix (Fin 3) (Fin 3) ℂ => WithLp.toLp 2 (matrix.mulVec value))
    (state.cofactorFlux_matrix grade angle point)
  refine matrix.trans ?_
  rw [Matrix.add_mulVec,Matrix.one_mulVec]
  have native := operatorMatrix_action
    (coefficientPhysicalValue (originalCofactorFamily parameters length state.epsilon state.field grade) angle
      point) value
  exact congrArg (fun other : ComplexEuclidean 3 => other + value) native.symm

end Grad.OriginalCoreRealization.OriginalUnitRankState
