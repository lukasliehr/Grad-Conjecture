import AKQ8TiltedAxisFrameAlgebra
import SCC7ActualSignedCofactor

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace Grad.FinitePhysicalJetLift
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollar Grad.SourceCollarCoefficients
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical
open Grad.GaugeCoefficients.Physical.Allocation Grad.GaugeCoefficients.Physical.Frame
open Grad.GaugeCoefficients.Physical.Ledger Grad.NonlinearDivision

/-- The actual two planar rows of the original physical frame at its axis. -/
def originalAxisPlanarMatrix (parameters : PhaseParameters) (length epsilon : ℝ)
    (field : ACore parameters 3) (angle : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  let frame := originalPhysicalFrameMatrix parameters length epsilon field angle closedOrigin
  !![frame 0 0,frame 0 1;frame 2 0,frame 2 1]

def originalAxisTilt (parameters : PhaseParameters) (length epsilon : ℝ)
    (field : ACore parameters 3) (angle : ℝ) : ComplexEuclidean 2 :=
  let frame := originalPhysicalFrameMatrix parameters length epsilon field angle closedOrigin
  WithLp.toLp 2 ![frame 1 0,frame 1 1]

def originalAxisInverseGram (parameters : PhaseParameters) (length epsilon : ℝ)
    (field : ACore parameters 3) (angle : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  let planar := originalAxisPlanarMatrix parameters length epsilon field angle
  (planar.transpose * planar)⁻¹

theorem originalAxis_cellDerivative_zero (parameters : PhaseParameters) (field : ACore parameters 3)
    (vanishes : ∀ cell, (field.val cell).value closedOrigin = 0) (order : ℕ) (angle : ℝ) :
    ordinaryDerivativeExtension (originalCoefficientCore parameters field) emptyCartesianWord order
      (closedOrigin,(angle : CellCircle)) = 0 := by
  rw [ordinaryDerivativeExtension_apply]
  simp only [originalCoefficientCore_apply,closedDerivative_zero_order,vanishes,smul_zero,tsum_zero]

theorem originalAxis_thirdColumn (parameters : PhaseParameters) (length epsilon : ℝ)
    (field : ACore parameters 3) (vanishes : ∀ cell, (field.val cell).value closedOrigin = 0)
    (angle : ℝ) (row : Fin 3) :
    originalPhysicalFrameMatrix parameters length epsilon field angle closedOrigin row 2 =
      if row = 1 then 1 else 0 := by
  have zeroth := originalAxis_cellDerivative_zero parameters field vanishes 0 angle
  have first := originalAxis_cellDerivative_zero parameters field vanishes 1 angle
  unfold originalPhysicalFrameMatrix originalPhysicalFrameDeviation
  dsimp only
  rw [zeroth,first,operatorMatrix_add,referenceFrame_matrix]
  fin_cases row <;>
    simp [operatorMatrix,columnEmbedding_apply,referenceStateValue,closedOrigin,physicalRotation]

/-- Exact axis frame of the original physical field, using the genuine
vanishing axis values of its full Fourier coefficients. -/
theorem originalAxis_frame (parameters : PhaseParameters) (length epsilon : ℝ)
    (field : ACore parameters 3) (vanishes : ∀ cell, (field.val cell).value closedOrigin = 0) (angle : ℝ) :
    originalPhysicalFrameMatrix parameters length epsilon field angle closedOrigin =
      tiltedAxisFrame (originalAxisPlanarMatrix parameters length epsilon field angle)
        (originalAxisTilt parameters length epsilon field angle) := by
  ext row column
  fin_cases row <;> fin_cases column <;>
    simp [tiltedAxisFrame,originalAxisPlanarMatrix,originalAxisTilt,originalAxis_thirdColumn parameters length epsilon field vanishes angle]

theorem originalAxisPlanarMatrix_isUnit_det (parameters : PhaseParameters) (length rho epsilon : ℝ)
    (field : ACore parameters 3) (vanishes : ∀ cell, (field.val cell).value closedOrigin = 0)
    (low : physicalBudget parameters field rho epsilon 6 ≤ originalCoefficientLowRadius parameters length)
    (angle : ℝ) : IsUnit (originalAxisPlanarMatrix parameters length epsilon field angle).det := by
  have margin := originalCoefficient_low_margin parameters length rho epsilon field low
  have laws := originalInverseFamily_matrix_identity parameters length epsilon field margin.2.2 0 angle closedOrigin
  have nonzero := Matrix.det_ne_zero_of_left_inverse laws.2
  rw [originalAxis_frame parameters length epsilon field vanishes,tiltedAxisFrame_det] at nonzero
  exact isUnit_iff_ne_zero.mpr (neg_ne_zero.mp nonzero)

/-- Literal AM26 specialization of the accepted original signed cofactor.
The inverse Gram and both tilt couplings are extracted from the same frame. -/
theorem originalAxis_signedCofactor (parameters : PhaseParameters) (length rho epsilon : ℝ)
    (field : ACore parameters 3) (vanishes : ∀ cell, (field.val cell).value closedOrigin = 0)
    (low : physicalBudget parameters field rho epsilon 6 ≤ originalCoefficientLowRadius parameters length)
    (angle : ℝ) :
    originalPhysicalSignedCofactor parameters length epsilon field angle closedOrigin =
      (-(originalAxisPlanarMatrix parameters length epsilon field angle).det) •
        tiltedAxisGram (originalAxisInverseGram parameters length epsilon field angle)
          (originalAxisTilt parameters length epsilon field angle) := by
  unfold originalPhysicalSignedCofactor
  rw [originalAxis_frame parameters length epsilon field vanishes]
  exact tiltedAxisFrame_signedCofactor_inverseGram _ _
    (originalAxisPlanarMatrix_isUnit_det parameters length rho epsilon field vanishes low angle)

end Grad.FinitePhysicalJetLift
