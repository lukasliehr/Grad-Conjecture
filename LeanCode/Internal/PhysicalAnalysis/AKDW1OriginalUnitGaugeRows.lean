import AKDS34OriginalUnitLedgerFidelity
import AKBT6ActualNativeCurrentRecovery
import AKBQ3SameMatrixActionAlgebra
import AKBL14OriginalPacketGaugeConsumer
import AKBL7OriginalPolarMeanToRoughOrbit

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 900000
open Set
namespace Grad.ActualScaledNativeCoefficients
open Grad.GaugeCoefficients.Physical.Allocation Grad.ActualGaugeSigmaPrimitives
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollar Grad.SourceCollarCoefficients Grad.SourceCollarDivision
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical Grad.GaugeCoefficients.Physical.Frame
open Grad.GaugeCoefficients.Physical.Ledger Grad.GaugeCoefficients.Physical.RadialLedger
open Grad.ActualSmoothPhysicalField Grad.ActualGaugeSigmaPrimitives Grad.OriginalKernelCovariantRecovery
open Grad.Constraints Grad.Constraints.Gauges Grad.CartesianStartup Grad.AnnularReconstruction

variable {L compact : ℝ} {parameters : PhaseParameters}
    (state : RadialCoefficientState parameters L compact)
    (gauge : CoefficientFamily 1 parameters.sigma0 parameters.gamma 1 3 3)
    (sameGauge : ∀ grade angle point, familyMatrix (fullGaugeFamily gauge) grade angle point =
      originalPhysicalGaugeMatrix parameters L state.data.rho state.data.alpha state.data.delta
        state.data.parameter state.data.epsilon state.data.field angle point)

include sameGauge

theorem originalUnitGauge_action (grade : ℕ) (axial : ℝ) (point : ClosedDisk) (value : ComplexEuclidean 3) :
    coefficientPhysicalValue (fullGaugeFamily gauge grade) axial point value =
      WithLp.toLp 2 ((originalPhysicalGaugeMatrix parameters L state.data.rho state.data.alpha state.data.delta
        state.data.parameter state.data.epsilon state.data.field axial
        point).mulVec value) := by
  rw [operatorMatrix_action]
  exact congrArg (fun matrix : Matrix (Fin 3) (Fin 3) ℂ => WithLp.toLp 2 (matrix.mulVec value))
    (sameGauge grade axial point)

/-- Both actual full C0 rows equal the existing native gauge product before any axial cell is selected. -/
theorem originalUnitGauge_nativeProduct (radius : ℝ) (positive : 0 < radius) (bounded : radius ≤ 1)
    (source : ℝ×ℝ → ComplexEuclidean 3) (polar axial : ℝ) :
    let point := Grad.SourceCollarDivision.polarClosedPoint radius polar positive.le bounded
    let product := coefficientPhysicalValue (fullGaugeFamily gauge 0) axial point
      (cartesianCovariantValue polar (source (polar,axial)))
    let r : RadialPoint := ⟨radius,positive.le,bounded⟩
    polarTangentialComponent polar (planarPartMap product) =
      originalTotalGaugeProduct parameters L compact state r 0 source (polar,axial) 0 ∧
    toroidalPartMap product = originalTotalGaugeProduct parameters L compact state r 1 source (polar,axial) := by
  have action := originalUnitGauge_action state gauge sameGauge 0 axial
    (Grad.SourceCollarDivision.polarClosedPoint radius polar positive.le bounded)
    (cartesianCovariantValue polar (source (polar,axial)))
  constructor
  · rw [action,polarGauge_action,originalTotalGaugeProduct_value]
    rfl
  · have native := originalTotalGaugeProduct_value parameters L compact state
      ⟨radius,positive.le,bounded⟩
      (1 : Fin 2) source (polar,axial)
    have algebra := toroidalGauge_action polar
      (originalPhysicalGaugeMatrix parameters L state.data.rho state.data.alpha state.data.delta
        state.data.parameter state.data.epsilon state.data.field axial
        (Grad.SourceCollarDivision.polarClosedPoint radius polar positive.le bounded))
      (source (polar,axial))
    have scalar := (congrArg (fun value : ComplexEuclidean 3 => toroidalPartMap value 0) action).trans
      (algebra.trans native.symm)
    apply PiLp.ext
    intro coordinate
    have unique : coordinate = 0 := Subsingleton.elim _ _
    subst coordinate
    exact scalar

end Grad.ActualScaledNativeCoefficients
