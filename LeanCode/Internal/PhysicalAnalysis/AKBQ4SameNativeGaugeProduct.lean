import AKBQ3SameMatrixActionAlgebra
import AKBL14OriginalPacketGaugeConsumer
import AKBL7OriginalPolarMeanToRoughOrbit

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 900000
open Set
namespace Grad.ActualScaledNativeCoefficients
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollar Grad.SourceCollarCoefficients Grad.SourceCollarDivision
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical Grad.GaugeCoefficients.Physical.Frame
open Grad.GaugeCoefficients.Physical.Ledger Grad.GaugeCoefficients.Physical.RadialLedger
open Grad.ActualSmoothPhysicalField Grad.ActualGaugeSigmaPrimitives Grad.OriginalKernelCovariantRecovery
open Grad.Constraints Grad.Constraints.Gauges Grad.CartesianStartup Grad.AnnularReconstruction

 theorem scaledPolarPoint {L ell : ℝ} {parameters : PhaseParameters}
    (admissible : Admissible L parameters.sigma0 parameters.gamma ell)
    (radius : ℝ) (nonnegative : 0 ≤ radius) (bounded : radius ≤ 1) (angle : ℝ) :
    physicalScaledPoint ell admissible.2.2.2.1.le
      (admissible.2.2.2.2.trans (min_le_left _ _)) (Grad.SourceCollarDivision.polarClosedPoint radius angle nonnegative bounded) =
    Grad.SourceCollarDivision.polarClosedPoint (ell*radius) angle (mul_nonneg admissible.2.2.2.1.le nonnegative)
      ((mul_le_of_le_one_left nonnegative (admissible.2.2.2.2.trans (min_le_left _ _))).trans bounded) := by
  apply Subtype.ext
  exact startupPolar_dilation ell radius angle

variable {L ell compact : ℝ} {parameters : PhaseParameters}
    (admissible : Admissible L parameters.sigma0 parameters.gamma ell)
    (state : RadialCoefficientState parameters L compact)
    (ledger : ActualLedger parameters admissible state.data.rho state.data.alpha state.data.delta
      state.data.parameter state.data.epsilon state.data.field)

theorem scaledGauge_action (grade : ℕ) (axial : ℝ) (point : ClosedDisk) (value : ComplexEuclidean 3) :
    coefficientPhysicalValue (fullGaugeFamily ledger.val.gaugeDeviation grade) axial point value =
      WithLp.toLp 2 ((originalPhysicalGaugeMatrix parameters L state.data.rho state.data.alpha state.data.delta
        state.data.parameter state.data.epsilon state.data.field axial
        (physicalScaledPoint ell admissible.2.2.2.1.le
          (admissible.2.2.2.2.trans (min_le_left _ _)) point)).mulVec value) := by
  rw [operatorMatrix_action]
  exact congrArg (fun matrix : Matrix (Fin 3) (Fin 3) ℂ => WithLp.toLp 2 (matrix.mulVec value))
    (scaledLedgerGauge_original ledger grade axial point)

/-- Both actual full C0 rows equal the existing native gauge product before any axial cell is selected. -/
theorem scaledGauge_nativeProduct (radius : ℝ) (positive : 0 < radius) (bounded : radius ≤ 1)
    (source : ℝ×ℝ → ComplexEuclidean 3) (polar axial : ℝ) :
    let point := Grad.SourceCollarDivision.polarClosedPoint radius polar positive.le bounded
    let product := coefficientPhysicalValue (fullGaugeFamily ledger.val.gaugeDeviation 0) axial point
      (cartesianCovariantValue polar (source (polar,axial)))
    let r : RadialPoint := ⟨ell*radius,mul_nonneg admissible.2.2.2.1.le positive.le,
      (mul_le_of_le_one_left positive.le (admissible.2.2.2.2.trans (min_le_left _ _))).trans bounded⟩
    polarTangentialComponent polar (planarPartMap product) =
      originalTotalGaugeProduct parameters L compact state r 0 source (polar,axial) 0 ∧
    toroidalPartMap product = originalTotalGaugeProduct parameters L compact state r 1 source (polar,axial) := by
  have action := scaledGauge_action admissible state ledger 0 axial
    (Grad.SourceCollarDivision.polarClosedPoint radius polar positive.le bounded)
    (cartesianCovariantValue polar (source (polar,axial)))
  rw [scaledPolarPoint admissible radius positive.le bounded] at action
  constructor
  · rw [action,polarGauge_action,originalTotalGaugeProduct_value]
    rfl
  · have native := originalTotalGaugeProduct_value parameters L compact state
      ⟨ell*radius,mul_nonneg admissible.2.2.2.1.le positive.le,
        (mul_le_of_le_one_left positive.le (admissible.2.2.2.2.trans (min_le_left _ _))).trans bounded⟩
      (1 : Fin 2) source (polar,axial)
    have algebra := toroidalGauge_action polar
      (originalPhysicalGaugeMatrix parameters L state.data.rho state.data.alpha state.data.delta
        state.data.parameter state.data.epsilon state.data.field axial
        (Grad.SourceCollarDivision.polarClosedPoint (ell*radius) polar
          (mul_nonneg admissible.2.2.2.1.le positive.le)
          ((mul_le_of_le_one_left positive.le (admissible.2.2.2.2.trans (min_le_left _ _))).trans bounded)))
      (source (polar,axial))
    have scalar := (congrArg (fun value : ComplexEuclidean 3 => toroidalPartMap value 0) action).trans
      (algebra.trans native.symm)
    apply PiLp.ext
    intro coordinate
    have unique : coordinate = 0 := Subsingleton.elim _ _
    subst coordinate
    exact scalar

end Grad.ActualScaledNativeCoefficients
