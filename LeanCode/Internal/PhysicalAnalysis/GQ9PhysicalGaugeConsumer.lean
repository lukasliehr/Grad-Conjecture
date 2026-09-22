import GQ8PhysicalScaling

noncomputable section

set_option maxHeartbeats 1600000

open scoped BigOperators

namespace Grad.GaugeCoefficients.Physical.GaugeTransfer

open Grad.ClosedJets Grad.CartesianState Grad.GenericCarriers
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Physical.Ledger
open Grad.GaugeCoefficients.Physical.Allocation Grad.GaugeCoefficients.Physical.Frame

/-- The exact two physical gauge means: U dot iota M JY and
U dot (L e_T+ell iota M'Y), with U=F^(-T)w. All dots are algebraic. -/
theorem actualGauge_zero_iff_physical_means {L ell : ℝ} {parameters : PhaseParameters}
    {admissible : Admissible L parameters.sigma0 parameters.gamma ell}
    {rho alpha delta parameter epsilon : ℝ} {base : ACore parameters 3}
    (ledger : ActualLedger parameters admissible rho alpha delta parameter epsilon base)
    {grade : ℕ} (large : 2 ≤ grade) (field : apGrade L parameters.sigma0 parameters.gamma ell 3 grade) :
    apGaugeMap admissible ledger.val.gaugeDeviation grade field = 0 ↔
      ∀ angle point,
        closedAngularMean (fun other => ∑ row : Fin 3,
          ((physicalInverseTranspose ledger grade angle other).mulVec (apPhysicalValue admissible large angle field other)) row *
            physicalTangentCovector (physicalSeedMatrix rho alpha delta parameter angle) other row) point = 0 ∧
        closedAngularMean (fun other => ∑ row : Fin 3,
          ((physicalInverseTranspose ledger grade angle other).mulVec (apPhysicalValue admissible large angle field other)) row *
            unscaledToroidalCovector L ell (operatorMatrix (deriv (harmonicSeedOperator rho alpha delta parameter) angle)) other row) point = 0 := by
  rw [apGaugeMap_zero_iff_means admissible _ ledger.property.1.2.2.2.1 large]
  have tangent (angle : ℝ) (other : ClosedDisk) :=
    actualGauge_tangent ledger grade angle (apPhysicalValue admissible large angle field) other
  have toroidal (angle : ℝ) (other : ClosedDisk) :=
    actualGauge_toroidal_unscaled ledger grade angle (apPhysicalValue admissible large angle field) other
  simp_rw [tangent, ← toroidal, closedAngularMean_const_mul]
  have nonzero : (L : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr admissible.1.ne'
  simp only [mul_eq_zero, nonzero, false_or]

/-- Exact physical realization of Q_a itself. Both coefficient actions
are the original GC18 AP2 multiplier; no projected replacement residual. -/
theorem apCurrentProjection_physical {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) (gauge : CoefficientFamily L sigma gamma ell 3 3)
    {grade : ℕ} (large : 2 ≤ grade) (angle : ℝ) (field : apGrade L sigma gamma ell 3 grade) :
    apPhysicalValue admissible large angle (apCurrentProjection admissible gauge grade field) =
      apPhysicalValue admissible large angle field -
        cMapAction (cMapCoefficient admissible grade 3 3 angle (complementExtensionFamily admissible gauge grade))
          (cMapComplement (cMapAction (cMapCoefficient admissible grade 3 3 angle (fullGaugeFamily gauge grade))
            (apPhysicalValue admissible large angle field))) := by
  rw [apCurrentProjection_apply, map_sub]
  change _ - apPhysicalValue admissible large angle (apMultiplier admissible (complementExtensionFamily admissible gauge grade)
    (apComplement L sigma gamma ell grade (apMultiplier admissible (fullGaugeFamily gauge grade) field))) = _
  rw [apMultiplier_physical, apComplement_physical, apMultiplier_physical]

/-- Immediate consumer of the public current-gauge construction, with
its original completed carriers and physical covectors checked together. -/
theorem actualGaugeProjectionConsumer (parameters : PhaseParameters) (L radius threshold : ℝ)
    (positive : 0 < L) (radiusNonnegative : 0 ≤ radius) (thresholdPositive : 0 < threshold) :
    ActualGaugeProjectionGoal parameters L radius threshold :=
  actualGaugeProjection parameters L radius threshold positive radiusNonnegative thresholdPositive

end Grad.GaugeCoefficients.Physical.GaugeTransfer
