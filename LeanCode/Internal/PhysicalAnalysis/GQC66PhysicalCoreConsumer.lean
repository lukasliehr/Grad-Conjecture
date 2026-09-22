import GQC65LiteralCompensatedCore

noncomputable section
set_option maxHeartbeats 1600000
open scoped BigOperators

namespace Grad.GaugeCoefficients.Physical.Compensated
open Grad.ClosedJets Grad.CartesianState Grad.GenericCarriers
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.Allocation Grad.GaugeCoefficients.Physical.Ledger
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Physical.GaugeTransfer
open Grad.GaugeCoefficients.Physical.Frame

def ActualPhysicalGaugeMeans {L ell : ℝ} {parameters : PhaseParameters}
    {admissible : Admissible L parameters.sigma0 parameters.gamma ell}
    {rho alpha delta parameter epsilon : ℝ} {base : ACore parameters 3}
    (ledger : ActualLedger parameters admissible rho alpha delta parameter epsilon base)
    {grade : ℕ} (large : 2 ≤ grade) (field : APSmooth L parameters.sigma0 parameters.gamma ell 3) : Prop :=
  ∀ angle point,
    closedAngularMean (fun other => ∑ row : Fin 3,
      ((physicalInverseTranspose ledger grade angle other).mulVec (apPhysicalValue admissible large angle (field.val grade) other)) row *
        physicalTangentCovector (physicalSeedMatrix rho alpha delta parameter angle) other row) point = 0 ∧
    closedAngularMean (fun other => ∑ row : Fin 3,
      ((physicalInverseTranspose ledger grade angle other).mulVec (apPhysicalValue admissible large angle (field.val grade) other)) row *
        unscaledToroidalCovector L ell (operatorMatrix (deriv (harmonicSeedOperator rho alpha delta parameter) angle)) other row) point = 0

theorem actualSmoothGauge_zero_iff_physical {L ell : ℝ} {parameters : PhaseParameters}
    {admissible : Admissible L parameters.sigma0 parameters.gamma ell}
    {rho alpha delta parameter epsilon : ℝ} {base : ACore parameters 3}
    (ledger : ActualLedger parameters admissible rho alpha delta parameter epsilon base)
    {grade : ℕ} (large : 2 ≤ grade) (field : APSmooth L parameters.sigma0 parameters.gamma ell 3) :
    apSmoothGauge admissible ledger.val.gaugeDeviation ledger.property.1.2.2.2.1 field = 0 ↔
      ActualPhysicalGaugeMeans ledger large field := by
  have completed : apSmoothGauge admissible ledger.val.gaugeDeviation ledger.property.1.2.2.2.1 field = 0 ↔
      apGaugeMap admissible ledger.val.gaugeDeviation grade (field.val grade) = 0 := by
    constructor
    · intro zero
      exact (congrArg (apSmoothGrade L parameters.sigma0 parameters.gamma ell 3 grade) zero).trans (map_zero _)
    · intro zero
      apply apSmoothGrade_injective admissible 3 grade
      exact zero.trans (map_zero (apSmoothGrade L parameters.sigma0 parameters.gamma ell 3 grade)).symm
  exact completed.trans (actualGauge_zero_iff_physical_means ledger large (field.val grade))

/-- Current target equals the literal physical two gauges and actual
Cartesian flatness. Both directions use the faithful original completion. -/
theorem currentCompensatedCore_physical_iff {L ell : ℝ} {parameters : PhaseParameters}
    {admissible : Admissible L parameters.sigma0 parameters.gamma ell}
    {rho alpha delta parameter epsilon : ℝ} {base : ACore parameters 3}
    (ledger : ActualLedger parameters admissible rho alpha delta parameter epsilon base)
    {grade : ℕ} (large : 2 ≤ grade) (data : CompensatedData L parameters.sigma0 parameters.gamma ell) :
    data ∈ currentCompensatedCore admissible ledger.val.gaugeDeviation ledger.property.1.2.2.2.1 ↔
      (APSmoothMeanZero admissible data.1 ∧ APSmoothPhysicalFirstJetZero admissible data.1) ∧
        APSmoothPhysicalFirstJetZero admissible (compensatedReconstruct admissible data) ∧
          ActualPhysicalGaugeMeans ledger large (compensatedReconstruct admissible data) := by
  constructor
  · intro member
    have flat := (mem_compensatedFlatCore admissible data).mp member.1
    exact ⟨⟨flat.1.1, (apSmoothAxisFirstJetZero_iff_physical admissible data.1).mp flat.1.2⟩,
      (apSmoothAxisFirstJetZero_iff_physical admissible (compensatedReconstruct admissible data)).mp flat.2,
      (actualSmoothGauge_zero_iff_physical ledger large (compensatedReconstruct admissible data)).mp member.2⟩
  · rintro ⟨theta, flat, gauges⟩
    refine ⟨(mem_compensatedFlatCore admissible data).mpr ?_, ?_⟩
    · exact ⟨⟨theta.1, (apSmoothAxisFirstJetZero_iff_physical admissible data.1).mpr theta.2⟩,
        (apSmoothAxisFirstJetZero_iff_physical admissible (compensatedReconstruct admissible data)).mpr flat⟩
    · exact (actualSmoothGauge_zero_iff_physical ledger large (compensatedReconstruct admissible data)).mpr gauges

end Grad.GaugeCoefficients.Physical.Compensated
