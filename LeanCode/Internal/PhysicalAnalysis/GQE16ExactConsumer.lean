import GQE15ActualLowBall

noncomputable section
set_option maxHeartbeats 800000
open scoped BigOperators

namespace Grad.GaugeCoefficients.Physical.Compensated
attribute [local instance] apNormedSpace graphNormedSpace coreGroup coreModule
attribute [local instance] closureGroup closureSeminormed closureNormedSpace
open Grad.ClosedJets Grad.CartesianState Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Physical.Ledger
open Grad.GaugeCoefficients.Physical.WeightedTrace Grad.BoundaryTrace

theorem completedNormalTrace_endpoint {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    (data : LedgerData L sigma gamma ell) (grade : ℕ) (large : 3 ≤ grade)
    (core : Submodule ℂ (CompensatedData L sigma gamma ell)) (field : compensatedClosure admissible grade core)
    (mode : ℤ × ℤ) :
    apBoundaryCoefficient L sigma gamma ell (grade + 1) (completedNormalTrace admissible data grade core field) mode =
      if 3 ≤ |mode.1| then
        fourierCoeff (fun angle : CellCircle =>
          apTrace admissible (by omega : 2 ≤ grade + 1) mode.2
            (apMultiplier admissible (normalRowFamily data (grade + 1)) (completedReconstruct admissible grade core field))
              (boundaryDiskPoint angle)) mode.1 else 0 :=
  apHighTrace_literal admissible (by omega) _ mode

theorem completedNormalTrace_original_norm {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    (data : LedgerData L sigma gamma ell) (grade : ℕ)
    (core : Submodule ℂ (CompensatedData L sigma gamma ell)) (field : compensatedClosure admissible grade core) :
    ‖completedNormalTrace admissible data grade core field‖ ^ 2 =
      ∑' mode : ℤ × ℤ, Real.exp (2 * apBoundaryPhase sigma gamma ell mode.2) *
        (Real.sqrt (1 + (mode.1 : ℝ)^2 + ((mode.2 : ℝ) * ell / L)^2)) ^ (2 * (grade + 1) - 1) *
          ‖apBoundaryCoefficient L sigma gamma ell (grade + 1)
            (completedNormalTrace admissible data grade core field) mode‖ ^ 2 :=
  apBoundary_norm_sq L sigma gamma ell (grade + 1) (completedNormalTrace admissible data grade core field)

theorem scalarBoundaryPreservation {L sigma gamma ell : ℝ} {admissible : Admissible L sigma gamma ell}
    (data : LedgerData L sigma gamma ell) (smooth : SmoothCompensatedCoreIsomorphism admissible data.gaugeDeviation)
    (grade : ℕ) (large : 3 ≤ grade) (field : circularCompensatedClosure admissible grade) :
    apBoundaryTrace L sigma gamma ell (grade + 1) (by omega)
        (completedPsi admissible grade (currentCompensatedCore admissible data.gaugeDeviation smooth.coherent)
          (completedTransfer smooth grade large field)) =
      apBoundaryTrace L sigma gamma ell (grade + 1) (by omega)
        (completedPsi admissible grade (circularCompensatedCore admissible) field) ∧
    apBoundaryTrace L sigma gamma ell (grade + 1) (by omega)
        (completedScalar admissible grade (currentCompensatedCore admissible data.gaugeDeviation smooth.coherent)
          (completedTransfer smooth grade large field)) =
      apBoundaryTrace L sigma gamma ell (grade + 1) (by omega)
        (completedScalar admissible grade (circularCompensatedCore admissible) field) ∧
    apBoundaryTrace L sigma gamma ell (grade + 1) (by omega)
        (completedRadial admissible grade (currentCompensatedCore admissible data.gaugeDeviation smooth.coherent)
          (completedTransfer smooth grade large field)) =
      apBoundaryTrace L sigma gamma ell (grade + 1) (by omega)
        (completedRadial admissible grade (circularCompensatedCore admissible) field) :=
  ⟨congrArg (apBoundaryTrace L sigma gamma ell (grade + 1) (by omega)) (completedPsi_transfer smooth grade large field),
    congrArg (apBoundaryTrace L sigma gamma ell (grade + 1) (by omega)) (completedScalar_transfer smooth grade large field),
    congrArg (apBoundaryTrace L sigma gamma ell (grade + 1) (by omega)) (completedRadial_transfer smooth grade large field)⟩

end Grad.GaugeCoefficients.Physical.Compensated
