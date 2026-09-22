import AFY5PhysicalStrongTraces

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000

namespace Grad.GaugeCoefficients.Physical.Compensated
attribute [local instance] apNormedSpace graphNormedSpace coreGroup coreModule
attribute [local instance] closureGroup closureSeminormed closureNormedSpace
open Grad.ClosedJets Grad.CartesianState Grad.Constraints
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Physical.Ledger
open Grad.GaugeCoefficients.Physical.Allocation
open Grad.GaugeCoefficients.Physical.WeightedTrace Grad.BoundaryTrace

variable {L sigma gamma ell : ℝ} {admissible : Admissible L sigma gamma ell}

/-- Scalar transfer preservation in its full native s+2 slot. -/
theorem completedNativeTheta_transfer {gauge : CoefficientFamily L sigma gamma ell 3 3}
    (smooth : SmoothCompensatedCoreIsomorphism admissible gauge) (grade : ℕ) (large : 3 ≤ grade)
    (field : circularCompensatedClosure admissible grade) :
    completedNativeTheta admissible grade (currentCompensatedCore admissible gauge smooth.coherent)
      (completedTransfer smooth grade large field) =
        completedNativeTheta admissible grade (circularCompensatedCore admissible) field := by
  apply observation_of_dense_core (compensatedIntoClosure admissible grade (circularCompensatedCore admissible))
    (compensatedIntoClosure_denseRange admissible grade (circularCompensatedCore admissible))
    (completedTransfer smooth grade large)
    (completedNativeTheta admissible grade (circularCompensatedCore admissible))
    (completedNativeTheta admissible grade (currentCompensatedCore admissible gauge smooth.coherent)) _ field
  intro source
  exact (congrArg (completedNativeTheta admissible grade (currentCompensatedCore admissible gauge smooth.coherent))
    (completedTransfer_core smooth grade large source)).trans
      ((completedNativeTheta_core admissible grade (currentCompensatedCore admissible gauge smooth.coherent)
        (smooth.equivalence source)).trans
          ((congrArg (apSmoothGrade L sigma gamma ell 1 (grade + 2)) (transfer_theta smooth source)).trans
            (completedNativeTheta_core admissible grade (circularCompensatedCore admissible) source).symm))

theorem completedStrongScalar_transfer {gauge : CoefficientFamily L sigma gamma ell 3 3}
    (smooth : SmoothCompensatedCoreIsomorphism admissible gauge) (grade : ℕ) (large : 3 ≤ grade)
    (field : circularCompensatedClosure admissible grade) :
    completedStrongScalar admissible grade (currentCompensatedCore admissible gauge smooth.coherent)
      (completedTransfer smooth grade large field) =
        completedStrongScalar admissible grade (circularCompensatedCore admissible) field := by
  exact congrArg (fun theta : apGrade L sigma gamma ell 1 (grade + 2) =>
    highAngularIsometry L sigma gamma ell (grade + 1)
      (highBoundaryProjection L sigma gamma ell (grade + 2)
        (apBoundaryTrace L sigma gamma ell (grade + 2) (by omega) theta)))
    (completedNativeTheta_transfer smooth grade large field)

/-- The accepted AR14 two-term physical error, now in the exact stronger target. -/
theorem completedStrongFlux_difference (data : LedgerData L sigma gamma ell)
    (smooth : SmoothCompensatedCoreIsomorphism admissible data.gaugeDeviation)
    (grade : ℕ) (large : 3 ≤ grade) (field : circularCompensatedClosure admissible grade) :
    let outputCore := currentCompensatedCore admissible data.gaugeDeviation smooth.coherent
    let output := completedTransfer smooth grade large field
    completedStrongFlux admissible data grade outputCore output -
      highAngularIsometry L sigma gamma ell grade
        (highBoundaryProjection L sigma gamma ell (grade + 1)
          (completedCircleMatchingP admissible grade (circularCompensatedCore admissible) field)) =
      highAngularIsometry L sigma gamma ell grade
        (highBoundaryProjection L sigma gamma ell (grade + 1)
          (apBoundaryTrace L sigma gamma ell (grade + 1) (by omega)
            (apMeanFree L sigma gamma ell 1 (grade + 1)
              (apRadialContraction admissible (grade + 1)
                (apMultiplier admissible (data.fluxDeviation (grade + 1))
                  (completedReconstruct admissible grade outputCore output)) +
               apTangentContraction admissible (grade + 1)
                 (apMultiplier admissible (data.fluxDeviation (grade + 1))
                   (apMatchingRadialColumn admissible (grade + 1)
                     (completedPsi admissible grade (circularCompensatedCore admissible) field))))))) := by
  dsimp only
  have result := congrArg (fun boundary : APBoundaryGrade L sigma gamma ell 1 (grade + 1) =>
    highAngularIsometry L sigma gamma ell grade (highBoundaryProjection L sigma gamma ell (grade + 1) boundary))
    (completedMatchingP_difference admissible data smooth grade large field)
  simp only [map_sub] at result
  exact result

/-- Coordinate norm calculation kept independent of the large native graph maps. -/
theorem strongPair_error_norm (L sigma gamma ell : ℝ) (grade : ℕ)
    (firstScalar secondScalar : StrongMatchingGrade L sigma gamma ell (grade + 1))
    (same : firstScalar = secondScalar)
    (first second : APBoundaryGrade L sigma gamma ell 1 (grade + 1)) :
    ‖(WithLp.toLp 1
        (firstScalar, highAngularIsometry L sigma gamma ell grade
          (highBoundaryProjection L sigma gamma ell (grade + 1) first)) : StrongMatchingPair L sigma gamma ell grade) -
      WithLp.toLp 1
        (secondScalar, highAngularIsometry L sigma gamma ell grade
          (highBoundaryProjection L sigma gamma ell (grade + 1) second))‖ =
      ‖apHighProjection L sigma gamma ell (grade + 1) (first - second)‖ := by
  subst firstScalar
  rw [strongMatchingPair_norm]
  change ‖secondScalar - secondScalar‖ +
    ‖highAngularIsometry L sigma gamma ell grade (highBoundaryProjection L sigma gamma ell (grade + 1) first) -
      highAngularIsometry L sigma gamma ell grade (highBoundaryProjection L sigma gamma ell (grade + 1) second)‖ = _
  rw [sub_self, norm_zero, zero_add, ← map_sub, ← map_sub]
  exact (highAngularIsometry L sigma gamma ell grade).norm_map _

/-- The transfer error's SUM norm is exactly the high primitive error norm. -/
theorem completedStrongPair_transfer_error_norm (data : LedgerData L sigma gamma ell)
    (smooth : SmoothCompensatedCoreIsomorphism admissible data.gaugeDeviation)
    (grade : ℕ) (large : 3 ≤ grade) (field : circularCompensatedClosure admissible grade) :
    let outputCore := currentCompensatedCore admissible data.gaugeDeviation smooth.coherent
    let output := completedTransfer smooth grade large field
    ‖completedStrongPair admissible data grade outputCore output -
      WithLp.toLp 1
        (completedStrongScalar admissible grade (circularCompensatedCore admissible) field,
         highAngularIsometry L sigma gamma ell grade
           (highBoundaryProjection L sigma gamma ell (grade + 1)
             (completedCircleMatchingP admissible grade (circularCompensatedCore admissible) field)))‖ =
      ‖apHighProjection L sigma gamma ell (grade + 1)
        (completedMatchingP admissible data grade outputCore output -
          completedCircleMatchingP admissible grade (circularCompensatedCore admissible) field)‖ :=
  strongPair_error_norm L sigma gamma ell grade
    (completedStrongScalar admissible grade (currentCompensatedCore admissible data.gaugeDeviation smooth.coherent)
      (completedTransfer smooth grade large field))
    (completedStrongScalar admissible grade (circularCompensatedCore admissible) field)
    (completedStrongScalar_transfer smooth grade large field)
    (completedMatchingP admissible data grade (currentCompensatedCore admissible data.gaugeDeviation smooth.coherent)
      (completedTransfer smooth grade large field))
    (completedCircleMatchingP admissible grade (circularCompensatedCore admissible) field)

/-- Original physical coefficients agree across all natural trace grades on
smooth data; only their exact AY norms change. -/
theorem completedStrongPair_core_grades (admissible : Admissible L sigma gamma ell)
    (data : LedgerData L sigma gamma ell) (coherent : LedgerCoherent data)
    (first second : ℕ) (firstLarge : 2 ≤ first) (secondLarge : 2 ≤ second)
    (core : Submodule ℂ (CompensatedData L sigma gamma ell)) (field : core) (mode : ℤ × ℤ) :
    strongMatchingCoefficient L sigma gamma ell (first + 1)
        (completedStrongPair admissible data first core (compensatedIntoClosure admissible first core field)).fst mode =
      strongMatchingCoefficient L sigma gamma ell (second + 1)
        (completedStrongPair admissible data second core (compensatedIntoClosure admissible second core field)).fst mode ∧
    strongMatchingCoefficient L sigma gamma ell first
        (completedStrongPair admissible data first core (compensatedIntoClosure admissible first core field)).snd mode =
      strongMatchingCoefficient L sigma gamma ell second
        (completedStrongPair admissible data second core (compensatedIntoClosure admissible second core field)).snd mode :=
  ⟨(completedStrongScalar_core admissible first (by omega) core field mode).trans
    (completedStrongScalar_core admissible second (by omega) core field mode).symm,
   (completedStrongFlux_core admissible data coherent first firstLarge core field mode).trans
    (completedStrongFlux_core admissible data coherent second secondLarge core field mode).symm⟩

end Grad.GaugeCoefficients.Physical.Compensated
