import ANJ12AllGradeUniqueness

noncomputable section
set_option maxHeartbeats 1200000
namespace Grad.InhomogeneousHighRobin
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.CircularHighWeak Grad.CircularHighRegularity
open Grad.OrdinaryDiskCalculus Grad.OrdinaryDiskFaithfulness Grad.CircularNormalLift Grad.ActualSmoothPDE
open Grad.ActualSmoothRobin Grad.SmoothRobinUniqueness Grad.BoundaryTrace Grad.NonlinearRange
local instance (priority := 2000) finalUnitSpace (grade : ℕ) : NormedSpace ℂ (unitDiskSobolev grade) := unitNormedSpace grade
local instance (priority := 2000) finalBoundarySpace (grade : ℕ) : NormedSpace ℂ (normalBoundaryGrade grade) :=
  (normalBoundaryGrade grade).normedSpace

/-- Exact completed AN23, with constants before all parameters and arbitrary
high completed source and boundary data in their original norms. -/
theorem actualCompletedHighRobinInverse (grade : ℕ) (ceiling : ℝ) :
    ∃ constant : ℝ, 0 ≤ constant ∧ ∀ (_parameters : PhaseParameters) (parameter : ℝ), |parameter| ≤ ceiling →
      ∀ (source : unitDiskSobolev grade), unitDiskBulk grade source ∈ highDiskL2 →
      ∀ (boundary : normalBoundaryGrade (grade + 2)),
        (∀ mode ∈ lowAngularModes, normalBoundaryCoefficient (grade + 2) boundary mode = 0) →
        ∃! solution : unitDiskSobolev (grade + 2),
          unitDiskBulk (grade + 2) solution ∈ highDiskL2 ∧
          unitScalarOperator grade parameter solution = source ∧
          ordinaryRobinTrace grade solution = boundary.val ∧
          HasDiskWeakLaplacian (unitDiskBulk (grade + 2) solution)
            (((parameter ^ 2 : ℝ) : ℂ) • diskB (unitDiskBulk (grade + 2) solution) - unitDiskBulk grade source) ∧
          ‖solution‖ ≤ constant * (‖source‖ + ‖boundary‖) := by
  refine ⟨inhomogeneousInverseConstant grade ceiling, inhomogeneousInverseConstant_nonnegative grade ceiling, ?_⟩
  intro parameters parameter bounded source sourceHigh boundary boundaryHigh
  refine ⟨inhomogeneousCompletedInverse grade parameters parameter (source, boundary), ?_, ?_⟩
  · exact ⟨inhomogeneousCompletedInverse_high grade parameters parameter source boundary boundaryHigh,
      inhomogeneousCompletedInverse_scalar grade parameters parameter source sourceHigh boundary boundaryHigh,
      inhomogeneousCompletedInverse_robin grade parameters parameter source boundary,
      inhomogeneousCompletedInverse_weak grade parameters parameter source sourceHigh boundary boundaryHigh,
      inhomogeneousCompletedInverse_bound grade ceiling parameters parameter bounded source boundary⟩
  · intro candidate laws
    exact completedGrade_unique parameters grade parameter candidate _ laws.1
      (inhomogeneousCompletedInverse_high grade parameters parameter source boundary boundaryHigh)
      (laws.2.1.trans (inhomogeneousCompletedInverse_scalar grade parameters parameter source sourceHigh boundary boundaryHigh).symm)
      (laws.2.2.1.trans (inhomogeneousCompletedInverse_robin grade parameters parameter source boundary).symm)

theorem inhomogeneousSmoothInverse_unique (parameters : PhaseParameters) (parameter : ℝ)
    (source boundary : ClosedJet 1) (sourceHigh : closedL2Core source ∈ highDiskL2)
    (boundaryHigh : ∀ mode ∈ lowAngularModes,
      fourierCoeff (fun angle : CellCircle => boundary.value (boundaryDiskPoint angle)) mode = 0)
    (candidate : ClosedJet 1) (candidateHigh : closedL2Core candidate ∈ highDiskL2)
    (equation : scalarResidualJet parameter candidate = source)
    (robin : ∀ angle : CellCircle, (eulerJet candidate).value (boundaryDiskPoint angle) +
      (2 : ℝ) • candidate.value (boundaryDiskPoint angle) = boundary.value (boundaryDiskPoint angle)) :
    candidate = inhomogeneousSmoothInverse parameters parameter source (boundaryJetData boundary) := by
  have dataHigh : ∀ mode ∈ lowAngularModes,
      normalBoundaryCoefficient 2 ((boundaryJetData boundary).grade 0) mode = 0 := by
    intro mode member
    exact (boundaryJetGrade_coefficient 0 boundary mode).trans (boundaryHigh mode member)
  apply scalarRobin_unique parameter candidate _ candidateHigh
    (inhomogeneousSmoothInverse_high parameters parameter source (boundaryJetData boundary) dataHigh)
  · exact equation.trans (inhomogeneousSmoothInverse_scalar parameters parameter source sourceHigh (boundaryJetData boundary) dataHigh).symm
  · intro angle
    have constructed := inhomogeneousSmoothInverse_boundary_value parameters parameter source boundary angle
    change (eulerJet (inhomogeneousSmoothInverse parameters parameter source (boundaryJetData boundary))).value
      (boundaryDiskPoint angle) + (2 : ℂ) •
        (inhomogeneousSmoothInverse parameters parameter source (boundaryJetData boundary)).value (boundaryDiskPoint angle) = _ at constructed
    exact (robin angle).trans (by simpa only [Complex.coe_smul] using! constructed.symm)

/-- One genuine smooth solution, fixed before the grade, retains the exact
Cartesian PDE and full pointwise outward Robin condition with all-grade bounds. -/
theorem actualSmoothHighRobinInverse (parameters : PhaseParameters) (parameter : ℝ)
    (source boundary : ClosedJet 1) (sourceHigh : closedL2Core source ∈ highDiskL2)
    (boundaryHigh : ∀ mode ∈ lowAngularModes,
      fourierCoeff (fun angle : CellCircle => boundary.value (boundaryDiskPoint angle)) mode = 0) :
    ∃! solution : ClosedJet 1,
      closedL2Core solution ∈ highDiskL2 ∧ scalarResidualJet parameter solution = source ∧
      (∀ point : ClosedDisk, -Grad.NonlinearQuotient.diskLaplacian (smoothClosedExtension solution) point.val +
        ((parameter ^ 2 : ℝ) : ℂ) • (smoothDiskBJet solution).value point = source.value point) ∧
      (∀ angle : CellCircle, fderiv ℝ (smoothClosedExtension solution) (boundaryCirclePoint angle) (boundaryCirclePoint angle) +
        (2 : ℝ) • solution.value (boundaryDiskPoint angle) = boundary.value (boundaryDiskPoint angle)) ∧
      (∀ grade ceiling, |parameter| ≤ ceiling → ‖unitDiskCoreInto (grade + 2) solution‖ ≤
        inhomogeneousInverseConstant grade ceiling * (‖unitDiskCoreInto grade source‖ + ‖boundaryJetGrade grade boundary‖)) := by
  let data := boundaryJetData boundary
  let solution := inhomogeneousSmoothInverse parameters parameter source data
  have dataHigh : ∀ mode ∈ lowAngularModes, normalBoundaryCoefficient 2 (data.grade 0) mode = 0 := by
    intro mode member
    exact (boundaryJetGrade_coefficient 0 boundary mode).trans (boundaryHigh mode member)
  have equation := inhomogeneousSmoothInverse_scalar parameters parameter source sourceHigh data dataHigh
  refine ⟨solution, ⟨inhomogeneousSmoothInverse_high parameters parameter source data dataHigh, equation, ?_,
    inhomogeneousSmoothInverse_pointwise_robin parameters parameter source boundary, ?_⟩, ?_⟩
  · intro point
    exact (scalarResidualJet_literal parameter solution point).symm.trans
      (congrArg (fun field : ClosedJet 1 => field.value point) equation)
  · intro grade ceiling bounded
    exact inhomogeneousSmoothInverse_bound grade ceiling parameters parameter bounded source data
  · intro candidate laws
    apply inhomogeneousSmoothInverse_unique parameters parameter source boundary sourceHigh boundaryHigh candidate laws.1 laws.2.1
    intro angle
    exact (congrArg (fun value : ComplexEuclidean 1 => value + (2 : ℝ) • candidate.value (boundaryDiskPoint angle))
      (eulerJet_extension_value candidate (boundaryDiskPoint angle))).trans (laws.2.2.2.1 angle)

end Grad.InhomogeneousHighRobin
