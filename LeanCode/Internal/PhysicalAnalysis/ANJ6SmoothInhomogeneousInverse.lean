import ANJ5CompletedInhomogeneousInverse

noncomputable section
set_option maxHeartbeats 1200000
namespace Grad.InhomogeneousHighRobin
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.CircularHighWeak Grad.CircularHighRegularity
open Grad.OrdinaryDiskCalculus Grad.ActualUniformGlobal Grad.CircularNormalLift Grad.ActualSmoothPDE
local instance (priority := 2000) smoothSolveUnitSpace (grade : ℕ) : NormedSpace ℂ (unitDiskSobolev grade) := unitNormedSpace grade
local instance (priority := 2000) smoothSolveBoundarySpace (grade : ℕ) : NormedSpace ℂ (normalBoundaryGrade grade) :=
  (normalBoundaryGrade grade).normedSpace

/-- One genuine smooth solution is chosen before every Sobolev grade. -/
def inhomogeneousSmoothInverse (parameters : PhaseParameters) (parameter : ℝ)
    (core : ClosedJet 1) (data : NormalSmoothBoundary) : ClosedJet 1 :=
  normalSmoothLift parameters data + actualSmoothInverse parameters parameter
    (core - scalarResidualJet parameter (normalSmoothLift parameters data))

theorem inhomogeneousSmoothInverse_grade (parameters : PhaseParameters) (parameter : ℝ)
    (core : ClosedJet 1) (data : NormalSmoothBoundary) (grade : ℕ) :
    unitDiskCoreInto (grade + 2) (inhomogeneousSmoothInverse parameters parameter core data) =
      inhomogeneousCompletedInverse grade parameters parameter (unitDiskCoreInto grade core, data.grade grade) := by
  let lift := normalSmoothLift parameters data
  have source : unitDiskCoreInto grade (core - scalarResidualJet parameter lift) =
      unitDiskCoreInto grade core - unitScalarOperator grade parameter (completedNormalLift (grade + 2) (data.grade grade)) :=
    ((unitDiskCoreInto grade).map_sub _ _).trans
      (congrArg (fun value => unitDiskCoreInto grade core - value)
        ((unitScalarOperator_core parameters grade parameter lift).symm.trans
          (congrArg (unitScalarOperator grade parameter) (normalSmoothLift_core parameters data grade))))
  have solution := (actualSmoothInverse_grade parameters parameter
    (core - scalarResidualJet parameter lift) grade).trans
      (congrArg (actualCompletedInverse grade parameters parameter) source)
  exact ((unitDiskCoreInto (grade + 2)).map_add _ _).trans
    (congrArg₂ (fun first second : unitDiskSobolev (grade + 2) => first + second)
      (normalSmoothLift_core parameters data grade) solution)

theorem inhomogeneousSmoothInverse_bound (grade : ℕ) (ceiling : ℝ) (parameters : PhaseParameters)
    (parameter : ℝ) (bounded : |parameter| ≤ ceiling) (core : ClosedJet 1) (data : NormalSmoothBoundary) :
    ‖unitDiskCoreInto (grade + 2) (inhomogeneousSmoothInverse parameters parameter core data)‖ ≤
      inhomogeneousInverseConstant grade ceiling * (‖unitDiskCoreInto grade core‖ + ‖data.grade grade‖) :=
  (congrArg norm (inhomogeneousSmoothInverse_grade parameters parameter core data grade)).le.trans
    (inhomogeneousCompletedInverse_bound grade ceiling parameters parameter bounded _ _)

theorem smoothBoundary_high_grade (data : NormalSmoothBoundary)
    (high : ∀ mode ∈ lowAngularModes, normalBoundaryCoefficient 2 (data.grade 0) mode = 0)
    (grade : ℕ) (mode : ℤ) (member : mode ∈ lowAngularModes) :
    normalBoundaryCoefficient (grade + 2) (data.grade grade) mode = 0 :=
  (smoothBoundary_coefficient data grade mode).trans (high mode member)

/-- The equation is an equality of the original closed jets, hence includes
all derivatives and the axis. -/
theorem inhomogeneousSmoothInverse_scalar (parameters : PhaseParameters) (parameter : ℝ)
    (core : ClosedJet 1) (sourceHigh : closedL2Core core ∈ highDiskL2) (data : NormalSmoothBoundary)
    (boundaryHigh : ∀ mode ∈ lowAngularModes, normalBoundaryCoefficient 2 (data.grade 0) mode = 0) :
    scalarResidualJet parameter (inhomogeneousSmoothInverse parameters parameter core data) = core := by
  have equation := inhomogeneousCompletedInverse_scalar 0 parameters parameter (unitDiskCoreInto 0 core)
    ((unitDiskBulk_core 0 core).symm ▸ sourceHigh) (data.grade 0) boundaryHigh
  have composed := (unitScalarOperator_core parameters 0 parameter
    (inhomogeneousSmoothInverse parameters parameter core data)).symm.trans
      ((congrArg (unitScalarOperator 0 parameter)
        (inhomogeneousSmoothInverse_grade parameters parameter core data 0)).trans equation)
  apply closedL2Core_injective
  exact (unitDiskBulk_core 0 _).symm.trans
    ((congrArg (unitDiskBulk 0) composed).trans (unitDiskBulk_core 0 core))

theorem inhomogeneousSmoothInverse_high (parameters : PhaseParameters) (parameter : ℝ)
    (core : ClosedJet 1) (data : NormalSmoothBoundary)
    (boundaryHigh : ∀ mode ∈ lowAngularModes, normalBoundaryCoefficient 2 (data.grade 0) mode = 0) :
    closedL2Core (inhomogeneousSmoothInverse parameters parameter core data) ∈ highDiskL2 := by
  have completed := inhomogeneousCompletedInverse_high 0 parameters parameter (unitDiskCoreInto 0 core) (data.grade 0) boundaryHigh
  have same := (unitDiskBulk_core 2 (inhomogeneousSmoothInverse parameters parameter core data)).symm.trans
    (congrArg (unitDiskBulk 2) (inhomogeneousSmoothInverse_grade parameters parameter core data 0))
  exact same.symm ▸ completed

theorem inhomogeneousSmoothInverse_robin_trace (parameters : PhaseParameters) (parameter : ℝ)
    (core : ClosedJet 1) (data : NormalSmoothBoundary) (grade : ℕ) :
    ordinaryRobinTrace grade (unitDiskCoreInto (grade + 2) (inhomogeneousSmoothInverse parameters parameter core data)) =
      (data.grade grade).val :=
  (congrArg (ordinaryRobinTrace grade) (inhomogeneousSmoothInverse_grade parameters parameter core data grade)).trans
    (inhomogeneousCompletedInverse_robin grade parameters parameter _ _)

end Grad.InhomogeneousHighRobin
