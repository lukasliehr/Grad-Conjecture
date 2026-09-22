import ANB9OriginalWeightedRows

noncomputable section
set_option maxHeartbeats 1400000
namespace Grad.BoundedScalarInverse
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.CircularHighWeak
open Grad.ActualCenterVolterra Grad.InhomogeneousHighRobin Grad.CircularNormalLift Grad.OrdinaryDiskCalculus
open Grad.GaugeCoefficients.Physical.Compensated (partialJetLinear)
open Grad.NonlinearDivision Grad.NonlinearQuotientBounds
local instance (priority := 2000) homogeneityUnitSpace (grade : ℕ) : NormedSpace ℂ (unitDiskSobolev grade) := unitNormedSpace grade
local instance (priority := 2000) homogeneityBoundarySpace (grade : ℕ) : NormedSpace ℂ (normalBoundaryGrade grade) :=
  (normalBoundaryGrade grade).normedSpace

def boundarySmul (scalar : ℂ) (data : NormalSmoothBoundary) : NormalSmoothBoundary where
  grade order := scalar • data.grade order
  coherent order := ((normalBoundaryLower 2 (order + 2)).map_smul scalar (data.grade order)).trans
    (congrArg (fun field => scalar • field) (data.coherent order))

theorem boundarySmul_high (scalar : ℂ) (data : NormalSmoothBoundary) (high : BoundaryIsHigh data) :
    BoundaryIsHigh (boundarySmul scalar data) := by
  intro mode member
  change normalBoundaryCoefficient 2 (scalar • data.grade 0) mode = 0
  change (normalBoundaryCoefficientCLM 2 mode) (scalar • data.grade 0) = 0
  rw [map_smul]
  change scalar • normalBoundaryCoefficient 2 (data.grade 0) mode = 0
  rw [high mode member, smul_zero]

theorem centerPinned_smul (scalar : ℂ) (field : ClosedJet 1) (pinned : CenterPinned field) :
    CenterPinned (scalar • field) := by
  constructor
  · change scalar • field.value closedOrigin = 0
    rw [pinned.1, smul_zero]
  · intro direction
    have same := (partialJetLinear 1 direction).map_smul scalar field
    change partialJet direction (scalar • field) = scalar • partialJet direction field at same
    rw [same]
    change scalar • (partialJet direction field).value closedOrigin = 0
    rw [pinned.2 direction, smul_zero]

theorem scalarNonexceptional_smul (scalar : ℂ) (field : ClosedJet 1) (excluded : IsScalarNonexceptional field) :
    IsScalarNonexceptional (scalar • field) := by
  simp only [IsScalarNonexceptional, angularClosedJet_smul, excluded.1, excluded.2.1, excluded.2.2, smul_zero, and_self]

theorem scalarSolution_smul (scalar : ℂ) (frequency : ℝ) (source : ClosedJet 1) (boundary : NormalSmoothBoundary)
    (field : ClosedJet 1) (laws : IsNonexceptionalScalarSolution frequency source boundary field) :
    IsNonexceptionalScalarSolution frequency (scalar • source) (boundarySmul scalar boundary) (scalar • field) := by
  refine ⟨scalarNonexceptional_smul scalar field laws.1, ?_, ?_, ?_⟩
  · exact ((fullScalarLinear frequency).map_smul scalar field).trans (congrArg (fun field => scalar • field) laws.2.1)
  · intro mode center
    rw [angularClosedJet_smul]
    exact centerPinned_smul scalar _ (laws.2.2.1 mode center)
  · intro grade
    have projection := (excludedAngularJetLinear 1 lowAngularModes).map_smul scalar field
    have core := ((unitDiskCoreInto (grade + 2)).map_smul scalar (excludedAngularJet lowAngularModes field))
    have trace := (ordinaryRobinTrace grade).map_smul scalar (unitDiskCoreInto (grade + 2) (excludedAngularJet lowAngularModes field))
    exact (congrArg (fun jet : ClosedJet 1 => ordinaryRobinTrace grade (unitDiskCoreInto (grade + 2) jet)) projection).trans
      ((congrArg (ordinaryRobinTrace grade) core).trans (trace.trans (congrArg (fun value => scalar • value) (laws.2.2.2 grade))))

/-- The actual common inverse commutes with constant complex multiplication,
including the large exp(sigma lambda_n) factor without a width change. -/
theorem scalarInverseJet_smul (scalar : ℂ) (parameters : PhaseParameters) (frequency : ℝ) (source : ClosedJet 1)
    (excluded : IsScalarNonexceptional source) (boundary : NormalSmoothBoundary) (high : BoundaryIsHigh boundary) :
    scalarInverseJet parameters frequency (scalar • source) (boundarySmul scalar boundary) =
      scalar • scalarInverseJet parameters frequency source boundary :=
  (scalarInverseJet_unique parameters frequency (scalar • source) (boundarySmul scalar boundary)
    (boundarySmul_high scalar boundary high) _
      (scalarSolution_smul scalar frequency source boundary _
        (scalarInverseJet_specification parameters frequency source excluded boundary high))).symm

end Grad.BoundedScalarInverse
