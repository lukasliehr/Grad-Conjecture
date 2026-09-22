import ANB3ActualSectorSolution

noncomputable section
set_option maxHeartbeats 1400000
open scoped BigOperators
namespace Grad.BoundedScalarInverse
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.CircularHighWeak
open Grad.ActualAngularInverse Grad.ActualSmoothPDE Grad.SmoothRobinUniqueness
open Grad.CircularHighRegularity Grad.ActualCenterVolterra Grad.InhomogeneousHighRobin Grad.CircularNormalLift
open Grad.OrdinaryDiskCalculus Grad.NonlinearDivision
local instance (priority := 2000) scalarLawUnitSpace (grade : ℕ) : NormedSpace ℂ (unitDiskSobolev grade) := unitNormedSpace grade

theorem fullScalarJet_excluded (frequency : ℝ) (modes : Finset ℤ) (field : ClosedJet 1) :
    fullScalarJet frequency (excludedAngularJet modes field) = excludedAngularJet modes (fullScalarJet frequency field) := by
  change fullScalarLinear frequency (field - selectedAngularJet modes field) =
    fullScalarJet frequency field - selectedAngularJet modes (fullScalarJet frequency field)
  rw [map_sub, selectedAngularJet_eq, selectedAngularJet_eq, map_sum]
  congr 1
  exact Finset.sum_congr rfl (fun mode _ => (fullScalarJet_angular frequency mode field).symm)

theorem scalarInverseJet_high_projection (parameters : PhaseParameters) (frequency : ℝ) (source : ClosedJet 1)
    (boundary : NormalSmoothBoundary) (high : BoundaryIsHigh boundary) :
    excludedAngularJet lowAngularModes (scalarInverseJet parameters frequency source boundary) =
      scalarHighPart parameters frequency source boundary := by
  have split := scalar_high_decomposition _ (scalarInverseJet_nonexceptional parameters frequency source boundary high)
  rw [scalarInverseJet_center_projection parameters frequency source boundary high 1 (Or.inl rfl),
    scalarInverseJet_center_projection parameters frequency source boundary high (-1) (Or.inr rfl)] at split
  exact add_left_cancel split

theorem scalarInverseJet_pinned (parameters : PhaseParameters) (frequency : ℝ) (source : ClosedJet 1)
    (boundary : NormalSmoothBoundary) (high : BoundaryIsHigh boundary) (mode : ℤ) (center : mode = 1 ∨ mode = -1) :
    CenterPinned (angularClosedJet mode (scalarInverseJet parameters frequency source boundary)) := by
  rw [scalarInverseJet_center_projection parameters frequency source boundary high mode center]
  exact pinnedCenterSolution_pinned mode frequency _

theorem scalarInverseJet_robin (parameters : PhaseParameters) (frequency : ℝ) (source : ClosedJet 1)
    (boundary : NormalSmoothBoundary) (high : BoundaryIsHigh boundary) (grade : ℕ) :
    ordinaryRobinTrace grade (unitDiskCoreInto (grade + 2)
      (excludedAngularJet lowAngularModes (scalarInverseJet parameters frequency source boundary))) = (boundary.grade grade).val := by
  rw [scalarInverseJet_high_projection parameters frequency source boundary high]
  exact inhomogeneousSmoothInverse_robin_trace parameters frequency _ boundary grade

/-- The exact original scalar support, pinned center jet, full nonexceptional
PDE, and actual high Robin trace. No condition is imposed on center boundary data. -/
def IsNonexceptionalScalarSolution (frequency : ℝ) (source : ClosedJet 1)
    (boundary : NormalSmoothBoundary) (field : ClosedJet 1) : Prop :=
  IsScalarNonexceptional field ∧ fullScalarJet frequency field = source ∧
    (∀ mode : ℤ, mode = 1 ∨ mode = -1 → CenterPinned (angularClosedJet mode field)) ∧
      ∀ grade : ℕ, ordinaryRobinTrace grade
        (unitDiskCoreInto (grade + 2) (excludedAngularJet lowAngularModes field)) = (boundary.grade grade).val

theorem scalarInverseJet_specification (parameters : PhaseParameters) (frequency : ℝ) (source : ClosedJet 1)
    (excluded : IsScalarNonexceptional source) (boundary : NormalSmoothBoundary) (high : BoundaryIsHigh boundary) :
    IsNonexceptionalScalarSolution frequency source boundary (scalarInverseJet parameters frequency source boundary) :=
  ⟨scalarInverseJet_nonexceptional parameters frequency source boundary high,
    scalarInverseJet_equation parameters frequency source excluded boundary high,
    scalarInverseJet_pinned parameters frequency source boundary high,
    scalarInverseJet_robin parameters frequency source boundary high⟩

theorem scalarInverseJet_unique (parameters : PhaseParameters) (frequency : ℝ) (source : ClosedJet 1)
    (boundary : NormalSmoothBoundary) (high : BoundaryIsHigh boundary) (candidate : ClosedJet 1)
    (laws : IsNonexceptionalScalarSolution frequency source boundary candidate) :
    candidate = scalarInverseJet parameters frequency source boundary := by
  have centerSame (mode : ℤ) (center : mode = 1 ∨ mode = -1) :
      angularClosedJet mode candidate = scalarCenterPart mode frequency source := by
    have equation := (fullScalarJet_angular frequency mode candidate).symm.trans
      (congrArg (angularClosedJet mode) laws.2.1)
    rw [fullScalarJet_center frequency mode center _ (angularClosedJet_pure mode candidate)] at equation
    have centerEquation := congrArg Neg.neg equation
    simp only [neg_neg] at centerEquation
    exact pinnedCenterSolution_unique mode center frequency _ (angularClosedJet_pure mode source) _
      (angularClosedJet_pure mode candidate) (laws.2.2.1 mode center) centerEquation
  have highSame : excludedAngularJet lowAngularModes candidate = scalarHighPart parameters frequency source boundary := by
    let first := excludedAngularJet lowAngularModes candidate
    let second := scalarHighPart parameters frequency source boundary
    have firstHigh := excludedSource_high candidate
    have secondHigh := scalarHighPart_high parameters frequency source boundary high
    have firstEquation : scalarResidualJet frequency first = excludedAngularJet lowAngularModes source :=
      (fullScalarJet_high frequency first firstHigh).symm.trans
        ((fullScalarJet_excluded frequency lowAngularModes candidate).trans
          (congrArg (excludedAngularJet lowAngularModes) laws.2.1))
    have secondEquation : scalarResidualJet frequency second = excludedAngularJet lowAngularModes source :=
      (fullScalarJet_high frequency second secondHigh).symm.trans (scalarHighPart_equation parameters frequency source boundary high)
    apply unitDiskCoreInto_injective 2
    apply completedGrade_unique parameters 0 frequency
    · exact (congrArg (fun field : DiskL2 1 => field ∈ highDiskL2) (unitDiskBulk_core 2 first)).mpr firstHigh
    · exact (congrArg (fun field : DiskL2 1 => field ∈ highDiskL2) (unitDiskBulk_core 2 second)).mpr secondHigh
    · exact (unitScalarOperator_core parameters 0 frequency first).trans
        ((congrArg (unitDiskCoreInto 0) (firstEquation.trans secondEquation.symm)).trans
          (unitScalarOperator_core parameters 0 frequency second).symm)
    · exact (laws.2.2.2 0).trans (inhomogeneousSmoothInverse_robin_trace parameters frequency _ boundary 0).symm
  exact (scalar_high_decomposition candidate laws.1).symm.trans
    (congrArg₂ (fun first second : ClosedJet 1 => first + second)
      (congrArg₂ (fun first second : ClosedJet 1 => first + second)
        (centerSame 1 (Or.inl rfl)) (centerSame (-1) (Or.inr rfl))) highSame)

theorem actual_nonexceptional_scalar_solver (parameters : PhaseParameters) (frequency : ℝ) (source : ClosedJet 1)
    (excluded : IsScalarNonexceptional source) (boundary : NormalSmoothBoundary) (high : BoundaryIsHigh boundary) :
    ∃! solution : ClosedJet 1, IsNonexceptionalScalarSolution frequency source boundary solution :=
  ⟨scalarInverseJet parameters frequency source boundary,
    scalarInverseJet_specification parameters frequency source excluded boundary high,
    fun candidate laws => scalarInverseJet_unique parameters frequency source boundary high candidate laws⟩

end Grad.BoundedScalarInverse
