import ANB2ScalarSectorAlgebra

noncomputable section
set_option maxHeartbeats 1400000
open scoped BigOperators
namespace Grad.BoundedScalarInverse
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.CircularHighWeak
open Grad.ActualAngularInverse Grad.ActualSmoothPDE Grad.SmoothRobinUniqueness
open Grad.CircularHighRegularity Grad.ActualCenterVolterra Grad.InhomogeneousHighRobin Grad.CircularNormalLift

abbrev BoundaryIsHigh (data : NormalSmoothBoundary) : Prop :=
  ∀ mode ∈ lowAngularModes, normalBoundaryCoefficient 2 (data.grade 0) mode = 0

def scalarCenterPart (mode : ℤ) (frequency : ℝ) (source : ClosedJet 1) : ClosedJet 1 :=
  pinnedCenterSolution mode frequency (angularClosedJet mode source)

def scalarHighPart (parameters : PhaseParameters) (frequency : ℝ) (source : ClosedJet 1)
    (boundary : NormalSmoothBoundary) : ClosedJet 1 :=
  inhomogeneousSmoothInverse parameters frequency (excludedAngularJet lowAngularModes source) boundary

/-- One genuine smooth scalar solution, fixed before all Sobolev grades. -/
def scalarInverseJet (parameters : PhaseParameters) (frequency : ℝ) (source : ClosedJet 1)
    (boundary : NormalSmoothBoundary) : ClosedJet 1 :=
  scalarCenterPart 1 frequency source + scalarCenterPart (-1) frequency source +
    scalarHighPart parameters frequency source boundary

theorem angularClosedJet_pure (mode : ℤ) (field : ClosedJet 1) :
    angularClosedJet mode (angularClosedJet mode field) = angularClosedJet mode field := by
  simpa only [ite_true] using angularClosedJet_projection mode mode field

theorem angularClosedJet_of_pure (other mode : ℤ) (field : ClosedJet 1)
    (pure : angularClosedJet mode field = field) :
    angularClosedJet other field = if other = mode then field else 0 := by
  exact (congrArg (angularClosedJet other) pure).symm.trans
    ((angularClosedJet_projection other mode field).trans (by
      by_cases same : other = mode
      · subst other; rw [if_pos rfl, if_pos rfl, pure]
      · rw [if_neg same, if_neg same]))

theorem scalarCenterPart_pure (mode : ℤ) (center : mode = 1 ∨ mode = -1)
    (frequency : ℝ) (source : ClosedJet 1) :
    angularClosedJet mode (scalarCenterPart mode frequency source) = scalarCenterPart mode frequency source :=
  pinnedCenterSolution_pure mode center frequency _ (angularClosedJet_pure mode source)

theorem scalarCenterPart_equation (mode : ℤ) (center : mode = 1 ∨ mode = -1)
    (frequency : ℝ) (source : ClosedJet 1) :
    fullScalarJet frequency (scalarCenterPart mode frequency source) = angularClosedJet mode source :=
  fullScalarJet_pinnedCenter mode center frequency _ (angularClosedJet_pure mode source)

theorem excludedSource_high (source : ClosedJet 1) : closedL2Core (excludedAngularJet lowAngularModes source) ∈ highDiskL2 :=
  (congrArg (fun field : DiskL2 1 => field ∈ highDiskL2) (highL2Projection_core source)).mp (highL2Projection_mem _)

theorem scalarHighPart_high (parameters : PhaseParameters) (frequency : ℝ) (source : ClosedJet 1)
    (boundary : NormalSmoothBoundary) (high : BoundaryIsHigh boundary) :
    closedL2Core (scalarHighPart parameters frequency source boundary) ∈ highDiskL2 :=
  inhomogeneousSmoothInverse_high parameters frequency _ boundary high

theorem scalarHighPart_equation (parameters : PhaseParameters) (frequency : ℝ) (source : ClosedJet 1)
    (boundary : NormalSmoothBoundary) (high : BoundaryIsHigh boundary) :
    fullScalarJet frequency (scalarHighPart parameters frequency source boundary) = excludedAngularJet lowAngularModes source :=
  (fullScalarJet_high frequency _ (scalarHighPart_high parameters frequency source boundary high)).trans
    (inhomogeneousSmoothInverse_scalar parameters frequency _ (excludedSource_high source) boundary high)

theorem scalarInverseJet_nonexceptional (parameters : PhaseParameters) (frequency : ℝ) (source : ClosedJet 1)
    (boundary : NormalSmoothBoundary) (high : BoundaryIsHigh boundary) :
    IsScalarNonexceptional (scalarInverseJet parameters frequency source boundary) :=
  scalarNonexceptional_add _ _
    (scalarNonexceptional_add _ _
      (pureMode_nonexceptional 1 (Or.inl rfl) _ (scalarCenterPart_pure 1 (Or.inl rfl) frequency source))
      (pureMode_nonexceptional (-1) (Or.inr rfl) _ (scalarCenterPart_pure (-1) (Or.inr rfl) frequency source)))
    (high_nonexceptional _ (scalarHighPart_high parameters frequency source boundary high))

theorem scalarInverseJet_equation (parameters : PhaseParameters) (frequency : ℝ) (source : ClosedJet 1)
    (excluded : IsScalarNonexceptional source) (boundary : NormalSmoothBoundary) (high : BoundaryIsHigh boundary) :
    fullScalarJet frequency (scalarInverseJet parameters frequency source boundary) = source := by
  change fullScalarLinear frequency (_ + _ + _) = _
  rw [map_add, map_add]
  change fullScalarJet frequency (scalarCenterPart 1 frequency source) +
    fullScalarJet frequency (scalarCenterPart (-1) frequency source) +
      fullScalarJet frequency (scalarHighPart parameters frequency source boundary) = _
  rw [scalarCenterPart_equation 1 (Or.inl rfl), scalarCenterPart_equation (-1) (Or.inr rfl),
    scalarHighPart_equation parameters frequency source boundary high]
  exact scalar_high_decomposition source excluded

theorem scalarInverseJet_center_projection (parameters : PhaseParameters) (frequency : ℝ) (source : ClosedJet 1)
    (boundary : NormalSmoothBoundary) (high : BoundaryIsHigh boundary) (mode : ℤ) (center : mode = 1 ∨ mode = -1) :
    angularClosedJet mode (scalarInverseJet parameters frequency source boundary) = scalarCenterPart mode frequency source := by
  have highZero : angularClosedJet mode (scalarHighPart parameters frequency source boundary) = 0 :=
    (congrArg (angularClosedJet mode) (smoothHigh_fixed _ (scalarHighPart_high parameters frequency source boundary high))).symm.trans
      (excludedAngularJet_low_zero _ mode (by rcases center with rfl | rfl <;> simp [lowAngularModes]))
  rw [scalarInverseJet, angularClosedJet_add, angularClosedJet_add,
    angularClosedJet_of_pure mode 1 _ (scalarCenterPart_pure 1 (Or.inl rfl) frequency source),
    angularClosedJet_of_pure mode (-1) _ (scalarCenterPart_pure (-1) (Or.inr rfl) frequency source), highZero]
  rcases center with rfl | rfl <;> norm_num

end Grad.BoundedScalarInverse
