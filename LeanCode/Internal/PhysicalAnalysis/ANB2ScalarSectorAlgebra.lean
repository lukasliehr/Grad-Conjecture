import ANB1FullNonexceptionalMultiplier
import ACB20NativeCenterConsumer

noncomputable section
set_option maxHeartbeats 1400000
open scoped BigOperators
namespace Grad.BoundedScalarInverse
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.CircularHighWeak
open Grad.ActualAngularInverse Grad.ActualSmoothPDE Grad.SmoothRobinUniqueness
open Grad.CircularHighRegularity Grad.NonlinearDivision Grad.ActualCenterVolterra

def fullScalarLinear (frequency : ℝ) : ClosedJet 1 →ₗ[ℂ] ClosedJet 1 :=
  -laplacianJetLinear + ((frequency ^ 2 : ℝ) : ℂ) • fullBLinear

def fullScalarJet (frequency : ℝ) (field : ClosedJet 1) : ClosedJet 1 := fullScalarLinear frequency field

theorem fullScalarJet_formula (frequency : ℝ) (field : ClosedJet 1) :
    fullScalarJet frequency field = -laplacianJet field + ((frequency ^ 2 : ℝ) : ℂ) • fullBJet field := rfl

theorem fullScalarJet_angular (frequency : ℝ) (mode : ℤ) (field : ClosedJet 1) :
    angularClosedJet mode (fullScalarJet frequency field) = fullScalarJet frequency (angularClosedJet mode field) := by
  rw [fullScalarJet_formula, angularClosedJet_add, angularClosedJet_smul]
  have negative := (angularClosedJetLinear 1 mode).map_neg (laplacianJet field)
  change angularClosedJet mode (-laplacianJet field) = -angularClosedJet mode (laplacianJet field) at negative
  rw [negative, ← laplacianJet_angular, fullBJet_angular]
  rfl

theorem fullScalarJet_high (frequency : ℝ) (field : ClosedJet 1) (high : closedL2Core field ∈ highDiskL2) :
    fullScalarJet frequency field = scalarResidualJet frequency field := by
  rw [fullScalarJet_formula, fullBJet_high field high]
  rfl

theorem fullScalarJet_center (frequency : ℝ) (mode : ℤ) (center : mode = 1 ∨ mode = -1)
    (field : ClosedJet 1) (pure : angularClosedJet mode field = field) :
    fullScalarJet frequency field = -(laplacianJet field + ((3 * frequency ^ 2 : ℝ) : ℂ) • field) := by
  rw [fullScalarJet_formula, fullBJet_center mode center field pure, smul_smul]
  have coefficient : ((frequency ^ 2 : ℝ) : ℂ) * (-3 : ℂ) = -((3 * frequency ^ 2 : ℝ) : ℂ) := by push_cast; ring
  rw [coefficient, neg_smul, neg_add_rev]
  abel

theorem fullScalarJet_pinnedCenter (mode : ℤ) (center : mode = 1 ∨ mode = -1)
    (frequency : ℝ) (source : ClosedJet 1) (pure : angularClosedJet mode source = source) :
    fullScalarJet frequency (pinnedCenterSolution mode frequency source) = source := by
  rw [fullScalarJet_center frequency mode center _ (pinnedCenterSolution_pure mode center frequency source pure),
    pinnedCenterSolution_equation mode center frequency source pure, neg_neg]

theorem scalar_high_decomposition (field : ClosedJet 1) (excluded : IsScalarNonexceptional field) :
    angularClosedJet 1 field + angularClosedJet (-1) field + excludedAngularJet lowAngularModes field = field := by
  have selected : selectedAngularJet lowAngularModes field = angularClosedJet 1 field + angularClosedJet (-1) field := by
    rw [selectedAngularJet_eq]
    simp [lowAngularModes, excluded.1, excluded.2.1, excluded.2.2, add_comm]
  change angularClosedJet 1 field + angularClosedJet (-1) field + (field - selectedAngularJet lowAngularModes field) = field
  rw [selected]
  abel

theorem pureMode_nonexceptional (mode : ℤ) (center : mode = 1 ∨ mode = -1)
    (field : ClosedJet 1) (pure : angularClosedJet mode field = field) : IsScalarNonexceptional field := by
  have coefficient (other : ℤ) (different : other ≠ mode) : angularClosedJet other field = 0 := by
    exact (congrArg (angularClosedJet other) pure).symm.trans
      ((angularClosedJet_projection other mode field).trans (if_neg different))
  exact ⟨coefficient 0 (by omega), coefficient 2 (by omega), coefficient (-2) (by omega)⟩

theorem high_nonexceptional (field : ClosedJet 1) (high : closedL2Core field ∈ highDiskL2) :
    IsScalarNonexceptional field := by
  have vanish (mode : ℤ) (member : mode ∈ lowAngularModes) : angularClosedJet mode field = 0 :=
    (congrArg (angularClosedJet mode) (smoothHigh_fixed field high)).symm.trans (excludedAngularJet_low_zero field mode member)
  exact ⟨vanish 0 (by simp [lowAngularModes]), vanish 2 (by simp [lowAngularModes]), vanish (-2) (by simp [lowAngularModes])⟩

theorem scalarNonexceptional_add (first second : ClosedJet 1)
    (firstExcluded : IsScalarNonexceptional first) (secondExcluded : IsScalarNonexceptional second) :
    IsScalarNonexceptional (first + second) := by
  simp only [IsScalarNonexceptional, angularClosedJet_add, firstExcluded.1, firstExcluded.2.1,
    firstExcluded.2.2, secondExcluded.1, secondExcluded.2.1, secondExcluded.2.2, zero_add, and_self]

end Grad.BoundedScalarInverse
