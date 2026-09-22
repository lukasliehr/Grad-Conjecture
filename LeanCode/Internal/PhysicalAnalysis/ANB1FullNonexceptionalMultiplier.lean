import ANS11InverseCompatibility

noncomputable section
set_option maxHeartbeats 1400000
open scoped BigOperators
namespace Grad.BoundedScalarInverse
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.CircularHighWeak
open Grad.ActualAngularInverse Grad.ActualSmoothPDE Grad.SmoothRobinUniqueness

/-- The actual full multiplier I+4R^{-2}. Only its restriction to modes
outside {0,2,-2} enters the nonexceptional scalar inverse. -/
def fullBLinear : ClosedJet 1 →ₗ[ℂ] ClosedJet 1 :=
  LinearMap.id + (4 : ℂ) • (shiftInverseLinear 1 0).comp (shiftInverseLinear 1 0)

def fullBJet (field : ClosedJet 1) : ClosedJet 1 := fullBLinear field

def IsScalarNonexceptional (field : ClosedJet 1) : Prop :=
  angularClosedJet 0 field = 0 ∧ angularClosedJet 2 field = 0 ∧ angularClosedJet (-2) field = 0

theorem fullBJet_formula (field : ClosedJet 1) :
    fullBJet field = field + (4 : ℂ) • shiftInverseJet 0 (shiftInverseJet 0 field) := rfl

theorem fullBJet_angular (mode : ℤ) (field : ClosedJet 1) :
    angularClosedJet mode (fullBJet field) = fullBJet (angularClosedJet mode field) := by
  rw [fullBJet_formula, angularClosedJet_add, angularClosedJet_smul,
    ← shiftInverseJet_angular, ← shiftInverseJet_angular]
  rfl

theorem fullBJet_coefficient (mode : ℤ) (nonzero : mode ≠ 0) (field : ClosedJet 1) :
    angularClosedJet mode (fullBJet field) =
      (1 - 4 / (mode : ℂ) ^ 2) • angularClosedJet mode field := by
  rw [fullBJet_formula, angularClosedJet_add, angularClosedJet_smul,
    shiftInverseJet_coefficient, shiftInverseJet_coefficient]
  simp only [neg_zero, add_zero, if_neg nonzero, smul_smul]
  have algebra : (1 : ℂ) + 4 * ((Complex.I * (mode : ℂ))⁻¹ * (Complex.I * (mode : ℂ))⁻¹) =
      1 - 4 / (mode : ℂ) ^ 2 := by
    have frequency : (mode : ℂ) ≠ 0 := by exact_mod_cast nonzero
    field_simp
    simp [Complex.I_sq]
    ring
  calc
    _ = (1 + 4 * ((Complex.I * (mode : ℂ))⁻¹ * (Complex.I * (mode : ℂ))⁻¹)) •
        angularClosedJet mode field := by rw [add_smul, one_smul]
    _ = _ := congrArg (fun scalar : ℂ => scalar • angularClosedJet mode field) algebra

theorem fullBJet_center (mode : ℤ) (center : mode = 1 ∨ mode = -1)
    (field : ClosedJet 1) (pure : angularClosedJet mode field = field) :
    fullBJet field = (-3 : ℂ) • field := by
  have identity := (fullBJet_angular mode field).symm.trans (fullBJet_coefficient mode (by omega) field)
  rw [pure] at identity
  rcases center with rfl | rfl <;> norm_num at identity ⊢ <;> exact identity

theorem primitive_of_zero_mean (field : ClosedJet 1) (meanZero : angularClosedJet 0 field = 0) :
    shiftInverseJet 0 field = angularPrimitiveJet field := by
  apply scalarJet_angular_ext
  intro mode
  rw [shiftInverseJet_coefficient, angularClosedJet_angularPrimitive]
  by_cases zero : mode = 0
  · subst mode
    simp [meanZero, angularPrimitiveJet_zero]
  · simp only [neg_zero, add_zero, if_neg zero]
    exact (angularPrimitiveJet_pureMode mode zero field).symm

theorem fullBJet_high (field : ClosedJet 1) (high : closedL2Core field ∈ highDiskL2) :
    fullBJet field = smoothDiskBJet field := by
  have fixed := smoothHigh_fixed field high
  have meanZero : angularClosedJet 0 field = 0 := by
    rw [← fixed]
    exact excludedAngularJet_low_zero field 0 (by simp [lowAngularModes])
  rw [fullBJet_formula, primitive_of_zero_mean field meanZero]
  have primitiveMean : angularClosedJet 0 (angularPrimitiveJet field) = 0 := by
    rw [angularClosedJet_angularPrimitive, meanZero, angularPrimitiveJet_zero]
  rw [primitive_of_zero_mean _ primitiveMean]
  exact (congrArg (fun jet : ClosedJet 1 => jet + (4 : ℂ) • angularPrimitiveJet (angularPrimitiveJet jet)) fixed).symm

end Grad.BoundedScalarInverse
