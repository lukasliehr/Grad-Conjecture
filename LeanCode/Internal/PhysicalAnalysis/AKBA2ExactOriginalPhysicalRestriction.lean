import AKBA1ScalarOriginalWeightedRestriction

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
open Set
open scoped ContDiff
namespace Grad.OriginalKernelGraphRestriction
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.BoundaryTrace
open Grad.NonlinearRange Grad.NonlinearQuotientBounds Grad.SourceCollarRestriction Grad.SourceCollarFullSource
open Grad.SourceCollarDivision Grad.SourceCollarCoefficients Grad.SourceBoundaryTrace
open Grad.AnnularGeneralSourceRegularity Grad.AnnularReconstruction Grad.ActualSmoothPhysicalField
open Grad.OriginalKernelRetainedDecay Grad.PhaseAlgebra

local instance : Fact (0 < 2*Real.pi) := ⟨by positivity⟩

theorem originalCoreCircle_angular_periodic {dimension : ℕ} (parameters : PhaseParameters)
    (field : ACore parameters dimension) (radius : RadialPoint) (axial : ℝ) :
    Function.Periodic (fun polar => originalCoreCircle parameters field radius (polar,axial)) (2*Real.pi) := by
  intro polar
  exact congrArg (fun point => coreValue field point axial)
    (divisionPolarPoint_periodic radius.val radius.property.1 radius.property.2 polar)

theorem originalCoreCircle_cell_periodic {dimension : ℕ} (parameters : PhaseParameters)
    (field : ACore parameters dimension) (radius : RadialPoint) (polar : ℝ) :
    Function.Periodic (fun axial => originalCoreCircle parameters field radius (polar,axial)) (2*Real.pi) := by
  intro axial
  unfold originalCoreCircle coreValue
  apply tsum_congr
  intro cell
  simp only [axialPhase_eq_character,AddCircle.coe_add_period]

theorem originalCore_weighted_radial_zero {dimension : ℕ} (parameters : PhaseParameters)
    (field : ACore parameters dimension) (radius : RadialPoint) (mode : ℤ × ℤ) :
    radialCoefficientJet (originalPolarValue (phaseWeightedJet parameters mode.2 (field.val mode.2))) mode.1 0 radius.val =
      (Real.exp (radialPhase parameters radius.val mode.2) : ℂ) •
        doubleCoefficient (originalCoreCircle parameters field radius) mode := by
  change angularCoefficient (fun angle => originalPolarValue (phaseWeightedJet parameters mode.2 (field.val mode.2)) (radius.val,angle)) mode.1 = _
  have value (angle : ℝ) : originalPolarValue (phaseWeightedJet parameters mode.2 (field.val mode.2)) (radius.val,angle) =
      (Real.exp (radialPhase parameters radius.val mode.2) : ℂ) • (field.val mode.2).value
        (Grad.SourceCollarDivision.polarClosedPoint radius.val angle radius.property.1 radius.property.2) := by
    rw [originalPolarValue_closed _ radius.val angle radius.property.1 radius.property.2,phaseWeightedJet_value]
    change (cartesianWeight parameters mode.2 (polarPlane (radius.val,angle))) • _ = _
    rw [cartesianWeight_polar parameters mode.2 radius.val angle radius.property.1,Complex.coe_smul]
  simp_rw [value]
  rw [← originalCoreCircleTrace_represents parameters field radius mode,originalCoreCircleTrace_unweighted]
  exact angularCoefficient_smul_continuous _ _ _

variable (parameters : PhaseParameters) (lower : ℝ) (positive : 0<lower) (bounded : lower<1)
    (field : ACore parameters 1)

theorem originalCoreLowCurves_physical_coefficient (radius : ℝ) (inside : radius ∈ Icc lower 1) (mode : ℤ × ℤ) :
    (originalCoreLowCurves parameters lower positive bounded field).physicalCurve 0 radius mode =
      doubleCoefficient (originalCoreCircle parameters field ⟨radius,positive.le.trans inside.1,inside.2⟩) mode := by
  rw [SmoothLowPhysicalRow.physicalCurve_coefficient _ bounded 0 radius inside mode]
  change (Real.exp (-radialPhase parameters radius mode.2) : ℂ) •
    cartesianWeightedRadialCurve parameters lower positive bounded field 0 0 radius mode = _
  rw [cartesianWeightedRadialCurve_coefficient parameters lower positive bounded field 0 0 mode radius inside]
  change (Real.exp (-radialPhase parameters radius mode.2) : ℂ) •
    ((annularFrequency mode.1 mode.2 : ℂ)^0 • radialCoefficientJet _ mode.1 0 radius) = _
  rw [pow_zero,one_smul,originalCore_weighted_radial_zero parameters field
    ⟨radius,positive.le.trans inside.1,inside.2⟩ mode,Real.exp_neg,Complex.ofReal_inv,
    inv_smul_smul₀ (Complex.ofReal_ne_zero.mpr (Real.exp_pos _).ne')]

/-- The reconstructed closed-collar field is pointwise the original ACore
physical value at every radius and both angles, including the collar ends. -/
theorem originalCoreLowCurves_fullField (radius : ℝ) (inside : radius ∈ Icc lower 1) (angles : ℝ × ℝ) :
    (originalCoreLowCurves parameters lower positive bounded field).fullField bounded (radius,angles) =
      originalCoreCircle parameters field ⟨radius,positive.le.trans inside.1,inside.2⟩ angles := by
  apply congrFun ((originalCoreLowCurves parameters lower positive bounded field).fullField_eq_of_doubleCoefficient
    bounded radius inside _ (originalCoreCircle_continuous parameters field _)
    (originalCoreCircle_angular_periodic parameters field _) (originalCoreCircle_cell_periodic parameters field _) _) angles
  exact fun mode => (originalCoreLowCurves_physical_coefficient parameters lower positive bounded field radius inside mode).symm

end Grad.OriginalKernelGraphRestriction
