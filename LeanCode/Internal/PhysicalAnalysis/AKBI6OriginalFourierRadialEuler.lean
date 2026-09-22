import AKBI5ActualHomogeneousXiEuler

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
open Set
open scoped ContDiff
namespace Grad.OriginalKernelHomogeneousGraph
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearQuotientBounds
open Grad.NonlinearRange Grad.SourceCollarRestriction Grad.SourceCollarDivision Grad.SourceBoundaryTrace Grad.SourceCollarCoefficients
open Grad.OriginalKernelRetainedDecay Grad.OriginalKernelCovariantRecovery Grad.OriginalKernelGraphRestriction
open Grad.AnnularReconstruction Grad.CircularHighRegularity
open Grad.BoundaryTrace Grad.AnnularOriginalSmoothCore Grad.ActualSmoothPhysicalField Grad.SourceCollarFullSource

theorem originalPolar_radialEuler {dimension : ℕ} (field : ClosedJet dimension) (radius : RadialPoint) (angle : ℝ) :
    radius.val • radialIter 1 (originalPolarValue field) (radius.val,angle)=
      (eulerJet field).value (Grad.SourceCollarDivision.polarClosedPoint radius.val angle radius.property.1 radius.property.2) := by
  change radius.val • radialField (smoothClosedExtension field ∘ polarPlane) (radius.val,angle)=_
  rw [polar_radial_first _ (smoothClosedExtension_smooth field),eulerJet_extension_value]
  change radius.val • fderiv ℝ (smoothClosedExtension field) (polarPlane (radius.val,angle)) (radialDirection angle)=
    fderiv ℝ (smoothClosedExtension field) (polarPlane (radius.val,angle)) (polarPlane (radius.val,angle))
  conv_rhs => arg 2; rw [polarPlane_eq]
  exact (map_smul (fderiv ℝ (smoothClosedExtension field) (polarPlane (radius.val,angle))) radius.val (radialDirection angle)).symm

theorem originalPolarCoefficient_radialEuler (field : ClosedJet 1) (radius : RadialPoint) (mode : ℤ) :
    (radius.val : ℂ) • radialCoefficientJet (originalPolarValue field) mode 1 radius.val=
      angularCoefficient (fun angle => (eulerJet field).value
        (Grad.SourceCollarDivision.polarClosedPoint radius.val angle radius.property.1 radius.property.2)) mode := by
  change (radius.val : ℂ) • angularCoefficient (fun angle => radialIter 1 (originalPolarValue field) (radius.val,angle)) mode=_
  rw [← angularCoefficient_smul_continuous]
  apply congrArg (fun function => angularCoefficient function mode)
  funext angle
  change (radius.val : ℂ) • radialIter 1 (originalPolarValue field) (radius.val,angle)=_
  exact (Complex.coe_smul radius.val (radialIter 1 (originalPolarValue field) (radius.val,angle))).trans
    (originalPolar_radialEuler field radius angle)

/-- The original stored scalar coefficient is exactly the unweighted
Fourier coefficient of its original closed-jet polar extension. -/
theorem originalCoreCoefficient_polar (parameters : PhaseParameters) (lower : ℝ) (positive : 0<lower) (bounded : lower<1)
    (field : ACore parameters 1) (radius : ℝ) (inside : radius∈Icc lower 1) (mode : ℤ×ℤ) :
    originalPhysicalCoefficient ((originalCoreLowCurves parameters lower positive bounded field).fullField bounded) radius mode=
      radialCoefficientJet (originalPolarValue (field.val mode.2)) mode.1 0 radius := by
  rw [originalPhysicalCoefficient,SmoothLowPhysicalRow.fullField_coefficient _ bounded radius inside mode,
    originalCoreLowCurves_physical_coefficient parameters lower positive bounded field radius inside mode,
    ← originalCoreCircleTrace_represents parameters field ⟨radius,positive.le.trans inside.1,inside.2⟩ mode,
    originalCoreCircleTrace_unweighted]
  change angularCoefficient (fun angle => (field.val mode.2).value (Grad.SourceCollarDivision.polarClosedPoint radius angle _ _)) mode.1=
    angularCoefficient (fun angle => originalPolarValue (field.val mode.2) (radius,angle)) mode.1
  apply congrArg (fun function => angularCoefficient function mode.1)
  funext angle
  exact (originalPolarValue_closed _ radius angle (positive.le.trans inside.1) inside.2).symm

/-- Genuine radial differentiation, including both collar endpoints, in the
original coefficient realization. The full original width is unchanged. -/
theorem originalCoreCoefficient_hasDerivWithinAt (parameters : PhaseParameters) (lower : ℝ)
    (positive : 0<lower) (bounded : lower<1) (field : ACore parameters 1)
    (radius : Icc lower (1 : ℝ)) (mode : ℤ×ℤ) :
    HasDerivWithinAt
      (fun location => originalPhysicalCoefficient ((originalCoreLowCurves parameters lower positive bounded field).fullField bounded) location mode)
      ((radius.val : ℂ)⁻¹ • originalPhysicalCoefficient
        ((originalCoreLowCurves parameters lower positive bounded (eulerCore parameters field)).fullField bounded) radius.val mode)
      (Icc lower 1) radius.val := by
  have derivative := (radialCoefficientJet_hasDerivAt (originalPolarValue (field.val mode.2))
    (originalPolarValue_smooth _) mode.1 0 radius.val).hasDerivWithinAt (s:=Icc lower 1)
  have slope := originalPolarCoefficient_radialEuler (field.val mode.2) (tupleRadius lower positive radius) mode.1
  dsimp only [tupleRadius] at slope
  have nonzero : (radius.val : ℂ)≠0 := Complex.ofReal_ne_zero.mpr (positive.trans_le radius.property.1).ne'
  have divided := congrArg ((radius.val : ℂ)⁻¹ • ·) slope
  rw [inv_smul_smul₀ nonzero] at divided
  rw [originalCoreCoefficient_polar parameters lower positive bounded (eulerCore parameters field) radius.val radius.property mode]
  have coefficient : radialCoefficientJet (originalPolarValue ((eulerCore parameters field).val mode.2)) mode.1 0 radius.val=
      angularCoefficient (fun angle => (eulerJet (field.val mode.2)).value
        (Grad.SourceCollarDivision.polarClosedPoint radius.val angle (positive.le.trans radius.property.1) radius.property.2)) mode.1 := by
    change angularCoefficient (fun angle => originalPolarValue ((eulerCore parameters field).val mode.2) (radius.val,angle)) mode.1=_
    simp_rw [originalPolarValue_closed _ radius.val _ (positive.le.trans radius.property.1) radius.property.2]
    rfl
  rw [coefficient,← divided]
  apply derivative.congr
  · intro query included
    exact originalCoreCoefficient_polar parameters lower positive bounded field query included mode
  · exact originalCoreCoefficient_polar parameters lower positive bounded field radius.val radius.property mode

end Grad.OriginalKernelHomogeneousGraph
