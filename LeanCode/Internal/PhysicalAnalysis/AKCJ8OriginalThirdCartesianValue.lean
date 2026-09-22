import AKCJ7OriginalCoreProductRotation

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open Set Filter
open scoped Topology
namespace Grad.OriginalCoreRealization
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearQuotientBounds Grad.NonlinearRange
open Grad.ActualCartesianDescent Grad.PhysicalFamily Grad.SourceCollar Grad.SourceCollarDivision
open Grad.OriginalKernelCovariantRecovery Grad.OriginalKernelRetainedDecay
open Grad.GaugeCoefficients.Physical.Ledger Grad.GaugeCoefficients.Physical.RadialLedger
open Grad.SourceCollarFullSource Grad.FinitePhysicalJetLift

/-- Exact Cartesian expression of the actual original fourth derivative row.
All fields are the literal original cores and the true original frame. -/
theorem originalThirdRow_cartesianValue (parameters : PhaseParameters) (length epsilon lower : ℝ)
    (nonzero : length≠0) (positive : 0<lower) (bounded : lower<1)
    (base vector : ACore parameters 3) (scalar : ACore parameters 1) (state : QuotientState parameters)
    (sameBase : state.2.1=planarReferenceCore parameters+base) (sameEpsilon : state.1=(epsilon : ℂ))
    (radius : ℝ) (inside : radius∈Ioo lower 1) (angles : ℝ×ℝ) :
    coreValue (quotientRowsDerivative parameters length 1 state ![(0,vector,scalar)] 3)
      (polarClosedPoint radius angles.1 (positive.le.trans inside.1.le) inside.2.le) angles.2 0=
      (length : ℂ) * fderiv ℝ
        (originalCoreProductLift parameters (originalCovariantCore parameters length epsilon base vector false))
        (polarPlane (radius,angles.1),angles.2) (planeQuarterTurn (polarPlane (radius,angles.1)),0) 2-
      fderiv ℝ (originalCoreProductLift parameters (originalKernelXi state.2.1 vector scalar))
        (polarPlane (radius,angles.1),angles.2) (0,1) 0+
      (length : ℂ) * removePolarMean (fun query =>
        (-2 : ℂ) * coreValue (originalCovariantCore parameters length epsilon base vector true)
          (polarClosedPoint radius query.1 (positive.le.trans inside.1.le) inside.2.le) query.2 2) angles := by
  have normInside : ‖polarPlane (radius,angles.1)‖<1 := by
    rw [polarPlane_norm,abs_of_pos (positive.trans inside.1)]
    exact inside.2
  have rotated := originalCoreProductLift_rotation parameters
    (originalCovariantCore parameters length epsilon base vector false)
    (polarPlane (radius,angles.1),angles.2) normInside
  have axial := originalCoreProductLift_axial parameters (originalKernelXi state.2.1 vector scalar)
    (polarPlane (radius,angles.1),angles.2) normInside
  have pointSame : (⟨polarPlane (radius,angles.1),normInside.le⟩ : ClosedDisk)=
      polarClosedPoint radius angles.1 (positive.le.trans inside.1.le) inside.2.le := by
    apply Subtype.ext
    rfl
  rw [pointSame] at rotated axial
  rw [← originalThirdRow_covariant_unscaled parameters length epsilon nonzero base vector scalar state sameBase sameEpsilon,
    coreValue_add,coreValue_subtract,coreValue_smul,coreValue_smul,PiLp.add_apply,PiLp.sub_apply,PiLp.smul_apply,PiLp.smul_apply,
    originalRotation_valueMap,coreValue_valueMap,originalCore_removeAngular_polar parameters lower positive bounded _ radius ⟨inside.1.le,inside.2.le⟩ angles]
  simp only [coreValue_smul,PiLp.smul_apply,coreValue_valueMap,matrixUnit_apply,operatorBasis,ite_true,smul_eq_mul,mul_one]
  rw [rotated,← axial]

end Grad.OriginalCoreRealization
