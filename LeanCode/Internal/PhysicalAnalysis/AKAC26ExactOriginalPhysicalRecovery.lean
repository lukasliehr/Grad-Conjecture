import AKAC25SameMatrixPointwiseAction

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open Set Filter MeasureTheory
open scoped ContDiff BigOperators
namespace Grad.ActualSmoothPhysicalField
open Grad.ClosedJets Grad.CartesianState Grad.BoundaryTrace Grad.SourceCollarFullSource
open Grad.SourceBoundaryTrace Grad.SourceCollarDivision Grad.SourceCollarCoefficients Grad.SourceCollarRestriction
open Grad.GaugeCoefficients.Physical.Ledger Grad.BoundaryLift Grad.PhaseAlgebra Grad.ActualPhysicalField
open Grad.SourceCollar Grad.AnnularCurrentLow
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope Grad.GaugeCoefficients.Physical.Allocation

variable (parameters : PhaseParameters) (length rho epsilon : ℝ) (base : ACore parameters 3)
    (small : physicalBudget parameters base rho epsilon 6 ≤ originalCoefficientLowRadius parameters length)
    (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    {polar : DivisionRow 3 lower} (curves : SmoothLowPhysicalRow parameters lower positive polar)

/-- Genuine original-frame recovery: Q converts the polar covariant to
Cartesian coordinates BEFORE multiplication by the literal Cartesian F^-T. -/
theorem SmoothLowPhysicalRow.fullField_physicalUFromPolar (radius : ℝ) (inside : radius ∈ Icc lower 1)
    (angles : ℝ × ℝ) :
    (curves.physicalUFromPolar parameters length rho epsilon base small lower positive bounded).fullField bounded (radius,angles) =
      WithLp.toLp 2 ((familyMatrix (originalInverseTransposeFamily parameters length epsilon base) 0 angles.2
        (polarClosedPoint radius angles.1 (positive.le.trans inside.1) inside.2)).mulVec
          (cartesianCovariantValue angles.1 (curves.fullField bounded (radius,angles)))) := by
  change (curves.cartesianCovariant.matrixAction parameters
    (originalInverseTransposeFamily parameters length epsilon base)
    (originalInverseTransposeFamily_coherent parameters length rho epsilon base small) lower positive bounded).fullField bounded (radius,angles) = _
  rw [curves.cartesianCovariant.fullField_matrixAction parameters _ _ lower positive bounded radius inside angles,
    physicalMatrixProduct_apply,curves.fullField_cartesianCovariant bounded radius inside angles]

/-- The actual Cartesian frame applied to the recovered SAME U returns
Q a_c exactly, so the rotation cannot be silently omitted. -/
theorem SmoothLowPhysicalRow.fullField_originalFrameRecovery (radius : ℝ) (inside : radius ∈ Icc lower 1)
    (angles : ℝ × ℝ) :
    WithLp.toLp 2 ((originalPhysicalFrameMatrix parameters length epsilon base angles.2
      (polarClosedPoint radius angles.1 (positive.le.trans inside.1) inside.2)).transpose.mulVec
        ((curves.physicalUFromPolar parameters length rho epsilon base small lower positive bounded).fullField bounded (radius,angles))) =
      cartesianCovariantValue angles.1 (curves.fullField bounded (radius,angles)) := by
  rw [curves.fullField_physicalUFromPolar parameters length rho epsilon base small lower positive bounded radius inside angles]
  change WithLp.toLp 2 (Matrix.mulVec _ (Matrix.mulVec _ (cartesianCovariantValue angles.1 (curves.fullField bounded (radius,angles))))) = _
  rw [Matrix.mulVec_mulVec]
  rw [(originalInverseTransposeFamily_two_sided parameters length rho epsilon base small 0 angles.2
    (polarClosedPoint radius angles.1 (positive.le.trans inside.1) inside.2)).1,Matrix.one_mulVec]

/-- The corrected pair has its original low-rho coefficients and joint
smooth representatives, together with bounds independent of the inner radius. -/
theorem correctedPhysicalPair_same_smooth_bound {xi : DivisionRow 1 lower}
    (scalar : SmoothLowPhysicalRow parameters lower positive xi) :
    let vector := curves.physicalUFromPolar parameters length rho epsilon base small lower positive bounded
    let scalarOverRadius := scalar.polarScalarOverRadius curves
    ContDiffOn ℝ ∞ (vector.fullField bounded) (Grad.AnnularClosedJointRegularity.annularJointClosed lower) ∧
    ContDiffOn ℝ ∞ (scalarOverRadius.fullField bounded) (Grad.AnnularClosedJointRegularity.annularJointClosed lower) ∧
    (∀ᵐ radius ∂volume.restrict (Icc lower 1), ∀ mode,
      doubleCoefficient (fun angles => vector.fullField bounded (radius,angles)) mode =
        lowRhoPhysicalCoefficient parameters lower positive
          (physicalUFromPolar parameters length rho epsilon base small lower positive bounded.le polar) radius mode) ∧
    (∀ᵐ radius ∂volume.restrict (Icc lower 1), ∀ mode,
      doubleCoefficient (fun angles => scalarOverRadius.fullField bounded (radius,angles)) mode =
        lowRhoPhysicalCoefficient parameters lower positive (polarScalarOverRadiusRow lower xi polar) radius mode) ∧
    ‖physicalUFromPolar parameters length rho epsilon base small lower positive bounded.le polar‖ ≤
      5 * physicalUActionConstant parameters length 0 * (1+physicalBudget parameters base rho epsilon 5) * ‖polar‖ ∧
    ‖polarScalarOverRadiusRow lower xi polar‖ ≤ ‖xi‖+‖polar‖ := by
  dsimp only
  refine ⟨(curves.physicalUFromPolar parameters length rho epsilon base small lower positive bounded).fullField_smooth bounded,
    (scalar.polarScalarOverRadius curves).fullField_smooth bounded,?_,?_,
    physicalUFromPolar_bound parameters length rho epsilon base small lower positive bounded.le polar,
    polarScalarOverRadiusRow_bound lower xi polar⟩
  · filter_upwards [(curves.physicalUFromPolar parameters length rho epsilon base small lower positive bounded).physicalCurve_actual bounded 0,
      ae_restrict_mem measurableSet_Icc] with radius same inside
    intro mode
    rw [SmoothLowPhysicalRow.fullField_doubleCoefficient _ bounded radius inside mode,same mode,pow_zero,one_smul]
  · filter_upwards [(scalar.polarScalarOverRadius curves).physicalCurve_actual bounded 0,
      ae_restrict_mem measurableSet_Icc] with radius same inside
    intro mode
    rw [SmoothLowPhysicalRow.fullField_doubleCoefficient _ bounded radius inside mode,same mode,pow_zero,one_smul]

end Grad.ActualSmoothPhysicalField
