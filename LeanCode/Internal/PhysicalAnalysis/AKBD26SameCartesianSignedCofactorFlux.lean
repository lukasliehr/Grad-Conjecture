import AKBD25SamePolarCofactorVector

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
open Set Filter
open scoped Topology ContDiff BigOperators
namespace Grad.ActualDeterminantEquations
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.ActualSmoothPhysicalField
open Grad.ActualCartesianEquations Grad.ActualCartesianDescent Grad.PhysicalFamily Grad.BoundaryTrace
open Grad.AnnularReconstruction Grad.GaugeCoefficients.Physical.Ledger Grad.ActualPolarFlux
open Grad.SourceCollar Grad.ActualGaugeSigmaPrimitives Grad.ActualCurrentPrimitives

/-- Q(B_polar a)=B_C Q a for the literal bilinear polar cofactor matrix. -/
theorem polarCofactorRotation_algebra (angle : ℝ) (matrix : Matrix (Fin 3) (Fin 3) ℂ) (value : ComplexEuclidean 3) :
    cartesianCovariantValue angle (WithLp.toLp 2 (fun row => ∑ column : Fin 3, polarMatrixEntry row column angle matrix * value column)) =
      WithLp.toLp 2 (matrix.mulVec (cartesianCovariantValue angle value)) := by
  simp_rw [polarMatrixEntry_matrix]
  change WithLp.toLp 2 ((polarDomainMatrix angle).mulVec (((polarDomainMatrix angle).transpose * matrix * polarDomainMatrix angle).mulVec value)) =
    WithLp.toLp 2 (matrix.mulVec ((polarDomainMatrix angle).mulVec value))
  rw [Matrix.mulVec_mulVec,Matrix.mulVec_mulVec]
  congr 2
  calc
    polarDomainMatrix angle * ((polarDomainMatrix angle).transpose * matrix * polarDomainMatrix angle) =
        (polarDomainMatrix angle * (polarDomainMatrix angle).transpose) * matrix * polarDomainMatrix angle := by simp only [Matrix.mul_assoc]
    _ = matrix * polarDomainMatrix angle := by rw [(polarDomainMatrix_orthogonal angle).2,Matrix.one_mul]

variable (parameters : PhaseParameters) (length compact lower : ℝ) (positive : 0 < lower)
    (bounded : lower < 1) (state : RetainedInverseState parameters length compact)
    {row : DivisionRow 7 lower} (curves : SmoothLowPhysicalRow parameters lower positive row)

/-- Exact fidelity of the SAME completed Cartesian cofactor flux. It is
B_C(Q a_c), with the original signed determinant and no omitted rotation. -/
theorem sameCartesianCofactorFlux_literal (radius : ℝ) (inside : radius ∈ Icc lower 1) (angles : ℝ × ℝ) :
    (samePolarCofactorVector parameters length compact lower positive bounded state curves).cartesianCovariant.fullField bounded (radius,angles) =
      WithLp.toLp 2 ((originalPhysicalSignedCofactor parameters length state.val.val.epsilon state.val.val.field angles.2
        (polarClosedPoint radius angles.1 (positive.le.trans inside.1) inside.2)).mulVec
        (cartesianCovariantValue angles.1 ((curves.covariant parameters length compact lower positive bounded state.val).fullField bounded (radius,angles)))) := by
  rw [SmoothLowPhysicalRow.fullField_cartesianCovariant bounded _ radius inside angles]
  have polar : (samePolarCofactorVector parameters length compact lower positive bounded state curves).fullField bounded (radius,angles) =
      WithLp.toLp 2 (fun component => ∑ column : Fin 3,
        originalSignedCofactorRow parameters length state.val.val.epsilon state.val.val.field component angles.2 angles.1
          (polarClosedPoint radius angles.1 (positive.le.trans inside.1) inside.2) column *
          (curves.covariant parameters length compact lower positive bounded state.val).fullField bounded (radius,angles) column) := by
    apply PiLp.ext
    intro component
    rw [samePolarCofactorVector_component parameters length compact lower positive bounded state curves component radius inside angles]
    exact fullField_signedCofactorRow parameters length compact lower positive bounded state component
      (curves.covariant parameters length compact lower positive bounded state.val) radius inside angles
  rw [polar]
  exact polarCofactorRotation_algebra angles.1 _ _

end Grad.ActualDeterminantEquations
