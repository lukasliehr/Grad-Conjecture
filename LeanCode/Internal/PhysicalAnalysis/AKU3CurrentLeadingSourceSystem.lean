import AKU2ScalarSourceJetLift

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace Grad.FinitePhysicalJetLift
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearRange
open Grad.NonlinearQuotientBounds Grad.CartesianScalarElimination
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.Allocation Grad.GaugeCoefficients.Physical.Frame
open Grad.GaugeCoefficients.Physical.Ledger Grad.NonlinearDivision

def quadraticScalarVectorProduct (vector : ComplexEuclidean 2) (scalar : QuadraticScalarCoefficients) :
    QuadraticPlanarCoefficients := fun index => scalar index • vector

def quadraticMappedDivergence (mapping : ComplexEuclidean 2 →L[ℂ] ComplexEuclidean 2) :
    QuadraticPlanarCoefficients →ₗ[ℂ] ComplexEuclidean 2 where
  toFun q := quadraticDivergenceCoefficients (quadraticValueMap mapping q)
  map_add' first second := by
    apply PiLp.ext
    intro component
    fin_cases component <;> simp [quadraticDivergenceCoefficients,quadraticValueMap,map_add] <;> ring
  map_smul' scalar q := by
    change quadraticDivergenceCoefficients (quadraticValueMap mapping (scalar • q)) =
      scalar • quadraticDivergenceCoefficients (quadraticValueMap mapping q)
    apply PiLp.ext
    intro component
    fin_cases component <;> simp [quadraticDivergenceCoefficients,quadraticValueMap,map_smul] <;> ring

/-- The forced part includes the original actual tilt term tau*c2. -/
def leadingForcedPlanarCoefficients (force : QuadraticPlanarCoefficients)
    (tilt : ComplexEuclidean 2) (toroidal : QuadraticScalarCoefficients) : QuadraticPlanarCoefficients :=
  -quadraticPlanarInverse force - quadraticScalarVectorProduct tilt toroidal

def leadingCubicTarget (length determinant : ℂ)
    (mapping : ComplexEuclidean 2 →L[ℂ] ComplexEuclidean 2)
    (force : QuadraticPlanarCoefficients) (divergence tilt : ComplexEuclidean 2)
    (toroidal : QuadraticScalarCoefficients) : ComplexEuclidean 2 :=
  -(length * determinant)⁻¹ • divergence -
    quadraticMappedDivergence mapping (leadingForcedPlanarCoefficients force tilt toroidal)

def originalLeadingCubicLinear (parameters : PhaseParameters) (length epsilon : ℝ)
    (field : ACore parameters 3) (grade : ℕ) (angle : ℝ)
    (force : QuadraticPlanarCoefficients) (divergence : ComplexEuclidean 2)
    (toroidal : QuadraticScalarCoefficients) : ComplexEuclidean 2 :=
  coefficientPhysicalValue (originalCubicInverseFamily parameters length epsilon field grade) angle closedOrigin
    (leadingCubicTarget length (originalAxisPlanarMatrix parameters length epsilon field angle).det
      (matrixOperator (originalAxisInverseGram parameters length epsilon field angle)) force divergence
      (originalAxisTilt parameters length epsilon field angle) toroidal)

def leadingPlanarLiftCoefficients (linear : ComplexEuclidean 2) (force : QuadraticPlanarCoefficients) :
    QuadraticPlanarCoefficients := cubicComplementVectorCoefficients linear - quadraticPlanarInverse force

theorem leadingPlanarLift_force (linear : ComplexEuclidean 2) (force : QuadraticPlanarCoefficients) :
    Grad.GaugeCoefficients.Physical.Compensated.gradientJet
        (cubicScalarJet (cubicComplementCoefficients linear)) -
      leadingPlanarJetOperator (quadraticPlanarJet (leadingPlanarLiftCoefficients linear force)) =
      quadraticPlanarJet force := by
  have identity : quadraticPlanarJet (leadingPlanarLiftCoefficients linear force) =
      cubicPlanarLift (cubicComplementCoefficients linear) + quadraticForceLift force := by
    rw [cubicPlanarLift,cubicComplementVector_is_inverse]
    change quadraticPlanarJetLinear (cubicComplementVectorCoefficients linear - quadraticPlanarInverse force) =
      quadraticPlanarJetLinear (cubicComplementVectorCoefficients linear) + quadraticPlanarJetLinear (-quadraticPlanarInverse force)
    rw [map_sub,map_neg,sub_eq_add_neg]
  rw [identity]
  exact cubicPlanarLift_forced_equation _ force

/-- Exact current degree-one determinant equation with the signed factor
-L*det A0. All source and tilt terms occur in the one cubic inverse input. -/
theorem originalLeadingCubic_divergence (parameters : PhaseParameters) (length rho epsilon : ℝ)
    (positive : 0 < length) (field : ACore parameters 3)
    (vanishes : ∀ cell, (field.val cell).value closedOrigin = 0)
    (low : physicalBudget parameters field rho epsilon 6 ≤ originalCubicLowRadius parameters length)
    (grade : ℕ) (angle : ℝ) (force : QuadraticPlanarCoefficients)
    (divergence : ComplexEuclidean 2) (toroidal : QuadraticScalarCoefficients) :
    (-((length : ℂ) * (originalAxisPlanarMatrix parameters length epsilon field angle).det)) •
      quadraticMappedDivergence
        (matrixOperator (originalAxisInverseGram parameters length epsilon field angle))
        (leadingPlanarLiftCoefficients
          (originalLeadingCubicLinear parameters length epsilon field grade angle force divergence toroidal) force -
            quadraticScalarVectorProduct (originalAxisTilt parameters length epsilon field angle) toroidal) = divergence := by
  let mapping := matrixOperator (originalAxisInverseGram parameters length epsilon field angle)
  let target := leadingCubicTarget length (originalAxisPlanarMatrix parameters length epsilon field angle).det
    mapping force divergence (originalAxisTilt parameters length epsilon field angle) toroidal
  have solved := congrArg (fun op : OperatorValue 2 2 => op target)
    (originalCubicInverseFamily_two_sided parameters length rho epsilon field vanishes low grade angle closedOrigin).1
  change cubicDeterminantOperator mapping
      (originalLeadingCubicLinear parameters length epsilon field grade angle force divergence toroidal) = target at solved
  have split : leadingPlanarLiftCoefficients
      (originalLeadingCubicLinear parameters length epsilon field grade angle force divergence toroidal) force -
        quadraticScalarVectorProduct (originalAxisTilt parameters length epsilon field angle) toroidal =
      cubicComplementVectorCoefficients
        (originalLeadingCubicLinear parameters length epsilon field grade angle force divergence toroidal) +
      leadingForcedPlanarCoefficients force (originalAxisTilt parameters length epsilon field angle) toroidal := by
    unfold leadingPlanarLiftCoefficients leadingForcedPlanarCoefficients
    abel
  rw [split,map_add]
  change _ • (cubicDeterminantOperator mapping
    (originalLeadingCubicLinear parameters length epsilon field grade angle force divergence toroidal) + _) = _
  rw [solved]
  change _ • ((-(length * (originalAxisPlanarMatrix parameters length epsilon field angle).det)⁻¹ • divergence - _) + _) = _
  rw [sub_add_cancel,smul_smul,neg_mul_neg,mul_inv_cancel₀,one_smul]
  exact mul_ne_zero (Complex.ofReal_ne_zero.mpr positive.ne')
    (isUnit_iff_ne_zero.mp (originalAxisPlanarMatrix_isUnit_det parameters length rho epsilon field vanishes
      (originalCubic_low_margin parameters length rho epsilon field low).1 angle))

end Grad.FinitePhysicalJetLift
