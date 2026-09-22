import AKCA21LiteralScalarOriginalCore
import AKBD2ProjectedParameterCalculus

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set
namespace Grad.OriginalCoreRealization
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarCoefficients Grad.SourceBoundaryTrace
open Grad.ActualPhysicalField Grad.ActualSmoothPhysicalField Grad.SourceCollarFullSource Grad.BoundaryTrace
open Grad.ActualDeterminantEquations Grad.GaugeCoefficients.Physical.Ledger

/-- The polynomial Cartesian contraction `(Jy) · a_C`, with its scalar value carrier. -/
def scalarTangentialPolynomial (point : SpatialPlane) (value : ComplexEuclidean 3) : ComplexEuclidean 1 :=
  (point 0 : ℂ) • matrixUnit (0 : Fin 1) (1 : Fin 3) value -
    (point 1 : ℂ) • matrixUnit (0 : Fin 1) (0 : Fin 3) value

 theorem scalarTangentialPolynomial_polar (radius angle : ℝ) (value : ComplexEuclidean 3) :
    scalarTangentialPolynomial (polarPlane (radius,angle)) (cartesianCovariantValue angle value)=
      radius • matrixUnit (0 : Fin 1) (1 : Fin 3) value := by
  apply PiLp.ext
  intro component
  fin_cases component
  simp only [scalarTangentialPolynomial,PiLp.sub_apply,PiLp.smul_apply,matrixUnit_apply]
  have basis : (operatorBasis (0 : Fin 1)) 0=(1 : ℂ) := rfl
  change (polarPlane (radius,angle) 0 : ℂ) • (cartesianCovariantValue angle value 1 • (operatorBasis (0 : Fin 1)) 0) -
    (polarPlane (radius,angle) 1 : ℂ) • (cartesianCovariantValue angle value 0 • (operatorBasis (0 : Fin 1)) 0)=
    radius • (value 1 • (operatorBasis (0 : Fin 1)) 0)
  rw [basis]
  simp only [smul_eq_mul,mul_one]
  have first : polarPlane (radius,angle) 0=radius * Real.cos angle := by simp [polarPlane,collarPlane]
  have second : polarPlane (radius,angle) 1=radius * Real.sin angle := by simp [polarPlane,collarPlane]
  rw [first,second]
  change (((radius * Real.cos angle : ℝ) : ℂ) * cartesianCovariantValue angle value 1 -
    ((radius * Real.sin angle : ℝ) : ℂ) * cartesianCovariantValue angle value 0) = (radius : ℂ) * value 1
  simp only [Complex.ofReal_mul]
  linear_combination (radius : ℂ) * cartesianCovariantValue_tangential angle value

/-- Literal original scalar recovery from Xi and the polynomial Cartesian covariant contraction. -/
 theorem correctedScalar_cartesianPolynomial {parameters : PhaseParameters} {lower : ℝ} {positive : 0 < lower}
    {xi : DivisionRow 1 lower} {polar : DivisionRow 3 lower}
    (scalar : SmoothLowPhysicalRow parameters lower positive xi)
    (covariant : SmoothLowPhysicalRow parameters lower positive polar) (bounded : lower<1)
    (radius : ℝ) (inside : radius ∈ Icc lower 1) (angles : ℝ×ℝ) :
    radius • (scalar.polarScalarOverRadius covariant).fullField bounded (radius,angles)=
      radius • scalar.fullField bounded (radius,angles) +
        removePolarMean (fun query => scalarTangentialPolynomial (polarPlane (radius,query.1))
          (cartesianCovariantValue query.1 (covariant.fullField bounded (radius,query)))) angles := by
  simp_rw [scalarTangentialPolynomial_polar]
  rw [scalar.fullField_polarScalarOverRadius bounded covariant radius inside angles,smul_add]
  congr 1
  simpa only [Complex.coe_smul] using
    (congrFun (removePolarMean_smul (radius : ℂ)
      (fun query => matrixUnit (0 : Fin 1) (1 : Fin 3) (covariant.fullField bounded (radius,query)))) angles).symm

end Grad.OriginalCoreRealization
