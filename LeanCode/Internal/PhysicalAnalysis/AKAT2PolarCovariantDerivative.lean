import AKAT1LiteralRadialForceContraction

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open Set Filter
open scoped ContDiff BigOperators
namespace Grad.ActualCartesianEquations
open Grad.ClosedJets Grad.CartesianState Grad.ActualSmoothPhysicalField
open Grad.GaugeCoefficients.Physical.Ledger Grad.Constraints

/-- The literal infinitesimal rotation acts only on the two planar coordinates. -/
def polarQuarter (value : ComplexEuclidean 3) : ComplexEuclidean 3 :=
  WithLp.toLp 2 ![-value 1,value 0,0]

private def planarProjection : ComplexEuclidean 3 →L[ℂ] ComplexEuclidean 3 :=
  matrixUnit 0 0 + matrixUnit 1 1
private def quarterProjection : ComplexEuclidean 3 →L[ℂ] ComplexEuclidean 3 :=
  matrixUnit 1 0 - matrixUnit 0 1
private def toroidalProjection : ComplexEuclidean 3 →L[ℂ] ComplexEuclidean 3 := matrixUnit 2 2

private theorem cartesianCovariantValue_linearForm (angle : ℝ) (value : ComplexEuclidean 3) :
    cartesianCovariantValue angle value = (Real.cos angle : ℂ) • planarProjection value +
      (Real.sin angle : ℂ) • quarterProjection value + toroidalProjection value := by
  rw [cartesianCovariantValue_apply]
  apply PiLp.ext
  intro component
  fin_cases component <;> simp [planarProjection,quarterProjection,toroidalProjection,
    matrixUnit_apply,operatorBasis]
  all_goals ring

/-- Genuine differentiation of Q(theta)a(theta), retaining the derivative
of the polar frame itself. -/
theorem cartesianCovariantValue_hasDerivAt (field : ℝ → ComplexEuclidean 3)
    (slope : ComplexEuclidean 3) (angle : ℝ) (derivative : HasDerivAt field slope angle) :
    HasDerivAt (fun query => cartesianCovariantValue query (field query))
      (cartesianCovariantValue angle (slope + polarQuarter (field angle))) angle := by
  have cosDerivative : HasDerivAt (fun query : ℝ => (Real.cos query : ℂ)) (-((Real.sin angle : ℝ) : ℂ)) angle := by
    simpa only [Function.comp_def, Complex.ofRealCLM_apply, Complex.ofReal_neg] using
      Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt angle (Real.hasDerivAt_cos angle)
  have sinDerivative : HasDerivAt (fun query : ℝ => (Real.sin query : ℂ)) (Real.cos angle : ℂ) angle :=
    Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt angle (Real.hasDerivAt_sin angle)
  have planar := planarProjection.restrictScalars ℝ |>.hasFDerivAt.comp_hasDerivAt angle derivative
  have quarter := quarterProjection.restrictScalars ℝ |>.hasFDerivAt.comp_hasDerivAt angle derivative
  have toroidal := toroidalProjection.restrictScalars ℝ |>.hasFDerivAt.comp_hasDerivAt angle derivative
  have law := ((cosDerivative.smul planar).add (sinDerivative.smul quarter)).add toroidal
  have source : (fun query => (Real.cos query : ℂ) • planarProjection (field query) +
      (Real.sin query : ℂ) • quarterProjection (field query) + toroidalProjection (field query)) =
      fun query => cartesianCovariantValue query (field query) :=
    funext (fun query => (cartesianCovariantValue_linearForm query (field query)).symm)
  change HasDerivAt (fun query => (Real.cos query : ℂ) • planarProjection (field query) +
      (Real.sin query : ℂ) • quarterProjection (field query) + toroidalProjection (field query)) _ angle at law
  rw [source] at law
  convert law using 1
  rw [cartesianCovariantValue_apply]
  apply PiLp.ext
  intro component
  fin_cases component <;> simp [polarQuarter,planarProjection,quarterProjection,toroidalProjection,
    matrixUnit_apply,operatorBasis]
  all_goals ring

end Grad.ActualCartesianEquations
