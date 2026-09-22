import GC18APGeneratorExt

noncomputable section

set_option maxHeartbeats 1000000

namespace Grad.GaugeCoefficients.Physical.RadialLedger

open Grad.ClosedJets Grad.CartesianState Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope

theorem apMultiplier_singleCoefficient_physical {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    {input output grade : ℕ} (large : 2 ≤ grade) (angle : ℝ) (shift : ℤ)
    (coefficient : SmoothOperatorJet input output) (field : apGrade L sigma gamma ell input grade) :
    apPhysicalValue admissible large angle
      (apMultiplier admissible (singleJetCoefficient L sigma gamma ell grade shift coefficient) field) =
      cMapAction (cMapCoefficient admissible grade input output angle (singleJetCoefficient L sigma gamma ell grade shift coefficient))
        (apPhysicalValue admissible large angle field) := by
  let first := (apPhysicalValue (dimension := output) admissible large angle).comp
    (apMultiplier admissible (singleJetCoefficient L sigma gamma ell grade shift coefficient))
  let second := (cMapAction
    (cMapCoefficient admissible grade input output angle (singleJetCoefficient L sigma gamma ell grade shift coefficient))).comp
      (apPhysicalValue (dimension := input) admissible large angle)
  have equality : first = second := apFiniteGenerator_ext L sigma gamma ell first second
    (fun inputCell core => apMultiplier_single_physical admissible large angle inputCell shift coefficient core)
  change first field = second field
  rw [equality]

/-- Literal full Fourier multiplication on the exact completed AP2 graph.
Both coefficient and data approximation are in their original norms. -/
theorem apMultiplier_physical {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    {input output grade : ℕ} (large : 2 ≤ grade) (angle : ℝ)
    (coefficient : Coefficient L sigma gamma ell grade input output) (field : apGrade L sigma gamma ell input grade) :
    apPhysicalValue admissible large angle (apMultiplier admissible coefficient field) =
      cMapAction (cMapCoefficient admissible grade input output angle coefficient)
        (apPhysicalValue admissible large angle field) := by
  let first : Coefficient L sigma gamma ell grade input output →L[ℂ] C(ClosedDisk, ComplexEuclidean output) :=
    (apPhysicalValue admissible large angle).comp
      ((ContinuousLinearMap.apply ℂ (apGrade L sigma gamma ell output grade) field).comp
        (apCompletedBilinear admissible input output grade))
  let second : Coefficient L sigma gamma ell grade input output →L[ℂ] C(ClosedDisk, ComplexEuclidean output) :=
    (ContinuousLinearMap.apply ℂ (C(ClosedDisk, ComplexEuclidean output)) (apPhysicalValue admissible large angle field)).comp
      ((cMapActionBilinear input output).comp (cMapCoefficient admissible grade input output angle))
  have equality : first = second := apCoefficientGenerator_ext L sigma gamma ell first second
    (fun shift core => apMultiplier_singleCoefficient_physical admissible large angle shift core field)
  change first coefficient = second coefficient
  rw [equality]

end Grad.GaugeCoefficients.Physical.RadialLedger
