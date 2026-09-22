import AKDT23SignedAxisPreservation

noncomputable section
open Set
open scoped ContDiff

namespace Grad.PhysicalGeometry
open Grad.MainTarget Grad.PhysicalFamily
open Grad.PhysicalFamily.IntegerSampling Grad.PhysicalFamily.SampledSmoothFamily
open Grad.MainAssembly.SampledAxisBasics Grad.MainAssembly.PhysicalNormalHessian
open Grad.MainAssembly.SampledAxisChartData Grad.MainAssembly.PhysicalSimilarityRigidity
open Grad.MainAssembly.SampledPhysicalSimilarityRigidity

/-- The unchanged normalized normal-Hessian tensor is realized by the actual
physical pressure; its axis chart is derived in DT22. -/
theorem actual_prescribed_normal_shape (length : ℝ) (positive : 0 < length)
    (family : CellSolutionFamily length) (period : ℕ) (periodPositive : 0 < period)
    (epsilonIn : sampledEpsilon period ∈ Ioo (-family.epsilonZero) family.epsilonZero)
    (potential : ℝ) (parameter : Icc family.lower family.upper)
    (valid : IsConfiguration .smooth (sampledRepresentativeFamily length family period epsilonIn potential parameter))
    (injective : ∀ (point : Plane), ‖point‖ ≤ 1 → ∀ time : ℝ,
      Function.Injective (fderiv ℝ (sampledPositionCoordinateValue length family period parameter.val)
        (coordinateDirection point time)))
    (magnetic : Vec → Vec) (pressure : Vec → ℝ)
    (magneticSmooth : ContDiff ℝ ∞ magnetic) (pressureSmooth : ContDiff ℝ ∞ pressure)
    (same : ∀ argument,
      magnetic ((sampledRepresentativeFamily length family period epsilonIn potential parameter).position argument) =
        (sampledRepresentativeFamily length family period epsilonIn potential parameter).magnetic argument ∧
      pressure ((sampledRepresentativeFamily length family period epsilonIn potential parameter).position argument) =
        (sampledRepresentativeFamily length family period epsilonIn potential parameter).pressure argument) :
    HasPrescribedNormalShape (sampledRepresentativeFamily length family period epsilonIn potential parameter)
      ((period : ℝ) * length) family.rho (sampledAlphaAngle period family.alpha family.delta parameter.val) := by
  exact hasPrescribedNormalShape_of_sampledAxisChartSeedData _ _ _ _ _ _ _
    (mul_pos (Nat.cast_pos.mpr periodPositive) positive) (by linarith [family.rhoPositive])
    (by linarith [family.rhoSmall])
    (actual_axis_chart_data length family period epsilonIn potential parameter valid injective
      magnetic pressure magneticSmooth pressureSmooth same)

end Grad.PhysicalGeometry
