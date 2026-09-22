import AED8SameReferenceInverse
import AAR27ExactPhysicalConsumer

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace Grad.AnnularTiltedReference
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.AnnularSourceGraph
open Grad.GaugeCoefficients.Physical.WeightedTrace
open Grad.AnnularVariational Grad.AnnularHighTilt Grad.AnnularReconstruction Grad.CircularHighRegularity

section Physical
variable (parameters : PhaseParameters) (lower length : ℝ) (positive : 0 < lower)
    (bounded : lower < 1) (lengthPositive : 0 < length)
    (widthHalf : parameters.gamma ≤ 1 / 2)
    (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * length))

/-- The same constructed tilted solution has the original physical value and
pressure weak derivatives. Pressure is reconstructed using the transformed
first source slot, with no derivative of that source assumed. -/
theorem annularTiltSolution_physical_weak (source : AnnularForcing lower) (incoming : AnnularBoundary)
    (mode : HighAnnularMode) :
    let physical := highEnergyUnweight lower length positive bounded.le
      (annularTiltVariationalSolution parameters lower length positive bounded lengthPositive widthHalf widthLength source incoming)
    let physicalSource := highForcingUnweight lower positive bounded.le source
    CollarWeakDerivative lower
      (annularPhysicalValue parameters lower length positive bounded.le mode physical)
      (annularPhysicalSlope parameters lower length positive bounded.le mode physical) ∧
    CollarWeakDerivative lower
      (annularPhysicalP parameters lower length positive lengthPositive widthHalf widthLength physical physicalSource.1 mode)
      (annularPhysicalPSlope parameters lower length positive lengthPositive widthHalf widthLength bounded.le physical physicalSource mode) := by
  dsimp only
  constructor
  · exact annularPhysicalValue_weak parameters lower length positive bounded.le mode _
  · rw [annularTiltSolution_same_reference]
    exact annularPhysicalP_weak parameters lower length positive lengthPositive widthHalf widthLength bounded
      (highForcingUnweight lower positive bounded.le source) (((lower ^ highTiltExponent : ℝ) : ℂ) • incoming) mode

/-- Full original retained equations, with the actual transformed sources. -/
theorem annularTiltSolution_physical_rows (source : AnnularForcing lower) (incoming : AnnularBoundary)
    (mode : HighAnnularMode) :
    let physical := highEnergyUnweight lower length positive bounded.le
      (annularTiltVariationalSolution parameters lower length positive bounded lengthPositive widthHalf widthLength source incoming)
    let physicalSource := highForcingUnweight lower positive bounded.le source
    (annularPhysicalSlope parameters lower length positive bounded.le mode physical +
      collarScalar 1 lower (annularRadialCurve lower positive)
        (annularPhysicalValue parameters lower length positive bounded.le mode physical) +
      annularDSymbol mode • annularPhysicalP parameters lower length positive lengthPositive widthHalf widthLength physical physicalSource.1 mode =
      annularDecodeMode parameters lower positive mode (physicalSource.1 mode)) ∧
    (annularPhysicalPSlope parameters lower length positive lengthPositive widthHalf widthLength bounded.le physical physicalSource mode -
      collarScalar 1 lower (annularInverseRadiusCurve lower positive)
        (annularPhysicalP parameters lower length positive lengthPositive widthHalf widthLength physical physicalSource.1 mode) -
      Complex.I • collarScalar 1 lower (annularSecondRealCurve lower length positive mode)
        (annularPhysicalValue parameters lower length positive bounded.le mode physical) =
      annularDecodeMode parameters lower positive mode (physicalSource.2.1 mode) +
        (((mode.val.2 : ℝ) / ((mode.val.1 : ℝ) * length) : ℝ) : ℂ) •
          annularDecodeMode parameters lower positive mode (physicalSource.2.2.1 mode)) := by
  constructor
  · exact annularPhysical_first_row parameters lower length positive lengthPositive widthHalf widthLength bounded.le _ _ mode
  · exact annularOriginal_second_row parameters lower length positive bounded.le lengthPositive widthHalf widthLength _ _ mode

/-- Immediate consumer retaining all accepted genuine sections, both physical
boundary laws and equations for the same inverse identified above. -/
theorem annularTiltReference_physical_consumer (source : AnnularForcing lower) (incoming : AnnularBoundary) :
    highEnergyUnweight lower length positive bounded.le
      (annularTiltVariationalSolution parameters lower length positive bounded lengthPositive widthHalf widthLength source incoming) =
      annularVariationalSolution parameters lower length positive bounded lengthPositive widthHalf widthLength
        (highForcingUnweight lower positive bounded.le source) (((lower ^ highTiltExponent : ℝ) : ℂ) • incoming) ∧
    ActualAnnularPhysicalLaws parameters lower length positive bounded lengthPositive widthHalf widthLength
      (highForcingUnweight lower positive bounded.le source) (((lower ^ highTiltExponent : ℝ) : ℂ) • incoming) :=
  ⟨annularTiltSolution_same_reference parameters lower length positive bounded lengthPositive widthHalf widthLength source incoming,
    actualAnnularPhysicalConsumer parameters lower length positive bounded lengthPositive widthHalf widthLength _ _⟩

end Physical
end Grad.AnnularTiltedReference
