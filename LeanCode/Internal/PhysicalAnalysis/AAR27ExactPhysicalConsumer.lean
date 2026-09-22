import AAR25OriginalSecondRow
import AAR26OriginalInnerBoundary
import AAG21ExactVariationalConsumer

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal
namespace Grad.AnnularReconstruction
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularVariational Grad.AnnularSourceGraph Grad.CircularHighRegularity Grad.PhaseAlgebra
open Grad.GaugeCoefficients.Physical.WeightedTrace

section Consumer
variable (parameters : PhaseParameters) (lower length : ℝ)
    (positive : 0 < lower) (bounded : lower < 1) (lengthPositive : 0 < length)
    (widthHalf : parameters.gamma ≤ 1 / 2)
    (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * length))

/-- Exact original physical retained system for the actual annular inverse.
All fields, derivatives and continuous representatives refer to this same
solution; no derivative or trace of the bulk forcing is assumed. -/
structure ActualAnnularPhysicalLaws (source : AnnularForcing lower) (innerValue : AnnularBoundary) : Prop where
  valueWeak : ∀ mode : HighAnnularMode,
    let field := annularVariationalSolution parameters lower length positive bounded lengthPositive widthHalf widthLength source innerValue
    CollarWeakDerivative lower
      (annularPhysicalValue parameters lower length positive bounded.le mode field)
      (annularPhysicalSlope parameters lower length positive bounded.le mode field)
  pressureWeak : ∀ mode : HighAnnularMode,
    let field := annularVariationalSolution parameters lower length positive bounded lengthPositive widthHalf widthLength source innerValue
    CollarWeakDerivative lower
      (annularPhysicalP parameters lower length positive lengthPositive widthHalf widthLength field source.1 mode)
      (annularPhysicalPSlope parameters lower length positive lengthPositive widthHalf widthLength bounded.le field source mode)
  valueRepresentation : ∀ mode : HighAnnularMode,
    let field := annularVariationalSolution parameters lower length positive bounded lengthPositive widthHalf widthLength source innerValue
    radialSectionL2 1 lower positive bounded.le
      (annularPhysicalValueSection parameters lower length positive bounded mode field) =
      annularPhysicalValue parameters lower length positive bounded.le mode field
  pressureRepresentation : ∀ mode : HighAnnularMode,
    let field := annularVariationalSolution parameters lower length positive bounded lengthPositive widthHalf widthLength source innerValue
    radialSectionL2 1 lower positive bounded.le
      (annularPhysicalPSection parameters lower length positive bounded lengthPositive widthHalf widthLength source innerValue mode) =
      annularPhysicalP parameters lower length positive lengthPositive widthHalf widthLength field source.1 mode
  firstRow : ∀ mode : HighAnnularMode,
    let field := annularVariationalSolution parameters lower length positive bounded lengthPositive widthHalf widthLength source innerValue
    annularPhysicalSlope parameters lower length positive bounded.le mode field +
      collarScalar 1 lower (annularRadialCurve lower positive)
        (annularPhysicalValue parameters lower length positive bounded.le mode field) +
      annularDSymbol mode • annularPhysicalP parameters lower length positive lengthPositive widthHalf widthLength field source.1 mode =
      annularDecodeMode parameters lower positive mode (source.1 mode)
  secondRow : ∀ mode : HighAnnularMode,
    let field := annularVariationalSolution parameters lower length positive bounded lengthPositive widthHalf widthLength source innerValue
    annularPhysicalPSlope parameters lower length positive lengthPositive widthHalf widthLength bounded.le field source mode -
      collarScalar 1 lower (annularInverseRadiusCurve lower positive)
        (annularPhysicalP parameters lower length positive lengthPositive widthHalf widthLength field source.1 mode) -
      Complex.I • collarScalar 1 lower (annularSecondRealCurve lower length positive mode)
        (annularPhysicalValue parameters lower length positive bounded.le mode field) =
      annularDecodeMode parameters lower positive mode (source.2.1 mode) +
        (((mode.val.2 : ℝ) / ((mode.val.1 : ℝ) * length) : ℝ) : ℂ) •
          annularDecodeMode parameters lower positive mode (source.2.2.1 mode)
  innerBoundary : ∀ mode : HighAnnularMode,
    annularPhysicalValueSection parameters lower length positive bounded mode
      (annularVariationalSolution parameters lower length positive bounded lengthPositive widthHalf widthLength source innerValue)
      ⟨lower, le_rfl, bounded.le⟩ = annularInnerDatum parameters lower mode (innerValue mode)
  outerBoundary : ∀ mode : HighAnnularMode,
    annularPhysicalPSection parameters lower length positive bounded lengthPositive widthHalf widthLength source innerValue mode
      ⟨1, bounded.le, le_rfl⟩ = annularOuterDatum parameters mode (source.2.2.2 mode)
  physicalBound :
    ‖annularVariationalSolution parameters lower length positive bounded lengthPositive widthHalf widthLength source innerValue‖ ≤
      annularInnerLiftConstant lower length * ‖innerValue‖ +
        (4 / 3 : ℝ) * (3 * ‖source.1‖ + ‖source.2.1‖ + ‖source.2.2.1‖ +
          annularTraceConstant lower length * ‖source.2.2.2‖ +
          4 * annularInnerLiftConstant lower length * ‖innerValue‖)

theorem actualAnnularPhysicalConsumer (source : AnnularForcing lower) (innerValue : AnnularBoundary) :
    ActualAnnularPhysicalLaws parameters lower length positive bounded lengthPositive widthHalf widthLength source innerValue := by
  constructor
  · intro mode
    exact annularPhysicalValue_weak parameters lower length positive bounded.le mode _
  · exact annularPhysicalP_weak parameters lower length positive lengthPositive widthHalf widthLength bounded source innerValue
  · intro mode
    exact annularPhysicalValueSection_bulk parameters lower length positive bounded mode _
  · exact annularPhysicalPSection_bulk parameters lower length positive bounded lengthPositive widthHalf widthLength source innerValue
  · intro mode
    exact annularPhysical_first_row parameters lower length positive lengthPositive widthHalf widthLength bounded.le _ source.1 mode
  · intro mode
    exact annularOriginal_second_row parameters lower length positive bounded.le lengthPositive widthHalf widthLength _ source mode
  · exact annularPhysicalValueSection_inner parameters lower length positive bounded lengthPositive widthHalf widthLength source innerValue
  · exact annularPhysicalPSection_outer parameters lower length positive bounded lengthPositive widthHalf widthLength source innerValue
  · exact annularVariationalSolution_bound parameters lower length positive bounded lengthPositive widthHalf widthLength source innerValue

end Consumer
end Grad.AnnularReconstruction
