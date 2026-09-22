import AKQ10NormalizedChartAxisColumns

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace Grad.FinitePhysicalJetLift
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.SourceCollar Grad.SourceCollarCoefficients
open Grad.NonlinearQuotientBounds Grad.NonlinearRange Grad.AxisSplit Grad.ChartAxisSplit
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical Grad.GaugeCoefficients.Physical.Frame
open Grad.GaugeCoefficients.Physical.Allocation Grad.GaugeCoefficients.Physical.Ledger Grad.NonlinearDivision

/-- The literal A0=aM of the current normalized chart. -/
def normalizedAxisPlanarMatrix {parameters : PhaseParameters} (seed : Seed.Parameters)
    (state : ChartState parameters) (angle : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  coefficientValue (rootChart state.1) angle •
    operatorMatrix (harmonicSeedOperator (seed 0) (seed 1) (seed 2) (seed 3) angle)

theorem operatorMatrix_single {input output : ℕ} (mapping : OperatorValue input output)
    (row : Fin output) (column : Fin input) :
    operatorMatrix mapping row column = mapping (EuclideanSpace.single column 1) row := by
  have basis : (WithLp.toLp 2 (fun index : Fin input => if index = column then (1 : ℂ) else 0)) =
      EuclideanSpace.single column 1 := by
    apply PiLp.ext
    intro index
    simp [eq_comm]
  exact congrArg (fun value : ComplexEuclidean input => mapping value row) basis

theorem normalizedAxisPlanarMatrix_actual (parameters : PhaseParameters) (length epsilon : ℝ)
    (seed : Seed.Parameters) (inside : seed ∈ Seed.parameterDomain) (state : ChartState parameters)
    (zeroJets : ∀ cell, ZeroCartesianFirstJets (state.2.1.val cell)) (angle : ℝ) :
    originalAxisPlanarMatrix parameters length epsilon (normalizedChartDisplacement parameters seed inside state) angle =
      normalizedAxisPlanarMatrix seed state angle := by
  have column := normalizedChartDisplacement_planarColumn parameters length epsilon seed inside state zeroJets angle
  ext row index
  fin_cases row <;> fin_cases index
  · simpa [originalAxisPlanarMatrix,normalizedAxisPlanarMatrix,operatorMatrix_single,
      tamePlanarInclusion,tameTangentInclusion] using column 0 0
  · simpa [originalAxisPlanarMatrix,normalizedAxisPlanarMatrix,operatorMatrix_single,
      tamePlanarInclusion,tameTangentInclusion] using column 1 0
  · simpa [originalAxisPlanarMatrix,normalizedAxisPlanarMatrix,operatorMatrix_single,
      tamePlanarInclusion,tameTangentInclusion] using column 0 2
  · simpa [originalAxisPlanarMatrix,normalizedAxisPlanarMatrix,operatorMatrix_single,
      tamePlanarInclusion,tameTangentInclusion] using column 1 2

theorem normalizedAxisTilt_actual (parameters : PhaseParameters) (length epsilon : ℝ)
    (seed : Seed.Parameters) (inside : seed ∈ Seed.parameterDomain) (state : ChartState parameters)
    (zeroJets : ∀ cell, ZeroCartesianFirstJets (state.2.1.val cell)) (angle : ℝ) :
    originalAxisTilt parameters length epsilon (normalizedChartDisplacement parameters seed inside state) angle =
      planarValue state.1 angle := by
  have column := normalizedChartDisplacement_planarColumn parameters length epsilon seed inside state zeroJets angle
  apply PiLp.ext
  intro coordinate
  fin_cases coordinate
  · simpa [originalAxisTilt,tamePlanarInclusion,tameTangentInclusion] using column 0 1
  · simpa [originalAxisTilt,tamePlanarInclusion,tameTangentInclusion] using column 1 1

/-- Literal current-axis AM26 for the original physical frame on its
accepted low ball. No new invertibility or small-matrix premise is inserted. -/
theorem normalizedChart_signedAxisCofactor (parameters : PhaseParameters) (length rho epsilon : ℝ)
    (seed : Seed.Parameters) (inside : seed ∈ Seed.parameterDomain) (state : ChartState parameters)
    (zeroJets : ∀ cell, ZeroCartesianFirstJets (state.2.1.val cell))
    (low : physicalBudget parameters (normalizedChartDisplacement parameters seed inside state) rho epsilon 6 ≤
      originalCoefficientLowRadius parameters length) (angle : ℝ) :
    originalPhysicalSignedCofactor parameters length epsilon
      (normalizedChartDisplacement parameters seed inside state) angle closedOrigin =
      (-(normalizedAxisPlanarMatrix seed state angle).det) •
        tiltedAxisGram (((normalizedAxisPlanarMatrix seed state angle).transpose *
          normalizedAxisPlanarMatrix seed state angle)⁻¹) (planarValue state.1 angle) := by
  rw [originalAxis_signedCofactor parameters length rho epsilon _
    (normalizedChartDisplacement_axis_zero parameters seed inside state zeroJets) low]
  simp only [originalAxisInverseGram,normalizedAxisPlanarMatrix_actual parameters length epsilon seed inside state zeroJets,
    normalizedAxisTilt_actual parameters length epsilon seed inside state zeroJets]

/-- The constant matrix entering D_K is exactly (A0ᵀA0)^−1 of this same
original chart. Its action on cubic fields is the genuine divergence from AKQ7. -/
def normalizedAxisCubicOperator {parameters : PhaseParameters} (seed : Seed.Parameters)
    (state : ChartState parameters) (angle : ℝ) : ComplexEuclidean 2 →L[ℂ] ComplexEuclidean 2 :=
  cubicDeterminantOperator (matrixOperator (((normalizedAxisPlanarMatrix seed state angle).transpose *
    normalizedAxisPlanarMatrix seed state angle)⁻¹))

theorem normalizedAxisCubicOperator_actual {parameters : PhaseParameters} (seed : Seed.Parameters)
    (state : ChartState parameters) (angle : ℝ) (linear : ComplexEuclidean 2) (point : ClosedDisk) :
    (Grad.CartesianScalarElimination.vectorDivJet
      (valueMapJet (matrixOperator (((normalizedAxisPlanarMatrix seed state angle).transpose *
        normalizedAxisPlanarMatrix seed state angle)⁻¹))
        (cubicPlanarLift (cubicComplementCoefficients linear)))).value point 0 =
      (point.val 0 : ℂ) * normalizedAxisCubicOperator seed state angle linear 0 +
        (point.val 1 : ℂ) * normalizedAxisCubicOperator seed state angle linear 1 :=
  cubicDeterminantOperator_actual _ _ _

end Grad.FinitePhysicalJetLift
