import AKU41ActualAxisCurrentProducts

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace Grad.FinitePhysicalJetLift
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearQuotientBounds
open Grad.AxisSplit Grad.AxisJet Grad.NonlinearRange Grad.NonlinearProduct
open Grad.SourceCollar Grad.SourceCollarCoefficients
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Physical.Frame
open Grad.GaugeCoefficients.Physical.Ledger Grad.NonlinearDivision

theorem matrixOperator_comp_apply {input middle output : ℕ}
    (outer : Matrix (Fin output) (Fin middle) ℂ) (inner : Matrix (Fin middle) (Fin input) ℂ)
    (value : ComplexEuclidean input) :
    matrixOperator outer (matrixOperator inner value) = matrixOperator (outer * inner) value := by
  have maps : (matrixOperator outer).comp (matrixOperator inner) = matrixOperator (outer*inner) := by
    apply operatorMatrix_injective
    rw [operatorMatrix_comp,operatorMatrix_matrixOperator,operatorMatrix_matrixOperator,operatorMatrix_matrixOperator]
  exact congrArg (fun map => map value) maps

theorem matrixOperator_one_apply {dimension : ℕ} (value : ComplexEuclidean dimension) :
    matrixOperator (1 : Matrix (Fin dimension) (Fin dimension) ℂ) value = value := by
  have maps : matrixOperator (1 : Matrix (Fin dimension) (Fin dimension) ℂ) =
      ContinuousLinearMap.id ℂ (ComplexEuclidean dimension) := by
    apply operatorMatrix_injective
    rw [operatorMatrix_matrixOperator,operatorMatrix_one]
  rw [maps,ContinuousLinearMap.id_apply]

theorem fullColumn_dot_inverseTranspose (frame inverse : Matrix (Fin 3) (Fin 3) ℂ)
    (law : inverse * frame = 1) (value : ComplexEuclidean 3) (column : Fin 3) :
    Grad.NonlinearQuotient.complexDot (WithLp.toLp 2 (fun row => frame row column))
      (matrixOperator inverse.transpose value) = value column := by
  have dot (vector : ComplexEuclidean 3) :
      Grad.NonlinearQuotient.complexDot (WithLp.toLp 2 (fun row => frame row column)) vector =
        matrixOperator frame.transpose vector column := by
    rw [threeColumnOperator_apply,operatorMatrix_matrixOperator]
    simp [Grad.NonlinearQuotient.complexDot,Fin.sum_univ_three]
  rw [dot,matrixOperator_comp_apply,← Matrix.transpose_mul,law,Matrix.transpose_one,matrixOperator_one_apply]

/-- Planar derivatives of the SAME total field are the first two columns
of the original frame formed from its displacement. -/
theorem originalTotalFirstJet_frame (parameters : PhaseParameters) (length epsilon : ℝ)
    (field : ACore parameters 3) (direction : Fin 2) (angle : ℝ) :
    axisPhysicalValue (traceFirst direction (planarReferenceCore parameters + field)) angle =
      WithLp.toLp 2 (fun row =>
        originalPhysicalFrameMatrix parameters length epsilon field angle closedOrigin row direction.castSucc) := by
  rw [traceFirst_physical,map_add,coreValue_add,planarReferenceCore,partialCore_valueMap,
    coreValue_valueMap]
  have coordinate : coreValue (partialCore parameters direction (tamePlanarCoordinateField parameters)) closedOrigin angle =
      EuclideanSpace.single direction 1 := axisDerivative_tamePlanarCoordinate direction angle
  rw [coordinate]
  apply PiLp.ext
  intro row
  exact (originalFrame_planarColumn parameters length epsilon field closedOrigin angle direction row).symm

end Grad.FinitePhysicalJetLift
