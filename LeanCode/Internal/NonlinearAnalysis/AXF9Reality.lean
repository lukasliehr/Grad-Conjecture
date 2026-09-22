import AXF8ProjectionBound

noncomputable section

set_option maxRecDepth 3000
set_option maxHeartbeats 500000

namespace Grad.FlatSourceProjection

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.AxisSplit Grad.AxisJet
open Grad.NonlinearQuotientBounds Grad.QuotientProjection Grad.AxisCore Grad.CompletedReality

variable {parameters : PhaseParameters}

theorem radialValueInsertion_conjugate {dimension : ℕ} (data : AxisSmoothCore parameters dimension) :
    cartesianCoreConjugation parameters (radialValueInsertion data) =
      radialValueInsertion (axisCoreInvolution parameters dimension data) := by
  change cartesianCoreConjugation parameters (angularCore parameters 0 (insertZero data)) = _
  rw [angularCore_conjugate, neg_zero, insertZero_conjugate]
  rfl

theorem nonlinearCoordinateCore_conjugate {dimension : ℕ} (coordinate : Fin 2)
    (field : ACore parameters dimension) :
    cartesianCoreConjugation parameters (Grad.NonlinearQuotientBounds.coordinateCore parameters coordinate field) =
      Grad.NonlinearQuotientBounds.coordinateCore parameters coordinate (cartesianCoreConjugation parameters field) := by
  apply Subtype.ext
  funext cell
  apply closedJet_eq_of_value_eq
  apply ContinuousMap.ext
  intro point
  change cartesianPhysicalConjugation dimension (point.val coordinate • ((field.val (-cell)).value point)) =
    point.val coordinate • cartesianPhysicalConjugation dimension ((field.val (-cell)).value point)
  exact (cartesianPhysicalConjugation dimension).map_smul _ _

theorem radialFirstInsertion_conjugate {dimension : ℕ} (coordinate : Fin 2)
    (data : AxisSmoothCore parameters dimension) :
    cartesianCoreConjugation parameters (radialFirstInsertion coordinate data) =
      radialFirstInsertion coordinate (axisCoreInvolution parameters dimension data) := by
  change cartesianCoreConjugation parameters
    (Grad.NonlinearQuotientBounds.coordinateCore parameters coordinate (radialValueInsertion data)) = _
  rw [nonlinearCoordinateCore_conjugate, radialValueInsertion_conjugate]
  rfl

theorem scalarGradientCorrection_conjugate (field : ACore parameters 1) :
    cartesianCoreConjugation parameters (scalarGradientCorrection field) =
      scalarGradientCorrection (cartesianCoreConjugation parameters field) := by
  simp only [scalarGradientCorrection_apply, map_add, radialFirstInsertion_conjugate,
    traceFirst_conjugate]

theorem valueCorrection_conjugate (source : SmoothQuotient parameters) :
    zCoreConjugation parameters (valueCorrection source) = valueCorrection (zCoreConjugation parameters source) := by
  funext coordinate
  fin_cases coordinate
  · change cartesianCoreConjugation parameters (radialValueInsertion (traceZero (source 1))) =
      radialValueInsertion (traceZero (cartesianCoreConjugation parameters (source 1)))
    rw [radialValueInsertion_conjugate, traceZero_conjugate]
  · change cartesianCoreConjugation parameters (radialValueInsertion (traceZero (source 0))) =
      radialValueInsertion (traceZero (cartesianCoreConjugation parameters (source 0)))
    rw [radialValueInsertion_conjugate, traceZero_conjugate]
  · exact map_zero (cartesianCoreConjugation parameters)
  · exact map_zero (cartesianCoreConjugation parameters)

theorem radialAffineInsertion_conjugate (data : AxisSmoothCore parameters 1) :
    zCoreConjugation parameters (radialAffineInsertion data) =
      radialAffineInsertion (axisCoreInvolution parameters 1 data) := by
  funext coordinate
  fin_cases coordinate
  · change cartesianCoreConjugation parameters
        ((-Complex.I) • (radialFirstInsertion 0 data - Complex.I • radialFirstInsertion 1 data)) =
      Complex.I • (radialFirstInsertion 0 (axisCoreInvolution parameters 1 data) +
        Complex.I • radialFirstInsertion 1 (axisCoreInvolution parameters 1 data))
    simp only [coreConjugation_complex_smul, map_sub, radialFirstInsertion_conjugate]
    norm_num
    module
  · change cartesianCoreConjugation parameters
        (Complex.I • (radialFirstInsertion 0 data + Complex.I • radialFirstInsertion 1 data)) =
      (-Complex.I) • (radialFirstInsertion 0 (axisCoreInvolution parameters 1 data) -
        Complex.I • radialFirstInsertion 1 (axisCoreInvolution parameters 1 data))
    simp only [coreConjugation_complex_smul, map_add, radialFirstInsertion_conjugate]
    norm_num
    module
  · exact map_zero (cartesianCoreConjugation parameters)
  · exact map_zero (cartesianCoreConjugation parameters)

theorem fourthCorrection_conjugate (source : SmoothQuotient parameters) :
    zCoreConjugation parameters (fourthCorrection source) = fourthCorrection (zCoreConjugation parameters source) := by
  funext coordinate
  fin_cases coordinate
  · exact map_zero (cartesianCoreConjugation parameters)
  · exact map_zero (cartesianCoreConjugation parameters)
  · exact map_zero (cartesianCoreConjugation parameters)
  · change cartesianCoreConjugation parameters
      (scalarGradientCorrection (source 3 - angularCore parameters 0 (source 3))) =
      scalarGradientCorrection (cartesianCoreConjugation parameters (source 3) -
        angularCore parameters 0 (cartesianCoreConjugation parameters (source 3)))
    rw [scalarGradientCorrection_conjugate, map_sub, angularCore_conjugate, neg_zero]

theorem meanPair_conjugate (source : SmoothQuotient parameters) :
    zCoreConjugation parameters (meanPair parameters source) = meanPair parameters (zCoreConjugation parameters source) := by
  change zCoreConjugation parameters (removeMean parameters 2 (removeMean parameters 3 source)) = _
  rw [← removeMean_conjugate parameters _ 2 (by decide), ← removeMean_conjugate parameters _ 3 (by decide)]
  rfl

theorem flatSourceProjection_conjugate (source : SmoothQuotient parameters) :
    zCoreConjugation parameters (flatSourceProjection source) = flatSourceProjection (zCoreConjugation parameters source) := by
  rw [flatSourceProjection_apply, map_sub, map_sub, map_sub, map_sub,
    meanPair_conjugate, ← modeProjection_conjugate, valueCorrection_conjugate,
    radialAffineInsertion_conjugate, fourthCorrection_conjugate, map_sub,
    ← modeProjection_conjugate, ← affineTrace_conjugate, flatSourceProjection_apply]

end Grad.FlatSourceProjection
