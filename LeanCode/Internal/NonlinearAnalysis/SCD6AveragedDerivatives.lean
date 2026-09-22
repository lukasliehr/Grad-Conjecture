import SCD5PaidGrades
import ProductWeightedInputs

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators

namespace Grad.SourceCollarDivision

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearRadial Grad.BoundaryTrace
open Grad.NonlinearProduct

theorem globalClosedJet_higherDerivative {dimension order : ℕ}
    (field : SpatialPlane → ComplexEuclidean dimension) (smooth : ContDiff ℝ ∞ field)
    (point : ClosedDisk) :
    iteratedFDeriv ℝ order field point.val =
      closedPlaneHigherDerivative (globalClosedJet field smooth) point.val := by
  apply continuousMultilinearMap_ext_spatialPlaneBasis
  intro word
  rw [closedPlaneHigherDerivative_basis, ambientClosedDisk_coe,
    globalClosedJet_derivative]
  rfl

theorem averagedPartial_word_paid {dimension grade order power : ℕ}
    (parameters : PhaseParameters) (cell : ℤ) (field : ClosedJet dimension)
    (coordinate : Fin 2) (word : CartesianWord order)
    (paid : order + power + 3 ≤ grade) (point : ClosedDisk) :
    cellFrequency cell ^ power *
      ‖cartesianDerivative order word
        (rayAverageValue (shiftedClosedJet (phaseWeightedJet parameters cell field)
          (fun _ : Fin 1 => coordinate))) point.val‖ ≤
      (6 * diskSupConstant) * ‖cellGradeRowLinear (grade := grade) parameters cell field‖ := by
  have rayBound := rayAverage_derivative_bound
    (shiftedClosedJet (phaseWeightedJet parameters cell field) (fun _ : Fin 1 => coordinate)) word point
  rw [rayAverageJet, globalClosedJet_derivative, shiftedClosedJet_closedDerivative] at rayBound
  exact (mul_le_mul_of_nonneg_left rayBound (pow_nonneg (cellFrequency_pos cell).le _)).trans
    (weighted_word_sup_paid parameters cell field (Fin.append word (fun _ : Fin 1 => coordinate)) (by omega))

theorem averagedPartial_tensor_paid {dimension grade order power : ℕ}
    (parameters : PhaseParameters) (cell : ℤ) (field : ClosedJet dimension)
    (coordinate : Fin 2) (paid : order + power + 3 ≤ grade) (point : ClosedDisk) :
    cellFrequency cell ^ power *
      ‖iteratedFDeriv ℝ order
        (rayAverageValue (shiftedClosedJet (phaseWeightedJet parameters cell field)
          (fun _ : Fin 1 => coordinate))) point.val‖ ≤
      (planarWordCoefficientSum order * (6 * diskSupConstant)) *
        ‖cellGradeRowLinear (grade := grade) parameters cell field‖ := by
  let averaged := rayAverageValue
    (shiftedClosedJet (phaseWeightedJet parameters cell field) (fun _ : Fin 1 => coordinate))
  have smooth : ContDiff ℝ ∞ averaged := rayAverageValue_smooth _
  have tensorBound := jetOperatorDerivative_point_bound (order := order) (globalClosedJet averaged smooth) point
  rw [jetOperatorDerivative_eq_closedPlane, ← globalClosedJet_higherDerivative] at tensorBound
  simp_rw [globalClosedJet_derivative] at tensorBound
  apply (mul_le_mul_of_nonneg_left tensorBound (pow_nonneg (cellFrequency_pos cell).le _)).trans
  rw [Finset.mul_sum, planarWordCoefficientSum, Finset.sum_mul, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro word _
  have bound := mul_le_mul_of_nonneg_left
    (averagedPartial_word_paid parameters cell field coordinate word paid point)
    (norm_nonneg (spatialPlaneWordCoefficient word))
  dsimp only [averaged] at *
  nlinarith only [bound]

def averagedEnvelopeConstant (order : ℕ) : ℝ :=
  ∑ index ∈ Finset.range (order + 1), planarWordCoefficientSum index * (6 * diskSupConstant)

theorem averagedEnvelopeConstant_nonnegative (order : ℕ) : 0 ≤ averagedEnvelopeConstant order :=
  Finset.sum_nonneg (fun index _ => mul_nonneg (planarWordCoefficientSum_nonnegative index)
    (mul_nonneg (by norm_num) diskSupConstant_pos.le))

theorem averagedPartial_envelope_paid {dimension grade order power : ℕ}
    (parameters : PhaseParameters) (cell : ℤ) (field : ClosedJet dimension)
    (coordinate : Fin 2) (paid : order + power + 3 ≤ grade) (point : ClosedDisk) :
    cellFrequency cell ^ power *
      spatialJetEnvelope (rayAverageValue (shiftedClosedJet (phaseWeightedJet parameters cell field)
        (fun _ : Fin 1 => coordinate))) order point.val ≤
      averagedEnvelopeConstant order * ‖cellGradeRowLinear (grade := grade) parameters cell field‖ := by
  rw [spatialJetEnvelope, averagedEnvelopeConstant, Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro index inside
  apply averagedPartial_tensor_paid parameters cell field coordinate
  have bound := Finset.mem_range.mp inside
  omega

end Grad.SourceCollarDivision
