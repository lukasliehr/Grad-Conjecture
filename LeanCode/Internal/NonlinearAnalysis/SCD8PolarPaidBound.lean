import SCD7PolarGeometryBounds

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators

namespace Grad.SourceCollarDivision

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearRadial Grad.BoundaryTrace

def divisionDerivativeConstant (order : ℕ) : ℝ :=
  2 * (polarProductConstant order order * averagedEnvelopeConstant order)

theorem divisionDerivativeConstant_nonnegative (order : ℕ) : 0 ≤ divisionDerivativeConstant order :=
  mul_nonneg (by norm_num) (mul_nonneg (polarProductConstant_nonnegative _ _)
    (averagedEnvelopeConstant_nonnegative _))

/-- All radial/angular derivatives of the actual weighted quotient are
uniform up to r=0, with exactly the three paid Cartesian grades. -/
theorem dividedPolarValue_derivative_paid {dimension grade order power : ℕ}
    (parameters : PhaseParameters) (cell : ℤ) (field : ClosedJet dimension)
    (paid : order + power + 3 ≤ grade) (point : ℝ × ℝ) (inside : point ∈ polarRectangle) :
    cellFrequency cell ^ power *
      ‖iteratedFDeriv ℝ order (dividedPolarValue (phaseWeightedJet parameters cell field)) point‖ ≤
      divisionDerivativeConstant order * ‖cellGradeRowLinear (grade := grade) parameters cell field‖ := by
  let part (coordinate : Fin 2) : ℝ × ℝ → ComplexEuclidean dimension := fun point =>
    polarAngularFactor coordinate point •
      rayAverageValue (shiftedClosedJet (phaseWeightedJet parameters cell field)
        (fun _ : Fin 1 => coordinate)) (polarPlane point)
  have partSmooth (coordinate : Fin 2) : ContDiff ℝ ∞ (part coordinate) :=
    (polarAngularFactor_smooth coordinate).smul ((rayAverageValue_smooth _).comp polarPlane_smooth)
  have expression : dividedPolarValue (phaseWeightedJet parameters cell field) = ∑ coordinate, part coordinate := by
    funext point
    simp only [dividedPolarValue, Finset.sum_apply, part, polarAngularFactor]
  have partBound (coordinate : Fin 2) :
      cellFrequency cell ^ power * ‖iteratedFDeriv ℝ order (part coordinate) point‖ ≤
        (polarProductConstant order order * averagedEnvelopeConstant order) *
          ‖cellGradeRowLinear (grade := grade) parameters cell field‖ := by
    have product := polarProduct_derivative_bound coordinate
      (rayAverageValue (shiftedClosedJet (phaseWeightedJet parameters cell field)
        (fun _ : Fin 1 => coordinate))) (rayAverageValue_smooth _) order order le_rfl point inside
    have envelope := averagedPartial_envelope_paid parameters cell field coordinate paid
      (polarClosedPoint point.1 point.2 inside.1.1 inside.1.2)
    change cellFrequency cell ^ power * spatialJetEnvelope _ order (polarPlane point) ≤ _ at envelope
    calc
      _ ≤ cellFrequency cell ^ power * (polarProductConstant order order *
          spatialJetEnvelope (rayAverageValue (shiftedClosedJet (phaseWeightedJet parameters cell field)
            (fun _ : Fin 1 => coordinate))) order (polarPlane point)) :=
        mul_le_mul_of_nonneg_left product (pow_nonneg (cellFrequency_pos cell).le _)
      _ = polarProductConstant order order * (cellFrequency cell ^ power *
          spatialJetEnvelope (rayAverageValue (shiftedClosedJet (phaseWeightedJet parameters cell field)
            (fun _ : Fin 1 => coordinate))) order (polarPlane point)) := by ring
      _ ≤ polarProductConstant order order * (averagedEnvelopeConstant order *
          ‖cellGradeRowLinear (grade := grade) parameters cell field‖) :=
        mul_le_mul_of_nonneg_left envelope (polarProductConstant_nonnegative _ _)
      _ = _ := by ring
  rw [expression, iteratedFDeriv_sum_apply]
  · calc
      _ ≤ cellFrequency cell ^ power * ∑ coordinate : Fin 2,
          ‖iteratedFDeriv ℝ order (part coordinate) point‖ :=
        mul_le_mul_of_nonneg_left (norm_sum_le _ _) (pow_nonneg (cellFrequency_pos cell).le _)
      _ = ∑ coordinate : Fin 2, cellFrequency cell ^ power *
          ‖iteratedFDeriv ℝ order (part coordinate) point‖ := Finset.mul_sum _ _ _
      _ ≤ ∑ _coordinate : Fin 2, (polarProductConstant order order * averagedEnvelopeConstant order) *
          ‖cellGradeRowLinear (grade := grade) parameters cell field‖ :=
        Finset.sum_le_sum (fun coordinate _ => partBound coordinate)
      _ = _ := by simp [divisionDerivativeConstant]; ring
  · intro coordinate _
    exact (partSmooth coordinate).contDiffAt.of_le
      (by exact_mod_cast (le_top : (order : ℕ∞) ≤ ⊤))

end Grad.SourceCollarDivision
