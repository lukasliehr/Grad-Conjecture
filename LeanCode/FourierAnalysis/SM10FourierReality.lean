import SM9Projection
import NGP01Reality

noncomputable section

open MeasureTheory
open scoped ComplexConjugate BigOperators

namespace Grad.SmoothingFamily

open Grad.ClosedJets Grad.CartesianState Grad.FourierGrade Grad.COR12Extension

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

theorem modeVector_neg (mode : FourierMode) : modeVector (-mode) = -modeVector mode := by
  funext coordinate
  fin_cases coordinate <;> rfl

theorem frequencyWeight_neg (mode : FourierMode) : frequencyWeight (-mode) = frequencyWeight mode := by
  have vectorEquality : frequencyVector (-mode) = -frequencyVector mode := by
    apply PiLp.ext
    intro coordinate
    fin_cases coordinate <;> simp [frequencyVector]
  simp [frequencyWeight, vectorEquality]

theorem torusCharacter_conjugate (mode : FourierMode) (point : ProductTorus) :
    conj (torusCharacter mode point) = torusCharacter (-mode) point := by
  simp only [torusCharacter, modeVector_neg, UnitAddTorus.mFourier_neg]

def FourierReality {dimension : ℕ} (values : JCore (ComplexEuclidean dimension)) : Prop :=
  ∀ mode coordinate, conj (values.1 (-mode) coordinate) = values.1 mode coordinate

theorem continuousFourierCoefficient_reality {dimension : ℕ}
    (field : C(ProductTorus, ComplexEuclidean dimension))
    (real : ∀ point coordinate, conj (field point coordinate) = field point coordinate)
    (mode : FourierMode) (coordinate : Fin dimension) :
    conj (UnitAddTorus.mFourierCoeff field (modeVector (-mode)) coordinate) =
      UnitAddTorus.mFourierCoeff field (modeVector mode) coordinate := by
  rw [euclideanContinuousComponent_mFourierCoeff, euclideanContinuousComponent_mFourierCoeff]
  simp only [UnitAddTorus.mFourierCoeff, modeVector_neg, neg_neg]
  rw [← integral_conj]
  apply integral_congr_ae
  filter_upwards [] with point
  change conj (UnitAddTorus.mFourier (modeVector mode) point * field point coordinate) =
    UnitAddTorus.mFourier (-modeVector mode) point * field point coordinate
  rw [map_mul, real, UnitAddTorus.mFourier_neg]

theorem fourierScaleDerivative_reality {dimension : ℕ} (order : ℕ) (scale : ℝ)
    (values : JCore (ComplexEuclidean dimension)) (real : FourierReality values) :
    FourierReality (fourierScaleDerivative order scale values) := by
  intro mode coordinate
  simp only [fourierScaleDerivative_apply, PiLp.smul_apply, smul_eq_mul, map_mul,
    frequencyWeight_neg, Complex.conj_ofReal]
  exact congrArg (fun value : ℂ => (scaleMultiplier order (frequencyWeight mode) scale : ℂ) * value)
    (real mode coordinate)

theorem fourierSmoothing_reality {dimension : ℕ} (scale : ℝ)
    (values : JCore (ComplexEuclidean dimension)) (real : FourierReality values) :
    FourierReality (fourierSmoothing scale values) := by
  rw [← fourierScaleDerivative_zero]
  exact fourierScaleDerivative_reality 0 scale values real

theorem reconstructedTorus_reality {dimension : ℕ}
    (values : JCore (ComplexEuclidean dimension)) (real : FourierReality values)
    (point : ProductTorus) (coordinate : Fin dimension) :
    conj (reconstructedTorus values point coordinate) = reconstructedTorus values point coordinate := by
  let evaluation : C(ProductTorus, ComplexEuclidean dimension) →L[ℂ] ℂ :=
    (PiLp.proj 2 (fun _ : Fin dimension => ℂ) coordinate).comp (ContinuousMap.evalCLM ℂ point)
  have series := (vectorTorusTerm_summable values).map evaluation evaluation.continuous
  have evaluationSum := evaluation.map_tsum (vectorTorusTerm_summable values)
  change reconstructedTorus values point coordinate =
    ∑' mode : FourierMode, torusCharacter mode point * values.1 mode coordinate at evaluationSum
  rw [evaluationSum]
  rw [show conj (∑' mode : FourierMode, torusCharacter mode point * values.1 mode coordinate) =
      ∑' mode : FourierMode, conj (torusCharacter mode point * values.1 mode coordinate) by
    exact Complex.conjLIE.toContinuousLinearEquiv.toContinuousLinearMap.map_tsum series]
  calc
    _ = ∑' mode : FourierMode, torusCharacter (-mode) point * values.1 (-mode) coordinate := by
      apply tsum_congr
      intro mode
      rw [map_mul, torusCharacter_conjugate]
      have reflected := real (-mode) coordinate
      simpa only [neg_neg] using congrArg (fun value : ℂ => torusCharacter (-mode) point * value) reflected
    _ = _ := by
      simpa only [Equiv.neg_apply] using (Equiv.neg FourierMode).tsum_eq
        (fun mode => torusCharacter mode point * values.1 mode coordinate)

end Grad.SmoothingFamily
