import GQC1ClosedDerivative

noncomputable section

set_option maxHeartbeats 1500000
set_option synthInstance.maxHeartbeats 200000

open Set Filter
open scoped Topology ContDiff

namespace Grad.GaugeCoefficients.Physical.Compensated

open Grad.ClosedJets Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Neumann.Regularity Grad.GaugeCoefficients.Physical.Allocation
open Grad.GaugeCoefficients.Physical.RadialLedger
open Grad.GaugeCoefficients.Physical.Frame

def planarCoordinate (coordinate : Fin 2) : SpatialPlane →L[ℝ] ℝ :=
  PiLp.proj 2 (fun _ : Fin 2 => ℝ) coordinate

def planarDerivative {Value : Type*} [NormedAddCommGroup Value] [NormedSpace ℝ Value]
    (first second : Value) : SpatialPlane →L[ℝ] Value :=
  (ContinuousLinearMap.smulRightL ℝ SpatialPlane Value) (planarCoordinate 0) first +
    (ContinuousLinearMap.smulRightL ℝ SpatialPlane Value) (planarCoordinate 1) second

theorem planarDerivative_apply {Value : Type*} [NormedAddCommGroup Value] [NormedSpace ℝ Value]
    (first second : Value) (direction : SpatialPlane) :
    planarDerivative first second direction = direction 0 • first + direction 1 • second := rfl

theorem planarDerivative_basis {Value : Type*} [NormedAddCommGroup Value] [NormedSpace ℝ Value]
    (first second : Value) (coordinate : Fin 2) :
    planarDerivative first second (spatialBasis coordinate) = if coordinate = 0 then first else second := by
  fin_cases coordinate <;> simp [planarDerivative_apply, spatialBasis]

def planarDerivativeMap {Value : Type*} [NormedAddCommGroup Value] [NormedSpace ℝ Value]
    (first second : C(ClosedDisk, Value)) : C(ClosedDisk, SpatialPlane →L[ℝ] Value) :=
  ⟨fun point => planarDerivative (first point) (second point),
    (((ContinuousLinearMap.smulRightL ℝ SpatialPlane Value) (planarCoordinate 0)).continuous.comp first.continuous).add
      (((ContinuousLinearMap.smulRightL ℝ SpatialPlane Value) (planarCoordinate 1)).continuous.comp second.continuous)⟩

theorem planarDerivativeMap_continuous {Value : Type*} [NormedAddCommGroup Value] [NormedSpace ℝ Value] :
    Continuous (fun pair : C(ClosedDisk, Value) × C(ClosedDisk, Value) => planarDerivativeMap pair.1 pair.2) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  exact (((ContinuousLinearMap.smulRightL ℝ SpatialPlane Value) (planarCoordinate 0)).continuous.comp
    (continuous_fst.fst.eval continuous_snd)).add
    (((ContinuousLinearMap.smulRightL ℝ SpatialPlane Value) (planarCoordinate 1)).continuous.comp
      (continuous_fst.snd.eval continuous_snd))

def coefficientClosedCoordinate {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    (grade input output : ℕ) (cell : ℤ) (index : DerivativeIndex grade) :
    Coefficient L sigma gamma ell grade input output →L[ℂ] C(ClosedDisk, OperatorValue input output) :=
  LinearMap.mkContinuous
    { toFun := fun coefficient => coefficientDerivative coefficient cell index
      map_add' := fun first second => by
        apply ContinuousMap.ext
        intro point
        exact coefficientDerivative_add_apply first second cell index point
      map_smul' := fun scalar coefficient => by
        apply ContinuousMap.ext
        intro point
        exact coefficientDerivative_smul_apply scalar coefficient cell index point }
    1 (fun coefficient => by
      rw [one_mul]
      apply (ContinuousMap.norm_le _ (norm_nonneg coefficient)).mpr
      intro point
      exact (coefficientDerivative_point_norm_le admissible coefficient cell index point).trans
        (lp.norm_apply_le_norm (p := 1) (by norm_num) coefficient.val (cell, index)))

theorem coefficientClosedCoordinate_apply {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) {grade input output : ℕ}
    (coefficient : Coefficient L sigma gamma ell grade input output) (cell : ℤ) (index : DerivativeIndex grade) :
    coefficientClosedCoordinate admissible grade input output cell index coefficient =
      coefficientDerivative coefficient cell index := rfl

def firstCoordinateIndex (coordinate : Fin 2) : DerivativeIndex 1 :=
  ![⟨(1, 0), by decide⟩, ⟨(0, 1), by decide⟩] coordinate

end Grad.GaugeCoefficients.Physical.Compensated
