import GQC21PhaseProductBound

noncomputable section

set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 200000

open Set Filter
open scoped Topology ContDiff

namespace Grad.GaugeCoefficients.Physical.Compensated

open Grad.ClosedJets Grad.CartesianState Grad.GaugeCoefficients.Algebra Grad.Constraints
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Envelope
open Grad.AnalyticWeights.Calculus Grad.AnalyticWeights.Higher

def partialJet {dimension : ℕ} (coordinate : Fin 2) (field : ClosedJet dimension) : ClosedJet dimension :=
  shiftedClosedJet field (fun _ : Fin 1 => coordinate)

theorem partialJet_value {dimension : ℕ} (coordinate : Fin 2) (field : ClosedJet dimension) :
    (partialJet coordinate field).value = closedDerivative field 1 (fun _ => coordinate) := rfl

theorem partialJet_value_fderiv {dimension : ℕ} (coordinate : Fin 2) (field : ClosedJet dimension)
    (point : ClosedDisk) (inside : point.val ∈ openUnitDisk) :
    (partialJet coordinate field).value point = fderiv ℝ (closedDiskLift field.value) point.val (spatialBasis coordinate) := by
  rw [partialJet_value, closedDerivative_spec field 1 (fun _ => coordinate) point inside]
  exact iteratedFDeriv_one_apply (fun _ : Fin 1 => spatialBasis coordinate)

theorem apWeightedJet_partial_value {dimension : ℕ} (sigma gamma ell : ℝ) (cell : ℤ)
    (coordinate : Fin 2) (field : ClosedJet dimension) (point : ClosedDisk) (inside : point.val ∈ openUnitDisk) :
    (partialJet coordinate (apWeightedJet sigma gamma ell cell field)).value point =
      phaseDirectional sigma gamma ell cell coordinate point.val • (apWeightedJet sigma gamma ell cell field).value point +
        originalWeight sigma gamma ell cell point.val • (partialJet coordinate field).value point := by
  have fieldDerivative := (field.smoothInterior.differentiableOn (by simp) point.val inside).differentiableAt
    (openUnitDisk_isOpen.mem_nhds inside) |>.hasFDerivAt
  have derivative := ((physicalWeight_hasFDerivAt sigma gamma ell cell point.val).smul fieldDerivative).fderiv
  have evaluation := congrArg (fun linear : SpatialPlane →L[ℝ] ComplexEuclidean dimension => linear (spatialBasis coordinate)) derivative
  change fderiv ℝ (fun candidate => physicalWeight sigma gamma ell cell candidate •
    closedDiskLift field.value candidate) point.val (spatialBasis coordinate) = _ at evaluation
  rw [← closedDiskLift_smoothScalarWeightedValue (physicalWeight sigma gamma ell cell)
    ((smoothGoal sigma gamma ell cell).2.1).continuous field] at evaluation
  change fderiv ℝ (closedDiskLift (apWeightedJet sigma gamma ell cell field).value)
    point.val (spatialBasis coordinate) = _ at evaluation
  rw [partialJet_value_fderiv coordinate _ point inside, partialJet_value_fderiv coordinate field point inside,
    apWeightedJet_value]
  rw [evaluation]
  simp only [add_apply, ContinuousLinearMap.smulRight_apply,
    smul_apply, smul_eq_mul, closedLift_value _ point.val inside,
    phaseDirectional, physicalPhase_fderiv, originalWeight]
  rw [smul_smul, mul_comm]
  exact add_comm _ _

/-- Exact weighted/unweighted differentiation identity at the level of
genuine closed jets. In particular the phase-gradient term is not discarded. -/
theorem apWeightedJet_partial {dimension : ℕ} (sigma gamma ell : ℝ) (cell : ℤ)
    (coordinate : Fin 2) (field : ClosedJet dimension) :
    apWeightedJet sigma gamma ell cell (partialJet coordinate field) =
      partialJet coordinate (apWeightedJet sigma gamma ell cell field) -
        apProductJet (apScalarOperatorJet dimension (phaseDirectional sigma gamma ell cell coordinate)
          (phaseDirectional_smooth sigma gamma ell cell coordinate)) (apWeightedJet sigma gamma ell cell field) := by
  apply closedJet_eq_of_value_eq
  rw [sub_eq_add_neg, closedJet_value_add, closedJet_value_neg, ← sub_eq_add_neg]
  apply continuousMap_eq_of_openDisk
  intro point inside
  change (apWeightedJet sigma gamma ell cell (partialJet coordinate field)).value point =
    (partialJet coordinate (apWeightedJet sigma gamma ell cell field)).value point -
      (apProductJet (apScalarOperatorJet dimension (phaseDirectional sigma gamma ell cell coordinate)
        (phaseDirectional_smooth sigma gamma ell cell coordinate)) (apWeightedJet sigma gamma ell cell field)).value point
  rw [apWeightedJet_value, apWeightedJet_partial_value sigma gamma ell cell coordinate field point inside, apProductJet_value]
  change _ = (_ + _) - phaseDirectional sigma gamma ell cell coordinate point.val •
    (apWeightedJet sigma gamma ell cell field).value point
  abel

end Grad.GaugeCoefficients.Physical.Compensated
