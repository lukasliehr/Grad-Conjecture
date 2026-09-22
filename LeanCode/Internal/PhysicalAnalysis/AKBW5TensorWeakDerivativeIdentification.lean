import AKBW4TensorFieldIdentification

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option synthInstance.maxHeartbeats 200000

namespace Grad.CartesianStartup
open MeasureTheory Grad.ClosedJets Grad.PDEBootstrap Grad.GenericCarriers Grad.TensorBootstrap
open Grad.WeakTesting Grad.WeakTesting.Commutation

theorem startupTensorValue_inner (dimension rank : ℕ)
    (vector : PhysicalValue (startupTensorDimension dimension rank))
    (tensor : Tensor rank (PhysicalValue dimension)) :
    inner ℂ vector (startupTensorValueEquiv dimension rank tensor) =
      ∑ word : DerivativeIndex rank, inner ℂ ((startupTensorValueEquiv dimension rank).symm vector word) (tensor word) := by
  have same := (startupTensorValueEquiv dimension rank).inner_map_map
    ((startupTensorValueEquiv dimension rank).symm vector) tensor
  simpa only [LinearIsometryEquiv.apply_symm_apply, PiLp.inner_apply] using same

/-- Actual compact pairings commute with the finite tensor identification;
all integer cells remain present and every physical component is retained. -/
theorem startupTensorField_integral (dimension rank : ℕ)
    (fields : Tensor rank (StartupL2 dimension)) (cell : ℤ)
    (vector : PhysicalValue (startupTensorDimension dimension rank))
    (test : Spatial → ℝ) (membership : MemLp test 2 (volume.restrict openUnitDisk)) :
    (∫ point in openUnitDisk, test point • inner ℂ vector
      (startupTensorFieldEquiv dimension rank fields point cell)) =
      ∑ word : DerivativeIndex rank,
        ∫ point in openUnitDisk, test point •
          inner ℂ ((startupTensorValueEquiv dimension rank).symm vector word) (fields word point cell) := by
  calc
    _ = ∫ point in openUnitDisk, ∑ word : DerivativeIndex rank,
        test point • inner ℂ ((startupTensorValueEquiv dimension rank).symm vector word) (fields word point cell) := by
      apply integral_congr_ae
      filter_upwards [startupTensorFieldEquiv_ae dimension rank fields] with point same
      rw [same cell, startupTensorValue_inner, Finset.smul_sum]
    _ = _ := integral_finsetSum _ (fun word _ =>
      pairing_integrable dimension openUnitDisk cell
        ((startupTensorValueEquiv dimension rank).symm vector word) test membership (fields word))

/-- Weak derivatives of a finite covector tuple are exactly the genuine weak
derivatives of its value identification; this assertion presupposes no new derivative. -/
theorem startupTensorField_weak_iff (dimension rank order : ℕ) (derivativeWord : Fin order → Fin 2)
    (fields derivatives : Tensor rank (StartupL2 dimension)) :
    HasWeakOrderedDerivative (startupTensorDimension dimension rank) openUnitDisk order derivativeWord
      (startupTensorFieldEquiv dimension rank fields) (startupTensorFieldEquiv dimension rank derivatives) ↔
      ∀ index : DerivativeIndex rank,
        HasWeakOrderedDerivative dimension openUnitDisk order derivativeWord (fields index) (derivatives index) := by
  constructor
  · intro weak index
    apply (hasWeakOrderedDerivative_iff_integral dimension openUnitDisk order derivativeWord (fields index) (derivatives index)).mpr
    intro cell vector test smooth compact supported
    let flatVector := startupTensorValueEquiv dimension rank
      (PiLp.single (β := fun _ : DerivativeIndex rank => PhysicalValue dimension) 2 index vector)
    have equation := (hasWeakOrderedDerivative_iff_integral (startupTensorDimension dimension rank)
      openUnitDisk order derivativeWord (startupTensorFieldEquiv dimension rank fields)
      (startupTensorFieldEquiv dimension rank derivatives)).mp weak cell flatVector test smooth compact supported
    rw [startupTensorField_integral dimension rank derivatives cell flatVector test
      (smooth.continuous.memLp_of_hasCompactSupport compact),
      startupTensorField_integral dimension rank fields cell flatVector
      (orderedTestDerivative order derivativeWord test)
      (orderedTestDerivative_memLp openUnitDisk order derivativeWord test smooth compact)] at equation
    have vectorCoordinates (word : DerivativeIndex rank) :
        (startupTensorValueEquiv dimension rank).symm flatVector word =
          if word = index then vector else 0 := by
      dsimp only [flatVector]
      rw [LinearIsometryEquiv.symm_apply_apply]
      simp only [PiLp.single_apply]
    have sumSingle (input : Tensor rank (StartupL2 dimension)) (scalar : Spatial → ℝ) :
        (∑ word : DerivativeIndex rank, ∫ point in openUnitDisk,
          scalar point • inner ℂ (if word = index then vector else 0) (input word point cell)) =
          ∫ point in openUnitDisk, scalar point • inner ℂ vector (input index point cell) := by
      rw [Finset.sum_eq_single index]
      · simp only [ite_true]
      · intro word _ different
        simp only [if_neg different, inner_zero_left, smul_zero, integral_zero]
      · simp
    simp only [vectorCoordinates, sumSingle] at equation
    exact equation
  · intro weak
    apply (hasWeakOrderedDerivative_iff_integral (startupTensorDimension dimension rank) openUnitDisk order derivativeWord
      (startupTensorFieldEquiv dimension rank fields) (startupTensorFieldEquiv dimension rank derivatives)).mpr
    intro cell vector test smooth compact supported
    rw [startupTensorField_integral dimension rank derivatives cell vector test
      (smooth.continuous.memLp_of_hasCompactSupport compact),
      startupTensorField_integral dimension rank fields cell vector
      (orderedTestDerivative order derivativeWord test)
      (orderedTestDerivative_memLp openUnitDisk order derivativeWord test smooth compact), Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro index _
    exact (hasWeakOrderedDerivative_iff_integral dimension openUnitDisk order derivativeWord
      (fields index) (derivatives index)).mp (weak index)
      cell ((startupTensorValueEquiv dimension rank).symm vector index) test smooth compact supported

end Grad.CartesianStartup
