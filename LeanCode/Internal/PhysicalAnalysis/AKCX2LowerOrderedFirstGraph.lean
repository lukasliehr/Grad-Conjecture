import AKCG7ActualMatrixAllOrderGraph

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1300000
open Set Filter MeasureTheory
open scoped ContDiff
namespace Grad.CartesianStartup
open Grad.PDEBootstrap Grad.GenericCarriers Grad.ClosedJets Grad.WeightedJets Grad.WeightedJets.Ordered
open Grad.WeakTesting Grad.WeakTesting.Commutation

private theorem orderedTestDerivative_snoc {rank : ℕ} (word : Fin rank → Fin 2)
    (direction : Fin 2) (test : Spatial → ℝ) (smooth : ContDiff ℝ ∞ test) :
    orderedTestDerivative (rank+1) (Fin.snoc word direction) test =
      orderedTestDerivative rank word (differentiate direction test) := by
  rw [← listDerivative_ofFn _ _ _ smooth,← listDerivative_ofFn _ _ _ (differentiate_contDiff direction test smooth)]
  rw [List.ofFn_succ']
  simp [listDerivative,List.foldr_append]

/-- A lower stored ordered derivative has its actual first graph whenever
one more spatial order is already available. This supplies the strict
complementary-word regularity in nonempty coefficient allocations. -/
theorem startupOrderedDerivative_first {dimension order rank weight : ℕ}
    (field : GraphGrade dimension order weight openUnitDisk) (bound : rank+1 ≤ order)
    (word : Fin rank → Fin 2) :
    ∃ graph : StartupFirst dimension, base dimension 1 openUnitDisk (fun _ => 0) graph =
      orderedDerivative dimension order rank openUnitDisk (fun _ => weight) (by omega) field word := by
  let value := orderedDerivative dimension order rank openUnitDisk (fun _ => weight) (by omega) field word
  let derivative := fun direction =>
    orderedDerivative dimension order (rank+1) openUnitDisk (fun _ => weight) bound field (Fin.snoc word direction)
  have weak : ∀ direction, HasWeakOrderedDerivative dimension openUnitDisk 1 (startupFirstWord direction) value (derivative direction) := by
    intro direction
    apply (hasWeakOrderedDerivative_iff_integral dimension openUnitDisk 1 (startupFirstWord direction) value (derivative direction)).mpr
    intro cell vector test smooth compact supported
    have lower := orderedDerivative_integral dimension order rank openUnitDisk (fun _ => weight) (by omega)
      field word cell vector (differentiate direction test) (differentiate_contDiff direction test smooth)
      (compact.of_isClosed_subset (isClosed_tsupport _)
        (tsupport_fderiv_apply_subset ℝ (spatialDirection direction)))
      ((tsupport_fderiv_apply_subset ℝ (spatialDirection direction)).trans supported)
    have upper := orderedDerivative_integral dimension order (rank+1) openUnitDisk (fun _ => weight) bound
      field (Fin.snoc word direction) cell vector test smooth compact supported
    rw [orderedTestDerivative_snoc word direction test smooth,pow_succ] at upper
    change (∫ point in openUnitDisk, test point • inner ℂ vector (derivative direction point cell)) = _ at upper
    have first : orderedTestDerivative 1 (startupFirstWord direction) test = differentiate direction test := by
      funext point
      simp only [orderedTestDerivative,iteratedFDeriv_one_apply]
      rfl
    rw [first,pow_one]
    rw [lower]
    simpa only [mul_assoc,mul_comm,mul_left_comm] using upper
  exact ⟨startupFirstGraph value derivative weak,startupFirstGraph_base value derivative weak⟩

end Grad.CartesianStartup
