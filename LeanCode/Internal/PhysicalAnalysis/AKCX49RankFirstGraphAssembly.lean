import AKCX45HigherGraphRankFirst

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 3000
open Set Filter MeasureTheory
open scoped ContDiff BigOperators
namespace Grad.CartesianStartup
open Grad.ClosedJets Grad.PDEBootstrap Grad.GenericCarriers Grad.WeightedJets
open Grad.WeightedJets.Ordered Grad.WeakTesting Grad.WeakTesting.Commutation

private theorem startupAppend_test {rank : ℕ} (word : Fin rank → Fin 2)
    (direction : Fin 2) (test : Spatial → ℝ) (smooth : ContDiff ℝ ∞ test) :
    orderedTestDerivative (rank+1) (Fin.snoc word direction) test =
      orderedTestDerivative rank word (differentiate direction test) := by
  rw [← listDerivative_ofFn _ _ _ smooth,← listDerivative_ofFn _ _ _ (differentiate_contDiff direction test smooth)]
  rw [List.ofFn_succ']
  simp [listDerivative,List.foldr_append]

theorem startupRankFirst_appendWeak {rank : ℕ} (field : GraphGrade 3 rank 0 openUnitDisk)
    (word : Fin rank → Fin 2) (first : StartupFirst 3)
    (same : base 3 1 openUnitDisk (fun _ => 0) first =
      orderedDerivative 3 rank rank openUnitDisk (fun _ => 0) le_rfl field word)
    (direction : Fin 2) :
    HasWeakOrderedDerivative 3 openUnitDisk (rank+1) (Fin.snoc word direction)
      (base 3 rank openUnitDisk (fun _ => 0) field) (startupFirstDerivative first direction) := by
  apply (hasWeakOrderedDerivative_iff_integral _ _ _ _ _ _).mpr
  intro cell vector test smooth compact supported
  have lower := orderedDerivative_integral 3 rank rank openUnitDisk (fun _ => 0) le_rfl field word cell vector
    (differentiate direction test) (differentiate_contDiff direction test smooth)
    (compact.of_isClosed_subset (isClosed_tsupport _) (tsupport_fderiv_apply_subset ℝ (spatialDirection direction)))
    ((tsupport_fderiv_apply_subset ℝ (spatialDirection direction)).trans supported)
  have upper := orderedDerivative_integral 3 1 1 openUnitDisk (fun _ => 0) le_rfl first
    (startupFirstWord direction) cell vector test smooth compact supported
  have firstTest : orderedTestDerivative 1 (startupFirstWord direction) test = differentiate direction test := by
    funext point
    simp only [orderedTestDerivative,iteratedFDeriv_one_apply]
    rfl
  rw [firstTest,same,lower] at upper
  rw [startupAppend_test word direction test smooth,pow_succ]
  simpa only [startupFirstDerivative,pow_one,mul_assoc,mul_comm,mul_left_comm] using upper

/-- Genuine first graphs of all top ordered derivatives close the next
spatial graph of the SAME original field. -/
theorem startupRankFirst_nextGraph {rank : ℕ} (field : GraphGrade 3 rank 0 openUnitDisk)
    (improved : ∀ word : Fin rank → Fin 2, ∃ first : StartupFirst 3,
      base 3 1 openUnitDisk (fun _ => 0) first =
        orderedDerivative 3 rank rank openUnitDisk (fun _ => 0) le_rfl field word) :
    ∃ next : GraphGrade 3 (rank+1) 0 openUnitDisk,
      base 3 (rank+1) openUnitDisk (fun _ => 0) next = base 3 rank openUnitDisk (fun _ => 0) field := by
  have supply (degree : ℕ) (bound : degree ≤ rank+1) (word : Fin degree → Fin 2) :
      ∃ derivative : StartupL2 3, HasWeakOrderedDerivative 3 openUnitDisk degree word
        (base 3 rank openUnitDisk (fun _ => 0) field) derivative := by
    by_cases lower : degree ≤ rank
    · exact ⟨orderedDerivative 3 rank degree openUnitDisk (fun _ => 0) lower field word,
        orderedDerivative_hasWeak 3 rank degree openUnitDisk (fun _ => 0) lower field word⟩
    · have top : degree = rank+1 := by omega
      subst degree
      obtain ⟨first,same⟩ := improved (Fin.init word)
      refine ⟨startupFirstDerivative first (word (Fin.last rank)),?_⟩
      have weak := startupRankFirst_appendWeak field (Fin.init word) first same (word (Fin.last rank))
      rw [Fin.snoc_init_self] at weak
      exact weak
  let derivatives := fun index : JetIndex (rank+1) => (supply (degree index) (degree_le index) (derivativeWord index)).choose
  have weak (index : JetIndex (rank+1)) : HasWeakOrderedDerivative 3 openUnitDisk (degree index) (derivativeWord index)
      (base 3 rank openUnitDisk (fun _ => 0) field) (derivatives index) :=
    (supply (degree index) (degree_le index) (derivativeWord index)).choose_spec
  have zero : derivatives (zeroIndex (rank+1)) = base 3 rank openUnitDisk (fun _ => 0) field :=
    (Grad.WeakTesting.Commutation.zero 3 openUnitDisk openUnitDisk_isOpen _ _ _).mp (weak (zeroIndex (rank+1)))
  exact ⟨startupGraphFromWeak _ derivatives zero weak,startupGraphFromWeak_base _ derivatives zero weak⟩

end Grad.CartesianStartup
