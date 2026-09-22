import WM1Averaging

noncomputable section

open MeasureTheory Grad.PDEBootstrap Grad.GenericCarriers Grad.WeightedJets
open Grad.WeakTesting Grad.SpatialTranslation
open scoped BigOperators ContDiff

namespace Grad.Mollifier.WeakJets

def translatedTest (offset : Spatial) (test : TestFunction Set.univ) : TestFunction Set.univ :=
  ⟨shiftedTest offset test.toFun, shiftedTest_contDiff offset test.toFun test.smooth,
    shiftedTest_compactSupport offset test.toFun test.compact, Set.subset_univ _⟩

theorem testPairing_translation (dimension : ℕ) (offset : Spatial)
    (field : FieldL2 dimension Set.univ) (cell : ℤ) (vector : PhysicalValue dimension)
    (test : TestFunction Set.univ) :
    testPairing dimension Set.univ cell vector test (translation (CellValues dimension) offset field) =
      testPairing dimension Set.univ cell vector (translatedTest offset test) field := by
  simp only [testPairing_apply, Measure.restrict_univ]
  exact integral_translation_test dimension offset field cell vector test.toFun

theorem derivativeTestPairing_translation (dimension order : ℕ) (index : JetIndex order)
    (offset : Spatial) (field : FieldL2 dimension Set.univ) (cell : ℤ) (vector : PhysicalValue dimension)
    (test : TestFunction Set.univ) :
    derivativeTestPairing dimension order Set.univ index cell vector test
        (translation (CellValues dimension) offset field) =
      derivativeTestPairing dimension order Set.univ index cell vector (translatedTest offset test) field := by
  simp only [derivativeTestPairing_apply, Measure.restrict_univ]
  rw [integral_translation_test]
  apply integral_congr_ae
  filter_upwards [] with point
  rw [show (translatedTest offset test).toFun = shiftedTest offset test.toFun from rfl,
    orderedTestDerivative_shifted]

theorem averaged_jet_identity (dimension order : ℕ) (exponent : JetIndex order → ℕ)
    (kernel : Spatial → ℝ) (integrability : Integrable kernel volume)
    (jet : WJet dimension order Set.univ exponent) (index : JetIndex order) (cell : ℤ)
    (vector : PhysicalValue dimension) (test : TestFunction Set.univ) :
    testPairing dimension Set.univ cell vector test (average (CellValues dimension) kernel (jet.val index)) =
      ((-1 : ℂ) ^ degree index * Grad.CellWeights.positiveFactor (exponent index) cell) *
        derivativeTestPairing dimension order Set.univ index cell vector test
          (average (CellValues dimension) kernel (base dimension order Set.univ exponent jet)) := by
  have translatedIdentity (offset : Spatial) :=
    jet_identity dimension order Set.univ exponent jet index cell vector (translatedTest offset test)
  simp_rw [← testPairing_translation, ← derivativeTestPairing_translation] at translatedIdentity
  rw [(functional_average (CellValues dimension) kernel integrability
    (testPairing dimension Set.univ cell vector test) (jet.val index)).2,
    (functional_average (CellValues dimension) kernel integrability
      (derivativeTestPairing dimension order Set.univ index cell vector test)
      (base dimension order Set.univ exponent jet)).2]
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with offset
  rw [translatedIdentity offset]
  exact smul_comm (kernel offset)
    ((-1 : ℂ) ^ degree index * Grad.CellWeights.positiveFactor (exponent index) cell) _

theorem graphGoal : GraphGoal := by
  intro dimension order exponent kernel integrability jet
  apply (jetGraph_mem dimension order Set.univ exponent _).mpr
  intro index cell vector test
  rw [averageTuple_base dimension order exponent kernel integrability]
  exact averaged_jet_identity dimension order exponent kernel integrability jet index cell vector test

theorem integralGoal : IntegralGoal := by
  intro dimension order exponent kernel integrability jet index cell vector test
  have identity := averaged_jet_identity dimension order exponent kernel integrability jet index cell vector test
  simp only [testPairing_apply, derivativeTestPairing_apply, Measure.restrict_univ] at identity
  exact identity

def jetAveraging (dimension order : ℕ) (exponent : JetIndex order → ℕ)
    (kernel : Spatial → ℝ) (integrability : Integrable kernel volume) :
    WJet dimension order Set.univ exponent →L[ℂ] WJet dimension order Set.univ exponent :=
  ((ambientAveraging dimension order kernel integrability).comp
    (jetGraph dimension order Set.univ exponent).subtypeL).codRestrict
      (jetGraph dimension order Set.univ exponent) (graphGoal dimension order exponent kernel integrability)

theorem jetAveraging_val (dimension order : ℕ) (exponent : JetIndex order → ℕ)
    (kernel : Spatial → ℝ) (integrability : Integrable kernel volume)
    (jet : WJet dimension order Set.univ exponent) :
    (jetAveraging dimension order exponent kernel integrability jet).val =
      averageTuple dimension order kernel jet.val := rfl

theorem jetAveraging_specification (dimension order : ℕ) (exponent : JetIndex order → ℕ)
    (kernel : Spatial → ℝ) (integrability : Integrable kernel volume) :
    LiftSpecification dimension order exponent kernel (jetAveraging dimension order exponent kernel integrability) :=
  ⟨jetAveraging_val dimension order exponent kernel integrability,
    fun jet => averageTuple_base dimension order exponent kernel integrability jet.val⟩

theorem jetAveraging_norm_le (dimension order : ℕ) (exponent : JetIndex order → ℕ)
    (kernel : Spatial → ℝ) (integrability : Integrable kernel volume) :
    ‖jetAveraging dimension order exponent kernel integrability‖ ≤ kernelL1 kernel := by
  apply ContinuousLinearMap.opNorm_le_bound _ (kernelL1_nonneg kernel)
  intro jet
  exact averageTuple_norm_le dimension order kernel jet.val

theorem liftGoal : LiftGoal := by
  intro dimension order exponent kernel integrability
  exact ⟨jetAveraging dimension order exponent kernel integrability,
    jetAveraging_specification dimension order exponent kernel integrability,
    jetAveraging_norm_le dimension order exponent kernel integrability⟩

theorem contractionGoal : ContractionGoal := by
  intro dimension order exponent kernel integrability nonnegative mass
  have bound (jet : WJet dimension order Set.univ exponent) :
      ‖averageTuple dimension order kernel jet.val‖ ≤ ‖jet‖ := by
    change ‖averageTuple dimension order kernel jet.val‖ ≤ ‖jet.val‖
    simpa only [kernelL1_eq_one kernel nonnegative mass, one_mul] using
      averageTuple_norm_le dimension order kernel jet.val
  refine ⟨bound, ?_⟩
  intro operator specification
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro jet
  change ‖(operator jet).val‖ ≤ 1 * ‖jet‖
  rw [specification.1 jet, one_mul]
  exact bound jet

end Grad.Mollifier.WeakJets
