import WeightedJetInterface

noncomputable section

open MeasureTheory Grad.PDEBootstrap
open Grad.GenericCarriers (PhysicalValue FieldL2)
open scoped BigOperators ContDiff

namespace Grad.WeightedJets

theorem degree_le {order : ℕ} (index : JetIndex order) : degree index ≤ order := index.property

theorem degree_zero (order : ℕ) : degree (zeroIndex order) = 0 := rfl

theorem coordinate_apply (dimension order : ℕ) (domain : Set Spatial) (index : JetIndex order)
    (tuple : JetTuple dimension order domain) : coordinate dimension order domain index tuple = tuple index := rfl

theorem ambientBase_apply (dimension order : ℕ) (domain : Set Spatial) (exponent : JetIndex order → ℕ)
    (tuple : JetTuple dimension order domain) :
    ambientBase dimension order domain exponent tuple =
      Grad.CellWeights.inverseFieldCLM dimension domain (exponent (zeroIndex order)) (tuple (zeroIndex order)) := rfl

theorem base_apply (dimension order : ℕ) (domain : Set Spatial) (exponent : JetIndex order → ℕ)
    (jet : WJet dimension order domain exponent) :
    base dimension order domain exponent jet =
      Grad.CellWeights.inverseFieldCLM dimension domain (exponent (zeroIndex order)) (jet.val (zeroIndex order)) := rfl

theorem testPairing_apply (dimension : ℕ) (domain : Set Spatial) (cell : ℤ)
    (vector : PhysicalValue dimension) (test : TestFunction domain) (field : FieldL2 dimension domain) :
    testPairing dimension domain cell vector test field =
      ∫ point in domain, test.toFun point • inner ℂ vector (field point cell) :=
  Grad.WeakTesting.compactPairing_apply dimension domain cell vector test.toFun test.smooth test.compact field

theorem derivativeTestPairing_apply (dimension order : ℕ) (domain : Set Spatial) (index : JetIndex order)
    (cell : ℤ) (vector : PhysicalValue dimension) (test : TestFunction domain) (field : FieldL2 dimension domain) :
    derivativeTestPairing dimension order domain index cell vector test field =
      ∫ point in domain,
        Grad.WeakTesting.orderedTestDerivative (degree index) (derivativeWord index) test.toFun point •
          inner ℂ vector (field point cell) :=
  Grad.WeakTesting.orderedDerivativePairing_apply dimension domain cell vector test.toFun test.smooth
    test.compact (degree index) (derivativeWord index) field

theorem jetGraph_mem (dimension order : ℕ) (domain : Set Spatial) (exponent : JetIndex order → ℕ)
    (tuple : JetTuple dimension order domain) :
    tuple ∈ jetGraph dimension order domain exponent ↔
      ∀ (index : JetIndex order) (cell : ℤ) (vector : PhysicalValue dimension) (test : TestFunction domain),
        testPairing dimension domain cell vector test (tuple index) =
          ((-1 : ℂ) ^ degree index * Grad.CellWeights.positiveFactor (exponent index) cell) *
            derivativeTestPairing dimension order domain index cell vector test
              (ambientBase dimension order domain exponent tuple) := by
  simp only [jetGraph, Submodule.mem_iInf, LinearMap.mem_ker]
  change (∀ index cell vector test,
    testPairing dimension domain cell vector test (tuple index) -
      ((-1 : ℂ) ^ degree index * Grad.CellWeights.positiveFactor (exponent index) cell) *
        derivativeTestPairing dimension order domain index cell vector test
          (ambientBase dimension order domain exponent tuple) = 0) ↔ _
  simp only [sub_eq_zero]

theorem jetGraph_closed (dimension order : ℕ) (domain : Set Spatial) (exponent : JetIndex order → ℕ) :
    IsClosed (jetGraph dimension order domain exponent : Set (JetTuple dimension order domain)) := by
  simp only [jetGraph, Submodule.coe_iInf]
  exact isClosed_iInter (fun index => isClosed_iInter (fun cell => isClosed_iInter (fun vector =>
    isClosed_iInter (fun test => (residual dimension order domain exponent index cell vector test).isClosed_ker))))

instance jetComplete (dimension order : ℕ) (domain : Set Spatial) (exponent : JetIndex order → ℕ) :
    CompleteSpace (WJet dimension order domain exponent) :=
  (jetGraph_closed dimension order domain exponent).completeSpace_coe

theorem jet_completeSeparable (dimension order : ℕ) (domain : Set Spatial) (exponent : JetIndex order → ℕ) :
    Grad.GenericCarriers.CompleteSeparable (WJet dimension order domain exponent) :=
  ⟨inferInstance, inferInstance, inferInstance⟩

theorem tuple_norm_sq (dimension order : ℕ) (domain : Set Spatial) (tuple : JetTuple dimension order domain) :
    ‖tuple‖ ^ 2 = ∑ index, ‖tuple index‖ ^ 2 :=
  PiLp.norm_sq_eq_of_L2 (fun _ : JetIndex order => FieldL2 dimension domain) tuple

theorem jet_norm_sq (dimension order : ℕ) (domain : Set Spatial) (exponent : JetIndex order → ℕ)
    (jet : WJet dimension order domain exponent) : ‖jet‖ ^ 2 = ∑ index, ‖jet.val index‖ ^ 2 :=
  tuple_norm_sq dimension order domain jet.val

theorem jet_eq {dimension order : ℕ} {domain : Set Spatial} {exponent : JetIndex order → ℕ}
    {first second : WJet dimension order domain exponent}
    (equality : ∀ index, first.val index = second.val index) : first = second :=
  Subtype.ext (PiLp.ext equality)

theorem jet_identity (dimension order : ℕ) (domain : Set Spatial) (exponent : JetIndex order → ℕ)
    (jet : WJet dimension order domain exponent) (index : JetIndex order) (cell : ℤ)
    (vector : PhysicalValue dimension) (test : TestFunction domain) :
    testPairing dimension domain cell vector test (jet.val index) =
      ((-1 : ℂ) ^ degree index * Grad.CellWeights.positiveFactor (exponent index) cell) *
        derivativeTestPairing dimension order domain index cell vector test (base dimension order domain exponent jet) :=
  (jetGraph_mem dimension order domain exponent jet.val).mp jet.property index cell vector test

def ofCoordinates (dimension order : ℕ) (domain : Set Spatial) (exponent : JetIndex order → ℕ)
    (fields : JetIndex order → FieldL2 dimension domain)
    (identities : ∀ (index : JetIndex order) (cell : ℤ) (vector : PhysicalValue dimension) (test : TestFunction domain),
      testPairing dimension domain cell vector test (fields index) =
        ((-1 : ℂ) ^ degree index * Grad.CellWeights.positiveFactor (exponent index) cell) *
          derivativeTestPairing dimension order domain index cell vector test
            (Grad.CellWeights.inverseFieldCLM dimension domain (exponent (zeroIndex order)) (fields (zeroIndex order)))) :
    WJet dimension order domain exponent :=
  ⟨WithLp.toLp 2 fields, (jetGraph_mem dimension order domain exponent _).mpr identities⟩

theorem ofCoordinates_apply (dimension order : ℕ) (domain : Set Spatial) (exponent : JetIndex order → ℕ)
    (fields : JetIndex order → FieldL2 dimension domain) (identities) (index : JetIndex order) :
    (ofCoordinates dimension order domain exponent fields identities).val index = fields index := rfl

theorem base_norm_le (dimension order : ℕ) (domain : Set Spatial) (exponent : JetIndex order → ℕ)
    (jet : WJet dimension order domain exponent) : ‖base dimension order domain exponent jet‖ ≤ ‖jet‖ := by
  rw [base_apply]
  calc
    ‖Grad.CellWeights.inverseFieldCLM dimension domain (exponent (zeroIndex order)) (jet.val (zeroIndex order))‖ ≤
        ‖Grad.CellWeights.inverseFieldCLM dimension domain (exponent (zeroIndex order))‖ * ‖jet.val (zeroIndex order)‖ :=
      ContinuousLinearMap.le_opNorm _ _
    _ ≤ 1 * ‖jet.val (zeroIndex order)‖ :=
      mul_le_mul_of_nonneg_right (Grad.CellWeights.inverseFieldCLM_norm_le dimension domain _) (norm_nonneg _)
    _ = ‖jet.val (zeroIndex order)‖ := one_mul _
    _ ≤ ‖jet‖ := PiLp.norm_apply_le jet.val (zeroIndex order)

theorem base_opNorm_le (dimension order : ℕ) (domain : Set Spatial) (exponent : JetIndex order → ℕ) :
    ‖base dimension order domain exponent‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro jet
  simpa only [one_mul] using base_norm_le dimension order domain exponent jet

theorem base_injective (dimension order : ℕ) (domain : Set Spatial) (openDomain : IsOpen domain)
    (exponent : JetIndex order → ℕ) : Function.Injective (base dimension order domain exponent) := by
  intro first second equality
  apply jet_eq
  intro index
  apply Grad.WeakTesting.Separation.equality dimension domain openDomain
  intro cell vector test smooth compact supported
  let testFunction : TestFunction domain := ⟨test, smooth, compact, supported⟩
  change testPairing dimension domain cell vector testFunction (first.val index) =
    testPairing dimension domain cell vector testFunction (second.val index)
  rw [jet_identity, jet_identity, equality]

theorem graph_consumer : GraphGoal := by
  intro dimension order domain exponent
  exact ⟨jetGraph_closed dimension order domain exponent, jetGraph_mem dimension order domain exponent,
    jet_norm_sq dimension order domain exponent⟩

theorem topology_consumer : TopologyGoal := jet_completeSeparable

theorem base_consumer : BaseGoal := by
  intro dimension order domain openDomain exponent
  exact ⟨base_opNorm_le dimension order domain exponent, base_injective dimension order domain openDomain exponent,
    base_apply dimension order domain exponent⟩

theorem integral_consumer : IntegralGoal := by
  intro dimension order domain exponent tuple
  rw [jetGraph_mem]
  simp only [testPairing_apply, derivativeTestPairing_apply]

theorem block_consumer : BlockGoal := ⟨graph_consumer, topology_consumer, base_consumer, integral_consumer⟩

theorem graphGrade_norm_sq (dimension order weight : ℕ) (domain : Set Spatial)
    (jet : GraphGrade dimension order weight domain) : ‖jet‖ ^ 2 = ∑ index, ‖jet.val index‖ ^ 2 :=
  jet_norm_sq dimension order domain (fun _ => weight) jet

theorem mixed_norm_sq (dimension grade : ℕ) (domain : Set Spatial) (jet : Mixed dimension grade domain) :
    ‖jet‖ ^ 2 = ∑ index, ‖jet.val index‖ ^ 2 :=
  jet_norm_sq dimension grade domain (fun index => grade - degree index) jet

theorem graphGrade_base_apply (dimension order weight : ℕ) (domain : Set Spatial)
    (jet : GraphGrade dimension order weight domain) :
    base dimension order domain (fun _ => weight) jet =
      Grad.CellWeights.inverseFieldCLM dimension domain weight (jet.val (zeroIndex order)) := rfl

theorem mixed_base_apply (dimension grade : ℕ) (domain : Set Spatial) (jet : Mixed dimension grade domain) :
    base dimension grade domain (fun index => grade - degree index) jet =
      Grad.CellWeights.inverseFieldCLM dimension domain grade (jet.val (zeroIndex grade)) := by
  rw [base_apply, degree_zero, Nat.sub_zero]

theorem graphGrade_mem (dimension order weight : ℕ) (domain : Set Spatial) (tuple : JetTuple dimension order domain) :
    tuple ∈ jetGraph dimension order domain (fun _ => weight) ↔
      ∀ (index : JetIndex order) (cell : ℤ) (vector : PhysicalValue dimension) (test : TestFunction domain),
        testPairing dimension domain cell vector test (tuple index) =
          ((-1 : ℂ) ^ degree index * Grad.CellWeights.positiveFactor weight cell) *
            derivativeTestPairing dimension order domain index cell vector test
              (Grad.CellWeights.inverseFieldCLM dimension domain weight (tuple (zeroIndex order))) :=
  jetGraph_mem dimension order domain (fun _ => weight) tuple

theorem mixed_mem (dimension grade : ℕ) (domain : Set Spatial) (tuple : JetTuple dimension grade domain) :
    tuple ∈ jetGraph dimension grade domain (fun index => grade - degree index) ↔
      ∀ (index : JetIndex grade) (cell : ℤ) (vector : PhysicalValue dimension) (test : TestFunction domain),
        testPairing dimension domain cell vector test (tuple index) =
          ((-1 : ℂ) ^ degree index * Grad.CellWeights.positiveFactor (grade - degree index) cell) *
            derivativeTestPairing dimension grade domain index cell vector test
              (Grad.CellWeights.inverseFieldCLM dimension domain grade (tuple (zeroIndex grade))) := by
  simpa only [ambientBase_apply, degree_zero, Nat.sub_zero] using
    jetGraph_mem dimension grade domain (fun index => grade - degree index) tuple

end Grad.WeightedJets
