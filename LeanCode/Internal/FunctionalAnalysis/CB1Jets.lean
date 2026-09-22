import CB1Multipliers

noncomputable section

open MeasureTheory Grad.PDEBootstrap
open Grad.GenericCarriers (FieldL2 fieldCellProjection)
open Grad.CellWeights Grad.WeightedJets
open scoped BigOperators

namespace Grad.CellBinomial

theorem zero_base (dimension order : ℕ) (domain : Set Spatial)
    (jet : GraphGrade dimension order 0 domain) :
    base dimension order domain (fun _ => 0) jet = jet.val (zeroIndex order) := by
  rw [base_apply, inverseFieldCLM_zero, ContinuousLinearMap.id_apply]

theorem zero_identity (dimension order : ℕ) (domain : Set Spatial)
    (jet : GraphGrade dimension order 0 domain) (index : JetIndex order) (cell : ℤ)
    (vector : Grad.GenericCarriers.PhysicalValue dimension) (test : TestFunction domain) :
    testPairing dimension domain cell vector test (jet.val index) =
      (-1 : ℂ) ^ degree index * derivativeTestPairing dimension order domain index cell vector test
        (base dimension order domain (fun _ => 0) jet) := by
  simpa only [positiveFactor, pow_zero, mul_one] using
    jet_identity dimension order domain (fun _ => 0) jet index cell vector test

def mapZeroJet (dimension order : ℕ) (domain : Set Spatial)
    (factor : ℤ → ℂ) (bound : ∀ cell, ‖factor cell‖ ≤ 1)
    (jet : GraphGrade dimension order 0 domain) : GraphGrade dimension order 0 domain :=
  ofCoordinates dimension order domain (fun _ => 0)
    (fun index => contractionFieldCLM dimension domain factor bound (jet.val index)) (by
      intro index cell vector test
      simp only [inverseFieldCLM_zero, ContinuousLinearMap.id_apply, positiveFactor, pow_zero, mul_one]
      rw [testPairing_graph dimension domain factor _ _
        (contractionFieldCLM_graph dimension domain factor bound (jet.val index)),
        zero_identity, ← zero_base dimension order domain jet,
        derivativeTestPairing_graph dimension order domain factor _ _
          (contractionFieldCLM_graph dimension domain factor bound
            (base dimension order domain (fun _ => 0) jet))]
      ring)

theorem mapZeroJet_apply (dimension order : ℕ) (domain : Set Spatial)
    (factor : ℤ → ℂ) (bound : ∀ cell, ‖factor cell‖ ≤ 1)
    (jet : GraphGrade dimension order 0 domain) (index : JetIndex order) :
    (mapZeroJet dimension order domain factor bound jet).val index =
      contractionFieldCLM dimension domain factor bound (jet.val index) := rfl

theorem mapZeroJet_base (dimension order : ℕ) (domain : Set Spatial)
    (factor : ℤ → ℂ) (bound : ∀ cell, ‖factor cell‖ ≤ 1)
    (jet : GraphGrade dimension order 0 domain) :
    base dimension order domain (fun _ => 0) (mapZeroJet dimension order domain factor bound jet) =
      contractionFieldCLM dimension domain factor bound (base dimension order domain (fun _ => 0) jet) := by
  rw [zero_base, zero_base, mapZeroJet_apply]

theorem weighted_zero_graph (dimension order weight : ℕ) (domain : Set Spatial)
    (jet : GraphGrade dimension order weight domain) :
    (base dimension order domain (fun _ => weight) jet, jet.val (zeroIndex order)) ∈
      fieldGraph dimension domain (positiveFactor weight) :=
  Realization.recoveredDerivative_fieldGraph dimension order domain (fun _ => weight) (zeroIndex order) jet

def unweightedJet (dimension order weight : ℕ) (domain : Set Spatial)
    (jet : GraphGrade dimension order weight domain) : GraphGrade dimension order 0 domain :=
  ⟨jet.val, by
    apply (jetGraph_mem dimension order domain (fun _ => 0) jet.val).mpr
    intro index cell vector test
    rw [ambientBase_apply, inverseFieldCLM_zero, ContinuousLinearMap.id_apply,
      derivativeTestPairing_graph dimension order domain (positiveFactor weight) _ _
        (weighted_zero_graph dimension order weight domain jet), jet_identity]
    simp only [positiveFactor, pow_zero, mul_one]
    ring⟩

def lambdaJetOfGrade (dimension order weight : ℕ) (domain : Set Spatial)
    (jet : GraphGrade dimension order weight domain) :
    LambdaJet dimension order weight domain (base dimension order domain (fun _ => weight) jet) :=
  operatorJetOfGraph dimension order domain (positiveFactor weight) _
    (unweightedJet dimension order weight domain jet) (by
      rw [zero_base]
      exact weighted_zero_graph dimension order weight domain jet)

theorem lambdaJetOfGrade_tuple (dimension order weight : ℕ) (domain : Set Spatial)
    (jet : GraphGrade dimension order weight domain) :
    (lambdaJetOfGrade dimension order weight domain jet).jet.val = jet.val := by
  apply PiLp.ext
  intro index
  rfl

theorem inverse_of_positive_graph (dimension : ℕ) (domain : Set Spatial) (weight : ℕ)
    (first second : FieldL2 dimension domain)
    (graph : (first, second) ∈ fieldGraph dimension domain (positiveFactor weight)) :
    inverseFieldCLM dimension domain weight second = first := by
  apply Lp.ext
  filter_upwards [inverseFieldCLM_coordinate dimension domain weight second,
    fieldGraph_ae dimension domain (positiveFactor weight) first second graph] with point inverse positive
  apply lp.ext
  funext cell
  rw [inverse cell, positive cell, smul_smul, Realization.inverse_positiveFactor, one_smul]

def weightedJetOfLambda (dimension order weight : ℕ) (domain : Set Spatial)
    (field : FieldL2 dimension domain) (lambda : LambdaJet dimension order weight domain field) :
    GraphGrade dimension order weight domain :=
  ofCoordinates dimension order domain (fun _ => weight) (fun index => lambda.jet.val index) (by
    intro index cell vector test
    rw [← zero_base dimension order domain lambda.jet,
      inverse_of_positive_graph dimension domain weight field _
        (operatorJet_graph dimension order domain (positiveFactor weight) field lambda),
      zero_identity,
      derivativeTestPairing_graph dimension order domain (positiveFactor weight) _ _
        (operatorJet_graph dimension order domain (positiveFactor weight) field lambda)]
    ring)

theorem weightedJetOfLambda_base (dimension order weight : ℕ) (domain : Set Spatial)
    (field : FieldL2 dimension domain) (lambda : LambdaJet dimension order weight domain field) :
    base dimension order domain (fun _ => weight)
      (weightedJetOfLambda dimension order weight domain field lambda) = field := by
  rw [base_apply]
  change inverseFieldCLM dimension domain weight (lambda.jet.val (zeroIndex order)) = field
  rw [← zero_base]
  exact inverse_of_positive_graph dimension domain weight field _
    (operatorJet_graph dimension order domain (positiveFactor weight) field lambda)

def derivativeJetOfGrade (dimension order weight power : ℕ) (domain : Set Spatial)
    (bound : power ≤ weight) (jet : GraphGrade dimension order weight domain) :
    DerivativeJet dimension order power domain (base dimension order domain (fun _ => weight) jet) :=
  operatorJetOfGraph dimension order domain (derivativeFactor power) _
    (mapZeroJet dimension order domain (derivativeRatio weight power)
      (derivativeRatio_norm_le weight power bound) (unweightedJet dimension order weight domain jet)) (by
        rw [mapZeroJet_base, zero_base]
        change (base dimension order domain (fun _ => weight) jet,
          contractionFieldCLM dimension domain (derivativeRatio weight power)
            (derivativeRatio_norm_le weight power bound) (jet.val (zeroIndex order))) ∈
              fieldGraph dimension domain (derivativeFactor power)
        have composition := fieldGraph_comp dimension domain (positiveFactor weight) (derivativeRatio weight power)
          (weighted_zero_graph dimension order weight domain jet)
          (contractionFieldCLM_graph dimension domain (derivativeRatio weight power)
            (derivativeRatio_norm_le weight power bound) (jet.val (zeroIndex order)))
        simpa only [derivativeRatio_positive] using composition)

theorem derivativeJetOfGrade_apply (dimension order weight power : ℕ) (domain : Set Spatial)
    (bound : power ≤ weight) (jet : GraphGrade dimension order weight domain) (index : JetIndex order) :
    (derivativeJetOfGrade dimension order weight power domain bound jet).jet.val index =
      contractionFieldCLM dimension domain (derivativeRatio weight power)
        (derivativeRatio_norm_le weight power bound) (jet.val index) := rfl

theorem derivativeJetOfGrade_coordinate_graph (dimension order weight power : ℕ) (domain : Set Spatial)
    (bound : power ≤ weight) (jet : GraphGrade dimension order weight domain) (index : JetIndex order) :
    (Realization.recoveredDerivative dimension order domain (fun _ => weight) index jet,
      (derivativeJetOfGrade dimension order weight power domain bound jet).jet.val index) ∈
        fieldGraph dimension domain (derivativeFactor power) := by
  rw [derivativeJetOfGrade_apply]
  have composition := fieldGraph_comp dimension domain (positiveFactor weight) (derivativeRatio weight power)
    (Realization.recoveredDerivative_fieldGraph dimension order domain (fun _ => weight) index jet)
    (contractionFieldCLM_graph dimension domain (derivativeRatio weight power)
      (derivativeRatio_norm_le weight power bound) (jet.val index))
  simpa only [derivativeRatio_positive] using composition

theorem conjugateRatio_bound (weight power : ℕ) (bound : power ≤ weight) (cell : ℤ) :
    ‖star (derivativeRatio weight power cell)‖ ≤ 1 := by
  rw [norm_star]
  exact derivativeRatio_norm_le weight power bound cell

def synthesisJet (dimension order weight : ℕ) (domain : Set Spatial) (field : FieldL2 dimension domain)
    (derivatives : (power : Fin (weight + 1)) → DerivativeJet dimension order power.val domain field) :
    GraphGrade dimension order 0 domain :=
  ∑ power : Fin (weight + 1), (weight.choose power.val : ℂ) •
    mapZeroJet dimension order domain (fun cell => star (derivativeRatio weight power.val cell))
      (conjugateRatio_bound weight power.val (by omega)) (derivatives power).jet

theorem synthesisJet_graph (dimension order weight : ℕ) (domain : Set Spatial)
    (field : FieldL2 dimension domain)
    (derivatives : (power : Fin (weight + 1)) → DerivativeJet dimension order power.val domain field) :
    (field, base dimension order domain (fun _ => 0) (synthesisJet dimension order weight domain field derivatives)) ∈
      fieldGraph dimension domain (positiveFactor weight) := by
  apply (fieldGraph_mem dimension domain _ _ _).mpr
  intro cell
  simp only [synthesisJet, map_sum, map_smul, mapZeroJet_base, contractionFieldCLM_projection]
  have derivativeCoordinates (power : Fin (weight + 1)) :=
    (fieldGraph_mem dimension domain (derivativeFactor power.val) _ _).mp
      (operatorJet_graph dimension order domain (derivativeFactor power.val) field (derivatives power)) cell
  simp only [derivativeCoordinates, smul_smul, ← mul_assoc]
  rw [← Finset.sum_smul, synthesis_identity]

def lambdaJetOfDerivatives (dimension order weight : ℕ) (domain : Set Spatial)
    (field : FieldL2 dimension domain)
    (derivatives : (power : Fin (weight + 1)) → DerivativeJet dimension order power.val domain field) :
    LambdaJet dimension order weight domain field :=
  operatorJetOfGraph dimension order domain (positiveFactor weight) field
    (synthesisJet dimension order weight domain field derivatives)
    (synthesisJet_graph dimension order weight domain field derivatives)

end Grad.CellBinomial
