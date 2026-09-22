import JRInterface

noncomputable section

open MeasureTheory Grad.PDEBootstrap
open Grad.GenericCarriers (PhysicalValue FieldL2 fieldCellProjection)
open scoped BigOperators ContDiff

namespace Grad.WeightedJets.Realization

theorem recoveredDerivative_apply (dimension order : ℕ) (domain : Set Spatial)
    (exponent : JetIndex order → ℕ) (index : JetIndex order)
    (jet : WJet dimension order domain exponent) :
    recoveredDerivative dimension order domain exponent index jet =
      Grad.CellWeights.inverseFieldCLM dimension domain (exponent index) (jet.val index) := rfl

theorem recoveredDerivative_norm_le (dimension order : ℕ) (domain : Set Spatial)
    (exponent : JetIndex order → ℕ) (index : JetIndex order)
    (jet : WJet dimension order domain exponent) :
    ‖recoveredDerivative dimension order domain exponent index jet‖ ≤ ‖jet‖ :=
  (Inclusions.inverse_norm_le dimension domain (exponent index) (jet.val index)).trans
    (PiLp.norm_apply_le jet.val index)

theorem recoveredDerivative_opNorm_le (dimension order : ℕ) (domain : Set Spatial)
    (exponent : JetIndex order → ℕ) (index : JetIndex order) :
    ‖recoveredDerivative dimension order domain exponent index‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro jet
  simpa only [one_mul] using recoveredDerivative_norm_le dimension order domain exponent index jet

theorem recoveredDerivative_zero (dimension order : ℕ) (domain : Set Spatial)
    (exponent : JetIndex order → ℕ) :
    recoveredDerivative dimension order domain exponent (zeroIndex order) =
      base dimension order domain exponent := rfl

theorem recoveredDerivative_coordinates (dimension order : ℕ) (domain : Set Spatial)
    (exponent : JetIndex order → ℕ) (index : JetIndex order)
    (jet : WJet dimension order domain exponent) :
    ∀ᵐ point ∂volume.restrict domain, ∀ cell : ℤ,
      recoveredDerivative dimension order domain exponent index jet point cell =
        Grad.CellWeights.inverseFactor (exponent index) cell • jet.val index point cell :=
  Grad.CellWeights.inverseFieldCLM_coordinate dimension domain (exponent index) (jet.val index)

theorem inverse_positiveFactor (power : ℕ) (cell : ℤ) :
    Grad.CellWeights.inverseFactor power cell * Grad.CellWeights.positiveFactor power cell = 1 := by
  simpa only [Nat.zero_add, Grad.CellWeights.positiveFactor, pow_zero] using
    Inclusions.inverseFactor_positiveFactor 0 power cell

theorem recoveredDerivative_weak (dimension order : ℕ) (domain : Set Spatial)
    (exponent : JetIndex order → ℕ) (index : JetIndex order)
    (jet : WJet dimension order domain exponent) (cell : ℤ)
    (vector : PhysicalValue dimension) (test : TestFunction domain) :
    testPairing dimension domain cell vector test
        (recoveredDerivative dimension order domain exponent index jet) =
      (-1 : ℂ) ^ degree index * derivativeTestPairing dimension order domain index cell vector test
        (base dimension order domain exponent jet) := by
  rw [recoveredDerivative_apply, Inclusions.testPairing_inverse, jet_identity]
  calc
    _ = (-1 : ℂ) ^ degree index *
        (Grad.CellWeights.inverseFactor (exponent index) cell *
          Grad.CellWeights.positiveFactor (exponent index) cell) *
        derivativeTestPairing dimension order domain index cell vector test
          (base dimension order domain exponent jet) := by ring
    _ = _ := by rw [inverse_positiveFactor, mul_one]

theorem recoveredDerivative_integral (dimension order : ℕ) (domain : Set Spatial)
    (exponent : JetIndex order → ℕ) (index : JetIndex order)
    (jet : WJet dimension order domain exponent) (cell : ℤ)
    (vector : PhysicalValue dimension) (test : TestFunction domain) :
    (∫ point in domain, test.toFun point •
      inner ℂ vector (recoveredDerivative dimension order domain exponent index jet point cell)) =
      (-1 : ℂ) ^ degree index * ∫ point in domain,
        Grad.WeakTesting.orderedTestDerivative (degree index) (derivativeWord index) test.toFun point •
          inner ℂ vector (base dimension order domain exponent jet point cell) := by
  simpa only [testPairing_apply, derivativeTestPairing_apply] using
    recoveredDerivative_weak dimension order domain exponent index jet cell vector test

theorem recoveredDerivative_positive_coordinates (dimension order : ℕ) (domain : Set Spatial)
    (exponent : JetIndex order → ℕ) (index : JetIndex order)
    (jet : WJet dimension order domain exponent) :
    ∀ᵐ point ∂volume.restrict domain, ∀ cell : ℤ,
      jet.val index point cell = Grad.CellWeights.positiveFactor (exponent index) cell •
        recoveredDerivative dimension order domain exponent index jet point cell := by
  filter_upwards [recoveredDerivative_coordinates dimension order domain exponent index jet] with point coordinates
  intro cell
  rw [coordinates cell, smul_smul, mul_comm, inverse_positiveFactor, one_smul]

theorem recoveredDerivative_fieldGraph (dimension order : ℕ) (domain : Set Spatial)
    (exponent : JetIndex order → ℕ) (index : JetIndex order)
    (jet : WJet dimension order domain exponent) :
    (recoveredDerivative dimension order domain exponent index jet, jet.val index) ∈
      Grad.CellWeights.fieldGraph dimension domain (Grad.CellWeights.positiveFactor (exponent index)) := by
  apply (Grad.CellWeights.fieldGraph_mem dimension domain _ _ _).mpr
  intro cell
  apply Lp.ext
  filter_upwards [recoveredDerivative_positive_coordinates dimension order domain exponent index jet,
    Grad.GenericCarriers.fieldCellProjection_ae dimension domain (jet.val index),
    Grad.GenericCarriers.fieldCellProjection_ae dimension domain
      (recoveredDerivative dimension order domain exponent index jet),
    Lp.coeFn_smul (Grad.CellWeights.positiveFactor (exponent index) cell)
      (fieldCellProjection dimension domain cell (recoveredDerivative dimension order domain exponent index jet))]
    with point positive stored recovered scalar
  rw [scalar]
  change fieldCellProjection dimension domain cell (jet.val index) point =
    Grad.CellWeights.positiveFactor (exponent index) cell •
      fieldCellProjection dimension domain cell
        (recoveredDerivative dimension order domain exponent index jet) point
  rw [stored cell, recovered cell]
  exact positive cell

theorem recoveredDerivative_operatorGraph (dimension order : ℕ) (domain : Set Spatial)
    (exponent : JetIndex order → ℕ) (index : JetIndex order)
    (jet : WJet dimension order domain exponent) :
    (recoveredDerivative dimension order domain exponent index jet, jet.val index) ∈
      (Grad.CellWeights.fieldOperator dimension domain
        (Grad.CellWeights.positiveFactor (exponent index))).graph := by
  rw [Grad.CellWeights.fieldOperator_graph]
  exact recoveredDerivative_fieldGraph dimension order domain exponent index jet

theorem recoveredDerivative_mem_domain (dimension order : ℕ) (domain : Set Spatial)
    (exponent : JetIndex order → ℕ) (index : JetIndex order)
    (jet : WJet dimension order domain exponent) :
    recoveredDerivative dimension order domain exponent index jet ∈
      (Grad.CellWeights.fieldOperator dimension domain
        (Grad.CellWeights.positiveFactor (exponent index))).domain := by
  apply (Grad.CellWeights.fieldOperator_domain dimension domain _ _).mpr
  exact ⟨jet.val index, (Grad.CellWeights.fieldGraph_mem dimension domain _ _ _).mp
    (recoveredDerivative_fieldGraph dimension order domain exponent index jet)⟩

theorem recoveredDerivative_operator_apply (dimension order : ℕ) (domain : Set Spatial)
    (exponent : JetIndex order → ℕ) (index : JetIndex order)
    (jet : WJet dimension order domain exponent)
    (membership : recoveredDerivative dimension order domain exponent index jet ∈
      (Grad.CellWeights.fieldOperator dimension domain
        (Grad.CellWeights.positiveFactor (exponent index))).domain) :
    Grad.CellWeights.fieldOperator dimension domain (Grad.CellWeights.positiveFactor (exponent index))
      ⟨recoveredDerivative dimension order domain exponent index jet, membership⟩ = jet.val index := by
  apply Grad.CellWeights.fieldGraph_unique dimension domain (Grad.CellWeights.positiveFactor (exponent index))
    (first := recoveredDerivative dimension order domain exponent index jet)
  · rw [← Grad.CellWeights.fieldOperator_graph]
    exact LinearPMap.mem_graph
      (Grad.CellWeights.fieldOperator dimension domain (Grad.CellWeights.positiveFactor (exponent index)))
      ⟨recoveredDerivative dimension order domain exponent index jet, membership⟩
  · exact recoveredDerivative_fieldGraph dimension order domain exponent index jet

theorem recoveredDerivative_inclusion_apply (dimension lower higher : ℕ) (domain : Set Spatial)
    (gap : ℕ) (bound : lower ≤ higher) (source : JetIndex higher → ℕ) (target : JetIndex lower → ℕ)
    (compatible : Inclusions.Compatible bound gap source target) (index : JetIndex lower)
    (jet : WJet dimension higher domain source) :
    recoveredDerivative dimension lower domain target index
        (Inclusions.inclusion dimension lower higher domain gap bound source target compatible jet) =
      recoveredDerivative dimension higher domain source (Inclusions.indexInclusion bound index) jet := by
  have composition := congrArg (fun mapping : FieldL2 dimension domain →L[ℂ] FieldL2 dimension domain =>
    mapping (jet.val (Inclusions.indexInclusion bound index)))
    (Grad.CellWeights.inverseFieldCLM_comp dimension domain (target index) gap)
  change Grad.CellWeights.inverseFieldCLM dimension domain (target index)
    (Grad.CellWeights.inverseFieldCLM dimension domain gap (jet.val (Inclusions.indexInclusion bound index))) =
      Grad.CellWeights.inverseFieldCLM dimension domain (source (Inclusions.indexInclusion bound index))
        (jet.val (Inclusions.indexInclusion bound index))
  simpa only [ContinuousLinearMap.comp_apply, compatible index] using composition

theorem recoveredDerivative_inclusion (dimension lower higher : ℕ) (domain : Set Spatial)
    (gap : ℕ) (bound : lower ≤ higher) (source : JetIndex higher → ℕ) (target : JetIndex lower → ℕ)
    (compatible : Inclusions.Compatible bound gap source target) (index : JetIndex lower) :
    (recoveredDerivative dimension lower domain target index).comp
        (Inclusions.inclusion dimension lower higher domain gap bound source target compatible) =
      recoveredDerivative dimension higher domain source (Inclusions.indexInclusion bound index) := by
  apply ContinuousLinearMap.ext
  intro jet
  exact recoveredDerivative_inclusion_apply dimension lower higher domain gap bound source target compatible index jet

end Grad.WeightedJets.Realization
