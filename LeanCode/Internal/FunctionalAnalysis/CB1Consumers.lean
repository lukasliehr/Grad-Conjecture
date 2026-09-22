import CB1Proof

noncomputable section

open MeasureTheory Grad.PDEBootstrap
open Grad.GenericCarriers (FieldL2 PhysicalValue)
open Grad.CellWeights Grad.WeightedJets
open scoped BigOperators

namespace Grad.CellBinomial

theorem membershipConsumer (dimension order weight : ℕ) (domain : Set Spatial)
    (openDomain : IsOpen domain) (field : FieldL2 dimension domain) :
    (∃ jet : GraphGrade dimension order weight domain,
      base dimension order domain (fun _ => weight) jet = field) ↔
    ∀ power : ℕ, power ≤ weight →
      ∃ membership : field ∈ (fieldOperator dimension domain (derivativeFactor power)).domain,
        ∃ jet : GraphGrade dimension order 0 domain,
          base dimension order domain (fun _ => 0) jet =
            fieldOperator dimension domain (derivativeFactor power) ⟨field, membership⟩ := by
  change InGrade dimension order weight domain field ↔ _
  rw [derivative_domain dimension order weight domain openDomain field]
  apply forall_congr'
  intro power
  exact imp_congr_right (fun _bound => (witness dimension order power domain field).1)

theorem normConsumer (dimension order weight : ℕ) (domain : Set Spatial)
    (openDomain : IsOpen domain) (field : FieldL2 dimension domain)
    (weighted : GraphGrade dimension order weight domain)
    (weightedBase : base dimension order domain (fun _ => weight) weighted = field)
    (lambdaDomain : field ∈ (fieldOperator dimension domain (positiveFactor weight)).domain)
    (lambdaJet : GraphGrade dimension order 0 domain)
    (lambdaBase : base dimension order domain (fun _ => 0) lambdaJet =
      fieldOperator dimension domain (positiveFactor weight) ⟨field, lambdaDomain⟩)
    (derivativeDomains : ∀ power : Fin (weight + 1),
      field ∈ (fieldOperator dimension domain (derivativeFactor power.val)).domain)
    (derivativeJets : Fin (weight + 1) → GraphGrade dimension order 0 domain)
    (derivativeBases : ∀ power : Fin (weight + 1),
      base dimension order domain (fun _ => 0) (derivativeJets power) =
        fieldOperator dimension domain (derivativeFactor power.val) ⟨field, derivativeDomains power⟩) :
    ‖weighted‖ ^ 2 = ‖lambdaJet‖ ^ 2 ∧
      ‖lambdaJet‖ ^ 2 = ∑ power : Fin (weight + 1),
        (weight.choose power.val : ℝ) * ‖derivativeJets power‖ ^ 2 :=
  normIdentity dimension order weight domain openDomain field weighted weightedBase
    ⟨lambdaDomain, lambdaJet, lambdaBase⟩
    (fun power => ⟨derivativeDomains power, derivativeJets power, derivativeBases power⟩)

theorem coordinateConsumer (dimension order weight : ℕ) (domain : Set Spatial)
    (openDomain : IsOpen domain) (field : FieldL2 dimension domain)
    (weighted : GraphGrade dimension order weight domain)
    (weightedBase : base dimension order domain (fun _ => weight) weighted = field)
    (lambda : LambdaJet dimension order weight domain field)
    (derivatives : (power : Fin (weight + 1)) → DerivativeJet dimension order power.val domain field)
    (power : Fin (weight + 1)) (index : JetIndex order) :
    ∀ᵐ point ∂volume.restrict domain, ∀ (cell : ℤ) (physical : Fin dimension),
      (derivatives power).jet.val index point cell physical =
        derivativeFactor power.val cell *
          Realization.recoveredDerivative dimension order domain (fun _ => weight) index weighted point cell physical := by
  filter_upwards [((equality dimension order weight domain openDomain field weighted weightedBase
    lambda derivatives).2 power index).2] with point coordinates
  intro cell physical
  exact congrArg (fun value : PhysicalValue dimension => value physical) (coordinates cell)

theorem allCellConsumer (dimension order : ℕ) (domain : Set Spatial) (openDomain : IsOpen domain)
    (field : FieldL2 dimension domain) :
    (∀ weight : ℕ, ∃ jet : GraphGrade dimension order weight domain,
      base dimension order domain (fun _ => weight) jet = field) ↔
    ∀ power : ℕ,
      ∃ membership : field ∈ (fieldOperator dimension domain (derivativeFactor power)).domain,
        ∃ jet : GraphGrade dimension order 0 domain,
          base dimension order domain (fun _ => 0) jet =
            fieldOperator dimension domain (derivativeFactor power) ⟨field, membership⟩ := by
  change AllCell dimension order domain field ↔ _
  rw [allCell dimension order domain openDomain field]
  exact forall_congr' (fun power => (witness dimension order power domain field).1)

theorem zeroConsumer : ZeroGoal := zero

theorem zeroDimensionConsumer (order weight : ℕ) (domain : Set Spatial) (openDomain : IsOpen domain)
    (field : FieldL2 0 domain) : InGrade 0 order weight domain field ↔
      ∀ power : ℕ, power ≤ weight → HasCellDerivative 0 order power domain field :=
  derivative_domain 0 order weight domain openDomain field

theorem blockConsumer : BlockGoal := block

end Grad.CellBinomial
