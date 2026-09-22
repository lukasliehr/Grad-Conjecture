import JRProof

noncomputable section

open MeasureTheory Grad.PDEBootstrap
open Grad.GenericCarriers (FieldL2)
open Grad.WeightedJets (GraphGrade JetIndex base)
open scoped BigOperators

namespace Grad.CellBinomial

abbrev derivativeOperator (dimension : ℕ) (domain : Set Spatial) (power : ℕ) :=
  Grad.CellWeights.fieldOperator dimension domain (Grad.CellWeights.derivativeFactor power)

abbrev lambdaOperator (dimension : ℕ) (domain : Set Spatial) (power : ℕ) :=
  Grad.CellWeights.fieldOperator dimension domain (Grad.CellWeights.positiveFactor power)

def InGrade (dimension order weight : ℕ) (domain : Set Spatial)
    (field : FieldL2 dimension domain) : Prop :=
  ∃ jet : GraphGrade dimension order weight domain,
    base dimension order domain (fun _ => weight) jet = field

structure OperatorJet (dimension order : ℕ) (domain : Set Spatial) (factor : ℤ → ℂ)
    (field : FieldL2 dimension domain) where
  inDomain : field ∈ (Grad.CellWeights.fieldOperator dimension domain factor).domain
  jet : GraphGrade dimension order 0 domain
  base_eq : base dimension order domain (fun _ => 0) jet =
    Grad.CellWeights.fieldOperator dimension domain factor ⟨field, inDomain⟩

abbrev DerivativeJet (dimension order power : ℕ) (domain : Set Spatial)
    (field : FieldL2 dimension domain) :=
  OperatorJet dimension order domain (Grad.CellWeights.derivativeFactor power) field

abbrev LambdaJet (dimension order power : ℕ) (domain : Set Spatial)
    (field : FieldL2 dimension domain) :=
  OperatorJet dimension order domain (Grad.CellWeights.positiveFactor power) field

def HasCellDerivative (dimension order power : ℕ) (domain : Set Spatial)
    (field : FieldL2 dimension domain) : Prop :=
  Nonempty (DerivativeJet dimension order power domain field)

def AllCell (dimension order : ℕ) (domain : Set Spatial)
    (field : FieldL2 dimension domain) : Prop :=
  ∀ weight : ℕ, InGrade dimension order weight domain field

def derivativeRatio (weight power : ℕ) (cell : ℤ) : ℂ :=
  Grad.CellWeights.derivativeFactor power cell * Grad.CellWeights.inverseFactor weight cell

def ScalarGoal : Prop :=
  ∀ (weight : ℕ) (cell : ℤ),
    Grad.CellWeights.cellWeight cell ^ (2 * weight) = (1 + (cell : ℝ) ^ 2) ^ weight ∧
    ‖Grad.CellWeights.positiveFactor weight cell‖ ^ 2 =
      ∑ power : Fin (weight + 1), (weight.choose power.val : ℝ) *
        ‖Grad.CellWeights.derivativeFactor power.val cell‖ ^ 2 ∧
    (∀ power : ℕ, ‖Grad.CellWeights.derivativeFactor power cell‖ = |(cell : ℝ)| ^ power) ∧
    (∀ power : ℕ, power ≤ weight → ‖derivativeRatio weight power cell‖ ≤ 1) ∧
    (∑ power : Fin (weight + 1), (weight.choose power.val : ℂ) *
      star (derivativeRatio weight power.val cell) *
        Grad.CellWeights.derivativeFactor power.val cell) =
      Grad.CellWeights.positiveFactor weight cell

def WitnessGoal : Prop :=
  ∀ (dimension order power : ℕ) (domain : Set Spatial) (field : FieldL2 dimension domain),
    (HasCellDerivative dimension order power domain field ↔
      ∃ membership : field ∈ (derivativeOperator dimension domain power).domain,
        InGrade dimension order 0 domain
          (derivativeOperator dimension domain power ⟨field, membership⟩)) ∧
    (Nonempty (LambdaJet dimension order power domain field) ↔
      ∃ membership : field ∈ (lambdaOperator dimension domain power).domain,
        InGrade dimension order 0 domain
          (lambdaOperator dimension domain power ⟨field, membership⟩))

def UniquenessGoal : Prop :=
  ∀ (dimension order weight : ℕ) (domain : Set Spatial), IsOpen domain →
    ∀ (field : FieldL2 dimension domain) (first second : GraphGrade dimension order weight domain),
      base dimension order domain (fun _ => weight) first = field →
      base dimension order domain (fun _ => weight) second = field →
      first = second ∧ ‖first‖ = ‖second‖

def DomainGoal : Prop :=
  ∀ (dimension order weight : ℕ) (domain : Set Spatial), IsOpen domain →
    ∀ field : FieldL2 dimension domain,
      InGrade dimension order weight domain field ↔
        ∀ power : ℕ, power ≤ weight → HasCellDerivative dimension order power domain field

def LambdaDomainGoal : Prop :=
  ∀ (dimension order weight : ℕ) (domain : Set Spatial), IsOpen domain →
    ∀ field : FieldL2 dimension domain,
      InGrade dimension order weight domain field ↔
        Nonempty (LambdaJet dimension order weight domain field)

def EqualityGoal : Prop :=
  ∀ (dimension order weight : ℕ) (domain : Set Spatial), IsOpen domain →
    ∀ (field : FieldL2 dimension domain) (weighted : GraphGrade dimension order weight domain),
      base dimension order domain (fun _ => weight) weighted = field →
      ∀ (lambda : LambdaJet dimension order weight domain field)
        (derivatives : (power : Fin (weight + 1)) →
          DerivativeJet dimension order power.val domain field),
        lambda.jet.val = weighted.val ∧
        ∀ (power : Fin (weight + 1)) (index : JetIndex order),
          (Grad.WeightedJets.Realization.recoveredDerivative dimension order domain
              (fun _ => weight) index weighted, (derivatives power).jet.val index) ∈
            (derivativeOperator dimension domain power.val).graph ∧
          (∀ᵐ point ∂volume.restrict domain, ∀ cell : ℤ,
            (derivatives power).jet.val index point cell =
              Grad.CellWeights.derivativeFactor power.val cell •
                Grad.WeightedJets.Realization.recoveredDerivative dimension order domain
                  (fun _ => weight) index weighted point cell)

def NormGoal : Prop :=
  ∀ (dimension order weight : ℕ) (domain : Set Spatial), IsOpen domain →
    ∀ (field : FieldL2 dimension domain) (weighted : GraphGrade dimension order weight domain),
      base dimension order domain (fun _ => weight) weighted = field →
      ∀ (lambda : LambdaJet dimension order weight domain field)
        (derivatives : (power : Fin (weight + 1)) →
          DerivativeJet dimension order power.val domain field),
        ‖weighted‖ ^ 2 = ‖lambda.jet‖ ^ 2 ∧
        ‖lambda.jet‖ ^ 2 = ∑ power : Fin (weight + 1),
          (weight.choose power.val : ℝ) * ‖(derivatives power).jet‖ ^ 2

def AllCellGoal : Prop :=
  ∀ (dimension order : ℕ) (domain : Set Spatial), IsOpen domain →
    ∀ field : FieldL2 dimension domain,
      AllCell dimension order domain field ↔
        ∀ power : ℕ, HasCellDerivative dimension order power domain field

def ZeroGoal : Prop :=
  (∀ power : ℕ, Grad.CellWeights.positiveFactor power 0 = 1) ∧
  (∀ cell : ℤ, Grad.CellWeights.derivativeFactor 0 cell = 1) ∧
  (∀ power : ℕ, Grad.CellWeights.derivativeFactor (power + 1) 0 = 0) ∧
  ∀ (dimension : ℕ) (domain : Set Spatial),
    (derivativeOperator dimension domain 0).domain = ⊤ ∧
    (lambdaOperator dimension domain 0).domain = ⊤ ∧
    (∀ (field : FieldL2 dimension domain)
      (membership : field ∈ (derivativeOperator dimension domain 0).domain),
      derivativeOperator dimension domain 0 ⟨field, membership⟩ = field) ∧
    (∀ (field : FieldL2 dimension domain)
      (membership : field ∈ (lambdaOperator dimension domain 0).domain),
      lambdaOperator dimension domain 0 ⟨field, membership⟩ = field)

def BlockGoal : Prop :=
  ScalarGoal ∧ WitnessGoal ∧ UniquenessGoal ∧ DomainGoal ∧ LambdaDomainGoal ∧
    EqualityGoal ∧ NormGoal ∧ AllCellGoal ∧ ZeroGoal

end Grad.CellBinomial
