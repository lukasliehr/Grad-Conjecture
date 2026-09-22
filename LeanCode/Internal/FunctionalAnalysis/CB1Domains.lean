import CB1Jets

noncomputable section

open MeasureTheory Grad.PDEBootstrap
open Grad.GenericCarriers (FieldL2)
open Grad.CellWeights Grad.WeightedJets

namespace Grad.CellBinomial

theorem witness : WitnessGoal := by
  intro dimension order power domain field
  constructor
  · constructor
    · rintro ⟨actual⟩
      exact ⟨actual.inDomain, actual.jet, actual.base_eq⟩
    · rintro ⟨membership, jet, equality⟩
      exact ⟨⟨membership, jet, equality⟩⟩
  · constructor
    · rintro ⟨actual⟩
      exact ⟨actual.inDomain, actual.jet, actual.base_eq⟩
    · rintro ⟨membership, jet, equality⟩
      exact ⟨⟨membership, jet, equality⟩⟩

theorem uniqueness : UniquenessGoal := by
  intro dimension order weight domain openDomain field first second firstBase secondBase
  have equality := base_injective dimension order domain openDomain (fun _ => weight)
    (firstBase.trans secondBase.symm)
  exact ⟨equality, congrArg norm equality⟩

theorem derivative_domain : DomainGoal := by
  intro dimension order weight domain _openDomain field
  constructor
  · rintro ⟨jet, rfl⟩ power bound
    exact ⟨derivativeJetOfGrade dimension order weight power domain bound jet⟩
  · intro membership
    let derivatives : (power : Fin (weight + 1)) → DerivativeJet dimension order power.val domain field :=
      fun power => Classical.choice (membership power.val (by omega))
    let lambda := lambdaJetOfDerivatives dimension order weight domain field derivatives
    exact ⟨weightedJetOfLambda dimension order weight domain field lambda,
      weightedJetOfLambda_base dimension order weight domain field lambda⟩

theorem lambda_domain : LambdaDomainGoal := by
  intro dimension order weight domain _openDomain field
  constructor
  · rintro ⟨jet, rfl⟩
    exact ⟨lambdaJetOfGrade dimension order weight domain jet⟩
  · rintro ⟨lambda⟩
    exact ⟨weightedJetOfLambda dimension order weight domain field lambda,
      weightedJetOfLambda_base dimension order weight domain field lambda⟩

theorem equality : EqualityGoal := by
  intro dimension order weight domain openDomain field weighted baseEquality lambda derivatives
  subst field
  constructor
  · have actualEquality := operatorJet_jet_unique dimension order domain openDomain (positiveFactor weight)
      _ lambda (lambdaJetOfGrade dimension order weight domain weighted)
    exact (congrArg Subtype.val actualEquality).trans (lambdaJetOfGrade_tuple dimension order weight domain weighted)
  · intro power index
    have actualEquality := operatorJet_jet_unique dimension order domain openDomain (derivativeFactor power.val)
      _ (derivatives power) (derivativeJetOfGrade dimension order weight power.val domain (by omega) weighted)
    rw [actualEquality]
    have graph := derivativeJetOfGrade_coordinate_graph dimension order weight power.val domain
      (by omega) weighted index
    constructor
    · rw [fieldOperator_graph]
      exact graph
    · exact fieldGraph_ae dimension domain (derivativeFactor power.val) _ _ graph

theorem allCell : AllCellGoal := by
  intro dimension order domain openDomain field
  constructor
  · intro membership power
    exact (derivative_domain dimension order power domain openDomain field).mp (membership power) power le_rfl
  · intro derivatives weight
    exact (derivative_domain dimension order weight domain openDomain field).mpr
      (fun power _bound => derivatives power)

end Grad.CellBinomial
