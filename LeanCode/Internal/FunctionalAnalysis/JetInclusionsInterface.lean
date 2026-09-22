import WeightedJetProof

noncomputable section

open MeasureTheory Grad.PDEBootstrap
open Grad.GenericCarriers (PhysicalValue FieldL2)
open scoped BigOperators ContDiff

namespace Grad.WeightedJets.Inclusions

def indexInclusion {lower higher : ℕ} (bound : lower ≤ higher) (index : JetIndex lower) : JetIndex higher :=
  ⟨index.val, index.property.trans bound⟩

def shiftedTuple (dimension lower higher : ℕ) (domain : Set Spatial) (gap : ℕ) (bound : lower ≤ higher)
    (tuple : JetTuple dimension higher domain) : JetTuple dimension lower domain :=
  WithLp.toLp 2 (fun index => Grad.CellWeights.inverseFieldCLM dimension domain gap (tuple (indexInclusion bound index)))

def Compatible {lower higher : ℕ} (bound : lower ≤ higher) (gap : ℕ)
    (source : JetIndex higher → ℕ) (target : JetIndex lower → ℕ) : Prop :=
  ∀ index, target index + gap = source (indexInclusion bound index)

def InclusionSpec (dimension lower higher : ℕ) (domain : Set Spatial) (gap : ℕ) (bound : lower ≤ higher)
    (source : JetIndex higher → ℕ) (target : JetIndex lower → ℕ)
    (inclusion : WJet dimension higher domain source →L[ℂ] WJet dimension lower domain target) : Prop :=
  ‖inclusion‖ ≤ 1 ∧
  Function.Injective inclusion ∧
  (∀ jet : WJet dimension higher domain source,
    (inclusion jet).val = shiftedTuple dimension lower higher domain gap bound jet.val) ∧
  (∀ jet : WJet dimension higher domain source,
    base dimension lower domain target (inclusion jet) = base dimension higher domain source jet)

def GeneralGoal : Prop :=
  ∀ (dimension lower higher : ℕ) (domain : Set Spatial), IsOpen domain →
    ∀ (gap : ℕ) (bound : lower ≤ higher) (source : JetIndex higher → ℕ) (target : JetIndex lower → ℕ),
      Compatible bound gap source target →
        ∃ inclusion : WJet dimension higher domain source →L[ℂ] WJet dimension lower domain target,
          InclusionSpec dimension lower higher domain gap bound source target inclusion

def ConstantGradeGoal : Prop :=
  ∀ (dimension lower higher lowWeight highWeight : ℕ) (domain : Set Spatial), IsOpen domain →
    ∀ (orderBound : lower ≤ higher), lowWeight ≤ highWeight →
      ∃ inclusion : GraphGrade dimension higher highWeight domain →L[ℂ] GraphGrade dimension lower lowWeight domain,
        InclusionSpec dimension lower higher domain (highWeight - lowWeight) orderBound
          (fun _ => highWeight) (fun _ => lowWeight) inclusion

def MixedGradeGoal : Prop :=
  ∀ (dimension lower higher : ℕ) (domain : Set Spatial), IsOpen domain →
    ∀ bound : lower ≤ higher,
      ∃ inclusion : Mixed dimension higher domain →L[ℂ] Mixed dimension lower domain,
        InclusionSpec dimension lower higher domain (higher - lower) bound
          (fun index => higher - degree index) (fun index => lower - degree index) inclusion

def BlockGoal : Prop := GeneralGoal ∧ ConstantGradeGoal ∧ MixedGradeGoal

end Grad.WeightedJets.Inclusions
