import JRProof
import CPGProof

noncomputable section

open MeasureTheory Filter Grad.PDEBootstrap
open Grad.GenericCarriers (PhysicalValue FieldL2)
open scoped Topology BigOperators

namespace Grad.WeightedJets.CellCutoff

def fieldCutoff (dimension : ℕ) (domain : Set Spatial) (cells : Finset ℤ) :
    FieldL2 dimension domain →L[ℂ] FieldL2 dimension domain :=
  Grad.CellProjections.Generic.fieldProjection (volume.restrict domain) (PhysicalValue dimension) cells

def cutoffTuple (dimension order : ℕ) (domain : Set Spatial) (cells : Finset ℤ)
    (tuple : JetTuple dimension order domain) : JetTuple dimension order domain :=
  WithLp.toLp 2 (fun index => fieldCutoff dimension domain cells (tuple index))

def FiniteCellJet (dimension order : ℕ) (domain : Set Spatial) (exponent : JetIndex order → ℕ)
    (jet : WJet dimension order domain exponent) : Prop :=
  ∃ cells : Finset ℤ, ∀ index : JetIndex order, ∀ᵐ point ∂volume.restrict domain,
    ∀ cell : ℤ, cell ∉ cells → jet.val index point cell = 0

def ConstructorGoal : Prop :=
  ∀ (dimension order : ℕ) (domain : Set Spatial) (exponent : JetIndex order → ℕ),
    ∃ cutoff : Finset ℤ → WJet dimension order domain exponent →L[ℂ] WJet dimension order domain exponent,
      (∀ (cells : Finset ℤ) (jet : WJet dimension order domain exponent),
        (cutoff cells jet).val = cutoffTuple dimension order domain cells jet.val ∧
        base dimension order domain exponent (cutoff cells jet) =
          fieldCutoff dimension domain cells (base dimension order domain exponent jet) ∧
        ‖cutoff cells jet‖ ≤ ‖jet‖ ∧ cutoff cells (cutoff cells jet) = cutoff cells jet ∧
        FiniteCellJet dimension order domain exponent (cutoff cells jet)) ∧
      (∀ cells : Finset ℤ, ‖cutoff cells‖ ≤ 1) ∧
      (∀ jet : WJet dimension order domain exponent,
        Tendsto (fun cells : Finset ℤ => cutoff cells jet) atTop (𝓝 jet))

def DensityGoal : Prop :=
  ∀ (dimension order : ℕ) (domain : Set Spatial) (exponent : JetIndex order → ℕ),
    Dense {jet : WJet dimension order domain exponent | FiniteCellJet dimension order domain exponent jet}

def BlockGoal : Prop := ConstructorGoal ∧ DensityGoal

end Grad.WeightedJets.CellCutoff
