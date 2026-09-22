import RSC7CompletedRestriction

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal
namespace Grad.SourceCollarRestriction
open Grad.SourceCollarDivision

open Grad.ClosedJets Grad.CartesianState

theorem restrictionModeLp_weak_derivative {dimension : ℕ}
    (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (power radial : ℕ) (parameters : PhaseParameters) (field : ACore parameters dimension) (mode : ℤ × ℤ) :
    HasWeakRadialDerivative lower positive
      (restrictionModeLp lower power radial parameters field mode)
      (restrictionModeLp lower power (radial + 1) parameters field mode) :=
  (radialCoefficient_weak_derivative lower positive bounded
    (originalPolarValue (phaseWeightedJet parameters mode.2 (field.val mode.2)))
    (originalPolarValue_smooth _) mode.1 radial).smul _

theorem completedRestrictionArray_graph {dimension : ℕ}
    (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (parameters : PhaseParameters) (power radial : ℕ)
    (field : AGrade parameters dimension (power + radial)) :
    completedRestrictionArray lower positive bounded parameters power radial field ∈
      annularDerivativeGraph dimension lower positive radial := by
  refine UniformSpace.Completion.induction_on field
    ((annularDerivativeGraph_closed dimension lower positive radial).preimage
      (completedRestrictionArray lower positive bounded parameters power radial).continuous) ?_
  intro core
  apply (annularDerivativeGraph_mem_iff lower positive radial _).mpr
  intro index mode
  change HasWeakRadialDerivative lower positive
    (completedRestrictionArray lower positive bounded parameters power radial
      (aGradeEta parameters core) index.castSucc mode)
    (completedRestrictionArray lower positive bounded parameters power radial
      (aGradeEta parameters core) index.succ mode)
  simp only [completedRestrictionArray_component, completedRestrictionRow_core]
  exact restrictionModeLp_weak_derivative lower positive bounded power index.val parameters core.toCore mode

end Grad.SourceCollarRestriction
