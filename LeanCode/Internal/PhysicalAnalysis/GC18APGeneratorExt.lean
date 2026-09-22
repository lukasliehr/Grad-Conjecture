import GC18APSingleValue
import GC18APBilinearCompleted

noncomputable section

set_option maxHeartbeats 1000000

namespace Grad.GaugeCoefficients.Physical.RadialLedger

open Grad.ClosedJets Grad.CartesianState Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope

theorem apFiniteGenerator_ext {T : Type*} [NormedAddCommGroup T] [NormedSpace ℂ T]
    {dimension grade : ℕ} (L sigma gamma ell : ℝ)
    (first second : apGrade L sigma gamma ell dimension grade →L[ℂ] T)
    (single : ∀ cell field, first (apFiniteInto L sigma gamma ell (Finsupp.single cell field)) =
      second (apFiniteInto L sigma gamma ell (Finsupp.single cell field))) : first = second := by
  have coreEquality : first.toLinearMap.comp (apFiniteInto L sigma gamma ell) =
      second.toLinearMap.comp (apFiniteInto L sigma gamma ell) := Finsupp.lhom_ext single
  apply ContinuousLinearMap.ext
  intro field
  apply isClosed_property (apFiniteInto_denseRange (dimension := dimension) (grade := grade) L sigma gamma ell)
    (isClosed_eq first.continuous second.continuous) _ field
  intro core
  exact LinearMap.congr_fun coreEquality core

theorem apCoefficientGenerator_ext {T : Type*} [NormedAddCommGroup T] [NormedSpace ℂ T]
    {input output grade : ℕ} (L sigma gamma ell : ℝ)
    (first second : Coefficient L sigma gamma ell grade input output →L[ℂ] T)
    (single : ∀ cell field, first (singleJetCoefficient L sigma gamma ell grade cell field) =
      second (singleJetCoefficient L sigma gamma ell grade cell field)) : first = second := by
  apply ContinuousLinearMap.ext
  intro coefficient
  apply isClosed_property (finiteCellCore_dense grade input output)
    (isClosed_eq first.continuous second.continuous) _ coefficient
  intro core
  have coreEquality : ∀ raw (member : raw ∈ smoothCore L sigma gamma ell grade input output),
      first ⟨raw, Submodule.le_topologicalClosure _ member⟩ = second ⟨raw, Submodule.le_topologicalClosure _ member⟩ := by
    intro raw member
    refine Submodule.span_induction ?_ ?_ ?_ ?_ member
    · rintro raw ⟨⟨cell, field⟩, rfl⟩
      exact single cell field
    · change first 0 = second 0
      rw [map_zero, map_zero]
    · intro left right leftMember rightMember leftEquality rightEquality
      change first (⟨left, Submodule.le_topologicalClosure _ leftMember⟩ +
        ⟨right, Submodule.le_topologicalClosure _ rightMember⟩) =
        second (⟨left, Submodule.le_topologicalClosure _ leftMember⟩ +
          ⟨right, Submodule.le_topologicalClosure _ rightMember⟩)
      rw [map_add, map_add, leftEquality, rightEquality]
    · intro scalar raw rawMember equality
      change first (scalar • (⟨raw, Submodule.le_topologicalClosure _ rawMember⟩ : Coefficient L sigma gamma ell grade input output)) =
        second (scalar • (⟨raw, Submodule.le_topologicalClosure _ rawMember⟩ : Coefficient L sigma gamma ell grade input output))
      rw [map_smul, map_smul, equality]
  exact coreEquality core.val core.property

end Grad.GaugeCoefficients.Physical.RadialLedger
