import BCT10ComposedPhysicalBoundary

noncomputable section

namespace Grad.ActualBoundaryPrimitives

open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.BoundaryKernelAction

/-- The literal high angular sector, with no restriction on the axial cell. -/
def IsHighAngularTrace {dimension : ℕ} (parameters : PhaseParameters) (angular cell : ℕ)
    (field : NegativeTrace parameters angular cell dimension) : Prop :=
  ∀ mode : ℤ × ℤ, |mode.1| < 3 →
    negativeTraceCoefficient parameters angular cell field mode = 0

def highAngularSubmodule (parameters : PhaseParameters) (angular cell dimension : ℕ) :
    Submodule ℂ (NegativeTrace parameters angular cell dimension) where
  carrier := {field | IsHighAngularTrace parameters angular cell field}
  zero_mem' := by
    intro mode _
    exact (negativeTraceCoefficientCLM parameters angular cell mode).map_zero
  add_mem' := by
    intro first second hfirst hsecond mode low
    change (negativeTraceCoefficientCLM parameters angular cell mode) (first + second) = 0
    rw [map_add, negativeTraceCoefficientCLM_apply, negativeTraceCoefficientCLM_apply,
      hfirst mode low, hsecond mode low, add_zero]
  smul_mem' := by
    intro scalar field supported mode low
    change (negativeTraceCoefficientCLM parameters angular cell mode) (scalar • field) = 0
    rw [map_smul, negativeTraceCoefficientCLM_apply, supported mode low, smul_zero]

theorem highAngularSubmodule_closed (parameters : PhaseParameters) (angular cell dimension : ℕ) :
    IsClosed (highAngularSubmodule parameters angular cell dimension :
      Set (NegativeTrace parameters angular cell dimension)) := by
  change IsClosed {field : NegativeTrace parameters angular cell dimension |
    ∀ mode : ℤ × ℤ, |mode.1| < 3 →
      negativeTraceCoefficient parameters angular cell field mode = 0}
  simp only [Set.ofPred_forall]
  exact isClosed_iInter fun mode => isClosed_iInter fun _ =>
    (negativeTraceCoefficientCLM (dimension := dimension) parameters angular cell mode).isClosed_ker

/-- AH16's high P_R space in derivative coordinates. A point records Rp in
the complete negative-half high sector; its physical p coefficients are
recovered by K. The inherited norm is exactly ‖Rp‖, as required by AH16. -/
abbrev HighBoundaryPrimitive (parameters : PhaseParameters) (angular cell : ℕ) :=
  highAngularSubmodule parameters angular cell 1

instance highBoundaryPrimitive_complete (parameters : PhaseParameters) (angular cell : ℕ) :
    CompleteSpace (HighBoundaryPrimitive parameters angular cell) :=
  (highAngularSubmodule_closed parameters angular cell 1).completeSpace_coe

def highBoundaryPrimitiveTrace (parameters : PhaseParameters) (angular cell : ℕ)
    (field : HighBoundaryPrimitive parameters angular cell) :
    NegativeTrace parameters angular cell 1 :=
  fullNegativeKernelAction parameters angular cell (angularInverseKernel parameters 1) field.val

theorem highBoundaryPrimitive_norm (parameters : PhaseParameters) (angular cell : ℕ)
    (field : HighBoundaryPrimitive parameters angular cell) :
    ‖field‖ = ‖field.val‖ := rfl

end Grad.ActualBoundaryPrimitives
