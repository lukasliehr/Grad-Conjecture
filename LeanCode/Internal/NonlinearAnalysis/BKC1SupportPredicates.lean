import BKB53ActualAFConsumer

noncomputable section

namespace Grad.BoundaryKernelAction

open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision
open Grad.SourceBoundaryTrace

/-- A negative-half trace whose angular zero mode vanishes.  This is the
closed coefficient formulation of the mean-free support used in AE14. -/
def IsAngularMeanFree {dimension : ℕ} (parameters : PhaseParameters)
    (angular cell : ℕ)
    (field : NegativeTrace parameters angular cell dimension) : Prop :=
  ∀ axial : ℤ,
    negativeTraceCoefficient parameters angular cell field (0, axial) = 0

/-- A negative-half trace supported on the angular zero mode. -/
def IsAngularConstant {dimension : ℕ} (parameters : PhaseParameters)
    (angular cell : ℕ)
    (field : NegativeTrace parameters angular cell dimension) : Prop :=
  ∀ mode : ℤ × ℤ, mode.1 ≠ 0 →
    negativeTraceCoefficient parameters angular cell field mode = 0

/-- One coordinate of a vector-valued trace is angularly mean-free. -/
def IsAngularMeanFreeComponent {dimension : ℕ}
    (parameters : PhaseParameters) (angular cell : ℕ)
    (coordinate : Fin dimension)
    (field : NegativeTrace parameters angular cell dimension) : Prop :=
  ∀ axial : ℤ,
    negativeTraceCoefficient parameters angular cell field (0, axial) coordinate = 0

/-- One coordinate of a vector-valued trace is angularly constant. -/
def IsAngularConstantComponent {dimension : ℕ}
    (parameters : PhaseParameters) (angular cell : ℕ)
    (coordinate : Fin dimension)
    (field : NegativeTrace parameters angular cell dimension) : Prop :=
  ∀ mode : ℤ × ℤ, mode.1 ≠ 0 →
    negativeTraceCoefficient parameters angular cell field mode coordinate = 0

/-- AE14's literal encoded support: `x₀` is angularly constant, while the
`Y` and `C` coordinates are angularly mean-free. -/
def EncodedSupport (parameters : PhaseParameters) (angular cell : ℕ)
    (field : NegativeTrace parameters angular cell 3) : Prop :=
  IsAngularConstantComponent parameters angular cell 0 field ∧
    IsAngularMeanFreeComponent parameters angular cell 1 field ∧
    IsAngularMeanFreeComponent parameters angular cell 2 field

end Grad.BoundaryKernelAction
