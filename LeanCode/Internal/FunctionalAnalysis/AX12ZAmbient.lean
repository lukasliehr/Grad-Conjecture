import AX11AmbientConsumer

noncomputable section

set_option maxHeartbeats 1600000

open scoped BigOperators

namespace Grad.AxisCore

open Grad.ClosedJets Grad.CartesianState
open Grad.ImplementationReadiness (QuotientAmbient)

/-- The literal fourfold quotient ambient carrier over the actual scalar
completion, ordered as `(gplus, gminus, g3, h)`: the checked generic
`QuotientAmbient` instantiated at the accepted `AGrade`. -/
abbrev ZAmbient (parameters : PhaseParameters) (grade : ℕ) :=
  QuotientAmbient (AGrade parameters 1 grade)

/-- The exact fourfold squared norm. -/
theorem zAmbient_norm_sq (parameters : PhaseParameters) (grade : ℕ)
    (element : ZAmbient parameters grade) :
    ‖element‖ ^ 2 = ∑ coordinate : Fin 4, ‖element coordinate‖ ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2]

/-- The complete Hilbert structure witnesses of the fourfold carrier. -/
theorem zAmbient_completeSpace (parameters : PhaseParameters) (grade : ℕ) :
    CompleteSpace (ZAmbient parameters grade) := inferInstance

theorem zAmbient_innerProductSpace (parameters : PhaseParameters) (grade : ℕ) :
    Nonempty (InnerProductSpace ℂ (ZAmbient parameters grade)) := ⟨inferInstance⟩

/-- The exposed linear component projections. -/
def zComponent (parameters : PhaseParameters) (grade : ℕ) (coordinate : Fin 4) :
    ZAmbient parameters grade →ₗ[ℂ] AGrade parameters 1 grade where
  toFun element := element coordinate
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem zComponent_apply (parameters : PhaseParameters) (grade : ℕ)
    (coordinate : Fin 4) (element : ZAmbient parameters grade) :
    zComponent parameters grade coordinate element = element coordinate := rfl

/-- Each component is bounded by the fourfold norm. -/
theorem zComponent_norm_le (parameters : PhaseParameters) (grade : ℕ)
    (coordinate : Fin 4) (element : ZAmbient parameters grade) :
    ‖element coordinate‖ ≤ ‖element‖ := by
  have squares : ‖element coordinate‖ ^ 2 ≤ ‖element‖ ^ 2 := by
    rw [zAmbient_norm_sq]
    exact Finset.single_le_sum (f := fun inner => ‖element inner‖ ^ 2)
      (fun inner _ => sq_nonneg _) (Finset.mem_univ coordinate)
  calc ‖element coordinate‖
      = Real.sqrt (‖element coordinate‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt (‖element‖ ^ 2) := Real.sqrt_le_sqrt squares
    _ = ‖element‖ := Real.sqrt_sq (norm_nonneg _)

end Grad.AxisCore
