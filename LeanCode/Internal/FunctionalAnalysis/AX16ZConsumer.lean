import AX15ZProof

noncomputable section

set_option maxHeartbeats 1600000

open scoped BigOperators

namespace Grad.AxisCore.Consumer

open Grad.ClosedJets Grad.CartesianState Grad.AxisCore

/-- The consumer-gate carrier identification: the target ambient is fixed
to the literal Hilbert fourfold quotient carrier over the actual scalar
completion — not a raw image, and not a sum or max norm. -/
theorem quotient_carrier_literal (parameters : PhaseParameters) (grade : ℕ) :
    ZAmbient parameters grade =
      PiLp 2 (fun _ : Fin 4 =>
        UniformSpace.Completion (GradeCore parameters 1 grade)) := rfl

/-- Immediate exact consumer: every fourfold ambient element is
`epsilon`-approximated by a smooth fourfold embedding carrying the exact
inherited L2 norm formula, inside the complete carrier. -/
theorem quotient_fourfold_ready (parameters : PhaseParameters) (grade : ℕ)
    (element : ZAmbient parameters grade) (epsilon : ℝ) (positive : 0 < epsilon) :
    CompleteSpace (ZAmbient parameters grade) ∧
    ∃ cores : Fin 4 → GradeCore parameters 1 grade,
      ‖element - zEmbedding parameters grade cores‖ < epsilon ∧
      ‖zEmbedding parameters grade cores‖ ^ 2 =
        ∑ coordinate : Fin 4, ‖cores coordinate‖ ^ 2 := by
  obtain ⟨-, complete, -, inherited, dense, -⟩ := actualQuotientAmbient parameters grade
  obtain ⟨cores, close⟩ := Metric.denseRange_iff.mp dense element epsilon positive
  rw [dist_eq_norm] at close
  exact ⟨complete, cores, close, (inherited cores).2⟩

end Grad.AxisCore.Consumer
