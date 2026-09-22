import AX13ZDensity

noncomputable section

set_option maxHeartbeats 1600000

open scoped BigOperators

namespace Grad.AxisCore

open Grad.ClosedJets Grad.CartesianState
open Grad.ImplementationReadiness (VectorBlock spinPack)

/-- The exact COR20 goal: the literal fourfold quotient ambient
`ZAmbient q = PiLp 2 (fun _ : Fin 4 => AGrade complex q)` with its exact
fourfold squared norm, complete Hilbert structure, dense smooth fourfold
embedding with inherited norm, and the checked spin packing identity with
the exact factor two. -/
def QuotientAmbientGoal : Prop :=
  ∀ (parameters : PhaseParameters) (grade : ℕ),
    (∀ element : ZAmbient parameters grade,
      ‖element‖ ^ 2 = ∑ coordinate : Fin 4, ‖element coordinate‖ ^ 2) ∧
    CompleteSpace (ZAmbient parameters grade) ∧
    Nonempty (InnerProductSpace ℂ (ZAmbient parameters grade)) ∧
    (∀ cores : Fin 4 → GradeCore parameters 1 grade,
      (∀ coordinate : Fin 4, zEmbedding parameters grade cores coordinate =
        aGradeEta parameters (cores coordinate)) ∧
      ‖zEmbedding parameters grade cores‖ ^ 2 =
        ∑ coordinate : Fin 4, ‖cores coordinate‖ ^ 2) ∧
    DenseRange (zEmbedding parameters grade) ∧
    (∀ (planar : VectorBlock (AGrade parameters 1 grade))
      (third fourth : AGrade parameters 1 grade),
      ‖(spinPack planar third fourth : ZAmbient parameters grade)‖ ^ 2 =
        2 * ‖planar‖ ^ 2 + ‖third‖ ^ 2 + ‖fourth‖ ^ 2)

end Grad.AxisCore
