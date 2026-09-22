import ASL3CutoffLocality

noncomputable section

set_option maxRecDepth 3000
set_option maxHeartbeats 1200000

namespace Grad.AxisSourceLift

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearQuotientBounds
open Grad.NonlinearProduct Grad.NonlinearRange Grad.AxisSplit Grad.ChartAxisLift Grad.RawForward
open Grad.GaugeCoefficients.Radial

variable {parameters : PhaseParameters} {radius : ℝ} {dimension : ℕ}

def OutsideEqual (radius : ℝ) (first second : ACore parameters dimension) : Prop :=
  ∀ cell point, radius ≤ ‖point.val‖ → coefficientValue cell point first = coefficientValue cell point second

theorem OutsideEqual.refl (field : ACore parameters dimension) : OutsideEqual radius field field :=
  fun _ _ _ => rfl

theorem OutsideEqual.add {first second third fourth : ACore parameters dimension}
    (left : OutsideEqual radius first second) (right : OutsideEqual radius third fourth) :
    OutsideEqual radius (first + third) (second + fourth) := by
  intro cell point outside
  rw [map_add, map_add, left cell point outside, right cell point outside]

theorem OutsideEqual.sub {first second third fourth : ACore parameters dimension}
    (left : OutsideEqual radius first second) (right : OutsideEqual radius third fourth) :
    OutsideEqual radius (first - third) (second - fourth) := by
  intro cell point outside
  rw [map_sub, map_sub, left cell point outside, right cell point outside]

theorem OutsideEqual.smul {first second : ACore parameters dimension}
    (equal : OutsideEqual radius first second) (scalar : ℂ) :
    OutsideEqual radius (scalar • first) (scalar • second) := by
  intro cell point outside
  rw [map_smul, map_smul, equal cell point outside]

theorem OutsideEqual.angular {first second : ACore parameters dimension}
    (equal : OutsideEqual radius first second) (mode : ℤ) :
    OutsideEqual radius (angularCore parameters mode first) (angularCore parameters mode second) := by
  intro cell point outside
  change (angularClosedJet mode (first.val cell)).value point =
    (angularClosedJet mode (second.val cell)).value point
  rw [angularClosedJet_value, angularClosedJet_value]
  congr 1
  apply intervalIntegral.integral_congr
  intro angle _
  apply congrArg (fun value => angularCharacter mode angle • value)
  apply equal cell (rotatedPoint angle point)
  have normLaw := (planeRotationEquiv angle).norm_map point.val
  change ‖planeRotation angle point.val‖ = ‖point.val‖ at normLaw
  change radius ≤ ‖planeRotation angle point.val‖
  rwa [normLaw]

theorem OutsideEqual.removeAngular {first second : ACore parameters dimension}
    (equal : OutsideEqual radius first second) :
    OutsideEqual radius (removeAngularCore parameters first) (removeAngularCore parameters second) :=
  equal.sub (equal.angular 0)

theorem OutsideEqual.time {first second : ACore parameters dimension}
    (equal : OutsideEqual radius first second) :
    OutsideEqual radius (timeDerivativeCore parameters first) (timeDerivativeCore parameters second) := by
  intro cell point outside
  change (((cell : ℂ) * Complex.I) • (first.val cell)).value point =
    (((cell : ℂ) * Complex.I) • (second.val cell)).value point
  rw [closedJet_value_smul, closedJet_value_smul, ContinuousMap.smul_apply, ContinuousMap.smul_apply]
  exact congrArg (fun value => ((cell : ℂ) * Complex.I) • value) (equal cell point outside)

theorem OutsideEqual.valueMap {output : ℕ} {first second : ACore parameters dimension}
    (equal : OutsideEqual radius first second)
    (mapping : ComplexEuclidean dimension →L[ℂ] ComplexEuclidean output) :
    OutsideEqual radius (valueMapCore parameters mapping first) (valueMapCore parameters mapping second) := by
  intro cell point outside
  change (valueMapJet mapping (first.val cell)).value point = (valueMapJet mapping (second.val cell)).value point
  rw [valueMapJet_value, valueMapJet_value]
  exact congrArg mapping (equal cell point outside)

theorem OutsideEqual.product {arity output : ℕ}
    (mapping : ContinuousMultilinearMap ℂ
      (fun _ : Fin (arity + 1) => ComplexEuclidean dimension) (ComplexEuclidean output))
    (first second : Fin (arity + 1) → ACore parameters dimension)
    (equal : ∀ index, OutsideEqual radius (first index) (second index)) :
    OutsideEqual radius (actualMultilinearProduct parameters mapping first)
      (actualMultilinearProduct parameters mapping second) := by
  intro cell point outside
  change ((actualMultilinearProduct parameters mapping first).val cell).value point =
    ((actualMultilinearProduct parameters mapping second).val cell).value point
  rw [actualMultilinearProduct_isActual, actualMultilinearProduct_isActual]
  unfold productCoefficientValue
  apply tsum_congr
  intro assignment
  congr 1
  funext index
  exact equal index (assignment.val index) point outside

theorem OutsideEqual.dot {a b c d : ACore parameters 3}
    (first : OutsideEqual radius a b) (second : OutsideEqual radius c d) :
    OutsideEqual radius (dotOperation parameters a c) (dotOperation parameters b d) := by
  change OutsideEqual radius (pairProductLinear parameters physicalDotProduct a c)
    (pairProductLinear parameters physicalDotProduct b d)
  rw [pairProductLinear_apply, pairProductLinear_apply]
  apply OutsideEqual.product
  intro index
  fin_cases index <;> assumption

theorem OutsideEqual.determinant {a b c d e f : ACore parameters 3}
    (first : OutsideEqual radius a b) (second : OutsideEqual radius c d)
    (third : OutsideEqual radius e f) :
    OutsideEqual radius (determinantOperation parameters a c e) (determinantOperation parameters b d f) := by
  change OutsideEqual radius (tripleProductLinear parameters determinantMultilinear a c e)
    (tripleProductLinear parameters determinantMultilinear b d f)
  rw [tripleProductLinear_apply, tripleProductLinear_apply]
  apply OutsideEqual.product
  intro index
  fin_cases index <;> assumption

end Grad.AxisSourceLift
