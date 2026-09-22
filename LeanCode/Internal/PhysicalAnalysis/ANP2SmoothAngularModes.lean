import ANP1OriginalAngularModes
import GQE4SmoothContractions

noncomputable section
set_option maxHeartbeats 1600000
namespace Grad.RawCircularSectors
open Grad.ClosedJets Grad.CartesianState Grad.Constraints
open Grad.GaugeCoefficients.Physical.Compensated Grad.GaugeCoefficients.Physical.RadialLedger
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope

/-- The completed operator is the literal angular projection of the faithful
continuous trace, with the same physical disk and analytic parameters. -/
theorem apAngularMode_trace {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    {dimension grade : ℕ} (large : 2 ≤ grade) (mode : ℤ)
    (field : apGrade L sigma gamma ell dimension grade) (cell : ℤ) :
    apTrace admissible large cell (apAngularMode L sigma gamma ell dimension grade mode field) =
      cMapAngular dimension mode (apTrace admissible large cell field) := by
  apply isClosed_property (apFiniteInto_denseRange (dimension := dimension) (grade := grade) L sigma gamma ell)
    (isClosed_eq ((apTrace admissible large cell).continuous.comp
      (apAngularMode L sigma gamma ell dimension grade mode).continuous)
      ((cMapAngular dimension mode).continuous.comp (apTrace admissible large cell).continuous)) _ field
  intro core
  simp only [Function.comp_apply]
  rw [apAngularMode_core, apTrace_core, apTrace_core]
  apply ContinuousMap.ext
  intro point
  exact (closedCharacterProjection_jet mode (core cell) point).symm

theorem apSmoothAngularMode_jet {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    {dimension : ℕ} (mode : ℤ) (field : APSmooth L sigma gamma ell dimension) (cell : ℤ) :
    apSmoothJet admissible dimension cell (apSmoothAngularMode L sigma gamma ell dimension mode field) =
      angularClosedJet mode (apSmoothJet admissible dimension cell field) := by
  apply closedJet_eq_of_value_eq
  change (apFamilyJet (apSmoothAngularMode L sigma gamma ell dimension mode field).val _ cell).value = _
  rw [apFamilyJet_value_trace admissible (apSmoothAngularMode L sigma gamma ell dimension mode field).val
    (apSmoothAngularMode L sigma gamma ell dimension mode field).property (by omega : 2 ≤ 2) cell]
  change apTrace admissible (by omega : 2 ≤ 2) cell
    (apAngularMode L sigma gamma ell dimension 2 mode (field.val 2)) = _
  rw [apAngularMode_trace, ← apFamilyJet_value_trace admissible field.val field.property (by omega : 2 ≤ 2) cell]
  apply ContinuousMap.ext
  intro point
  exact closedCharacterProjection_jet mode (apSmoothJet admissible dimension cell field) point

theorem apSmoothAngularMode_bound {L sigma gamma ell : ℝ} {dimension : ℕ}
    (mode : ℤ) (field : APSmooth L sigma gamma ell dimension) (grade : ℕ) :
    ‖apSmoothGrade L sigma gamma ell dimension grade
      (apSmoothAngularMode L sigma gamma ell dimension mode field)‖ ≤
      orthogonalGradeConstant grade * ‖apSmoothGrade L sigma gamma ell dimension grade field‖ :=
  apAngularMode_bound L sigma gamma ell dimension grade mode (field.val grade)

theorem apSmoothAngularMode_projection {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    {dimension : ℕ} (first second : ℤ) (field : APSmooth L sigma gamma ell dimension) :
    apSmoothAngularMode L sigma gamma ell dimension first (apSmoothAngularMode L sigma gamma ell dimension second field) =
      if first = second then apSmoothAngularMode L sigma gamma ell dimension first field else 0 := by
  apply apSmoothJet_ext admissible
  intro cell
  have composed := (apSmoothAngularMode_jet admissible first _ cell).trans
    ((congrArg (angularClosedJet first) (apSmoothAngularMode_jet admissible second field cell)).trans
      (angularClosedJet_projection first second _))
  split_ifs with same
  · exact composed.trans ((if_pos same).trans (apSmoothAngularMode_jet admissible first field cell).symm)
  · exact composed.trans ((if_neg same).trans (map_zero (apSmoothJet admissible dimension cell)).symm)

theorem apSmoothAngularMode_zero {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    {dimension : ℕ} (field : APSmooth L sigma gamma ell dimension) :
    apSmoothAngularMode L sigma gamma ell dimension 0 field = apSmoothAngularMean L sigma gamma ell dimension field := by
  apply apSmoothJet_ext admissible
  intro cell
  exact (apSmoothAngularMode_jet admissible 0 field cell).trans (apSmoothAngularMean_jet admissible field cell).symm

end Grad.RawCircularSectors
