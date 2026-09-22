import AKCO5ExactSignedCellFamilies
import AKBP8SamePhaseDivDivEquation

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set Filter MeasureTheory
namespace Grad.CartesianStartup
open Grad.PDEBootstrap Grad.GenericCarriers Grad.ClosedJets Grad.WeightedJets

/-- The actual cellwise weak pairing acquires precisely its signed
frequency power, without commuting that power through any coefficient. -/
theorem StartupSignedFamily.pairing {L ell : ℝ} (family : StartupSignedFamily 3 L ell)
    (power : ℕ) (cell : ℤ) (vector : PhysicalValue 3) (test : TestFunction openUnitDisk) :
    startupTestPairing cell vector test (family.moment power) =
      startupAxialFrequency L ell cell ^ power * startupTestPairing cell vector test family.field := by
  rw [startupTestPairing_apply,startupTestPairing_apply]
  calc
    _ = ∫ point in openUnitDisk, startupAxialFrequency L ell cell ^ power •
        (test.toFun point • inner ℂ vector (family.field point cell)) := by
      apply integral_congr_ae
      filter_upwards [family.same power] with point same
      rw [same cell,inner_smul_right]
      exact smul_comm (test.toFun point) (startupAxialFrequency L ell cell ^ power)
        (inner ℂ vector (family.field point cell))
    _ = _ := integral_smul _ _

/-- The SAME native weak div-div equation at every signed axial power.
Each tensor/flux family consists of actual output moments, so this lemma
does not diagonalize or commute the variable coefficient matrix. -/
theorem startupSame_signed_weakDivDiv {L ell : ℝ}
    (field zeroth : StartupSignedFamily 3 L ell)
    (tensor : Fin 2 → Fin 2 → StartupSignedFamily 3 L ell)
    (flux : Fin 2 → StartupSignedFamily 3 L ell)
    (equation : StartupWeakDivDivEquation field.field zeroth.field
      (fun outer inner => (tensor outer inner).field) (fun direction => (flux direction).field))
    (power : ℕ) :
    StartupWeakDivDivEquation (field.moment power) (zeroth.moment power)
      (fun outer inner => (tensor outer inner).moment power) (fun direction => (flux direction).moment power) := by
  intro cell vector test
  simp only [StartupSignedFamily.pairing]
  simpa only [Fin.sum_univ_two,mul_add] using
    congrArg (fun value : ℂ => startupAxialFrequency L ell cell ^ power * value) (equation cell vector test)

end Grad.CartesianStartup
