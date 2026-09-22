import ACE6RadialPowers

noncomputable section
set_option maxHeartbeats 1000000
open Set Filter MeasureTheory
open scoped Topology ContDiff BigOperators
namespace Grad.ActualCenterVolterra
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearRadial
open Grad.NonlinearProduct Grad.NonlinearRange Grad.NonlinearQuotientBounds

/-- The regular W4 operator; all sampling scales lie in the closed disk. -/
def volterraJet {dimension : ℕ} (field : ClosedJet dimension) : ClosedJet dimension :=
  radiusPowerJet 1 (powerDilationJet 1 (powerDilationJet 3 field))

def volterraLinear (dimension : ℕ) : ClosedJet dimension →ₗ[ℂ] ClosedJet dimension :=
  (radiusPowerLinear dimension 1).comp ((powerDilationLinear dimension 1).comp (powerDilationLinear dimension 3))

theorem volterraLinear_apply {dimension : ℕ} (field : ClosedJet dimension) :
    volterraLinear dimension field = volterraJet field := rfl

def volterraPower {dimension : ℕ} (count : ℕ) (field : ClosedJet dimension) : ClosedJet dimension :=
  Nat.rec field (fun _ previous => volterraJet previous) count

/-- The positive dilation kernel of W6, kept as nested compact integrals
rather than introducing an auxiliary pushforward measure. -/
def positiveKernel {dimension : ℕ} (count : ℕ) (field : ClosedJet dimension) : ClosedJet dimension :=
  Nat.rec field (fun count previous => powerDilationJet (2 * count + 1) (powerDilationJet (2 * count + 3) previous)) count

theorem volterraPower_zero {dimension : ℕ} (field : ClosedJet dimension) : volterraPower 0 field = field := rfl

theorem volterraPower_succ {dimension : ℕ} (count : ℕ) (field : ClosedJet dimension) :
    volterraPower (count + 1) field = volterraJet (volterraPower count field) := rfl

theorem positiveKernel_zero {dimension : ℕ} (field : ClosedJet dimension) : positiveKernel 0 field = field := rfl

theorem volterraPower_kernel {dimension : ℕ} (count : ℕ) (field : ClosedJet dimension) :
    volterraPower count field = radiusPowerJet count (positiveKernel count field) := by
  induction count with
  | zero => exact (radiusPowerJet_zero field).symm
  | succ count inductionHypothesis =>
    change volterraJet (volterraPower count field) = _
    rw [inductionHypothesis, volterraJet, powerDilation_radiusPower, powerDilation_radiusPower, radiusPowerJet_addPower]
    have first : 1 + 2 * count = 2 * count + 1 := by omega
    have second : 3 + 2 * count = 2 * count + 3 := by omega
    rw [first, second, Nat.add_comm 1 count]
    rfl

theorem volterraJet_W4 {dimension : ℕ} (field : ClosedJet dimension) (point : ClosedDisk) :
    (volterraJet field).value point = ‖point.val‖ ^ 2 •
      ∫ a in Icc (0 : ℝ) 1, a • ∫ b in Icc (0 : ℝ) 1,
        b ^ 3 • smoothClosedExtension field ((a * b) • point.val) := by
  rw [volterraJet, radiusPowerJet_value, pow_one, radiusSquare_eq, powerDilationJet_value]
  congr 1
  apply setIntegral_congr_fun measurableSet_Icc
  intro scale inside
  dsimp only
  rw [pow_one]
  congr 1
  have equality := (smoothClosedExtension_value (powerDilationJet 3 field)
    (dilationPoint scale inside.1 inside.2 point)).trans (powerDilationJet_value 3 field _)
  refine equality.trans ?_
  apply setIntegral_congr_fun measurableSet_Icc
  intro second _
  change second ^ 3 • smoothClosedExtension field (second • (scale • point.val)) =
    second ^ 3 • smoothClosedExtension field ((scale * second) • point.val)
  rw [smul_smul, mul_comm second scale]

def kernelMass (count : ℕ) : ℝ :=
  1 / (4 ^ count * (count.factorial : ℝ) * ((count + 1).factorial : ℝ))

theorem kernelMass_positive (count : ℕ) : 0 < kernelMass count := by
  unfold kernelMass
  positivity

theorem kernelMass_zero : kernelMass 0 = 1 := by norm_num [kernelMass]

theorem kernelMass_succ (count : ℕ) :
    kernelMass (count + 1) = kernelMass count / ((2 * count + 2 : ℝ) * (2 * count + 4 : ℝ)) := by
  unfold kernelMass
  rw [pow_succ, Nat.factorial_succ (count + 1), Nat.factorial_succ count]
  push_cast
  field_simp
  ring

end Grad.ActualCenterVolterra
