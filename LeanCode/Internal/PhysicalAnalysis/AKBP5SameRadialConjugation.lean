import AKBP4LiteralPrincipalCoordinateConsumer
import AKBL32SameRoughNativeGaugeConsumer

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
open Set MeasureTheory
open scoped ContDiff
namespace Grad.CartesianStartup
open Grad.PDEBootstrap Grad.ClosedJets Grad.CartesianState Grad.GaugeCoefficients.Radial Grad.GenericCarriers Grad.Constraints Grad.Constraints.Gauges
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Physical.RadialLedger Grad.WeightedJets

/-- Exact cellwise multiplication, without declaring the generally unbounded
radial phase or cell moment to be a bounded operator. -/
def StartupRadialRelated {dimension : ℕ} (symbol : ℤ → Spatial → ℝ)
    (weighted original : StartupL2 dimension) : Prop :=
  ∀ᵐ point ∂volume.restrict openUnitDisk, ∀ cell : ℤ,
    weighted point cell = symbol cell point • original point cell

namespace StartupRadialRelated
variable {dimension : ℕ} {symbol : ℤ → Spatial → ℝ}

theorem zero : StartupRadialRelated symbol (0 : StartupL2 dimension) 0 := by
  have zeroValue : (fun point => (0 : StartupL2 dimension) point) =ᵐ[volume.restrict openUnitDisk] 0 := Lp.coeFn_zero _ _ _
  filter_upwards [zeroValue] with point value
  intro cell
  simp only [value, lp.coeFn_zero, Pi.zero_apply, smul_zero]

theorem add {first second firstRaw secondRaw : StartupL2 dimension}
    (one : StartupRadialRelated symbol first firstRaw) (two : StartupRadialRelated symbol second secondRaw) :
    StartupRadialRelated symbol (first+second) (firstRaw+secondRaw) := by
  filter_upwards [one,two,Lp.coeFn_add first second,Lp.coeFn_add firstRaw secondRaw] with point one two value raw
  intro cell
  simp only [value,raw,lp.coeFn_add,Pi.add_apply,one cell,two cell,smul_add]

theorem sub {first second firstRaw secondRaw : StartupL2 dimension}
    (one : StartupRadialRelated symbol first firstRaw) (two : StartupRadialRelated symbol second secondRaw) :
    StartupRadialRelated symbol (first-second) (firstRaw-secondRaw) := by
  filter_upwards [one,two,Lp.coeFn_sub first second,Lp.coeFn_sub firstRaw secondRaw] with point one two value raw
  intro cell
  simp only [value,raw,lp.coeFn_sub,Pi.sub_apply,one cell,two cell,smul_sub]

theorem smul {weighted original : StartupL2 dimension} (same : StartupRadialRelated symbol weighted original)
    (constant : ℂ) : StartupRadialRelated symbol (constant • weighted) (constant • original) := by
  filter_upwards [same,Lp.coeFn_smul constant weighted,Lp.coeFn_smul constant original] with point same value raw
  intro cell
  simp only [value,raw,lp.coeFn_smul,Pi.smul_apply,same cell]
  exact smul_comm constant (symbol cell point) (original point cell)

theorem value {input output : ℕ} {weighted original : StartupL2 input}
    (same : StartupRadialRelated symbol weighted original) (mapping : OperatorValue input output) :
    StartupRadialRelated symbol (originalValueKernel mapping weighted) (originalValueKernel mapping original) := by
  filter_upwards [same,startupPointKernel_field_ae mapping (LinearIsometryEquiv.refl ℝ _) weighted,
    startupPointKernel_field_ae mapping (LinearIsometryEquiv.refl ℝ _) original] with point same value raw
  intro cell
  change ∀ index : ℤ, originalValueKernel mapping weighted point index = mapping (weighted point index) at value
  change ∀ index : ℤ, originalValueKernel mapping original point index = mapping (original point index) at raw
  rw [value cell,raw cell,same cell]
  simp only [RCLike.real_smul_eq_coe_smul (K := ℂ),map_smul]

/-- Radial phase and all cell moments commute with the actual angular
integral on the SAME rough L2 fields. No spatial derivative is commuted. -/
theorem angular {weighted original : StartupL2 dimension}
    (same : StartupRadialRelated symbol weighted original)
    (radial : ∀ (cell : ℤ) (angle : ℝ) (point : Spatial), symbol cell (planeRotationEquiv angle point) = symbol cell point)
    (weight : ℝ → ℂ) (smooth : ContDiff ℝ ∞ weight) :
    StartupRadialRelated symbol (startupAngularKernel dimension weight smooth weighted)
      (startupAngularKernel dimension weight smooth original) := by
  apply ae_all_iff.mpr
  intro cell
  have moved := Grad.KernelIntegral.transported_ae_eq_sections
    (volume.restrict (Icc (0 : ℝ) (2*Real.pi))) openUnitDisk_isOpen.measurableSet planeRotationEquiv
    (fun angle point => by change ‖planeRotationEquiv angle point‖ < 1 ↔ ‖point‖ < 1; rw [LinearIsometryEquiv.norm_map])
    continuous_planeRotation_joint.measurable (same.mono (fun _ same => same cell))
  filter_upwards [moved,startupAngularKernel_action_ae dimension weight smooth weighted cell,
    startupAngularKernel_action_ae dimension weight smooth original cell] with point moved weightedValue originalValue
  rw [weightedValue,originalValue,← integral_smul]
  apply integral_congr_ae
  filter_upwards [moved] with angle moved
  rw [moved,radial]
  simp only [RCLike.real_smul_eq_coe_smul (K := ℂ),map_smul]

end StartupRadialRelated
end Grad.CartesianStartup
