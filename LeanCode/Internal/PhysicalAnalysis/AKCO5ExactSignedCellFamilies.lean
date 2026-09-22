import AKCO4NativeSignedMomentFamilies
import AKCG10ActualAxialLeadingSplit

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1100000
open Set Filter MeasureTheory
namespace Grad.CartesianStartup
open Grad.PDEBootstrap Grad.GenericCarriers Grad.ClosedJets Grad.WeightedJets
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.Allocation Grad.GaugeCoefficients.Physical.RadialLedger

/-- Simultaneous literal signed scaled moments of one fixed joint-cell
field. This record contains only L2 data, with no spatial regularity. -/
structure StartupSignedFamily (dimension : ℕ) (L ell : ℝ) where
  field : StartupL2 dimension
  moment : ℕ → StartupL2 dimension
  same : ∀ power, ∀ᵐ point ∂volume.restrict openUnitDisk, ∀ cell : ℤ,
    moment power point cell = startupAxialFrequency L ell cell ^ power • field point cell

namespace StartupSignedFamily

def ofNatural {dimension : ℕ} (family : StartupAllMoments dimension) (L ell : ℝ) :
    StartupSignedFamily dimension L ell where
  field := family.field
  moment power := (family.signedMoments L ell power).field
  same := family.signedMoments_same L ell

theorem projection {dimension : ℕ} {L ell : ℝ} (family : StartupSignedFamily dimension L ell)
    (power : ℕ) (cell : ℤ) :
    fieldCellProjection dimension openUnitDisk cell (family.moment power) =
      startupAxialFrequency L ell cell ^ power • fieldCellProjection dimension openUnitDisk cell family.field := by
  apply Lp.ext
  filter_upwards [family.same power,fieldCellProjection_ae dimension openUnitDisk (family.moment power),
    fieldCellProjection_ae dimension openUnitDisk family.field,
    Lp.coeFn_smul (startupAxialFrequency L ell cell ^ power)
      (fieldCellProjection dimension openUnitDisk cell family.field)] with point same one two scaled
  rw [one cell,scaled,Pi.smul_apply,two cell,same cell]

theorem zero {dimension : ℕ} {L ell : ℝ} (family : StartupSignedFamily dimension L ell) :
    family.moment 0 = family.field := by
  apply Grad.CellWeights.fields_ext dimension openUnitDisk
  intro cell
  simpa only [pow_zero,one_smul] using family.projection 0 cell

/-- The accepted full-cell binomial realizes every actual output moment;
all coefficient displacements remain present, at the original width. -/
def matrix {input output : ℕ} {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell)
    (coefficients : CoefficientFamily L sigma gamma ell input output) (coherent : FamilyCoherent coefficients)
    (family : StartupSignedFamily input L ell) : StartupSignedFamily output L ell where
  field := originalMatrixKernel admissible coefficients coherent family.field
  moment power := startupKernelAxialMoment admissible coefficients coherent zeroDerivativeIndex power family.moment
  same power := startupKernelAxialMoment_ae admissible coefficients coherent zeroDerivativeIndex power
    family.field family.moment (fun power _ => family.projection power)

/-- A fixed cell-diagonal action preserves the same signed output cells. -/
def map {input output : ℕ} {L ell : ℝ} (family : StartupSignedFamily input L ell)
    (operator : StartupL2 input →L[ℂ] StartupL2 output) (diagonal : StartupCellwise operator) :
    StartupSignedFamily output L ell where
  field := operator family.field
  moment power := operator (family.moment power)
  same power := by
    apply ae_all_iff.mpr
    intro cell
    have projected := diagonal.signedProjection (fun cell => startupAxialFrequency L ell cell ^ power)
      family.field (family.moment power) (family.projection power) cell
    filter_upwards [Lp.ext_iff.mp projected,
      fieldCellProjection_ae output openUnitDisk (operator (family.moment power)),
      fieldCellProjection_ae output openUnitDisk (operator family.field),
      Lp.coeFn_smul (startupAxialFrequency L ell cell ^ power)
        (fieldCellProjection output openUnitDisk cell (operator family.field))] with point same one two scaled
    rw [one cell,scaled,Pi.smul_apply,two cell] at same
    exact same

end StartupSignedFamily
end Grad.CartesianStartup
