import AEN10OriginalSmoothNormTools

noncomputable section
set_option maxHeartbeats 1400000
namespace Grad.ExceptionalNative
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.ActualExceptionalInverse
open Grad.FlatSourceProjection
open Grad.ActualCenterVolterra Grad.NonlinearRadial Grad.NonlinearQuotientBounds
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.Compensated Grad.GaugeCoefficients.Physical.RadialLedger
variable {L sigma gamma ell : ℝ}

theorem regularPrimitive_smul (sign : ℤ) (scalar : ℂ) (field : ClosedJet 1) :
    regularSecondPrimitive sign (scalar • field) = scalar • regularSecondPrimitive sign field := by
  simp only [regularSecondPrimitive, centerCoordinate_decomposition, centerCoordinate_smul,
    powerDilationJet_add, powerDilationJet_smul, smul_add, smul_comm scalar]

theorem signedLowering_smul (sign : ℤ) (scalar : ℂ) (field : ClosedJet 1) :
    signedLowering sign (scalar • field) = scalar • signedLowering sign field := by
  simp only [signedLowering, centerDifferential, centerPartial_smul, smul_sub, smul_comm scalar]

theorem pinnedPrimitive_smul (sign : ℤ) (scalar : ℂ) (field : ClosedJet 1) :
    pinnedSpinPrimitive sign (scalar • field) = scalar • pinnedSpinPrimitive sign field := by
  simp only [pinnedSpinPrimitive, secondModeQuotient, signedQuotient, signedLowering_smul,
    powerDilationJet_smul, radiusPower_one_decomposition, centerCoordinate_smul,
    centerCoordinate_decomposition, centerCoordinate_add, smul_add, smul_comm scalar]

theorem regularPrimitive_zero (sign : ℤ) : regularSecondPrimitive sign (0 : ClosedJet 1) = 0 := by
  simpa only [zero_smul] using regularPrimitive_smul sign 0 (0 : ClosedJet 1)

theorem pinnedPrimitive_zero (sign : ℤ) : pinnedSpinPrimitive sign (0 : ClosedJet 1) = 0 := by
  simpa only [zero_smul] using pinnedPrimitive_smul sign 0 (0 : ClosedJet 1)

theorem signedLowering_zero (sign : ℤ) : signedLowering sign (0 : ClosedJet 1) = 0 := by
  simpa only [zero_smul] using signedLowering_smul sign 0 (0 : ClosedJet 1)

theorem smoothSupport_spin (admissible : Admissible L sigma gamma ell) (cells : ℤ → Prop) (sign : ℤ)
    (field : APSmooth L sigma gamma ell 2) (supported : SmoothCellSupported admissible cells field) :
    SmoothCellSupported admissible cells (smoothSpin L sigma gamma ell sign field) := by
  intro cell outside
  rw [smoothSpin_jet, supported cell outside]
  exact (valueMapJetLinear 2 1 (spinValue (sign : ℂ))).map_zero

theorem smoothSupport_signedDerivative (admissible : Admissible L sigma gamma ell) (cells : ℤ → Prop) (sign : ℤ)
    (field : APSmooth L sigma gamma ell 1) (supported : SmoothCellSupported admissible cells field) :
    SmoothCellSupported admissible cells (smoothSignedDerivative admissible 1 sign field) := by
  intro cell outside
  rw [smoothSignedDerivative_jet, supported cell outside, signedLowering_zero]

theorem smoothSupport_axial (admissible : Admissible L sigma gamma ell) {dimension : ℕ} (cells : ℤ → Prop)
    (field : APSmooth L sigma gamma ell dimension) (supported : SmoothCellSupported admissible cells field) :
    SmoothCellSupported admissible cells (apSmoothAxial L sigma gamma ell dimension field) := by
  intro cell outside
  rw [apSmoothAxial_jet, supported cell outside, smul_zero]

theorem smoothSupport_pinnedPrimitive (admissible : Admissible L sigma gamma ell) (cells : ℤ → Prop) (sign : ℤ)
    (field : APSmooth L sigma gamma ell 1) (supported : SmoothCellSupported admissible cells field) :
    SmoothCellSupported admissible cells (smoothPinnedPrimitive admissible 1 sign field) := by
  intro cell outside
  rw [smoothPinnedPrimitive_jet, supported cell outside, pinnedPrimitive_zero]

theorem exceptionalPsi_support (admissible : Admissible L sigma gamma ell) (cells : ℤ → Prop) (sign : ℤ)
    (source : SmoothCapSource L sigma gamma ell) (supported : SmoothCellSupported admissible cells source.1) :
    SmoothCellSupported admissible cells (exceptionalPsi admissible sign source) := by
  intro cell outside
  rw [exceptionalPsi_jet, supported cell outside]
  have zero : valueMapJet (spinValue ((-sign : ℤ) : ℂ)) (0 : ClosedJet 2) = 0 :=
    (valueMapJetLinear 2 1 (spinValue ((-sign : ℤ) : ℂ))).map_zero
  rw [zero, regularPrimitive_zero]

theorem exceptionalFixedSpin_support (admissible : Admissible L sigma gamma ell) (cells : ℤ → Prop) (sign : ℤ)
    (source : SmoothCapSource L sigma gamma ell) (supported : SmoothCellSupported admissible cells source.1) :
    SmoothCellSupported admissible cells (exceptionalFixedSpin admissible sign source) :=
  smoothSupport_smul admissible cells _ _ (smoothSupport_sub admissible cells _ _
    (smoothSupport_signedDerivative admissible cells _ _ (exceptionalPsi_support admissible cells sign source supported))
    (smoothSupport_spin admissible cells sign source.1 supported))

theorem exceptionalToroidal_support (admissible : Admissible L sigma gamma ell) (cells : ℤ → Prop) (sign : ℤ)
    (source : SmoothCapSource L sigma gamma ell) (force : SmoothCellSupported admissible cells source.1)
    (third : SmoothCellSupported admissible cells source.2.2) :
    SmoothCellSupported admissible cells (exceptionalToroidal admissible sign source) :=
  smoothSupport_smul admissible cells _ _ (smoothSupport_add admissible cells _ _ third
    (smoothSupport_axial admissible cells _ (exceptionalPsi_support admissible cells sign source force)))

theorem exceptionalFreeForcing_support (admissible : Admissible L sigma gamma ell) (cells : ℤ → Prop) (sign : ℤ)
    (source : SmoothCapSource L sigma gamma ell) (force : SmoothCellSupported admissible cells source.1)
    (determinant : SmoothCellSupported admissible cells source.2.1) (third : SmoothCellSupported admissible cells source.2.2) :
    SmoothCellSupported admissible cells (exceptionalFreeForcing admissible sign source) :=
  smoothSupport_sub admissible cells _ _ (smoothSupport_add admissible cells _ _
    (smoothSupport_smul admissible cells _ _ determinant)
    (smoothSupport_smul admissible cells _ _ (smoothSupport_axial admissible cells _
      (exceptionalToroidal_support admissible cells sign source force third))))
    (smoothSupport_signedDerivative admissible cells sign _ (exceptionalFixedSpin_support admissible cells sign source force))

theorem smoothOriginal_lower (admissible : Admissible L sigma gamma ell) {dimension low high : ℕ}
    (ordered : low ≤ high) (field : APSmooth L sigma gamma ell dimension) :
    ‖apSmoothGrade L sigma gamma ell dimension low field‖ ≤
      apLoweringConstant low * ‖apSmoothGrade L sigma gamma ell dimension high field‖ :=
  smoothNorm_of_cellBounds admissible field field high low (apLoweringConstant low) (apLoweringConstant_nonnegative low)
    (fun cell => apLowerRow_bound L sigma gamma ell ordered cell (apSmoothJet admissible dimension cell field))

end Grad.ExceptionalNative
