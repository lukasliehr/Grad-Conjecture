import AIA12ActualPotentialPairing
import AIA13CircularScalarAlgebra

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
open Set Filter MeasureTheory
open scoped Topology BigOperators ENNReal
namespace Grad.AnnularCircularForm
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularReconstruction Grad.BoundaryKernelAction Grad.AnnularCurrentEnergy Grad.AnnularVariational
open Grad.AnnularTiltedReference Grad.AnnularGrades Grad.CircularHighWeak Grad.CircularHighRegularity

theorem annularEnergyMass_pairing_decomposed (lower L : ℝ) (positive : 0 < lower)
    (mode : HighAnnularMode) (test field : annularEnergySpace lower L positive) :
    inner ℂ (annularEnergyMass lower L positive test mode) (annularEnergyMass lower L positive field mode) =
      4 * inner ℂ (highEnergyRadius lower L positive test mode) (highEnergyRadius lower L positive field mode) +
      (highMultiplier mode.val.1 : ℂ) *
        (inner ℂ (highEnergyCell lower L positive test mode) (highEnergyCell lower L positive field mode) +
          inner ℂ (highEnergyAngularRadius lower L positive test mode) (highEnergyAngularRadius lower L positive field mode)) := by
  rw [annularEnergyMass_pairing_mode, highEnergyCell_mode, highEnergyCell_mode,
    highEnergyAngularRadius_mode, highEnergyAngularRadius_mode]
  simp only [inner_smul_left, inner_smul_right, map_mul, Complex.conj_I, Complex.conj_ofReal, map_intCast]
  push_cast
  have modeIdentity := highMultiplier_angular_identity mode
  ring_nf
  simp only [Complex.I_sq]
  linear_combination -inner ℂ (highEnergyRadius lower L positive test mode)
    (highEnergyRadius lower L positive field mode) * modeIdentity

variable (parameters : PhaseParameters) (lower L : ℝ) (positive : 0 < lower)
    (lengthPositive : 0 < L) (widthHalf : parameters.gamma ≤ 1 / 2)
    (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * L))

/-- All original circular flux signs, decode factors, and phase terms give the SAME mode energy pairing. -/
theorem circularPhysical_pairing_mode (mode : HighAnnularMode) (field test : annularEnergySpace lower L positive) :
    -(inner ℂ (highPhysicalTestDerivative parameters lower L positive lengthPositive widthHalf widthLength test mode)
        (circularHighX parameters lower L positive lengthPositive widthHalf widthLength field mode) +
      inner ℂ (highEnergyCell lower L positive (bEnergyDecode lower L positive test) mode)
        (circularHighC lower L positive field mode) +
      inner ℂ (highEnergyAngularRadius lower L positive (bEnergyDecode lower L positive test) mode)
        (circularHighRV parameters lower L positive lengthPositive widthHalf widthLength field mode)) =
      inner ℂ (annularEnergyDerivative lower L positive test mode +
        annularTiltEnergyPhase parameters lower L positive lengthPositive widthHalf widthLength test mode)
        (annularEnergyDerivative lower L positive field mode -
          annularTiltEnergyPhase parameters lower L positive lengthPositive widthHalf widthLength field mode) +
      2 * (inner ℂ (annularEnergyDerivative lower L positive test mode) (highEnergyRadius lower L positive field mode) +
        inner ℂ (highEnergyRadius lower L positive test mode) (annularEnergyDerivative lower L positive field mode)) +
      inner ℂ (annularEnergyMass lower L positive test mode) (annularEnergyMass lower L positive field mode) := by
  let h : ℂ := Real.sqrt (highMultiplier mode.val.1)
  let dt := annularEnergyDerivative lower L positive test mode
  let df := annularEnergyDerivative lower L positive field mode
  let pt := annularTiltEnergyPhase parameters lower L positive lengthPositive widthHalf widthLength test mode
  let pf := annularTiltEnergyPhase parameters lower L positive lengthPositive widthHalf widthLength field mode
  let rt := highEnergyRadius lower L positive test mode
  let rf := highEnergyRadius lower L positive field mode
  let ct := highEnergyCell lower L positive test mode
  let cf := highEnergyCell lower L positive field mode
  let af := highEnergyAngularRadius lower L positive field mode
  have xLaw : circularHighX parameters lower L positive lengthPositive widthHalf widthLength field mode =
      -retainedBInverseMultiplier mode.val • (h • (df - pf + (2 : ℂ) • rf)) := by
    rw [circularHighX_mode, highPhysicalDerivative_decoded_mode, decodedRadius_mode]
    change -retainedBInverseMultiplier mode.val • (h • (df - pf) + (2 : ℂ) • (h • rf)) = _
    congr 1
    rw [smul_add, smul_comm (2 : ℂ) h]
  have tLaw : highPhysicalTestDerivative parameters lower L positive lengthPositive widthHalf widthLength test mode = h • (dt + pt) :=
    highPhysicalTestDerivative_decoded_mode parameters lower L positive lengthPositive widthHalf widthLength test mode
  have ctLaw : highEnergyCell lower L positive (bEnergyDecode lower L positive test) mode = h • ct :=
    decodedCell_mode lower L positive test mode
  have cfLaw : highEnergyCell lower L positive (bEnergyDecode lower L positive field) mode = h • cf :=
    decodedCell_mode lower L positive field mode
  have cLaw : circularHighC lower L positive field mode = -(h • cf) :=
    (circularHighC_mode lower L positive field mode).trans (congrArg Neg.neg cfLaw)
  have atLaw : highEnergyAngularRadius lower L positive (bEnergyDecode lower L positive test) mode =
      h • ((Complex.I * (mode.val.1 : ℂ)) • rt) :=
    (decodedAngularRadius_mode lower L positive test mode).trans
      (congrArg (fun vector => h • vector) (highEnergyAngularRadius_mode lower L positive test mode))
  have afLaw : highEnergyAngularRadius lower L positive (bEnergyDecode lower L positive field) mode = h • af :=
    decodedAngularRadius_mode lower L positive field mode
  have rvLaw : circularHighRV parameters lower L positive lengthPositive widthHalf widthLength field mode =
      -(h • af) - (2 : ℂ) • (angularInverseMultiplier mode.val •
        (-retainedBInverseMultiplier mode.val • (h • (df - pf + (2 : ℂ) • rf)))) :=
    (circularHighRV_mode parameters lower L positive lengthPositive widthHalf widthLength field mode).trans
      (congrArg₂ (· - ·) (congrArg Neg.neg afLaw)
        (congrArg (fun vector => (2 : ℂ) • (angularInverseMultiplier mode.val • vector)) xLaw))
  have first := congrArg₂ (fun left right : RadialL2 1 lower => inner ℂ left right) tLaw xLaw
  have second := congrArg₂ (fun left right : RadialL2 1 lower => inner ℂ left right) ctLaw cLaw
  have third := congrArg₂ (fun left right : RadialL2 1 lower => inner ℂ left right) atLaw rvLaw
  have decoded := congrArg Neg.neg (congrArg₂ (· + ·) (congrArg₂ (· + ·) first second) third)
  apply decoded.trans
  have scalar := circular_scalar_pairing mode (dt + pt) rt ct (df - pf + (2 : ℂ) • rf) af cf
  change -(inner ℂ (h • (dt + pt)) (-retainedBInverseMultiplier mode.val • (h • (df - pf + (2 : ℂ) • rf))) +
    inner ℂ (h • ct) (-(h • cf)) + inner ℂ (h • ((Complex.I * (mode.val.1 : ℂ)) • rt))
      (-(h • af) - (2 : ℂ) • (angularInverseMultiplier mode.val •
        (-retainedBInverseMultiplier mode.val • (h • (df - pf + (2 : ℂ) • rf)))))) = _
  rw [scalar, annularEnergyMass_pairing_decomposed]
  have commute := phase_radius_pairing parameters lower L positive lengthPositive widthHalf widthLength mode test field
  change inner ℂ pt rf = inner ℂ rt pf at commute
  change inner ℂ (dt + pt) (df - pf + (2 : ℂ) • rf) +
    2 * inner ℂ rt (df - pf + (2 : ℂ) • rf) +
    (highMultiplier mode.val.1 : ℂ) * (inner ℂ ct cf + inner ℂ ((Complex.I * (mode.val.1 : ℂ)) • rt) af) =
    inner ℂ (dt + pt) (df - pf) + 2 * (inner ℂ dt rf + inner ℂ rt df) +
      (4 * inner ℂ rt rf + (highMultiplier mode.val.1 : ℂ) *
        (inner ℂ ct cf + inner ℂ (highEnergyAngularRadius lower L positive test mode) af))
  rw [highEnergyAngularRadius_mode]
  simp only [inner_add_left, inner_add_right, inner_sub_right, inner_smul_right]
  rw [commute]
  ring

end Grad.AnnularCircularForm
