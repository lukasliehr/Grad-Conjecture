import ADY6OriginalLowDataAndTrace

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal
namespace Grad.AnnularLowEnergy
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularVariational Grad.AnnularSourceGraph Grad.AnnularReconstruction Grad.AnnularFluxTrace
open Grad.CircularHighRegularity Grad.PhaseAlgebra
open Grad.GaugeCoefficients.Physical.WeightedTrace

/-- The original BE2 constants, independent of the inner radius. -/
def lowEta (length gamma : ℝ) : ℝ :=
  min (Real.sqrt 2 * gamma * length) (length / (2 * (length + 1)))

def lowBalanceConstant (length gamma : ℝ) : ℝ :=
  max 1 (max (16 / (gamma * length)) (16 / lowEta length gamma))

def lowAmplitude (length gamma : ℝ) (mode : LowAnnularMode) : ℝ :=
  if |mode.val.1| = 1 then (Real.sqrt 3)⁻¹ else lowBalanceConstant length gamma

theorem lowAmplitude_pos (length gamma : ℝ) (mode : LowAnnularMode) : 0 < lowAmplitude length gamma mode := by
  unfold lowAmplitude
  split_ifs
  · positivity
  · exact zero_lt_one.trans_le (le_max_left _ _)

/-- The physical coordinate map is exactly exp(Phi)(a_m mu xi,x). -/
def lowPhysicalFactor (parameters : PhaseParameters) (length radius : ℝ) (index : LowAnnularIndex) : ℝ :=
  Real.exp (radialPhase parameters radius index.2.val.2) *
    if index.1 = 0 then lowAmplitude length parameters.gamma index.2 * lowMu length radius index.2.val.2 else 1

theorem lowPhysicalFactor_pos (parameters : PhaseParameters) (length radius : ℝ)
    (positive : 0 < radius) (index : LowAnnularIndex) : 0 < lowPhysicalFactor parameters length radius index := by
  unfold lowPhysicalFactor
  apply mul_pos (Real.exp_pos _)
  split_ifs
  · exact mul_pos (lowAmplitude_pos _ _ _) (lowMu_pos _ _ _ positive)
  · exact zero_lt_one

/-- Both directions on the full untruncated physical Fourier family. -/
def lowPhysicalCoordinateEquiv (parameters : PhaseParameters) (length radius : ℝ) (positive : 0 < radius) :
    (LowAnnularIndex → ComplexEuclidean 1) ≃ₗ[ℂ] (LowAnnularIndex → ComplexEuclidean 1) where
  toFun physical index := lowPhysicalFactor parameters length radius index • physical index
  invFun weighted index := (lowPhysicalFactor parameters length radius index)⁻¹ • weighted index
  map_add' first second := by funext index; exact smul_add _ _ _
  map_smul' scalar physical := by funext index; exact smul_comm (lowPhysicalFactor parameters length radius index) scalar (physical index)
  left_inv physical := by
    funext index
    dsimp only
    rw [smul_smul, inv_mul_cancel₀ (lowPhysicalFactor_pos parameters length radius positive index).ne', one_smul]
  right_inv weighted := by
    funext index
    dsimp only
    rw [smul_smul, mul_inv_cancel₀ (lowPhysicalFactor_pos parameters length radius positive index).ne', one_smul]

def lowPhysicalInverseCurve (parameters : PhaseParameters) (lower length : ℝ)
    (positive : 0 < lower) (index : LowAnnularIndex) : C(ℝ, ℝ) :=
  if index.1 = 0 then
    (lowAmplitude length parameters.gamma index.2)⁻¹ •
      (annularInversePhase parameters index.2.val.2 * lowMuInverseCurve lower length positive index.2.val.2)
  else annularInversePhase parameters index.2.val.2

theorem lowPhysicalInverseCurve_original (parameters : PhaseParameters) (lower length : ℝ)
    (positive : 0 < lower) (index : LowAnnularIndex) (radius : ℝ) (inside : radius ∈ Icc lower 1) :
    lowPhysicalInverseCurve parameters lower length positive index radius =
      (lowPhysicalFactor parameters length radius index)⁻¹ := by
  unfold lowPhysicalInverseCurve lowPhysicalFactor
  split_ifs with component
  · change (lowAmplitude length parameters.gamma index.2)⁻¹ *
      (Real.exp (-radialPhase parameters radius index.2.val.2) *
        (lowMu length (max lower radius) index.2.val.2)⁻¹) = _
    rw [max_eq_right inside.1, Real.exp_neg, mul_inv_rev, mul_inv_rev]
    ring
  · change Real.exp (-radialPhase parameters radius index.2.val.2) = _
    rw [mul_one, Real.exp_neg]

/-- The two physical entries are xi and x=Rp, realized on the same closed interval. -/
def lowPhysicalSection (parameters : PhaseParameters) (lower length : ℝ)
    (positive : 0 < lower) (bounded : lower < 1) (field : lowEnergyGraph lower length positive)
    (index : LowAnnularIndex) : RadialContinuousSection 1 lower :=
  radialSectionScalar lower (lowPhysicalInverseCurve parameters lower length positive index)
    (lowEnergySection lower length positive bounded field index)

theorem lowPhysicalSection_encode (parameters : PhaseParameters) (lower length : ℝ)
    (positive : 0 < lower) (bounded : lower < 1) (field : lowEnergyGraph lower length positive)
    (index : LowAnnularIndex) (radius : Icc lower (1 : ℝ)) :
    lowPhysicalFactor parameters length radius.val index •
      lowPhysicalSection parameters lower length positive bounded field index radius =
        lowEnergySection lower length positive bounded field index radius := by
  change lowPhysicalFactor parameters length radius.val index •
    (lowPhysicalInverseCurve parameters lower length positive index radius.val •
      lowEnergySection lower length positive bounded field index radius) = _
  rw [lowPhysicalInverseCurve_original parameters lower length positive index radius.val radius.property,
    smul_smul, mul_inv_cancel₀ (lowPhysicalFactor_pos parameters length radius.val (positive.trans_le radius.property.1) index).ne', one_smul]

theorem lowPhysicalSection_xi (parameters : PhaseParameters) (lower length : ℝ)
    (positive : 0 < lower) (bounded : lower < 1) (field : lowEnergyGraph lower length positive)
    (mode : LowAnnularMode) (radius : Icc lower (1 : ℝ)) :
    Real.exp (radialPhase parameters radius.val mode.val.2) •
      ((lowAmplitude length parameters.gamma mode * lowMu length radius.val mode.val.2) •
        lowPhysicalSection parameters lower length positive bounded field (0, mode) radius) =
      lowEnergySection lower length positive bounded field (0, mode) radius := by
  rw [smul_smul]
  exact lowPhysicalSection_encode parameters lower length positive bounded field (0, mode) radius

theorem lowPhysicalSection_x (parameters : PhaseParameters) (lower length : ℝ)
    (positive : 0 < lower) (bounded : lower < 1) (field : lowEnergyGraph lower length positive)
    (mode : LowAnnularMode) (radius : Icc lower (1 : ℝ)) :
    Real.exp (radialPhase parameters radius.val mode.val.2) •
        lowPhysicalSection parameters lower length positive bounded field (1, mode) radius =
      lowEnergySection lower length positive bounded field (1, mode) radius := by
  have equality := lowPhysicalSection_encode parameters lower length positive bounded field (1, mode) radius
  simpa only [lowPhysicalFactor, show (1 : Fin 2) ≠ 0 from by decide, ↓reduceIte, mul_one] using equality

def lowRotationSymbol (mode : LowAnnularMode) : ℂ := Complex.I * (mode.val.1 : ℂ)

theorem lowRotationSymbol_ne_zero (mode : LowAnnularMode) : lowRotationSymbol mode ≠ 0 := by
  have nonzero : mode.val.1 ≠ 0 := by
    intro zero
    have property := mode.property
    rw [zero, abs_zero] at property
    norm_num at property
  exact mul_ne_zero Complex.I_ne_zero (by exact_mod_cast nonzero)

/-- The incoming p convention is recovered from x using the actual R symbol. -/
def lowPhysicalPSection (parameters : PhaseParameters) (lower length : ℝ)
    (positive : 0 < lower) (bounded : lower < 1) (field : lowEnergyGraph lower length positive)
    (mode : LowAnnularMode) : RadialContinuousSection 1 lower :=
  (lowRotationSymbol mode)⁻¹ • lowPhysicalSection parameters lower length positive bounded field (1, mode)

theorem lowPhysicalPSection_R (parameters : PhaseParameters) (lower length : ℝ)
    (positive : 0 < lower) (bounded : lower < 1) (field : lowEnergyGraph lower length positive)
    (mode : LowAnnularMode) (radius : Icc lower (1 : ℝ)) :
    lowRotationSymbol mode • lowPhysicalPSection parameters lower length positive bounded field mode radius =
      lowPhysicalSection parameters lower length positive bounded field (1, mode) radius := by
  change lowRotationSymbol mode • ((lowRotationSymbol mode)⁻¹ •
    lowPhysicalSection parameters lower length positive bounded field (1, mode) radius) = _
  rw [smul_smul, mul_inv_cancel₀ (lowRotationSymbol_ne_zero mode), one_smul]

/-- The incoming flux datum is the normalized exp(Phi) R p, never a replacement p. -/
theorem lowIncomingTrace_physical_p (parameters : PhaseParameters) (lower length : ℝ)
    (positive : 0 < lower) (bounded : lower < 1) (field : lowEnergyGraph lower length positive)
    (mode : LowAnnularMode) :
    lowIncomingTrace lower length positive bounded field (1, mode) =
      (lower ^ (-(7 / 4 : ℝ)) * (Real.sqrt (lowMu length lower mode.val.2))⁻¹) •
        (Real.exp (radialPhase parameters lower mode.val.2) •
          (lowRotationSymbol mode • lowPhysicalPSection parameters lower length positive bounded field mode
            ⟨lower, le_rfl, bounded.le⟩)) := by
  have encoded := lowPhysicalSection_x parameters lower length positive bounded field mode ⟨lower, le_rfl, bounded.le⟩
  rw [lowPhysicalPSection_R, encoded, lowIncomingTrace_apply]
  rfl

end Grad.AnnularLowEnergy
