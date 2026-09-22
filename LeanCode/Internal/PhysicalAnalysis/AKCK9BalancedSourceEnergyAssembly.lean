import AKCK6SameKnownSevenSourceEnergy
import AKCK8SameActualBalancedSource

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open Set Filter MeasureTheory
open scoped BigOperators ENNReal Topology
namespace Grad.OriginalCartesianTameEstimate
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.SourceCollarCoefficients Grad.SourceCollarFullSource Grad.AnnularGeneralSourceRegularity
open Grad.AnnularKernelL2 Grad.AnnularReconstruction Grad.AnnularStrongData Grad.AnnularSmoothCore
open Grad.AxisCore Grad.QuotientProjection Grad.FlatSourceProjection Grad.ExhaustionSourceAllocation
open Grad.GaugeCoefficients.Physical.Allocation

/-- Combining the literal four source inputs preserves a single high-source
payment and a single coefficient-times-independent-base payment. -/
theorem fourInput_squareEnergy {α E F G H J : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedAddCommGroup G]
    [NormedAddCommGroup H] [NormedAddCommGroup J]
    (measure : Measure α) (output : α → E) (first : α → F) (second : α → G)
    (third : α → H) (fourth : α → J)
    (firstM : AEStronglyMeasurable first measure) (secondM : AEStronglyMeasurable second measure)
    (thirdM : AEStronglyMeasurable third measure) (fourthM : AEStronglyMeasurable fourth measure)
    (C B A D T U : ℝ) (C0 : 0≤C) (B0 : 0≤B) (A0 : 0≤A) (D0 : 0≤D) (T0 : 0≤T) (U0 : 0≤U)
    (bound : ∀ᵐ point ∂measure, ‖output point‖ ≤ C*(‖first point‖+B*‖second point‖+‖third point‖+‖fourth point‖))
    (firstE : (∫⁻ point, ENNReal.ofReal (‖first point‖^2) ∂measure) ≤ ENNReal.ofReal (A^2))
    (secondE : (∫⁻ point, ENNReal.ofReal (‖second point‖^2) ∂measure) ≤ ENNReal.ofReal (D^2))
    (thirdE : (∫⁻ point, ENNReal.ofReal (‖third point‖^2) ∂measure) ≤ ENNReal.ofReal (T^2))
    (fourthE : (∫⁻ point, ENNReal.ofReal (‖fourth point‖^2) ∂measure) ≤ ENNReal.ofReal (U^2)) :
    (∫⁻ point, ENNReal.ofReal (‖output point‖^2) ∂measure) ≤
      ENNReal.ofReal ((4*C*(A+B*D+T+U))^2) := by
  let known := fun point => ‖first point‖+B*‖second point‖
  let direct := fun point => ‖third point‖+‖fourth point‖
  have knownN (point : α) : 0 ≤ known point := by dsimp only [known]; positivity
  have directN (point : α) : 0 ≤ direct point := by dsimp only [direct]; positivity
  have knownE := twoInput_squareEnergy measure known first second firstM secondM 1 B A D
    zero_le_one B0 A0 D0 (Filter.Eventually.of_forall (fun point => by
      rw [Real.norm_of_nonneg (knownN point),one_mul])) firstE secondE
  have directE := twoInput_squareEnergy measure direct third fourth thirdM fourthM 1 1 T U
    zero_le_one zero_le_one T0 U0 (Filter.Eventually.of_forall (fun point => by
      rw [Real.norm_of_nonneg (directN point),one_mul,one_mul])) thirdE fourthE
  have combined := twoInput_squareEnergy measure output known direct
    (firstM.norm.add (secondM.norm.const_mul B)) (thirdM.norm.add fourthM.norm)
    C 1 (2*1*(A+B*D)) (2*1*(T+1*U)) C0 zero_le_one (by positivity) (by positivity)
    (by filter_upwards [bound] with point bound
        simpa only [Real.norm_of_nonneg (knownN point),Real.norm_of_nonneg (directN point),
          one_mul,known,direct,add_assoc] using bound) knownE directE
  have scalar : 2*C*(2*1*(A+B*D)+1*(2*1*(T+1*U))) = 4*C*(A+B*D+T+U) := by ring
  rw [scalar] at combined
  exact combined

theorem radius_smul_squareEnergy {E : Type*}
    (norm : E → ℝ) (act : ℝ → E → E)
    (nonnegative : ∀ value, 0 ≤ norm value)
    (homogeneous : ∀ radius value, norm (act radius value) = |radius| * norm value)
    (lower : ℝ) (positive : 0 < lower) (curve : ℝ → E) (payment : ℝ)
    (energy : (∫⁻ radius in Icc lower 1, ENNReal.ofReal ((norm (curve radius))^2)) ≤ ENNReal.ofReal (payment^2)) :
    (∫⁻ radius in Icc lower 1, ENNReal.ofReal ((norm (act radius (curve radius)))^2)) ≤ ENNReal.ofReal (payment^2) := by
  apply (lintegral_mono_ae ?_).trans energy
  filter_upwards [ae_restrict_mem measurableSet_Icc] with radius inside
  apply ENNReal.ofReal_le_ofReal
  apply (sq_le_sq₀ (nonnegative _) (nonnegative _)).mpr
  rw [homogeneous, abs_of_nonneg (positive.le.trans inside.1)]
  exact (mul_le_mul_of_nonneg_right inside.2 (nonnegative _)).trans_eq (one_mul _)

attribute [local irreducible] actualOriginalG3RadialCurves originalAngularDecode actualOriginalG3Row fullG3Row

/-- Literal wrapper equality is proved before energy assembly, so dependent
source-row normalization is not repeated beneath the integral. -/
theorem actualThirdCurve_formula (parameters : PhaseParameters) (length rho epsilon : ℝ)
    (field : ACore parameters 3)
    (small : physicalBudget parameters field rho epsilon 6 ≤ originalCoefficientLowRadius parameters length)
    (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1) (grade : ℕ)
    (source : SmoothQuotient parameters) (flat : IsFlat source) (radius : ℝ) :
    actualCartesianThirdCurve parameters length rho epsilon field small lower positive bounded source flat (grade+1) radius =
    radius • (actualOriginalG3RadialCurves parameters length rho epsilon field small lower positive bounded source flat).curve (grade+1) radius := by
  unfold actualCartesianThirdCurve
  congr

/-- The literal rG3 keeps the q+4 sharp energy on the fixed positive collar. -/
theorem actualThirdCurve_fourEnergy (parameters : PhaseParameters) (length rho epsilon : ℝ)
    (field : ACore parameters 3)
    (small : physicalBudget parameters field rho epsilon 6 ≤ originalCoefficientLowRadius parameters length)
    (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1) (grade : ℕ)
    (source : SmoothQuotient parameters) (flat : IsFlat source) :
    (∫⁻ radius in Icc lower 1, ENNReal.ofReal
      (‖actualCartesianThirdCurve parameters length rho epsilon field small lower positive bounded source flat (grade+1) radius‖^2)) ≤
      ENNReal.ofReal ((lower⁻¹ *
        (g3HighConstant parameters length grade * ‖quotientEta parameters (grade+4) source‖ +
          g3LowConstant parameters length grade * physicalBudget parameters field rho epsilon (grade+6) *
            ‖quotientEta parameters 3 source‖))^2) := by
  have same :
      (∫⁻ radius in Icc lower 1, ENNReal.ofReal
        (‖actualCartesianThirdCurve parameters length rho epsilon field small lower positive bounded source flat (grade+1) radius‖^2)) =
      ∫⁻ radius in Icc lower 1, ENNReal.ofReal
        (‖radius • (actualOriginalG3RadialCurves parameters length rho epsilon field small lower positive bounded source flat).curve (grade+1) radius‖^2) :=
    lintegral_congr_ae (Filter.Eventually.of_forall (fun radius =>
      congrArg (fun value : CellL2 1 => ENNReal.ofReal (‖value‖^2))
        (actualThirdCurve_formula parameters length rho epsilon field small lower positive bounded grade source flat radius)))
  apply same.trans_le
  exact radius_smul_squareEnergy (fun value : CellL2 1 => ‖value‖)
    (fun (radius : ℝ) (value : CellL2 1) => radius • value) norm_nonneg
    (fun radius value => by rw [norm_smul, Real.norm_eq_abs]) lower positive _ _
    (actualG3SourceCurve_fourEnergy parameters length rho epsilon field small lower positive bounded grade source flat)

end Grad.OriginalCartesianTameEstimate
