import AKV17OriginalEquationRadialRegularity
import AKN21OriginalSourceGraphRealization

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open Set Filter MeasureTheory
open scoped ContDiff
namespace Grad.AnnularGeneralSourceRegularity
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.SourceCollarRestriction Grad.SourceCollarCoefficients Grad.AnnularSourceGraph
open Grad.ExhaustionSourceAllocation Grad.AnnularSmoothCore

variable {dimension : ℕ} (parameters : PhaseParameters) (lower : ℝ)
    (positive : 0 < lower) (bounded : lower < 1) (field : ACore parameters dimension)

/-- The actual RSC source row at every radial order and original Fourier grade. -/
def cartesianWeightedRadialRow (grade order : ℕ) : DivisionRow dimension lower :=
  ⟨restrictionModeLp lower grade order parameters field,
    restrictionModeLp_memlp (grade := grade+order) lower positive bounded.le parameters field le_rfl⟩

def cartesianWeightedRadialGraph (grade order : ℕ) : AnnularSourceH1 parameters dimension lower 0 0 :=
  sourceGraphRealization parameters dimension lower positive bounded 0 0
    (cartesianWeightedRadialRow parameters lower positive bounded field grade order)
    (cartesianWeightedRadialRow parameters lower positive bounded field grade (order+1))
    (restrictionModeLp_weak_derivative lower positive bounded.le grade order parameters field)

def cartesianWeightedRadialSection (grade order : ℕ) : FourierContinuousSection dimension lower :=
  annularFourierSection parameters dimension lower positive bounded 0 0
    (cartesianWeightedRadialGraph parameters lower positive bounded field grade order)

/-- Literal scalar jets of W applied before radial differentiation. -/
def cartesianWeightedRadialCoefficient (grade order : ℕ) (mode : ℤ × ℤ) (radius : ℝ) : ComplexEuclidean dimension :=
  (annularFrequency mode.1 mode.2 : ℂ)^grade •
    radialCoefficientJet (originalPolarValue (phaseWeightedJet parameters mode.2 (field.val mode.2))) mode.1 order radius

theorem cartesianWeightedRadialCoefficient_smooth (grade order : ℕ) (mode : ℤ × ℤ) :
    ContDiff ℝ ∞ (cartesianWeightedRadialCoefficient parameters field grade order mode) :=
  (radialCoefficientJet_smooth _ (originalPolarValue_smooth _) _ _).const_smul _

theorem cartesianWeightedRadialGraph_mode (grade order : ℕ) (mode : ℤ × ℤ) :
    cartesianWeightedRadialGraph parameters lower positive bounded field grade order mode =
      weightedRadialCoreInto dimension lower
        (smoothRadialFunctionCore (cartesianWeightedRadialCoefficient parameters field grade order mode)
          (cartesianWeightedRadialCoefficient_smooth parameters field grade order mode)) := by
  apply weightedRadial_value_injective dimension lower positive bounded.le
  have value := congrArg (fun row : DivisionRow dimension lower => row mode)
    (sourceGraphRealization_value parameters dimension lower positive bounded 0 0
      (cartesianWeightedRadialRow parameters lower positive bounded field grade order)
      (cartesianWeightedRadialRow parameters lower positive bounded field grade (order+1))
      (restrictionModeLp_weak_derivative lower positive bounded.le grade order parameters field))
  change weightedRadialCoordinate dimension lower 0
    (cartesianWeightedRadialGraph parameters lower positive bounded field grade order mode) =
    restrictionModeLp lower grade order parameters field mode at value
  rw [value,weightedRadialCoordinate_core_zero]
  change (annularFrequency mode.1 mode.2 : ℂ)^grade • radialToLp lower _ _ =
    radialToLp lower (cartesianWeightedRadialCoefficient parameters field grade order mode)
      (cartesianWeightedRadialCoefficient_smooth parameters field grade order mode).continuous
  symm
  apply radialToLp_smul_of_interior lower positive ((annularFrequency mode.1 mode.2 : ℂ)^grade)
  intro radius inside
  rfl

theorem cartesianWeightedRadialSection_coefficient (grade order : ℕ) (mode : ℤ × ℤ) (radius : Icc lower (1 : ℝ)) :
    cartesianWeightedRadialSection parameters lower positive bounded field grade order radius mode =
      cartesianWeightedRadialCoefficient parameters field grade order mode radius.val := by
  unfold cartesianWeightedRadialSection
  rw [annularFourierSection_apply,cartesianWeightedRadialGraph_mode,weightedRadialSection_core]
  rfl

/-- The full actual Fourier sequence is continuous, including both collar endpoints. -/
def cartesianWeightedRadialCurve (grade order : ℕ) (radius : ℝ) : CellL2 dimension :=
  cartesianWeightedRadialSection parameters lower positive bounded field grade order (radialClamp lower bounded.le radius)

theorem cartesianWeightedRadialCurve_continuous (grade order : ℕ) :
    Continuous (cartesianWeightedRadialCurve parameters lower positive bounded field grade order) :=
  (cartesianWeightedRadialSection parameters lower positive bounded field grade order).continuous.comp (radialClamp_continuous lower bounded.le)

theorem cartesianWeightedRadialCurve_coefficient (grade order : ℕ) (mode : ℤ × ℤ) (radius : ℝ)
    (inside : radius ∈ Icc lower 1) :
    cartesianWeightedRadialCurve parameters lower positive bounded field grade order radius mode =
      cartesianWeightedRadialCoefficient parameters field grade order mode radius := by
  unfold cartesianWeightedRadialCurve
  rw [radialClamp_eq lower bounded.le radius inside]
  exact cartesianWeightedRadialSection_coefficient parameters lower positive bounded field grade order mode _

end Grad.AnnularGeneralSourceRegularity
