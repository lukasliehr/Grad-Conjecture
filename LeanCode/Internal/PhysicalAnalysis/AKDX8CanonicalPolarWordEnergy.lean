import AKDX7FiniteCellAngularEnergy
import AKV19ActualCartesianWeightedRadialSmoothness

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1700000
open Set Filter MeasureTheory
open scoped BigOperators ContDiff Topology ENNReal
namespace Grad.OriginalCollarNorm
open Grad.ClosedJets Grad.CartesianState Grad.BoundaryTrace Grad.BoundaryLift
open Grad.SourceCollarDivision Grad.SourceCollarRestriction Grad.SourceCollarCoefficients
open Grad.AnnularGeneralSourceRegularity

/-- The SAME canonical weighted radial curve pays each full polar tensor
word over every finite axial support, at exactly radial plus angular order. -/
theorem canonicalPolarWord_energy {dimension : ℕ} (parameters : PhaseParameters)
    (lower : ℝ) (positive : 0<lower) (bounded : lower<1) (core : ACore parameters dimension)
    (order : ℕ) (word : CartesianWord order) (radius : ℝ) (inside : radius∈Icc lower 1)
    (cells : Finset ℤ) :
    (∑ cell∈cells,∫ angle in -Real.pi..Real.pi,
      ‖polarWordField (originalPolarValue (phaseWeightedJet parameters cell (core.val cell))) word (radius,angle)‖^2)≤
      (2*Real.pi)*‖cartesianWeightedRadialCurve parameters lower positive bounded core
        (polarWordCount word 1) (polarWordCount word 0) radius‖^2 := by
  apply finiteCell_angular_energy_bound cells _ _
    (fun cell => (polarWordField_smooth _ (originalPolarValue_smooth _) word).continuous.comp
      (continuous_const.prodMk continuous_id))
  intro cell mode
  change ‖angularCoefficient (fun angle => polarWordField
    (originalPolarValue (phaseWeightedJet parameters cell (core.val cell))) word (radius,angle)) mode‖ ≤
    ‖(cartesianWeightedRadialCurve parameters lower positive bounded core
      (polarWordCount word 1) (polarWordCount word 0) radius).val (mode,cell)‖
  rw [polarWordField_coefficient _ (originalPolarValue_smooth _) (originalPolarValue_periodic _),
    cartesianWeightedRadialCurve_coefficient parameters lower positive bounded core _ _ (mode,cell) radius inside]
  change ‖(Complex.I*(mode:ℂ))^(polarWordCount word 1) •
      radialCoefficientJet _ mode (polarWordCount word 0) radius‖≤
    ‖(annularFrequency mode cell:ℂ)^(polarWordCount word 1) •
      radialCoefficientJet _ mode (polarWordCount word 0) radius‖
  rw [norm_smul,norm_smul,norm_pow,norm_pow]
  apply mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) ?_ _) (norm_nonneg _)
  rw [norm_mul,Complex.norm_I,one_mul]
  have modeNorm : ‖(mode:ℂ)‖=|(mode:ℝ)| := by norm_cast
  rw [modeNorm,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (annularFrequency_nonnegative mode cell)]
  unfold annularFrequency
  linarith [abs_nonneg (cell:ℝ)]

end Grad.OriginalCollarNorm
