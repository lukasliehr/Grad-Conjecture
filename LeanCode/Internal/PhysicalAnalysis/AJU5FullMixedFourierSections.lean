import AJU4FullPhysicalFourierSymbols

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open Set Filter MeasureTheory
open scoped ContDiff Interval ENNReal BigOperators
namespace Grad.AnnularPhysicalFourier
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularSourceGraph Grad.AnnularJointRegularity Grad.AnnularRegularity

variable (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (jet : PhysicalFourierJet lower positive bounded)

def physicalMixedFourierSection (radial angular cell : ℕ) (angles : ℝ × ℝ) : RadialContinuousSection 1 lower :=
  ∑' mode : ℤ × ℤ, physicalFourierCoefficient angular cell mode angles • jet.sections radial mode

theorem physicalFourierSection_terms_summable (radial angular cell : ℕ) (angles : ℝ × ℝ) :
    Summable (fun mode : ℤ × ℤ => physicalFourierCoefficient angular cell mode angles • jet.sections radial mode) := by
  apply Summable.of_norm_bounded (jet.summable radial (angular + cell))
  intro mode
  rw [norm_smul]
  exact mul_le_mul_of_nonneg_right (physicalFourierCoefficient_norm_le angular cell mode angles) (norm_nonneg _)

theorem physicalMixedFourierSection_apply (radial angular cell : ℕ) (angles : ℝ × ℝ)
    (radius : Icc lower (1 : ℝ)) :
    physicalMixedFourierSection lower positive bounded jet radial angular cell angles radius =
      ∑' mode : ℤ × ℤ, physicalFourierCoefficient angular cell mode angles • jet.sections radial mode radius :=
  (ContinuousMap.tsum_apply
    (physicalFourierSection_terms_summable lower positive bounded jet radial angular cell angles) radius).symm

theorem physicalMixedFourierSection_continuous (radial angular cell : ℕ) :
    Continuous (physicalMixedFourierSection lower positive bounded jet radial angular cell) := by
  apply continuous_tsum
    (fun mode => (physicalFourierCoefficient_continuous angular cell mode).smul continuous_const)
    (jet.summable radial (angular + cell))
  intro mode angles
  change ‖physicalFourierCoefficient angular cell mode angles • jet.sections radial mode‖ ≤ _
  rw [norm_smul]
  exact mul_le_mul_of_nonneg_right (physicalFourierCoefficient_norm_le angular cell mode angles) (norm_nonneg _)

/-- Full-mode Fourier summation retains the genuine closed radial primitive
law established for the actual Hilbert jets. -/
theorem physicalMixedFourierSection_radial (radial angular cell : ℕ) (angles : ℝ × ℝ) :
    AnnularSectionDerivative lower positive bounded.le
      (physicalMixedFourierSection lower positive bounded jet radial angular cell angles)
      (physicalMixedFourierSection lower positive bounded jet (radial + 1) angular cell angles) :=
  annularSectionDerivative_tsum lower positive bounded.le _ _
    (physicalFourierSection_terms_summable lower positive bounded jet radial angular cell angles)
    (physicalFourierSection_terms_summable lower positive bounded jet (radial + 1) angular cell angles)
    (fun mode => annularSectionDerivative_smul lower positive bounded.le _ _
      (jet.derivative radial mode) (physicalFourierCoefficient angular cell mode angles))

theorem physicalMixedFourierSection_radialDerivative (radial angular cell : ℕ) (angles : ℝ × ℝ)
    (radius : ℝ) (inside : radius ∈ Icc lower 1) :
    HasDerivWithinAt
      (radialSectionExtension 1 lower bounded.le
        (physicalMixedFourierSection lower positive bounded jet radial angular cell angles))
      (physicalMixedFourierSection lower positive bounded jet (radial + 1) angular cell angles ⟨radius, inside⟩)
      (Icc lower 1) radius :=
  annularSectionDerivative_hasDerivWithinAt lower positive bounded.le _ _
    (physicalMixedFourierSection_radial lower positive bounded jet radial angular cell angles) radius inside

end Grad.AnnularPhysicalFourier
