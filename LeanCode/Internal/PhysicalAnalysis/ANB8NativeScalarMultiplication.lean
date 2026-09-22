import ANB7BandWeightDerivatives

noncomputable section
set_option maxHeartbeats 1400000
open scoped ContDiff BigOperators
namespace Grad.BoundedScalarInverse
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.CircularHighWeak
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Algebra
open Grad.NonlinearProduct Grad.GaugeCoefficients.Physical.Compensated Grad.AnalyticWeights.Higher

def scalarMultiplicationConstant (grade : ℕ) (bounds : ℕ → ℝ) : ℝ :=
  Real.sqrt (Fintype.card (DerivativeIndex grade)) * ∑ index : DerivativeIndex grade,
    ∑ split : DerivativeSplit index, (splitMultiplicity index split : ℝ) *
      bounds (cartesianOrder (derivativeMultiIndex (lowerDerivativeIndex index split)))

theorem scalarMultiplicationConstant_nonnegative (grade : ℕ) (bounds : ℕ → ℝ) (nonnegative : ∀ order, 0 ≤ bounds order) :
    0 ≤ scalarMultiplicationConstant grade bounds :=
  mul_nonneg (Real.sqrt_nonneg _) (Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg
    (fun _ _ => mul_nonneg (Nat.cast_nonneg _) (nonnegative _))))

theorem scalarOperatorDerivative_bound (scalar : SpatialPlane → ℝ) (smooth : ContDiff ℝ ∞ scalar)
    (bounds : ℕ → ℝ) (nonnegative : ∀ order, 0 ≤ bounds order)
    (estimate : ∀ order (point : ClosedDisk), ‖iteratedFDeriv ℝ order scalar point.val‖ ≤ bounds order)
    (index : CartesianMultiIndex) :
    ‖smoothOperatorDerivative (apScalarOperatorJet 1 scalar smooth) index‖ ≤ bounds (cartesianOrder index) := by
  apply (ContinuousMap.norm_le _ (nonnegative _)).mpr
  intro point
  rw [apScalarOperatorJet_derivative, norm_smul]
  exact (mul_le_of_le_one_right (norm_nonneg _) (ContinuousLinearMap.norm_id_le)).trans
    ((orderedDerivative_norm_le _ _ _ _).trans (estimate _ point))

/-- Ordinary Hs multiplication from the genuine coefficient derivatives;
every derivative remains in the original Cartesian norm. -/
theorem native_scalar_multiplication (grade : ℕ) (scalar : SpatialPlane → ℝ) (smooth : ContDiff ℝ ∞ scalar)
    (bounds : ℕ → ℝ) (nonnegative : ∀ order, 0 ≤ bounds order)
    (estimate : ∀ order (point : ClosedDisk), ‖iteratedFDeriv ℝ order scalar point.val‖ ≤ bounds order)
    (field : ClosedJet 1) :
    ‖unitDiskCoreInto grade (smoothScalarWeightedJet scalar smooth field)‖ ≤
      scalarMultiplicationConstant grade bounds * ‖unitDiskCoreInto grade field‖ := by
  have constants : unitProductConstant grade (apScalarOperatorJet 1 scalar smooth) ≤ scalarMultiplicationConstant grade bounds := by
    unfold unitProductConstant scalarMultiplicationConstant
    apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
    apply Finset.sum_le_sum
    intro index _
    unfold unitProductIndexConstant
    exact Finset.sum_le_sum (fun split _ => mul_le_mul_of_nonneg_left
      (scalarOperatorDerivative_bound scalar smooth bounds nonnegative estimate _) (Nat.cast_nonneg _))
  rw [unitDiskCore_norm, unitDiskCore_norm, apScalarWeightedJet_eq_product]
  exact (unitProduct_bound grade _ field).trans (mul_le_mul_of_nonneg_right constants (norm_nonneg _))

def bandMultiplicationConstant (length gamma ceiling : ℝ) (grade : ℕ) : ℝ :=
  scalarMultiplicationConstant grade (bandWeightDerivativeConstant length gamma ceiling)

theorem bandMultiplicationConstant_nonnegative (length gamma ceiling : ℝ) (nonnegative : 0 ≤ gamma) (grade : ℕ) :
    0 ≤ bandMultiplicationConstant length gamma ceiling grade :=
  scalarMultiplicationConstant_nonnegative grade _ (bandWeightDerivativeConstant_nonnegative length gamma ceiling nonnegative)

theorem normalizedBandWeight_native {length sigma gamma scale : ℝ}
    (admissible : Grad.GaugeCoefficients.Envelope.Admissible length sigma gamma scale)
    (ceiling : ℝ) (cell : ℤ) (band : InCellBand length scale ceiling cell) (grade : ℕ) (field : ClosedJet 1) :
    ‖unitDiskCoreInto grade (smoothScalarWeightedJet (normalizedBandWeight gamma scale cell)
      (normalizedBandWeight_smooth gamma scale cell) field)‖ ≤
      bandMultiplicationConstant length gamma ceiling grade * ‖unitDiskCoreInto grade field‖ :=
  native_scalar_multiplication grade _ _ _
    (bandWeightDerivativeConstant_nonnegative length gamma ceiling (Grad.GaugeCoefficients.Envelope.admissible_gamma_nonnegative admissible))
    (normalizedBandWeight_derivative_bound admissible ceiling cell band) field

theorem inverseBandWeight_native {length sigma gamma scale : ℝ}
    (admissible : Grad.GaugeCoefficients.Envelope.Admissible length sigma gamma scale)
    (ceiling : ℝ) (cell : ℤ) (band : InCellBand length scale ceiling cell) (grade : ℕ) (field : ClosedJet 1) :
    ‖unitDiskCoreInto grade (smoothScalarWeightedJet (inverseBandWeight gamma scale cell)
      (inverseBandWeight_smooth gamma scale cell) field)‖ ≤
      bandMultiplicationConstant length gamma ceiling grade * ‖unitDiskCoreInto grade field‖ :=
  native_scalar_multiplication grade _ _ _
    (bandWeightDerivativeConstant_nonnegative length gamma ceiling (Grad.GaugeCoefficients.Envelope.admissible_gamma_nonnegative admissible))
    (inverseBandWeight_derivative_bound admissible ceiling cell band) field

end Grad.BoundedScalarInverse
