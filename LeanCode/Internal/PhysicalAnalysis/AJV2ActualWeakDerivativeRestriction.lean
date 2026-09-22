import AJV1ActualCollarL2Restriction

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
open Set Filter MeasureTheory
open scoped ContDiff
namespace Grad.AnnularRestriction
open Grad.ClosedJets Grad.GaugeCoefficients.Physical.WeightedTrace Grad.AnnularSourceGraph

/-- Supported interior tests see the same physical integral on both collars. -/
theorem collarPairing_restrict (dimension : ℕ) (lower upper : ℝ) (included : lower ≤ upper)
    (test : C(ℝ, ℝ)) (supported : tsupport test ⊆ Icc upper 1)
    (vector : ComplexEuclidean dimension) (field : CollarL2 (ComplexEuclidean dimension) lower) :
    collarPairing upper test vector (collarL2Restriction dimension lower upper included field) =
      collarPairing lower test vector field := by
  rw [collarPairing_integral, collarPairing_integral]
  calc
    _ = ∫ radius in Icc upper 1, test radius • inner ℂ vector (field radius) := by
      apply integral_congr_ae
      filter_upwards [collarL2Restriction_ae dimension lower upper included field] with radius actual
      rw [actual]
    _ = ∫ radius : ℝ, test radius • inner ℂ vector (field radius) := by
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro radius outside
      have zero : test radius = 0 := image_eq_zero_of_notMem_tsupport
        (fun member => outside (supported member))
      rw [zero, zero_smul]
    _ = ∫ radius in Icc lower 1, test radius • inner ℂ vector (field radius) := by
      symm
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro radius outside
      have zero : test radius = 0 := image_eq_zero_of_notMem_tsupport
        (fun member => outside (Icc_subset_Icc included le_rfl (supported member)))
      rw [zero, zero_smul]

/-- Restricting an actual weak derivative creates no boundary source: tests
have compact support inside the new collar and are valid old-collar tests. -/
theorem collarWeakDerivative_restrict (dimension : ℕ) (lower upper : ℝ)
    (included : lower ≤ upper) (positive : 0 < upper) (bounded : upper < 1)
    (field derivative : CollarL2 (ComplexEuclidean dimension) lower)
    (weak : CollarWeakDerivative lower field derivative) :
    CollarWeakDerivative upper (collarL2Restriction dimension lower upper included field)
      (collarL2Restriction dimension lower upper included derivative) := by
  apply (compactWeak_iff_collarWeak dimension upper positive bounded _ _).mp
  intro test smooth _compact supported vector
  have supportedClosed : tsupport test ⊆ Icc upper 1 := supported.trans Ioo_subset_Icc_self
  have derivativeSupported : tsupport (deriv test) ⊆ Icc upper 1 :=
    tsupport_deriv_subset.trans supportedClosed
  rw [collarPairing_restrict dimension lower upper included ⟨test, smooth.continuous⟩ supportedClosed,
    collarPairing_restrict dimension lower upper included
      ⟨deriv test, (contDiff_infty_iff_deriv.mp smooth).2.continuous⟩ derivativeSupported]
  exact weak (collarCompactTest lower test smooth
    (fun _ member => ⟨included.trans_lt (supported member).1, (supported member).2⟩)) vector

end Grad.AnnularRestriction
