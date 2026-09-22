import GQF15ProjectionBounds

noncomputable section
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 200000

namespace Grad.GaugeCoefficients.Physical.Compensated
attribute [local instance] apNormedSpace

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.Constraints.Gauges
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Physical.Ledger
open Grad.GaugeCoefficients.Physical.WeightedTrace

theorem hilbertPair_norm_le {F G : Type*} [NormedAddCommGroup F] [NormedAddCommGroup G]
    (first : F) (second : G) : ‖WithLp.toLp 2 (first, second)‖ ≤ ‖first‖ + ‖second‖ := by
  have square := WithLp.prod_norm_sq_eq_of_L2 (WithLp.toLp 2 (first, second))
  change ‖WithLp.toLp 2 (first, second)‖ ^ 2 = ‖first‖ ^ 2 + ‖second‖ ^ 2 at square
  nlinarith [norm_nonneg (WithLp.toLp 2 (first, second)), norm_nonneg first, norm_nonneg second,
    mul_nonneg (norm_nonneg first) (norm_nonneg second)]

theorem hilbertTriple_norm_sq {F G H : Type*} [NormedAddCommGroup F]
    [NormedAddCommGroup G] [NormedAddCommGroup H] (first : F) (second : G) (third : H) :
    ‖WithLp.toLp 2 (first, WithLp.toLp 2 (second, third))‖ ^ 2 =
      ‖first‖ ^ 2 + ‖second‖ ^ 2 + ‖third‖ ^ 2 := by
  rw [WithLp.prod_norm_sq_eq_of_L2]
  change ‖first‖ ^ 2 + ‖WithLp.toLp 2 (second, third)‖ ^ 2 = _
  rw [WithLp.prod_norm_sq_eq_of_L2]
  change ‖first‖ ^ 2 + (‖second‖ ^ 2 + ‖third‖ ^ 2) = _
  ring

variable {L sigma gamma ell : ℝ}

/-- Exact AN8 source square norm, not the auxiliary sum used for estimates. -/
theorem capSourceGrade_norm_sq (grade : ℕ) (source : SmoothCapSource L sigma gamma ell) :
    ‖capSourceGrade grade source‖ ^ 2 =
      ‖apSmoothGrade L sigma gamma ell 2 (grade + 1) source.1‖ ^ 2 +
        ‖apSmoothGrade L sigma gamma ell 1 grade source.2.1‖ ^ 2 +
          ‖apSmoothGrade L sigma gamma ell 1 (grade + 1) source.2.2‖ ^ 2 :=
  hilbertTriple_norm_sq (source.1.val (grade + 1)) (source.2.1.val grade) (source.2.2.val (grade + 1))

theorem capSourceGrade_norm_le (grade : ℕ) (source : SmoothCapSource L sigma gamma ell) :
    ‖capSourceGrade grade source‖ ≤
      ‖apSmoothGrade L sigma gamma ell 2 (grade + 1) source.1‖ +
        ‖apSmoothGrade L sigma gamma ell 1 grade source.2.1‖ +
          ‖apSmoothGrade L sigma gamma ell 1 (grade + 1) source.2.2‖ := by
  have first := hilbertPair_norm_le (source.1.val (grade + 1))
    (WithLp.toLp 2 (source.2.1.val grade, source.2.2.val (grade + 1)))
  have second := hilbertPair_norm_le (source.2.1.val grade) (source.2.2.val (grade + 1))
  exact first.trans ((add_le_add le_rfl second).trans_eq (add_assoc _ _ _).symm)

theorem hilbertPairLinear_norm_le {E F G : Type*} [AddCommMonoid E] [Module ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [NormedAddCommGroup G] [NormedSpace ℂ G]
    (first : E →ₗ[ℂ] F) (second : E →ₗ[ℂ] G) (field : E) :
    ‖hilbertPairLinear first second field‖ ≤ ‖first field‖ + ‖second field‖ :=
  hilbertPair_norm_le _ _

theorem apSmoothGrade_denseRange (L sigma gamma ell : ℝ) (dimension grade : ℕ) :
    DenseRange (apSmoothGrade L sigma gamma ell dimension grade) := by
  apply (apFiniteInto_denseRange (dimension := dimension) (grade := grade) L sigma gamma ell).mono
  rintro _ ⟨core, rfl⟩
  exact ⟨apSmoothCoreInto L sigma gamma ell dimension core, rfl⟩

end Grad.GaugeCoefficients.Physical.Compensated
