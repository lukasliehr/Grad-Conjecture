import SCS25KappaDoubleSynthesis

noncomputable section
open Set MeasureTheory
open scoped BigOperators

namespace Grad.SourceCollarFullSource
open Grad.ClosedJets Grad.CartesianState Grad.BoundaryTrace

/-- Uniformly absolutely dominated sums commute with the literal original
angular Fourier integral. This will identify the physical full product. -/
theorem angularCoefficient_hasSum {Index : Type*} [Countable Index] {dimension : ℕ}
    (fields : Index → ℝ → ComplexEuclidean dimension) (target : ℝ → ComplexEuclidean dimension)
    (continuousFields : ∀ index, Continuous (fields index))
    (majorant : Index → ℝ) (summable : Summable majorant)
    (dominated : ∀ index, ∀ angle ∈ Icc (-Real.pi) Real.pi, ‖fields index angle‖ ≤ majorant index)
    (series : ∀ angle ∈ Icc (-Real.pi) Real.pi, HasSum (fun index => fields index angle) (target angle))
    (mode : ℤ) : HasSum (fun index => angularCoefficient (fields index) mode) (angularCoefficient target mode) := by
  let measure := volume.restrict (Icc (-Real.pi) Real.pi)
  let term : Index → ℝ → ComplexEuclidean dimension :=
    fun index angle => cellExponential (-mode) angle • fields index angle
  have continuousTerm (index : Index) : Continuous (term index) :=
    (cellExponential_smooth (-mode)).continuous.smul (continuousFields index)
  have integrable (index : Index) : Integrable (term index) measure :=
    (continuousTerm index).continuousOn.integrableOn_Icc
  have integralBound (index : Index) : (∫ angle, ‖term index angle‖ ∂measure) ≤
      measure.real univ * majorant index := by
    calc
      _ ≤ ∫ _angle, majorant index ∂measure := by
        apply integral_mono_ae (integrable index).norm (integrable_const _)
        filter_upwards [ae_restrict_mem measurableSet_Icc] with angle inside
        simpa only [term, norm_smul, cellExponential_norm, one_mul] using dominated index angle inside
      _ = _ := by rw [integral_const, smul_eq_mul]
  have integralNorms : Summable (fun index => ∫ angle, ‖term index angle‖ ∂measure) :=
    Summable.of_nonneg_of_le (fun _ => integral_nonneg (fun _ => norm_nonneg _)) integralBound
      (summable.mul_left (measure.real univ))
  have integralSummable : Summable (fun index => ∫ angle, term index angle ∂measure) :=
    Summable.of_norm_bounded integralNorms (fun index => norm_integral_le_integral_norm _)
  have integrated := integralSummable.hasSum
  rw [integral_tsum_of_summable_integral_norm integrable integralNorms] at integrated
  have limit : (∫ angle, ∑' index, term index angle ∂measure) =
      ∫ angle, cellExponential (-mode) angle • target angle ∂measure := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Icc] with angle inside
    exact ((series angle inside).const_smul (cellExponential (-mode) angle)).tsum_eq
  rw [limit] at integrated
  have scaled := integrated.const_smul ((2 * Real.pi)⁻¹)
  simpa only [angularCoefficient_compact, measure, term] using scaled

end Grad.SourceCollarFullSource
