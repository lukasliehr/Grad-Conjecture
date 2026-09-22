import ASG24IntrinsicFourierCompletion

noncomputable section
set_option maxHeartbeats 800000
open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal

namespace Grad.AnnularSourceGraph
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.GaugeCoefficients.Physical.WeightedTrace Grad.BoundaryKernelAction

theorem annularSourceMode_energy (parameters : PhaseParameters) (dimension : ℕ) (lower : ℝ)
    (positive : 0 < lower) (bounded : lower < 1) (angular cell : ℕ)
    (field : AnnularSourceH1 parameters dimension lower angular cell) (mode : ℤ × ℤ) :
    ‖field mode‖ ^ 2 = splitTangentialWeight angular cell mode ^ 2 * weakRadialEnergy dimension lower
      (annularConjugatedCoordinate parameters dimension lower positive bounded.le angular cell field mode 0)
      (annularConjugatedCoordinate parameters dimension lower positive bounded.le angular cell field mode 1) := by
  rw [weightedRadialH1_norm_sq,
    annularConjugatedCoordinate_storage parameters dimension lower positive bounded.le angular cell field mode 0,
    annularConjugatedCoordinate_storage parameters dimension lower positive bounded.le angular cell field mode 1]
  simp only [norm_smul, Real.norm_of_nonneg (splitTangentialWeight_pos angular cell mode).le, mul_pow]
  rw [radialSqrtMap_norm_sq dimension lower positive bounded.le, radialSqrtMap_norm_sq dimension lower positive bounded.le,
    ← mul_add]
  congr 1
  rw [← intervalIntegral.integral_add
    (radialWeightedEnergy_integrable dimension lower positive bounded.le
      (annularConjugatedCoordinate parameters dimension lower positive bounded.le angular cell field mode 0))
    (radialWeightedEnergy_integrable dimension lower positive bounded.le
      (annularConjugatedCoordinate parameters dimension lower positive bounded.le angular cell field mode 1))]
  apply intervalIntegral.integral_congr
  intro radius _
  ring

theorem annularSource_finite_weak_energy (parameters : PhaseParameters) (dimension : ℕ) (lower : ℝ)
    (positive : 0 < lower) (bounded : lower < 1) (angular cell : ℕ)
    (field : AnnularSourceH1 parameters dimension lower angular cell) :
    Summable (fun mode : ℤ × ℤ => splitTangentialWeight angular cell mode ^ 2 * weakRadialEnergy dimension lower
      (annularConjugatedCoordinate parameters dimension lower positive bounded.le angular cell field mode 0)
      (annularConjugatedCoordinate parameters dimension lower positive bounded.le angular cell field mode 1)) := by
  have finite := (memℓp_gen_iff (p := 2) (by norm_num)).1 (lp.memℓp field)
  norm_num at finite
  exact finite.congr (fun mode => annularSourceMode_energy parameters dimension lower positive bounded angular cell field mode)

theorem annularConjugated_value_injective (parameters : PhaseParameters) (dimension : ℕ) (lower : ℝ)
    (positive : 0 < lower) (bounded : lower < 1) (angular cell : ℕ)
    (first second : AnnularSourceH1 parameters dimension lower angular cell)
    (same : ∀ mode, annularConjugatedCoordinate parameters dimension lower positive bounded.le angular cell first mode 0 =
      annularConjugatedCoordinate parameters dimension lower positive bounded.le angular cell second mode 0) : first = second := by
  apply annularSourceCoefficient_faithful parameters dimension lower positive bounded.le angular cell first second
  intro mode
  filter_upwards with radius
  unfold annularSourceCoefficient
  rw [same mode]

/-- Exact AH10 intrinsic/completion identification. Finite weighted weak
radial graphs and the original smooth Fourier completion determine one another
uniquely. Both endpoints and the grade laws are the same ASG16 operators. -/
theorem actualAH10_intrinsic_iff (parameters : PhaseParameters) (dimension : ℕ) (lower : ℝ)
    (positive : 0 < lower) (bounded : lower < 1) (angular cell : ℕ)
    (value derivative : (ℤ × ℤ) → CollarL2 (ComplexEuclidean dimension) lower) :
    ((∀ mode, CollarWeakDerivative lower (value mode) (derivative mode)) ∧
      Summable (fun mode : ℤ × ℤ => splitTangentialWeight angular cell mode ^ 2 *
        weakRadialEnergy dimension lower (value mode) (derivative mode))) ↔
    ∃! field : AnnularSourceH1 parameters dimension lower angular cell,
      ∀ mode, annularConjugatedCoordinate parameters dimension lower positive bounded.le angular cell field mode 0 = value mode ∧
        annularConjugatedCoordinate parameters dimension lower positive bounded.le angular cell field mode 1 = derivative mode := by
  constructor
  · rintro ⟨weak, finiteEnergy⟩
    let field := weakSourceRealization parameters dimension lower positive bounded angular cell value derivative weak finiteEnergy
    refine ⟨field, ?_, ?_⟩
    · intro mode
      exact ⟨weakSourceRealization_value parameters dimension lower positive bounded angular cell value derivative weak finiteEnergy mode,
        weakSourceRealization_slope parameters dimension lower positive bounded angular cell value derivative weak finiteEnergy mode⟩
    · intro other otherLaw
      apply annularConjugated_value_injective parameters dimension lower positive bounded angular cell
      intro mode
      exact (otherLaw mode).1.trans
        (weakSourceRealization_value parameters dimension lower positive bounded angular cell value derivative weak finiteEnergy mode).symm
  · rintro ⟨field, coordinates, _unique⟩
    have values : (fun mode => annularConjugatedCoordinate parameters dimension lower positive bounded.le angular cell field mode 0) = value :=
      funext (fun mode => (coordinates mode).1)
    have slopes : (fun mode => annularConjugatedCoordinate parameters dimension lower positive bounded.le angular cell field mode 1) = derivative :=
      funext (fun mode => (coordinates mode).2)
    refine ⟨?_, ?_⟩
    · intro mode
      have weak := annularConjugatedCoordinate_weak parameters dimension lower positive bounded.le angular cell field mode
      rwa [(coordinates mode).1, (coordinates mode).2] at weak
    · convert annularSource_finite_weak_energy parameters dimension lower positive bounded angular cell field using 1
      rw [← values, ← slopes]

end Grad.AnnularSourceGraph
