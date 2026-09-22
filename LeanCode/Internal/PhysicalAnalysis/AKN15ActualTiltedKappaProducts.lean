import AKN14TiltedOriginalCoefficientAlgebra

noncomputable section

open Set Filter MeasureTheory
open scoped Topology BigOperators

namespace Grad.ExhaustionSourceAllocation

open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarFullSource
open Grad.SourceCollarCoefficients Grad.AnnularCurrentSource Grad.GaugeCoefficients.Physical.Allocation

/-- The same actual cofactor product receives the BF tilt on both sides.
Only the accepted original-width radial product estimate is used. -/
theorem actualKappaProduct_tilted_bound (parameters : PhaseParameters) (L rho epsilon : ℝ)
    (field : ACore parameters 3)
    (small : physicalBudget parameters field rho epsilon 6 ≤ originalCoefficientLowRadius parameters L)
    (component : Fin 3) (power radial : ℕ) (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (high low product : DivisionRow 1 lower) (compatible : RadialRowsCompatible lower power high low)
    (literal : ∀ᵐ radius ∂volume.restrict (Icc lower 1), ∀ mode : ℤ × ℤ,
      HasSum (fun shift : ℤ × ℤ => kappaScalar parameters L rho epsilon field small component radial radius shift •
        originalRowCoefficient parameters 0 lower low radius (mode - shift))
        (originalRowCoefficient parameters power lower product radius mode)) :
    ‖divisionHighWeight lower positive bounded product‖ ≤ productPhaseConstant parameters power *
      ((kappaFourierConstant parameters L 0 radial * physicalBudget parameters field rho epsilon (radial + 5)) *
          ‖divisionHighWeight lower positive bounded high‖ +
        (kappaFourierConstant parameters L power radial * physicalBudget parameters field rho epsilon (power + radial + 5)) *
          ‖divisionHighWeight lower positive bounded low‖) := by
  obtain ⟨weighted, estimate, weightedLiteral⟩ := actualKappaRadialProduct parameters L rho epsilon field small
    component power radial lower positive (divisionHighWeight lower positive bounded high)
    (divisionHighWeight lower positive bounded low)
    (divisionHighWeight_compatible positive bounded power high low compatible)
  have related : RadialScaleRelated lower (fun radius => ((radius ^ (-9 / 4 : ℝ) : ℝ) : ℂ)) weighted product := by
    apply radialScaleRelated_of_originalCoefficient parameters power lower positive
    filter_upwards [literal, weightedLiteral,
      divisionHighWeight_originalCoefficient parameters 0 lower positive bounded low] with radius original actual same
    intro mode
    have scaled := (((radius ^ (-9 / 4 : ℝ) : ℝ) : ℂ) •
      ContinuousLinearMap.id ℂ (ComplexEuclidean 1)).hasSum (original mode)
    simp only [smul_apply, ContinuousLinearMap.id_apply] at scaled
    have aligned : HasSum (fun shift : ℤ × ℤ =>
        kappaScalar parameters L rho epsilon field small component radial radius shift •
          originalRowCoefficient parameters 0 lower (divisionHighWeight lower positive bounded low) radius (mode - shift))
        (((radius ^ (-9 / 4 : ℝ) : ℝ) : ℂ) • originalRowCoefficient parameters power lower product radius mode) :=
      scaled.congr_fun (fun shift => by
        rw [same]
        exact smul_comm _ _ _)
    exact (actual mode).unique aligned
  rw [← related.eq_actualHighWeight positive bounded]
  exact estimate

end Grad.ExhaustionSourceAllocation
