import AAV4MomentGraphSingleTest

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal
namespace Grad.AnnularConverse
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularVariational Grad.AnnularSourceGraph Grad.CircularHighRegularity Grad.PhaseAlgebra
open Grad.AnnularReconstruction Grad.GaugeCoefficients.Physical.WeightedTrace

theorem annularTestFunctional_vanish (lower length : ℝ) (positive : 0 < lower)
    (bounded : lower < 1) (lengthPositive : 0 < length)
    (functional : annularEnergySpace lower length positive →L[ℝ] ℝ)
    (single : ∀ (mode : HighAnnularMode) (test : complexSmoothRadialCore 1),
      test.val.1 lower = 0 → functional
        (annularEnergyCoreInto lower length positive (Finsupp.single mode test)) = 0)
    (test : annularInnerZero lower length positive bounded lengthPositive) : functional test.val = 0 := by
  classical
  apply isClosed_property (annularZeroSmoothInto_denseRange lower length positive bounded lengthPositive)
    (isClosed_eq (functional.continuous.comp continuous_subtype_val) continuous_const) _ test
  intro core
  change functional (annularEnergyCoreInto lower length positive core.val) = 0
  have decomposition : core.val = ∑ mode ∈ core.val.support, Finsupp.single mode (core.val mode) := by
    exact (Finsupp.sum_single core.val).symm
  rw [decomposition, map_sum, map_sum]
  apply Finset.sum_eq_zero
  intro mode _
  exact single mode (core.val mode) ((annularZeroSmoothCore_iff lower core.val).mp core.property mode)

section Converse
variable (parameters : PhaseParameters) (lower length : ℝ)
    (positive : 0 < lower) (bounded : lower < 1) (lengthPositive : 0 < length)
    (widthHalf : parameters.gamma ≤ 1 / 2)
    (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * length))

theorem annularSingleTests_imply_variational (field : annularEnergySpace lower length positive)
    (source : AnnularForcing lower)
    (single : ∀ (mode : HighAnnularMode) (test : complexSmoothRadialCore 1), test.val.1 lower = 0 →
      annularFormValue parameters lower length positive lengthPositive widthHalf widthLength field
        (annularEnergyCoreInto lower length positive (Finsupp.single mode test)) =
      annularFunctionalValue parameters lower length positive bounded lengthPositive widthHalf widthLength source
        (annularEnergyCoreInto lower length positive (Finsupp.single mode test)))
    (test : annularInnerZero lower length positive bounded lengthPositive) :
    annularFormValue parameters lower length positive lengthPositive widthHalf widthLength field test.val =
      annularFunctionalValue parameters lower length positive bounded lengthPositive widthHalf widthLength source test.val := by
  let residual := annularForm parameters lower length positive lengthPositive widthHalf widthLength field -
    annularFunctional parameters lower length positive bounded lengthPositive widthHalf widthLength source
  have realLaw (point : annularInnerZero lower length positive bounded lengthPositive) :
      (annularFormValue parameters lower length positive lengthPositive widthHalf widthLength field point.val).re =
      (annularFunctionalValue parameters lower length positive bounded lengthPositive widthHalf widthLength source point.val).re := by
    have zero := annularTestFunctional_vanish lower length positive bounded lengthPositive residual
      (fun mode core innerZero => by
        change annularForm parameters lower length positive lengthPositive widthHalf widthLength field
          (annularEnergyCoreInto lower length positive (Finsupp.single mode core)) -
          annularFunctional parameters lower length positive bounded lengthPositive widthHalf widthLength source
            (annularEnergyCoreInto lower length positive (Finsupp.single mode core)) = 0
        rw [annularForm_literal, annularFunctional_literal, single mode core innerZero, sub_self]) point
    change annularForm parameters lower length positive lengthPositive widthHalf widthLength field point.val -
      annularFunctional parameters lower length positive bounded lengthPositive widthHalf widthLength source point.val = 0 at zero
    rw [annularForm_literal, annularFunctional_literal] at zero
    exact sub_eq_zero.mp zero
  apply Complex.ext (realLaw test)
  have imaginaryLaw := realLaw (Complex.I • test)
  have formLaw := congrArg Complex.re
    (annularFormValue_test_smul parameters lower length positive lengthPositive widthHalf widthLength field test.val Complex.I)
  have forcingLaw := congrArg Complex.re
    (annularFunctionalValue_test_smul parameters lower length positive bounded lengthPositive widthHalf widthLength source test.val Complex.I)
  have equality := formLaw.symm.trans (imaginaryLaw.trans forcingLaw)
  simpa using equality

end Converse
end Grad.AnnularConverse
