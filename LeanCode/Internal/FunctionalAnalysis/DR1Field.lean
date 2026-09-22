import JRProof

noncomputable section

open MeasureTheory Grad.PDEBootstrap
open Grad.GenericCarriers (PhysicalValue CellValues FieldL2 DomainL2)
open scoped BigOperators ContDiff

namespace Grad.WeightedJets.Restriction

variable (Value : Type*) [NormedAddCommGroup Value] [InnerProductSpace ℂ Value]
variable {smaller larger : Set Spatial}

def restrictValue (inclusion : smaller ⊆ larger) (field : DomainL2 Value larger) : DomainL2 Value smaller :=
  ((Lp.memLp field).mono_measure (Measure.restrict_mono inclusion le_rfl)).toLp field

omit [InnerProductSpace ℂ Value] in
theorem restrictValue_ae (inclusion : smaller ⊆ larger) (field : DomainL2 Value larger) :
    restrictValue Value inclusion field =ᵐ[volume.restrict smaller] field :=
  MemLp.coeFn_toLp _

omit [InnerProductSpace ℂ Value] in
theorem restrictValue_add (inclusion : smaller ⊆ larger) (first second : DomainL2 Value larger) :
    restrictValue Value inclusion (first + second) =
      restrictValue Value inclusion first + restrictValue Value inclusion second := by
  apply Lp.ext
  filter_upwards [restrictValue_ae Value inclusion (first + second),
    restrictValue_ae Value inclusion first, restrictValue_ae Value inclusion second,
    ae_restrict_of_ae_restrict_of_subset inclusion (Lp.coeFn_add first second),
    Lp.coeFn_add (restrictValue Value inclusion first) (restrictValue Value inclusion second)]
    with point total firstAt secondAt sourceSum targetSum
  rw [total, sourceSum, targetSum, Pi.add_apply, Pi.add_apply, firstAt, secondAt]

theorem restrictValue_smul (inclusion : smaller ⊆ larger) (scalar : ℂ) (field : DomainL2 Value larger) :
    restrictValue Value inclusion (scalar • field) = scalar • restrictValue Value inclusion field := by
  apply Lp.ext
  filter_upwards [restrictValue_ae Value inclusion (scalar • field),
    restrictValue_ae Value inclusion field,
    ae_restrict_of_ae_restrict_of_subset inclusion (Lp.coeFn_smul scalar field),
    Lp.coeFn_smul scalar (restrictValue Value inclusion field)]
    with point scaled fieldAt sourceScaled targetScaled
  rw [scaled, sourceScaled, targetScaled, Pi.smul_apply, Pi.smul_apply, fieldAt]

omit [InnerProductSpace ℂ Value] in
theorem restrictValue_norm_le (inclusion : smaller ⊆ larger) (field : DomainL2 Value larger) :
    ‖restrictValue Value inclusion field‖ ≤ ‖field‖ := by
  rw [Lp.norm_def, Lp.norm_def, eLpNorm_congr_ae (restrictValue_ae Value inclusion field)]
  exact ENNReal.toReal_mono (Lp.eLpNorm_ne_top field)
    (eLpNorm_mono_measure field (Measure.restrict_mono inclusion le_rfl))

def fieldRestriction (inclusion : smaller ⊆ larger) :
    DomainL2 Value larger →L[ℂ] DomainL2 Value smaller :=
  ({ toFun := restrictValue Value inclusion
     map_add' := restrictValue_add Value inclusion
     map_smul' := restrictValue_smul Value inclusion } :
    DomainL2 Value larger →ₗ[ℂ] DomainL2 Value smaller).mkContinuous 1
      (fun field => by
        change ‖restrictValue Value inclusion field‖ ≤ 1 * ‖field‖
        simpa only [one_mul] using restrictValue_norm_le Value inclusion field)

theorem fieldRestriction_ae (inclusion : smaller ⊆ larger) (field : DomainL2 Value larger) :
    fieldRestriction Value inclusion field =ᵐ[volume.restrict smaller] field :=
  restrictValue_ae Value inclusion field

theorem fieldRestriction_norm_le (inclusion : smaller ⊆ larger) (field : DomainL2 Value larger) :
    ‖fieldRestriction Value inclusion field‖ ≤ ‖field‖ :=
  restrictValue_norm_le Value inclusion field

theorem fieldRestriction_opNorm_le (inclusion : smaller ⊆ larger) :
    ‖fieldRestriction Value inclusion‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro field
  simpa only [one_mul] using fieldRestriction_norm_le Value inclusion field

theorem fieldRestriction_self (domain : Set Spatial) :
    fieldRestriction Value (Set.Subset.rfl : domain ⊆ domain) = ContinuousLinearMap.id ℂ _ := by
  apply ContinuousLinearMap.ext
  intro field
  exact Lp.ext (fieldRestriction_ae Value Set.Subset.rfl field)

theorem fieldRestriction_comp {small middle large : Set Spatial}
    (first : small ⊆ middle) (second : middle ⊆ large) :
    (fieldRestriction Value first).comp (fieldRestriction Value second) =
      fieldRestriction Value (first.trans second) := by
  apply ContinuousLinearMap.ext
  intro field
  apply Lp.ext
  filter_upwards [fieldRestriction_ae Value first (fieldRestriction Value second field),
    ae_restrict_of_ae_restrict_of_subset first (fieldRestriction_ae Value second field),
    fieldRestriction_ae Value (first.trans second) field] with point firstAt secondAt directAt
  exact firstAt.trans (secondAt.trans directAt.symm)

theorem fieldRestriction_naturality (Other : Type*) [NormedAddCommGroup Other]
    [InnerProductSpace ℂ Other] (mapping : Value →L[ℂ] Other)
    (inclusion : smaller ⊆ larger) (field : DomainL2 Value larger) :
    fieldRestriction Other inclusion (mapping.compLpL 2 (volume.restrict larger) field) =
      mapping.compLpL 2 (volume.restrict smaller) (fieldRestriction Value inclusion field) := by
  apply Lp.ext
  filter_upwards [fieldRestriction_ae Other inclusion (mapping.compLpL 2 (volume.restrict larger) field),
    ae_restrict_of_ae_restrict_of_subset inclusion
      (ContinuousLinearMap.coeFn_compLpL mapping field),
    ContinuousLinearMap.coeFn_compLpL mapping (fieldRestriction Value inclusion field),
    fieldRestriction_ae Value inclusion field] with point restricted sourceAt targetAt fieldAt
  rw [restricted, sourceAt, targetAt, fieldAt]

theorem fieldRestriction_inverse (dimension : ℕ) (inclusion : smaller ⊆ larger)
    (power : ℕ) (field : FieldL2 dimension larger) :
    fieldRestriction (CellValues dimension) inclusion
        (Grad.CellWeights.inverseFieldCLM dimension larger power field) =
      Grad.CellWeights.inverseFieldCLM dimension smaller power
        (fieldRestriction (CellValues dimension) inclusion field) :=
  fieldRestriction_naturality (CellValues dimension) (CellValues dimension)
    (Grad.CellWeights.inverseCellCLM (PhysicalValue dimension) power) inclusion field

def widenTest (inclusion : smaller ⊆ larger) (test : TestFunction smaller) : TestFunction larger where
  toFun := test.toFun
  smooth := test.smooth
  compact := test.compact
  supported := test.supported.trans inclusion

theorem integral_restriction (dimension : ℕ) (inclusion : smaller ⊆ larger)
    (measurableOuter : MeasurableSet larger) (field : FieldL2 dimension larger)
    (cell : ℤ) (vector : PhysicalValue dimension) (test : Spatial → ℝ)
    (supported : tsupport test ⊆ smaller) :
    (∫ point in smaller, test point • inner ℂ vector
      (fieldRestriction (CellValues dimension) inclusion field point cell)) =
      ∫ point in larger, test point • inner ℂ vector (field point cell) := by
  calc
    _ = ∫ point in smaller, test point • inner ℂ vector (field point cell) := by
      apply integral_congr_ae
      filter_upwards [fieldRestriction_ae (CellValues dimension) inclusion field] with point represented
      rw [represented]
    _ = _ := by
      symm
      apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableOuter inclusion
      intro point outside
      have zero : test point = 0 := by
        by_contra nonzero
        exact outside.2 (supported (subset_tsupport test nonzero))
      rw [zero, zero_smul]

theorem testPairing_restriction (dimension : ℕ) (inclusion : smaller ⊆ larger)
    (measurableOuter : MeasurableSet larger) (field : FieldL2 dimension larger)
    (cell : ℤ) (vector : PhysicalValue dimension) (test : TestFunction smaller) :
    testPairing dimension smaller cell vector test (fieldRestriction (CellValues dimension) inclusion field) =
      testPairing dimension larger cell vector (widenTest inclusion test) field := by
  rw [testPairing_apply, testPairing_apply]
  exact integral_restriction dimension inclusion measurableOuter field cell vector test.toFun test.supported

theorem derivativeTestPairing_restriction (dimension order : ℕ) (inclusion : smaller ⊆ larger)
    (measurableOuter : MeasurableSet larger) (field : FieldL2 dimension larger)
    (index : JetIndex order) (cell : ℤ) (vector : PhysicalValue dimension) (test : TestFunction smaller) :
    derivativeTestPairing dimension order smaller index cell vector test
        (fieldRestriction (CellValues dimension) inclusion field) =
      derivativeTestPairing dimension order larger index cell vector (widenTest inclusion test) field := by
  rw [derivativeTestPairing_apply, derivativeTestPairing_apply]
  exact integral_restriction dimension inclusion measurableOuter field cell vector _
    ((Grad.WeakTesting.derivativeTests smaller test.toFun test.smooth test.compact test.supported
      (degree index) (derivativeWord index)).2)

end Grad.WeightedJets.Restriction
