import AKCX19ActualMixedMatrixCoordinate

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
open MeasureTheory
namespace Grad.CartesianStartup
open Grad.ClosedJets Grad.GenericCarriers Grad.PDEBootstrap Grad.WeightedJets Grad.TensorBootstrap
open Grad.GaugeCoefficients.Envelope Grad.GaugeCoefficients.Physical.Allocation
open Grad.GaugeCoefficients.Physical.RadialLedger
open Grad.WeightedJets.Ordered

theorem startupActualMatrix_mixedRankFirst {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) {input output rank : ℕ}
    (coefficients : CoefficientFamily L sigma gamma ell input output) (coherent : FamilyCoherent coefficients)
    (lengthNonzero : L ≠ 0) (scaleNonzero : ell ≠ 0)
    (family : StartupSignedFamily input L ell) (regular : family.HasSpatialGrade rank) (power : ℕ)
    (lower : ∀ q < power, ∃ first : StartupFirst (startupTensorDimension input rank),
      base (startupTensorDimension input rank) 1 openUnitDisk (fun _ => 0) first = family.rankDerivative regular q) :
    ∃ remainder : StartupFirst (startupTensorDimension output rank),
      (family.matrix admissible coefficients coherent).rankDerivative
        (regular.matrix admissible coefficients coherent lengthNonzero scaleNonzero) power =
      (StartupRankOperator.matrix admissible rank coefficients coherent).coarse (family.rankDerivative regular power) +
      base (startupTensorDimension output rank) 1 openUnitDisk (fun _ => 0) remainder := by
  let jets (q : ℕ) : GraphGrade input rank rank openUnitDisk := (regular q rank).choose
  have jetsSame (q : ℕ) : base input rank openUnitDisk (fun _ => rank) (jets q) = family.moment q :=
    (regular q rank).choose_spec
  have topSame (q : ℕ) : startupTensorFieldEquiv input rank
      (orderedDerivative input rank rank openUnitDisk (fun _ => rank) le_rfl (jets q)) = family.rankDerivative regular q :=
    family.rankDerivative_of_graph regular q (jets q) le_rfl (jetsSame q)
  have lowerCoordinates (word : Grad.TensorBootstrap.DerivativeIndex rank) (q : ℕ) (less : q < power) :
      ∃ graph : StartupFirst input, base input 1 openUnitDisk (fun _ => 0) graph =
        orderedDerivative input rank rank openUnitDisk (fun _ => rank) le_rfl (jets q) word := by
    obtain ⟨first,firstSame⟩ := lower q less
    have flatSame : startupFirstValue first = startupTensorFieldEquiv input rank
        (orderedDerivative input rank rank openUnitDisk (fun _ => rank) le_rfl (jets q)) :=
      firstSame.trans (topSame q).symm
    have values := startupTensorFirstEquiv_symm_values input rank first
    rw [flatSame,LinearIsometryEquiv.symm_apply_apply] at values
    refine ⟨(startupTensorFirstEquiv input rank).symm first word,?_⟩
    exact congrArg (fun fields : Tensor rank (StartupL2 input) => fields word) values
  let outputRegular := regular.matrix admissible coefficients coherent lengthNonzero scaleNonzero
  let image : GraphGrade output rank 0 openUnitDisk := (outputRegular power 0).choose
  have imageSame : base output rank openUnitDisk (fun _ => 0) image =
      (family.matrix admissible coefficients coherent).moment power := (outputRegular power 0).choose_spec
  let firsts (word : Grad.TensorBootstrap.DerivativeIndex rank) : StartupFirst output :=
    (startupActualMatrix_mixedCoordinateFirst admissible coefficients coherent family jets jetsSame power word
      (lowerCoordinates word) image imageSame).choose
  have firstSame (word : Grad.TensorBootstrap.DerivativeIndex rank) :
      orderedDerivative output rank rank openUnitDisk (fun _ => 0) le_rfl image word =
      originalMatrixKernel admissible coefficients coherent
        (orderedDerivative input rank rank openUnitDisk (fun _ => rank) le_rfl (jets power) word) +
      base output 1 openUnitDisk (fun _ => 0) (firsts word) :=
    (startupActualMatrix_mixedCoordinateFirst admissible coefficients coherent family jets jetsSame power word
      (lowerCoordinates word) image imageSame).choose_spec
  have tensors : orderedDerivative output rank rank openUnitDisk (fun _ => 0) le_rfl image =
      hilbertLift (Index := Grad.TensorBootstrap.DerivativeIndex rank) (originalMatrixKernel admissible coefficients coherent)
        (orderedDerivative input rank rank openUnitDisk (fun _ => rank) le_rfl (jets power)) +
      startupTensorFirstValues (WithLp.toLp 2 firsts) := by
    apply PiLp.ext
    exact firstSame
  refine ⟨startupTensorFirstEquiv output rank (WithLp.toLp 2 firsts),?_⟩
  change startupTensorFieldEquiv output rank
    (orderedDerivative output rank rank openUnitDisk (fun _ => 0) le_rfl image) = _
  rw [tensors,map_add]
  have flatFirst : base (startupTensorDimension output rank) 1 openUnitDisk (fun _ => 0)
      (startupTensorFirstEquiv output rank (WithLp.toLp 2 firsts)) =
      startupTensorFieldEquiv output rank (startupTensorFirstValues (WithLp.toLp 2 firsts)) :=
    startupTensorFirstEquiv_base output rank (WithLp.toLp 2 firsts)
  rw [flatFirst,← topSame power]
  congr 1
  exact (StartupRankOperator.entrywise_coarse rank (originalMatrixKernel admissible coefficients coherent)
    (startupMatrixFirstGraphCLM admissible coefficients coherent)
    (startupMatrixFirstGraph_compatible admissible coefficients coherent) _).symm

end Grad.CartesianStartup
