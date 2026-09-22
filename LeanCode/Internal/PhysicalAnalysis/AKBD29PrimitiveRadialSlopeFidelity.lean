import AKBD28OriginalCartesianDeterminantConsumer
import AKBB12ActualCartesianSourcePRadial

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open Set Filter
open scoped Topology ContDiff BigOperators
namespace Grad.ActualDeterminantEquations
open Grad.BoundaryTrace Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarCoefficients
open Grad.SourceCollarFullSource Grad.SourceBoundaryTrace Grad.AnnularCurrentLow Grad.AnnularReconstruction
open Grad.ActualSmoothPhysicalField Grad.ActualPolarEquations Grad.BoundaryKernelAction Grad.AnnularKernelL2
open Grad.AnnularKernelContinuity Grad.AnnularWeightedSmoothness Grad.GaugeCoefficients.Physical.Ledger
open Grad.ActualBoundaryPrimitives Grad.ActualCurrentPrimitives Grad.ActualGaugeSigmaPrimitives Grad.SourceCollar Grad.BoundaryLift Grad.PhaseAlgebra
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Physical.Allocation Grad.ActualPolarFlux Grad.ActualCartesianEquations
open Grad.AnnularStrongData Grad.AnnularStrongSolution Grad.AnnularCoupledInverse Grad.AnnularSourceGraph
open Grad.AnnularGeneralSourceRegularity Grad.AnnularHighGenerators Grad.AnnularForwardDatum Grad.AnnularRestriction

private theorem primitiveSlopeScalarTransport (radius length p b v g actualB actualV : ℂ)
    (sameB : b=actualB) (sameV : v=actualV) :
    (-radius⁻¹)*p-length⁻¹*b-radius⁻¹*v+g = -p/radius-actualB/length-actualV/radius+g := by
  rw [sameB,sameV]
  ring

/-- The accepted angularJet of a full angular field is its genuine axial
derivative, evaluated in the same full three-variable reconstruction. -/
theorem sameFullField_axialJet_scalar {parameters : PhaseParameters} {lower : ℝ} {positive : 0 < lower}
    {row : DivisionRow 1 lower} (curves : SmoothLowPhysicalRow parameters lower positive row)
    (bounded : lower < 1) (radius : ℝ) (inside : radius ∈ Ioo lower 1) (polar axial : ℝ) :
    angularJet 1 (fun angles => curves.fullField bounded (radius,angles)) (polar,axial) 0 =
      scalarDirectionalField curves bounded 0 (0,0,1) (radius,polar,axial) := by
  have vector := angularJet_hasDerivAt 0 (fun angles => curves.fullField bounded (radius,angles))
    (physicalField_angles_smooth curves bounded radius ⟨inside.1.le,inside.2.le⟩) polar axial
  simp only [angularJet_zero,zero_add] at vector
  have scalar := ((PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin 1 => ℂ) 0).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt axial vector
  exact ((scalarAxial_hasDerivAt curves bounded 0 radius inside polar axial).unique scalar).symm

variable (parameters : PhaseParameters) (length compact lower : ℝ) (positive : 0 < lower)
    (lowerHalf : lower ≤ 1/2) (state : RetainedInverseState parameters length compact)

theorem sameOriginalPhysicalRow_fullField {row : DivisionRow 7 lower}
    (curves : SmoothLowPhysicalRow parameters lower positive row) (component : Fin 3)
    (radius : ℝ) (inside : radius ∈ Icc lower 1) (angles : ℝ × ℝ) :
    (SmoothLowPhysicalRow.originalPhysicalRow parameters length compact lower positive lowerHalf state curves component).fullField
      (lowerHalf.trans_lt (by norm_num)) (radius,angles) =
    (curves.lowPhysicalCurves parameters length compact lower positive (lowerHalf.trans_lt (by norm_num)) state component).fullField
      (lowerHalf.trans_lt (by norm_num)) (radius,angles) :=
  samePhysical_fullField_eq _ _ (lowerHalf.trans_lt (by norm_num)) (Eventually.of_forall (fun _ _ => rfl)) radius inside angles

variable (lengthPositive : 0 < length)
    (data : StrongDataCarrier parameters lower positive (lowerHalf.trans (by norm_num)) 0 0)
    (solution : CoupledSpace lower length positive lengthPositive)
    (curves : SmoothLowPhysicalRow parameters lower positive
      (fullStrongSevenInput parameters length lower lengthPositive positive (lowerHalf.trans (by norm_num)) data solution))
    (third : SmoothLowPhysicalRow parameters lower positive
      (strongToLow parameters lower positive (lowerHalf.trans (by norm_num)) 0 0 data).ofLp.1.ofLp.2)

/-- Literal scalar fidelity of the already proved corrected-p radial RHS. -/
theorem actualPrimitiveRHS_scalar (radius : ℝ) (inside : radius ∈ Ioo lower 1) (angles : ℝ × ℝ) :
    primitiveDeterminantRHS length radius
      (actualPrimitiveDeterminantFields parameters length compact lower positive lowerHalf lengthPositive state data solution curves third radius) angles 0 =
      removePolarMean (fun query =>
        -(curves.correctedP parameters length compact lower positive (lowerHalf.trans_lt (by norm_num)) state).fullField (lowerHalf.trans_lt (by norm_num)) (radius,query) 0 / (radius : ℂ) -
        scalarDirectionalField (curves.bThree parameters length compact lower positive (lowerHalf.trans_lt (by norm_num)) state) (lowerHalf.trans_lt (by norm_num)) 0 (0,0,1) (radius,query) / (length : ℂ) -
        (curves.lowPhysicalCurves parameters length compact lower positive (lowerHalf.trans_lt (by norm_num)) state 2).fullField (lowerHalf.trans_lt (by norm_num)) (radius,query) 0 / (radius : ℂ) +
        third.fullField (lowerHalf.trans_lt (by norm_num)) (radius,query) 0) angles := by
  have continuousRaw := rawPrimitiveDeterminantRHS_continuous length radius _
    (actualPrimitiveDeterminantFields_smooth parameters length compact lower positive lowerHalf lengthPositive state data solution curves third radius ⟨inside.1.le,inside.2.le⟩)
  change removePolarMean (rawPrimitiveDeterminantRHS length radius _) angles 0 = _
  apply (removePolarMean_coordinate _ continuousRaw angles).trans
  apply congrArg (fun field : ℝ × ℝ → ℂ => removePolarMean field angles)
  funext query
  simp only [rawPrimitiveDeterminantRHS,actualPrimitiveDeterminantFields,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_two,Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons]
  simp only [PiLp.add_apply,PiLp.sub_apply,PiLp.smul_apply,smul_eq_mul]
  have vector := sameOriginalPhysicalRow_fullField parameters length compact lower positive lowerHalf state curves 2 radius ⟨inside.1.le,inside.2.le⟩ query
  have sameV := congrArg (fun value : ComplexEuclidean 1 => value 0) vector
  have sameB := sameFullField_axialJet_scalar (curves.bThree parameters length compact lower positive (lowerHalf.trans_lt (by norm_num)) state)
    (lowerHalf.trans_lt (by norm_num)) radius inside query.1 query.2
  exact primitiveSlopeScalarTransport _ _ _ _ _ _ _ _ sameB sameV

end Grad.ActualDeterminantEquations
