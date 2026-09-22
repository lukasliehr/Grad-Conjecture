import Q23DerivativeDot
import GaugeSliceTransfer
import CompletedAverages

noncomputable section

set_option maxRecDepth 4000
set_option maxHeartbeats 2400000

open Set Filter
open scoped ContDiff Topology

namespace Grad.NonlinearQuotientBounds

open Grad.ClosedJets Grad.CartesianState Grad.Constraints
open Grad.Constraints.Multipliers Grad.Constraints.Gauges Grad.Constraints.Seed

/-- Restrict the scalar field of a complex continuous linear map, bundled as
a continuous real-linear operation on the operator space itself. -/
def q23RestrictScalarsCLM {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [NormedSpace ℝ F]
    [IsScalarTower ℝ ℂ E] [IsScalarTower ℝ ℂ F] :
    (E →L[ℂ] F) →L[ℝ] (E →L[ℝ] F) :=
  LinearMap.mkContinuous
    { toFun := fun mapping => mapping.restrictScalars ℝ
      map_add' := fun first second => by
        apply ContinuousLinearMap.ext
        intro value
        rfl
      map_smul' := fun scalar mapping => by
        apply ContinuousLinearMap.ext
        intro value
        exact congrArg (fun operator : E →L[ℂ] F => operator value)
          (((ContinuousLinearMap.id ℂ (E →L[ℂ] F)).restrictScalars ℝ).map_smul scalar mapping) }
    1 (fun mapping => by
      change ‖mapping.restrictScalars ℝ‖ ≤ 1 * ‖mapping‖
      rw [ContinuousLinearMap.norm_restrictScalars, one_mul])

/-- Smoothness of composition for complex-linear operators depending on real
parameters.  The explicit scalar restriction avoids Mathlib's nested
real/complex operator-space instance diamond. -/
theorem q23ContDiffOn_complexCLM_comp
    {X E F G : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℂ G] [NormedSpace ℝ G]
    [IsScalarTower ℝ ℂ E] [IsScalarTower ℝ ℂ F] [IsScalarTower ℝ ℂ G]
    {outer : X → F →L[ℂ] G} {inner : X → E →L[ℂ] F}
    {domain : Set X} (outerSmooth : ContDiffOn ℝ ∞ outer domain)
    (innerSmooth : ContDiffOn ℝ ∞ inner domain) :
    ContDiffOn ℝ ∞ (fun point => (outer point).comp (inner point)) domain := by
  have nested : ContDiffOn ℝ ∞
      (fun point => (ContinuousLinearMap.compL ℂ E F G) (outer point)) domain :=
    q23RealSmooth_linearFunction_comp
      (fun mapping => (ContinuousLinearMap.compL ℂ E F G) mapping)
      (fun first second => (ContinuousLinearMap.compL ℂ E F G).map_add first second)
      (fun scalar mapping => by
        apply ContinuousLinearMap.ext
        intro innerMapping
        apply ContinuousLinearMap.ext
        intro value
        rfl)
      (ContinuousLinearMap.compL ℂ E F G).continuous outer domain outerSmooth
  have realNested : ContDiffOn ℝ ∞
      (fun point => ((ContinuousLinearMap.compL ℂ E F G) (outer point)).restrictScalars ℝ)
      domain := q23RealSmooth_linearFunction_comp
    (fun mapping => mapping.restrictScalars ℝ)
    (fun first second => by
      apply ContinuousLinearMap.ext
      intro value
      rfl)
    (fun scalar mapping => by
      apply ContinuousLinearMap.ext
      intro value
      rfl)
    (q23RestrictScalarsCLM
      (E := E →L[ℂ] F) (F := E →L[ℂ] G)).continuous
    (fun point => (ContinuousLinearMap.compL ℂ E F G) (outer point)) domain nested
  change ContDiffOn ℝ ∞ (fun point =>
    ((ContinuousLinearMap.compL ℂ E F G) (outer point)).restrictScalars ℝ
      (inner point)) domain
  exact realNested.clm_apply innerSmooth

def completedSeedMatrixFamily (phase : PhaseParameters) (grade : ℕ)
    (parameter : Seed.Parameters) :
    AGrade phase 2 grade →L[ℂ] AGrade phase 2 grade :=
  ContinuousLinearMap.id ℂ (AGrade phase 2 grade) +
    completedSeedDeviationFamily phase grade 0 parameter

def completedSeedTransposeFamily (phase : PhaseParameters) (grade : ℕ)
    (parameter : Seed.Parameters) :
    AGrade phase 2 grade →L[ℂ] AGrade phase 2 grade :=
  ContinuousLinearMap.id ℂ (AGrade phase 2 grade) +
    completedSeedTransposeDeviationFamily phase grade 0 parameter

def completedSeedInverseFixed (phase : PhaseParameters) (grade : ℕ)
    (reference : Seed.Parameters) :
    AGrade phase 2 grade →L[ℂ] AGrade phase 2 grade :=
  ContinuousLinearMap.id ℂ (AGrade phase 2 grade) +
    completedSeedDeviationFamily phase grade 1 reference

def completedSeedDerivativeDotFamily (phase : PhaseParameters) (grade : ℕ)
    (parameter : Seed.Parameters) :
    AGrade phase 2 grade →L[ℂ] AGrade phase 1 grade :=
  let weightedMap := (derivativeDotLift phase grade).comp
    (weightedCompletedTransposeMap phase grade)
  weightedMap (Seed.weightedSeedFamilies phase grade 2 parameter)

def completedSeedSliceFamily (phase : PhaseParameters) (grade : ℕ)
    (parameter : Seed.Parameters) :
    AGrade phase 2 grade →L[ℂ] AGrade phase 2 grade :=
  ContinuousLinearMap.id ℂ (AGrade phase 2 grade) -
    (tangentialCompleted phase).comp
      ((completedSeedTransposeFamily phase grade parameter).comp
        (completedSeedMatrixFamily phase grade parameter))

def completedPlanarTransferFamily (phase : PhaseParameters) (grade : ℕ)
    (reference parameter : Seed.Parameters) :
    AGrade phase 2 grade →L[ℂ] AGrade phase 2 grade :=
  (completedSeedMatrixFamily phase grade parameter).comp
    ((completedSeedSliceFamily phase grade parameter).comp
      (completedSeedInverseFixed phase grade reference))

/-- The literal N18 transfer as a same-grade completed operator-valued
function of the moving finite seed. -/
def completedSeedTransferFamily (phase : PhaseParameters) (grade : ℕ)
    (reference parameter : Seed.Parameters) :
    AGrade phase 3 grade →L[ℂ] AGrade phase 3 grade :=
  let planarPart := q23ValueMapCompleted (grade := grade) phase planarPartMap
  let planarInclusion := q23ValueMapCompleted (grade := grade) phase planarInclusionMap
  let toroidalPart := q23ValueMapCompleted (grade := grade) phase toroidalPartMap
  let toroidalInclusion := q23ValueMapCompleted (grade := grade) phase toroidalInclusionMap
  let angular := angularCompleted (dimension := 1) (grade := grade) phase 0
  let planar := completedPlanarTransferFamily phase grade reference parameter
  let dot := completedSeedDerivativeDotFamily phase grade parameter
  planarInclusion.comp (planar.comp planarPart) +
    toroidalInclusion.comp
      ((toroidalPart - angular.comp toroidalPart) -
        (phase.length⁻¹ : ℂ) • angular.comp (dot.comp (planar.comp planarPart)))

theorem completedSeedMatrixFamily_contDiffOn (phase : PhaseParameters) (grade : ℕ) :
    ContDiffOn ℝ ∞ (completedSeedMatrixFamily phase grade) Seed.parameterDomain :=
  contDiffOn_const.add (completedSeedDeviationFamily_contDiffOn phase grade 0)

theorem completedSeedTransposeFamily_contDiffOn (phase : PhaseParameters) (grade : ℕ) :
    ContDiffOn ℝ ∞ (completedSeedTransposeFamily phase grade) Seed.parameterDomain :=
  contDiffOn_const.add (completedSeedTransposeDeviationFamily_contDiffOn phase grade 0)

theorem completedSeedDerivativeDotFamily_contDiffOn (phase : PhaseParameters) (grade : ℕ) :
    ContDiffOn ℝ ∞ (completedSeedDerivativeDotFamily phase grade) Seed.parameterDomain := by
  exact q23RealSmooth_linearFunction_comp
    (fun sequence => (derivativeDotLift phase grade).comp
      (weightedCompletedTransposeMap phase grade) sequence)
    (fun x y => ((derivativeDotLift phase grade).comp
      (weightedCompletedTransposeMap phase grade)).map_add x y)
    (fun r x => by
      apply ContinuousLinearMap.ext
      intro field
      exact congrArg
        (fun operator : AGrade phase 2 grade →L[ℂ] AGrade phase 1 grade => operator field)
        ((((derivativeDotLift phase grade).comp
          (weightedCompletedTransposeMap phase grade)).restrictScalars ℝ).map_smul r x))
    ((derivativeDotLift phase grade).comp
      (weightedCompletedTransposeMap phase grade)).continuous
    (Seed.weightedSeedFamilies phase grade 2) Seed.parameterDomain
    (Seed.weightedSeedFamilies_contDiffOn phase grade 2)

theorem completedSeedSliceFamily_contDiffOn (phase : PhaseParameters) (grade : ℕ) :
    ContDiffOn ℝ ∞ (completedSeedSliceFamily phase grade) Seed.parameterDomain := by
  have product := q23ContDiffOn_complexCLM_comp
    (completedSeedTransposeFamily_contDiffOn phase grade)
    (completedSeedMatrixFamily_contDiffOn phase grade)
  have gauged := q23ContDiffOn_complexCLM_comp (contDiffOn_const : ContDiffOn ℝ ∞
    (fun _ : Seed.Parameters => tangentialCompleted (grade := grade) phase)
      Seed.parameterDomain) product
  exact contDiffOn_const.sub gauged

theorem completedPlanarTransferFamily_contDiffOn (phase : PhaseParameters) (grade : ℕ)
    (reference : Seed.Parameters) :
    ContDiffOn ℝ ∞ (completedPlanarTransferFamily phase grade reference)
      Seed.parameterDomain := by
  have inner := q23ContDiffOn_complexCLM_comp
    (completedSeedSliceFamily_contDiffOn phase grade)
    (contDiffOn_const : ContDiffOn ℝ ∞
      (fun _ : Seed.Parameters => completedSeedInverseFixed phase grade reference)
        Seed.parameterDomain)
  exact q23ContDiffOn_complexCLM_comp
    (completedSeedMatrixFamily_contDiffOn phase grade) inner

theorem completedSeedTransferFamily_contDiffOn (phase : PhaseParameters) (grade : ℕ)
    (reference : Seed.Parameters) :
    ContDiffOn ℝ ∞ (completedSeedTransferFamily phase grade reference)
      Seed.parameterDomain := by
  let planarPart := q23ValueMapCompleted (grade := grade) phase planarPartMap
  let planarInclusion := q23ValueMapCompleted (grade := grade) phase planarInclusionMap
  let toroidalPart := q23ValueMapCompleted (grade := grade) phase toroidalPartMap
  let toroidalInclusion := q23ValueMapCompleted (grade := grade) phase toroidalInclusionMap
  let angular := angularCompleted (dimension := 1) (grade := grade) phase 0
  have planar := completedPlanarTransferFamily_contDiffOn phase grade reference
  have planarInput := q23ContDiffOn_complexCLM_comp planar
    (contDiffOn_const : ContDiffOn ℝ ∞
    (fun _ : Seed.Parameters => planarPart) Seed.parameterDomain)
  have planarOutput := q23ContDiffOn_complexCLM_comp (contDiffOn_const : ContDiffOn ℝ ∞
    (fun _ : Seed.Parameters => planarInclusion) Seed.parameterDomain) planarInput
  have dotPlanar := q23ContDiffOn_complexCLM_comp
    (completedSeedDerivativeDotFamily_contDiffOn phase grade) planarInput
  have meanDot := q23ContDiffOn_complexCLM_comp (contDiffOn_const : ContDiffOn ℝ ∞
    (fun _ : Seed.Parameters => angular) Seed.parameterDomain) dotPlanar
  have toroidalFixed : ContDiffOn ℝ ∞
      (fun _ : Seed.Parameters => toroidalPart - angular.comp toroidalPart)
      Seed.parameterDomain := contDiffOn_const
  have toroidalScalar := toroidalFixed.sub (meanDot.const_smul (phase.length⁻¹ : ℂ))
  have toroidalOutput := q23ContDiffOn_complexCLM_comp (contDiffOn_const : ContDiffOn ℝ ∞
    (fun _ : Seed.Parameters => toroidalInclusion) Seed.parameterDomain) toroidalScalar
  change ContDiffOn ℝ ∞ (fun parameter =>
    planarInclusion.comp
        ((completedPlanarTransferFamily phase grade reference parameter).comp planarPart) +
      toroidalInclusion.comp
        ((toroidalPart - angular.comp toroidalPart) -
          (phase.length⁻¹ : ℂ) • angular.comp
            ((completedSeedDerivativeDotFamily phase grade parameter).comp
              ((completedPlanarTransferFamily phase grade reference parameter).comp
                planarPart)))) Seed.parameterDomain
  exact planarOutput.add toroidalOutput

theorem completedSeedMatrixFamily_core (phase : PhaseParameters) (grade : ℕ)
    (parameter : Seed.Parameters) (inside : parameter ∈ Seed.parameterDomain)
    (field : ACore phase 2) :
    completedSeedMatrixFamily phase grade parameter
        (aGradeEta phase (GradeCore.ofCoreLinear field)) =
      aGradeEta phase (GradeCore.ofCoreLinear (seedMatrixCore phase parameter inside field)) := by
  unfold completedSeedMatrixFamily
  simp only [add_apply, ContinuousLinearMap.id_apply]
  rw [completedSeedDeviationFamily_core phase grade 0 parameter inside field, ← map_add]
  rfl

theorem completedSeedTransposeFamily_core (phase : PhaseParameters) (grade : ℕ)
    (parameter : Seed.Parameters) (inside : parameter ∈ Seed.parameterDomain)
    (field : ACore phase 2) :
    completedSeedTransposeFamily phase grade parameter
        (aGradeEta phase (GradeCore.ofCoreLinear field)) =
      aGradeEta phase (GradeCore.ofCoreLinear (seedTransposeCore phase parameter inside field)) := by
  unfold completedSeedTransposeFamily
  simp only [add_apply, ContinuousLinearMap.id_apply]
  rw [completedSeedTransposeDeviationFamily_core phase grade 0 parameter inside field,
    ← map_add, ← map_add,
    seedTransposeCore_eq_identity_add_deviation]

theorem completedSeedInverseFixed_core (phase : PhaseParameters) (grade : ℕ)
    (reference : Seed.Parameters) (inside : reference ∈ Seed.parameterDomain)
    (field : ACore phase 2) :
    completedSeedInverseFixed phase grade reference
        (aGradeEta phase (GradeCore.ofCoreLinear field)) =
      aGradeEta phase (GradeCore.ofCoreLinear (seedInverseCore phase reference inside field)) := by
  unfold completedSeedInverseFixed
  simp only [add_apply, ContinuousLinearMap.id_apply]
  rw [completedSeedDeviationFamily_core phase grade 1 reference inside field, ← map_add]
  rfl

theorem completedSeedDerivativeDotFamily_core (phase : PhaseParameters) (grade : ℕ)
    (parameter : Seed.Parameters) (inside : parameter ∈ Seed.parameterDomain)
    (field : ACore phase 2) :
    completedSeedDerivativeDotFamily phase grade parameter
        (aGradeEta phase (GradeCore.ofCoreLinear field)) =
      aGradeEta phase (GradeCore.ofCoreLinear (derivativeDotCore phase parameter inside field)) := by
  change completedDerivativeDotParameterDerivative phase grade 0 parameter
      (fun position => position.elim0) (aGradeEta phase (GradeCore.ofCoreLinear field)) = _
  rw [completedDerivativeDotParameterDerivative_core phase grade 0 parameter inside
      (fun position => position.elim0) field,
    seedDerivativeDotParameterDerivative_zero]

theorem completedSeedSliceFamily_core (phase : PhaseParameters) (grade : ℕ)
    (parameter : Seed.Parameters) (inside : parameter ∈ Seed.parameterDomain)
    (field : ACore phase 2) :
    completedSeedSliceFamily phase grade parameter
        (aGradeEta phase (GradeCore.ofCoreLinear field)) =
      aGradeEta phase (GradeCore.ofCoreLinear (sliceProjection phase parameter inside field)) := by
  unfold completedSeedSliceFamily
  simp only [sub_apply, ContinuousLinearMap.id_apply, ContinuousLinearMap.comp_apply]
  rw [completedSeedMatrixFamily_core phase grade parameter inside field,
    completedSeedTransposeFamily_core phase grade parameter inside,
    tangentialCompleted_eta, ← map_sub]
  rfl

theorem completedPlanarTransferFamily_core (phase : PhaseParameters) (grade : ℕ)
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain)
    (parameter : Seed.Parameters) (inside : parameter ∈ Seed.parameterDomain)
    (field : ACore phase 2) :
    completedPlanarTransferFamily phase grade reference parameter
        (aGradeEta phase (GradeCore.ofCoreLinear field)) =
      aGradeEta phase (GradeCore.ofCoreLinear
        (planarTransfer phase reference insideR parameter inside field)) := by
  unfold completedPlanarTransferFamily
  simp only [ContinuousLinearMap.comp_apply]
  rw [completedSeedInverseFixed_core phase grade reference insideR field,
    completedSeedSliceFamily_core phase grade parameter inside,
    completedSeedMatrixFamily_core phase grade parameter inside]
  rfl

theorem completedSeedTransferFamily_core (phase : PhaseParameters) (grade : ℕ)
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain)
    (parameter : Seed.Parameters) (inside : parameter ∈ Seed.parameterDomain)
    (field : ACore phase 3) :
    completedSeedTransferFamily phase grade reference parameter
        (aGradeEta phase (GradeCore.ofCoreLinear field)) =
      aGradeEta phase (GradeCore.ofCoreLinear
        (seedTransfer phase reference insideR parameter inside field)) := by
  unfold completedSeedTransferFamily
  simp only [add_apply, sub_apply, smul_apply, ContinuousLinearMap.comp_apply]
  rw [q23ValueMapCompleted_core, completedPlanarTransferFamily_core phase grade reference
      insideR parameter inside, q23ValueMapCompleted_core,
    q23ValueMapCompleted_core, angularCompleted_eta]
  rw [completedSeedDerivativeDotFamily_core phase grade parameter inside
    (planarTransfer phase reference insideR parameter inside
      (valueMapCore planarPartMap phase field)), angularCompleted_eta,
    ← map_smul, ← map_sub, ← map_sub]
  have toroidalInput :
      aGradeEta phase
          (GradeCore.ofCoreLinear (grade := grade) (valueMapCore toroidalPartMap phase field) -
            angularGradeCore phase 0
              (GradeCore.ofCoreLinear (grade := grade)
                (valueMapCore toroidalPartMap phase field)) -
            (phase.length⁻¹ : ℂ) • angularGradeCore phase 0
              (GradeCore.ofCoreLinear (grade := grade)
                (derivativeDotCore phase parameter inside
                  (planarTransfer phase reference insideR parameter inside
                    (valueMapCore planarPartMap phase field))))) =
        aGradeEta phase (GradeCore.ofCoreLinear (grade := grade)
          (transferToroidalComponent phase reference insideR parameter inside field)) := by
    congr 1
  rw [toroidalInput, q23ValueMapCompleted_core, ← map_add]
  rfl

end Grad.NonlinearQuotientBounds
