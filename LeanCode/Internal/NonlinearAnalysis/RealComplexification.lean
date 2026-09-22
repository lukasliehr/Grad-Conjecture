import SmoothRowFields

noncomputable section

namespace Grad.NonlinearQuotient

open Grad.MainTarget Grad.PhysicalFamily

def complexifyVec (point : Vec) : ComplexVec :=
  WithLp.toLp 2 (fun coordinate => (point coordinate : ℂ))

def complexifyVecLinear : Vec →ₗ[ℝ] ComplexVec where
  toFun := complexifyVec
  map_add' first second := by ext coordinate; simp [complexifyVec]
  map_smul' scalar point := by ext coordinate; simp [complexifyVec]

def complexifyVecCLM : Vec →L[ℝ] ComplexVec := complexifyVecLinear.toContinuousLinearMap

@[simp] theorem complexifyVecCLM_apply (point : Vec) :
    complexifyVecCLM point = complexifyVec point := rfl

@[simp] theorem complexifyVec_apply (point : Vec) (coordinate : Fin 3) :
    complexifyVec point coordinate = (point coordinate : ℂ) := rfl

theorem complexDot_complexify (first second : Vec) :
    complexDot (complexifyVec first) (complexifyVec second) = (inner ℝ first second : ℂ) := by
  simp [complexDot, PiLp.inner_apply, Fin.sum_univ_three]
  ring

theorem complexDeterminant_complexify (first second third : Vec) :
    complexDeterminant (complexifyVec first) (complexifyVec second) (complexifyVec third) =
      (tripleDeterminant first second third : ℂ) := by
  have matrixIdentity :
      (fun row column : Fin 3 => (![complexifyVec first, complexifyVec second, complexifyVec third] column) row) =
      Complex.ofRealHom.mapMatrix (fun row column : Fin 3 => (![first, second, third] column) row) := by
    funext row column
    fin_cases column <;> rfl
  unfold complexDeterminant
  rw [matrixIdentity]
  exact (Complex.ofRealHom.map_det _).symm

theorem complexTangentGenerator_complexify (point : Vec) :
    complexTangentGenerator (complexifyVec point) = complexifyVec (tangentGenerator point) := by
  ext coordinate
  fin_cases coordinate <;> simp [complexTangentGenerator, complexifyVec, tangentGenerator, vector]

theorem fderiv_postcompose
    {Source Target Output : Type*}
    [NormedAddCommGroup Source] [NormedSpace ℝ Source]
    [NormedAddCommGroup Target] [NormedSpace ℝ Target]
    [NormedAddCommGroup Output] [NormedSpace ℝ Output]
    (linear : Target →L[ℝ] Output) (field : Source → Target) (point : Source)
    (differentiable : DifferentiableAt ℝ field point) :
    fderiv ℝ (fun argument => linear (field argument)) point =
      linear.comp (fderiv ℝ field point) :=
  (linear.hasFDerivAt.comp point differentiable.hasFDerivAt).fderiv

theorem diskEuler_postcompose
    {Target Output : Type*}
    [NormedAddCommGroup Target] [NormedSpace ℝ Target]
    [NormedAddCommGroup Output] [NormedSpace ℝ Output]
    (linear : Target →L[ℝ] Output) (field : Plane → ℝ → Target) (point : Plane) (time : ℝ)
    (differentiable : DifferentiableAt ℝ (fun argument => field argument time) point) :
    diskEuler (fun argument cellTime => linear (field argument cellTime)) point time =
      linear (diskEuler field point time) := by
  unfold diskEuler
  rw [fderiv_postcompose linear _ _ differentiable]
  rfl

theorem diskAngular_postcompose
    {Target Output : Type*}
    [NormedAddCommGroup Target] [NormedSpace ℝ Target]
    [NormedAddCommGroup Output] [NormedSpace ℝ Output]
    (linear : Target →L[ℝ] Output) (field : Plane → ℝ → Target) (point : Plane) (time : ℝ)
    (differentiable : DifferentiableAt ℝ (fun argument => field argument time) point) :
    diskAngular (fun argument cellTime => linear (field argument cellTime)) point time =
      linear (diskAngular field point time) := by
  unfold diskAngular
  rw [fderiv_postcompose linear _ _ differentiable]
  rfl

theorem cellDerivative_postcompose
    {Target Output : Type*}
    [NormedAddCommGroup Target] [NormedSpace ℝ Target]
    [NormedAddCommGroup Output] [NormedSpace ℝ Output]
    (linear : Target →L[ℝ] Output) (field : Plane → ℝ → Target) (point : Plane) (time : ℝ)
    (differentiable : DifferentiableAt ℝ (field point) time) :
    cellDerivative (fun argument cellTime => linear (field argument cellTime)) point time =
      linear (cellDerivative field point time) := by
  unfold cellDerivative
  rw [fderiv_postcompose linear _ _ differentiable]
  rfl

end Grad.NonlinearQuotient
