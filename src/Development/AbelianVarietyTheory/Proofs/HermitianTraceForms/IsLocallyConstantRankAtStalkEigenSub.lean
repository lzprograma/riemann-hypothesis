module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.CategoryTheory.Category.Basic
public import Mathlib.LinearAlgebra.Charpoly.Basic
public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Mathlib.NumberTheory.NumberField.Discriminant.Defs
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Idempotents
import Mathlib.Algebra.AffineMonoid.UniqueSums
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Algebra.Algebra.Hom.Rat
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings
public import Mathlib.RingTheory.LocalRing.Module

@[expose] public section

open scoped TensorProduct NumberField
open Polynomial

namespace GlobalTheory

namespace EigenSplit

section Algebra

variable {O : Type*} [CommRing O] {R : Type*} [CommRing R] {ι : Type*}

noncomputable def splitMap (σ : ι → O →+* R) : R ⊗[ℤ] O →ₐ[R] (ι → R) :=
  Algebra.TensorProduct.lift (Algebra.ofId R (ι → R)) (RingHom.pi σ).toIntAlgHom
    (fun _ _ => Commute.all _ _)

@[simp] theorem splitMap_tmul (σ : ι → O →+* R) (r : R) (a : O) (i : ι) :
    splitMap σ (r ⊗ₜ a) i = r * σ i a := by
  simp [splitMap, Algebra.ofId_apply]

def IsSplitting (σ : ι → O →+* R) : Prop := Function.Bijective (splitMap σ)

noncomputable def splitEquiv {σ : ι → O →+* R} (h : IsSplitting σ) : R ⊗[ℤ] O ≃ₐ[R] (ι → R) :=
  AlgEquiv.ofBijective (splitMap σ) h

variable [DecidableEq ι]

noncomputable def idem {σ : ι → O →+* R} (h : IsSplitting σ) (i : ι) : R ⊗[ℤ] O :=
  (splitEquiv h).symm (Pi.single i 1)

@[simp] theorem splitMap_idem {σ : ι → O →+* R} (h : IsSplitting σ) (i : ι) :
    splitMap σ (idem h i) = Pi.single i 1 :=
  (splitEquiv h).apply_symm_apply _

theorem mul_idem {σ : ι → O →+* R} (h : IsSplitting σ) (i : ι) (t : R ⊗[ℤ] O) :
    t * idem h i = splitMap σ t i • idem h i := by
  apply h.1
  ext j
  rcases eq_or_ne j i with rfl | hj
  · simp
  · simp [hj]

theorem one_tmul_mul_idem {σ : ι → O →+* R} (h : IsSplitting σ) (i : ι) (a : O) :
    (1 ⊗ₜ a) * idem h i = σ i a • idem h i := by
  rw [mul_idem]; simp

theorem completeOrthogonalIdempotents_idem [Fintype ι] {σ : ι → O →+* R} (h : IsSplitting σ) :
    CompleteOrthogonalIdempotents (idem h) :=
  (CompleteOrthogonalIdempotents.single (fun _ : ι => R)).map
    (f := ((splitEquiv h).symm : (ι → R) →+* R ⊗[ℤ] O))

theorem isSplitting_of_idem [Fintype ι] {σ : ι → O →+* R} (e : ι → R ⊗[ℤ] O)
    (h1 : ∀ i, splitMap σ (e i) = Pi.single i 1) (h2 : ∑ i, e i = 1)
    (h3 : ∀ i a, (1 ⊗ₜ a) * e i = σ i a • e i) : IsSplitting σ := by
  have h4 : ∀ i t, t * e i = splitMap σ t i • e i := by
    intro i t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul r a =>
      have : (r ⊗ₜ[ℤ] a : R ⊗[ℤ] O) = r • (1 ⊗ₜ[ℤ] a) := by
        simp [TensorProduct.smul_tmul']
      rw [splitMap_tmul, this, smul_mul_assoc, h3, smul_smul]
    | add x y hx hy => simp [add_mul, hx, hy, add_smul]
  refine ⟨(injective_iff_map_eq_zero _).2 fun t ht => ?_, fun v => ⟨∑ i, v i • e i, ?_⟩⟩
  · rw [← mul_one t, ← h2, Finset.mul_sum]
    simp [h4, ht]
  · ext j
    simp [h1, Pi.single_apply]


omit [DecidableEq ι] in
theorem IsSplitting.map [Finite ι] {σ : ι → O →+* R} (h : IsSplitting σ) {R' : Type*}
    [CommRing R'] (f : R →+* R') : IsSplitting (fun i => f.comp (σ i)) := by
  classical
  have := Fintype.ofFinite ι
  let F : R ⊗[ℤ] O →ₐ[ℤ] R' ⊗[ℤ] O := Algebra.TensorProduct.map f.toIntAlgHom (AlgHom.id ℤ O)
  have hF : ∀ t i, splitMap (fun i => f.comp (σ i)) (F t) i = f (splitMap σ t i) := by
    intro t i
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul r a => simp [F]
    | add x y hx hy => simp [hx, hy]
  have hF' : ∀ (r : R) t, F (r • t) = f r • F t := by
    intro r t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul s a => simp [F, TensorProduct.smul_tmul']
    | add x y hx hy => simp [hx, hy]
  refine isSplitting_of_idem (fun i => F (idem h i)) (fun i => ?_) ?_ (fun i a => ?_)
  · ext j
    rw [hF, splitMap_idem]
    rcases eq_or_ne j i with rfl | hj
    · simp
    · simp [hj]

  · rw [← map_sum, (completeOrthogonalIdempotents_idem h).complete, map_one]
  · have : ((1 : R') ⊗ₜ[ℤ] a) = F (1 ⊗ₜ a) := by simp [F]
    rw [this, ← map_mul, one_tmul_mul_idem, hF']
    rfl


omit [DecidableEq ι] in
theorem IsSplitting.injective [Nontrivial R] {σ : ι → O →+* R} (h : IsSplitting σ) :
    Function.Injective σ := by
  classical
  intro i j hij
  by_contra hne
  have : ∀ t, splitMap σ t i = splitMap σ t j := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul r a => simp [hij]
    | add x y hx hy => simp [hx, hy]
  have h2 := this (idem h i)
  simp [Ne.symm hne] at h2

theorem isSplitting_iff_isUnit_det [Fintype ι] (σ : ι → O →+* R) (b : Module.Basis ι ℤ O) :
    IsSplitting σ ↔ IsUnit (Matrix.of fun i j => σ i (b j)).det := by
  have key : LinearMap.toMatrix (Algebra.TensorProduct.basis R b) (Pi.basisFun R ι)
      (splitMap σ).toLinearMap = Matrix.of fun i j => σ i (b j) := by
    ext i j
    simp [LinearMap.toMatrix_apply]
  constructor
  · intro h
    rw [← key]
    exact LinearEquiv.isUnit_det (splitEquiv h).toLinearEquiv _ _
  · intro h
    rw [← key] at h
    exact (LinearEquiv.ofIsUnitDet h).bijective

end Algebra

section Module

variable {O : Type*} [CommRing O] {R : Type*} [CommRing R] {ι : Type*}
  {N : Type*} [AddCommGroup N] [Module R N] {N' : Type*} [AddCommGroup N'] [Module R N']
  {N'' : Type*} [AddCommGroup N''] [Module R N'']

def eigenSub (ρ : O →+* Module.End R N) (χ : O →+* R) : Submodule R N :=
  ⨅ a, (ρ a).eigenspace (χ a)

theorem mem_eigenSub {ρ : O →+* Module.End R N} {χ : O →+* R} {x : N} :
    x ∈ eigenSub ρ χ ↔ ∀ a, ρ a x = χ a • x := by
  simp [eigenSub]

theorem apply_mem_eigenSub {ρ : O →+* Module.End R N} {χ : O →+* R} {x : N}
    (hx : x ∈ eigenSub ρ χ) (a : O) : ρ a x ∈ eigenSub ρ χ := by
  rw [mem_eigenSub.1 hx a]; exact Submodule.smul_mem _ _ hx

noncomputable def tensorAction (ρ : O →+* Module.End R N) : R ⊗[ℤ] O →ₐ[R] Module.End R N :=
  Algebra.TensorProduct.lift (Algebra.ofId R _) ρ.toIntAlgHom
    (fun r a => show Commute (Algebra.ofId R (Module.End R N) r) (ρ.toIntAlgHom a) from
      Algebra.commute_algebraMap_left r _)

@[simp] theorem tensorAction_tmul (ρ : O →+* Module.End R N) (r : R) (a : O) (x : N) :
    tensorAction ρ (r ⊗ₜ a) x = r • ρ a x := by
  rw [tensorAction, Algebra.TensorProduct.lift_tmul]
  simp [Algebra.ofId_apply]

theorem tensorAction_of_mem {ρ : O →+* Module.End R N} {σ : ι → O →+* R} {i : ι} {x : N}
    (hx : x ∈ eigenSub ρ (σ i)) (t : R ⊗[ℤ] O) :
    tensorAction ρ t x = splitMap σ t i • x := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul r a => simp [mem_eigenSub.1 hx a, smul_smul]
  | add s t hs ht => simp [hs, ht, add_smul]

def IsEquivariant (ρ : O →+* Module.End R N) (ρ' : O →+* Module.End R N') (f : N →ₗ[R] N') :
    Prop :=
  ∀ a x, f (ρ a x) = ρ' a (f x)

theorem isEquivariant_action (ρ : O →+* Module.End R N) (c : O) : IsEquivariant ρ ρ (ρ c) :=
  fun a x => by
    rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul, mul_comm]

theorem IsEquivariant.comp {ρ : O →+* Module.End R N} {ρ' : O →+* Module.End R N'}
    {ρ'' : O →+* Module.End R N''} {g : N' →ₗ[R] N''} {f : N →ₗ[R] N'}
    (hg : IsEquivariant ρ' ρ'' g) (hf : IsEquivariant ρ ρ' f) : IsEquivariant ρ ρ'' (g ∘ₗ f) :=
  fun a x => by simp [hf a, hg a]

theorem IsEquivariant.tensorAction {ρ : O →+* Module.End R N} {ρ' : O →+* Module.End R N'}
    {f : N →ₗ[R] N'} (hf : IsEquivariant ρ ρ' f) (t : R ⊗[ℤ] O) (x : N) :
    f (tensorAction ρ t x) = tensorAction ρ' t (f x) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul r a => simp [hf a]
  | add s t hs ht => simp [hs, ht]

theorem IsEquivariant.map_mem {ρ : O →+* Module.End R N} {ρ' : O →+* Module.End R N'}
    {f : N →ₗ[R] N'} (hf : IsEquivariant ρ ρ' f) {χ : O →+* R} {x : N}
    (hx : x ∈ eigenSub ρ χ) : f x ∈ eigenSub ρ' χ :=
  mem_eigenSub.2 fun a => by rw [← hf a, mem_eigenSub.1 hx a, map_smul]

def IsEquivariant.eigenMap {ρ : O →+* Module.End R N} {ρ' : O →+* Module.End R N'}
    {f : N →ₗ[R] N'} (hf : IsEquivariant ρ ρ' f) (χ : O →+* R) :
    eigenSub ρ χ →ₗ[R] eigenSub ρ' χ :=
  f.restrict fun _ hx => hf.map_mem hx

theorem IsEquivariant.eigenMap_injective {ρ : O →+* Module.End R N}
    {ρ' : O →+* Module.End R N'} {f : N →ₗ[R] N'} (hf : IsEquivariant ρ ρ' f) (χ : O →+* R)
    (hi : Function.Injective f) : Function.Injective (hf.eigenMap χ) :=
  fun _ _ hxy => Subtype.ext (hi (congrArg Subtype.val hxy))

section Split

variable [DecidableEq ι] {σ : ι → O →+* R} (h : IsSplitting σ) (ρ : O →+* Module.End R N)

noncomputable def proj (i : ι) : Module.End R N := tensorAction ρ (idem h i)

theorem proj_mem (i : ι) (x : N) : proj h ρ i x ∈ eigenSub ρ (σ i) := by
  refine mem_eigenSub.2 fun a => ?_
  have : ρ a (proj h ρ i x) = tensorAction ρ ((1 ⊗ₜ a) * idem h i) x := by
    simp [proj]
  rw [this, one_tmul_mul_idem]
  simp [proj]

variable {ρ} in
theorem proj_of_mem {i : ι} {x : N} (hx : x ∈ eigenSub ρ (σ i)) : proj h ρ i x = x := by
  simp [proj, tensorAction_of_mem hx]

variable {ρ} in
theorem proj_of_mem_ne {i j : ι} (hij : j ≠ i) {x : N} (hx : x ∈ eigenSub ρ (σ j)) :
    proj h ρ i x = 0 := by
  simp [proj, tensorAction_of_mem hx, hij]

theorem completeOrthogonalIdempotents_proj [Fintype ι] :
    CompleteOrthogonalIdempotents (proj h ρ) :=
  (completeOrthogonalIdempotents_idem h).map
    (f := (tensorAction ρ : R ⊗[ℤ] O →+* Module.End R N))

theorem sum_proj [Fintype ι] (x : N) : ∑ i, proj h ρ i x = x := by
  have := congrArg (fun p : Module.End R N => p x)
    (completeOrthogonalIdempotents_proj h ρ).complete
  simpa using this

variable {ρ} in
theorem IsEquivariant.proj {ρ' : O →+* Module.End R N'} {f : N →ₗ[R] N'}
    (hf : IsEquivariant ρ ρ' f) (i : ι) (x : N) : f (proj h ρ i x) = proj h ρ' i (f x) :=
  hf.tensorAction _ _

noncomputable def projTo (i : ι) : N →ₗ[R] eigenSub ρ (σ i) :=
  (proj h ρ i).codRestrict _ (proj_mem h ρ i)

@[simp] theorem coe_projTo (i : ι) (x : N) : (projTo h ρ i x : N) = proj h ρ i x := rfl

theorem projTo_comp_subtype (i : ι) :
    projTo h ρ i ∘ₗ (eigenSub ρ (σ i)).subtype = LinearMap.id := by
  ext x
  simp [proj_of_mem h x.2]

noncomputable def eigenEquiv [Fintype ι] : N ≃ₗ[R] (∀ i, eigenSub ρ (σ i)) :=
  LinearEquiv.ofLinearMap (LinearMap.pi (projTo h ρ))
    (∑ i, (eigenSub ρ (σ i)).subtype ∘ₗ LinearMap.proj i)
    (by
      refine LinearMap.ext fun v => funext fun i => Subtype.ext ?_

      simp only [LinearMap.comp_apply, LinearMap.pi_apply, coe_projTo, LinearMap.sum_apply,
      map_sum, LinearMap.id_apply, Submodule.coe_sum]
      rw [Finset.sum_eq_single i]
      · exact proj_of_mem h (v i).2
      · intro j _ hj; exact proj_of_mem_ne h hj (v j).2
      · simp)
    (by
      ext x
      simpa using sum_proj h ρ x)

theorem eigenEquiv_symm_apply [Fintype ι] (v : ∀ i, eigenSub ρ (σ i)) :
    (eigenEquiv h ρ).symm v = ∑ i, (v i : N) := by
  simp [eigenEquiv]


include h in
theorem isInternal_eigenSub [Finite ι] : DirectSum.IsInternal fun i => eigenSub ρ (σ i) := by
  have := Fintype.ofFinite ι
  rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top]
  constructor
  · intro i
    rw [Submodule.disjoint_def]
    intro x hx hx'
    rw [← proj_of_mem h hx]
    have : (⨆ j, ⨆ (_ : j ≠ i), eigenSub ρ (σ j)) ≤ LinearMap.ker (proj h ρ i) :=
      iSup₂_le fun j hj y hy => proj_of_mem_ne h hj hy
    exact this hx'
  · rw [eq_top_iff]
    intro x _
    rw [← sum_proj h ρ x]
    exact Submodule.sum_mem _ fun i _ =>
      Submodule.mem_iSup_of_mem i (proj_mem h ρ i x)

end Split

section Exact

variable {σ : ι → O →+* R} (h : IsSplitting σ) {ρ : O →+* Module.End R N}
  {ρ' : O →+* Module.End R N'} {ρ'' : O →+* Module.End R N''}
include h

theorem IsEquivariant.eigenMap_surjective {f : N →ₗ[R] N'} (hf : IsEquivariant ρ ρ' f) (i : ι)
    (hs : Function.Surjective f) : Function.Surjective (hf.eigenMap (σ i)) := by
  classical
  intro y
  obtain ⟨x, hx⟩ := hs y
  refine ⟨projTo h ρ i x, Subtype.ext ?_⟩
  change f (EigenSplit.proj h ρ i x) = (y : N')
  rw [hf.proj h, hx, proj_of_mem h y.2]

theorem IsEquivariant.eigenMap_exact {f : N →ₗ[R] N'} {g : N' →ₗ[R] N''}
    (hf : IsEquivariant ρ ρ' f) (hg : IsEquivariant ρ' ρ'' g) (i : ι)
    (he : Function.Exact f g) :
    Function.Exact (hf.eigenMap (σ i)) (hg.eigenMap (σ i)) := by
  classical
  intro y
  constructor
  · intro hy
    obtain ⟨x, hx⟩ := (he y).1 (congrArg Subtype.val hy)
    refine ⟨projTo h ρ i x, Subtype.ext ?_⟩
    change f (EigenSplit.proj h ρ i x) = (y : N')
    rw [hf.proj h, hx, proj_of_mem h y.2]
  · rintro ⟨x, rfl⟩
    exact Subtype.ext ((he _).2 ⟨x, rfl⟩)

variable (ρ)

theorem finite_eigenSub [Module.Finite R N] (i : ι) : Module.Finite R (eigenSub ρ (σ i)) := by
  classical
  exact Module.Finite.of_surjective (projTo h ρ i) fun y =>
    ⟨y, LinearMap.congr_fun (projTo_comp_subtype h ρ i) y⟩

end Exact

end Module

section BaseChange

variable {O : Type*} [CommRing O] {R : Type*} [CommRing R] {ι : Type*}
  {N : Type*} [AddCommGroup N] [Module R N] {R' : Type*} [CommRing R'] [Algebra R R']
  {M : Type*} [AddCommGroup M] [Module R M] [Module R' M] [IsScalarTower R R' M]
  {ρ : O →+* Module.End R N} {ρ' : O →+* Module.End R' M} {f : N →ₗ[R] M}

theorem map_mem_eigenSub_algebraMap (hf : ∀ a x, f (ρ a x) = ρ' a (f x)) {χ : O →+* R} {x : N}
    (hx : x ∈ eigenSub ρ χ) : f x ∈ eigenSub ρ' ((algebraMap R R').comp χ) :=
  mem_eigenSub.2 fun a => by
    rw [← hf a, mem_eigenSub.1 hx a, map_smul]
    simp

def eigenMapAlgebra (hf : ∀ a x, f (ρ a x) = ρ' a (f x)) (χ : O →+* R) :
    eigenSub ρ χ →ₗ[R] eigenSub ρ' ((algebraMap R R').comp χ) where
  toFun x := ⟨f x, map_mem_eigenSub_algebraMap hf x.2⟩
  map_add' x y := Subtype.ext (by simp)
  map_smul' r x := Subtype.ext (by simp)

variable {σ : ι → O →+* R}

theorem map_proj_algebraMap [Finite ι] [DecidableEq ι] (h : IsSplitting σ)
    (hf : ∀ a x, f (ρ a x) = ρ' a (f x)) (i : ι) (x : N) :
    f (proj h ρ i x) = proj (h.map (algebraMap R R')) ρ' i (f x) := by
  have := Fintype.ofFinite ι

  conv_rhs => rw [← sum_proj h ρ x, map_sum, map_sum]
  rw [Finset.sum_eq_single i]
  · exact (proj_of_mem (h.map (algebraMap R R'))
      (map_mem_eigenSub_algebraMap hf (proj_mem h ρ i x))).symm
  · intro j _ hj
    exact proj_of_mem_ne (h.map (algebraMap R R')) hj
      (map_mem_eigenSub_algebraMap hf (proj_mem h ρ j x))
  · simp

theorem isBaseChange_eigenMapAlgebra [Finite ι] (h : IsSplitting σ)
    (hf : ∀ a x, f (ρ a x) = ρ' a (f x)) (hb : IsBaseChange R' f) (i : ι) :
    IsBaseChange R' (eigenMapAlgebra hf (σ i)) := by
  classical
  let h' := h.map (algebraMap R R')
  let F : R' ⊗[R] eigenSub ρ (σ i) →ₗ[R'] eigenSub ρ' ((algebraMap R R').comp (σ i)) :=
    (eigenMapAlgebra hf (σ i)).liftBaseChange R'
  have h1 : ∀ t, (F t : M) = hb.equiv ((eigenSub ρ (σ i)).subtype.baseChange R' t) := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul r x => simp [F, IsBaseChange.equiv_tmul, eigenMapAlgebra]
    | add s t hs ht => simp [hs, ht]
  have h2 : ∀ t, (F ((projTo h ρ i).baseChange R' t) : M) = proj h' ρ' i (hb.equiv t) := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul r x => simp [F, IsBaseChange.equiv_tmul, eigenMapAlgebra, map_proj_algebraMap h hf]
    | add s t hs ht => simp [hs, ht]
  have h3 : ∀ t, (projTo h ρ i).baseChange R' ((eigenSub ρ (σ i)).subtype.baseChange R' t) = t := by
    intro t
    rw [← LinearMap.comp_apply, ← LinearMap.baseChange_comp, projTo_comp_subtype]
    simp
  have hF : Function.Bijective F := by
    constructor
    · intro s t hst
      have := congrArg Subtype.val hst
      rw [h1, h1] at this
      rw [← h3 s, ← h3 t, hb.equiv.injective this]
    · intro y
      refine ⟨(projTo h ρ i).baseChange R' (hb.equiv.symm y), Subtype.ext ?_⟩
      rw [h2, LinearEquiv.apply_symm_apply]
      exact proj_of_mem h' y.2
  exact IsBaseChange.of_equiv (LinearEquiv.ofBijective F hF) fun x => by simp [F]

variable (R') (ρ)

noncomputable def baseChangeAction : O →+* Module.End R' (R' ⊗[R] N) :=
  (Module.End.baseChangeHom R R' N).toRingHom.comp ρ

theorem mk_equivariant (a : O) (x : N) :
    TensorProduct.mk R R' N 1 (ρ a x) = baseChangeAction R' ρ a (TensorProduct.mk R R' N 1 x) := by
  change 1 ⊗ₜ[R] (ρ a x) = (ρ a).baseChange R' (1 ⊗ₜ[R] x)
  rw [LinearMap.baseChange_tmul]

end BaseChange

section Charpoly

variable {O : Type*} [CommRing O] {R : Type*} [CommRing R] {ι : Type*} [Fintype ι]
  {N : Type*} [AddCommGroup N] [Module R N]

variable {σ : ι → O →+* R} (h : IsSplitting σ) (ρ : O →+* Module.End R N)
  [Module.Free R N] [Module.Finite R N]
include h

theorem charpoly_eq_prod (hfree : ∀ i, Module.Free R (eigenSub ρ (σ i))) (a : O) :
    (ρ a).charpoly = ∏ i, (X - C (σ i a)) ^ Module.finrank R (eigenSub ρ (σ i)) := by
  classical
  nontriviality R
  have hfin := fun i => finite_eigenSub h ρ i
  let b := (isInternal_eigenSub h ρ).collectedBasis
    fun i => Module.Free.chooseBasis R (eigenSub ρ (σ i))
  have hm : LinearMap.toMatrix b b (ρ a) = Matrix.diagonal fun k => σ k.1 a := by
    ext k l
    have hl : b l ∈ eigenSub ρ (σ l.1) := (isInternal_eigenSub h ρ).collectedBasis_mem _ l
    rw [LinearMap.toMatrix_apply, mem_eigenSub.1 hl a]
    rcases eq_or_ne k l with rfl | hkl
    · simp
    · simp [hkl]
  rw [← LinearMap.charpoly_toMatrix (ρ a) b, hm, Matrix.charpoly_diagonal, Fintype.prod_sigma]
  refine Finset.prod_congr rfl fun i _ => ?_
  simp [Module.finrank_eq_card_chooseBasisIndex]

end Charpoly

section Discr

variable {E : Type*} [Field E] [NumberField E] {R : Type*} [CommRing R] {ι : Type*} [Fintype ι]
  [DecidableEq ι]


omit [DecidableEq ι] in
theorem nonempty_basis (hc : Fintype.card ι = Module.finrank ℚ E) :
    Nonempty (Module.Basis ι ℤ (𝓞 E)) :=
  ⟨(Module.finBasis ℤ (𝓞 E)).reindex (Fintype.equivFinOfCardEq
    (by rw [hc, NumberField.RingOfIntegers.rank])).symm⟩

omit [DecidableEq ι] in
theorem card_eq_of_basis (b : Module.Basis ι ℤ (𝓞 E)) :
    Fintype.card ι = Module.finrank ℚ E := by
  rw [← NumberField.RingOfIntegers.rank, Module.finrank_eq_card_basis b]

theorem det_sq_eq_discr_map {σ : ι → 𝓞 E →+* R} {b : Module.Basis ι ℤ (𝓞 E)}
    (hd : (Matrix.of fun i j => σ i (b j)).det ^ 2 = (NumberField.discr E : R))
    {R' : Type*} [CommRing R'] (f : R →+* R') :
    (Matrix.of fun i j => f.comp (σ i) (b j)).det ^ 2 = (NumberField.discr E : R') := by
  have := congrArg f hd
  rw [map_pow, RingHom.map_det, map_intCast] at this
  exact this

theorem det_sq_eq_discr_of_field {L : Type*} [Field L] {φ : ι → E →+* L}
    (hφ : Function.Injective φ) (b : Module.Basis ι ℤ (𝓞 E)) :
    (Matrix.of fun i j => φ i (b j)).det ^ 2 = (NumberField.discr E : L) := by
  rcases isEmpty_or_nonempty ι with hι | ⟨⟨i₀⟩⟩
  · have := card_eq_of_basis b
    rw [Fintype.card_eq_zero] at this
    exact absurd this Module.finrank_pos.ne
  have : CharZero L := charZero_of_injective_ringHom (φ i₀).injective
  let A := AlgebraicClosure L
  let ψ : ι → (E →ₐ[ℚ] A) := fun i => ((algebraMap L A).comp (φ i)).toRatAlgHom
  have hψ : Function.Bijective ψ := by
    rw [Fintype.bijective_iff_injective_and_card, AlgHom.card, card_eq_of_basis b]
    exact ⟨fun i j hij => hφ (RingHom.ext fun x =>
      (algebraMap L A).injective (DFunLike.congr_fun hij x)), rfl⟩
  have h1 := Algebra.discr_eq_det_embeddingsMatrixReindex_pow_two ℚ A
    (fun j => (b j : E)) (Equiv.ofBijective ψ hψ)
  have h2 : Algebra.discr ℚ (fun j => (b j : E)) = (NumberField.discr E : ℚ) := by
    have := Algebra.discr_localizationLocalization ℤ (Rₘ := ℚ) (nonZeroDivisors ℤ) E b
    rw [NumberField.discr_eq_discr] at this
    rw [eq_intCast] at this
    convert this using 2
    ext j
    simp
  apply (algebraMap L A).injective
  rw [h2] at h1
  rw [map_pow, RingHom.map_det, map_intCast, ← Matrix.det_transpose]
  rw [map_intCast] at h1
  rw [h1]
  congr 2

theorem det_sq_eq_discr_of_isDomain {S : Type*} [CommRing S] [IsDomain S] [CharZero S]
    {σ : ι → 𝓞 E →+* S} (hσ : Function.Injective σ) (b : Module.Basis ι ℤ (𝓞 E)) :
    (Matrix.of fun i j => σ i (b j)).det ^ 2 = (NumberField.discr E : S) := by
  let L := FractionRing S
  have hL : Function.Injective (algebraMap S L) := IsFractionRing.injective S L
  have hinj : ∀ i, Function.Injective ((algebraMap S L).comp (σ i)) := by
    intro i
    rw [RingHom.injective_iff_ker_eq_bot]
    refine Ideal.eq_bot_of_under_eq_bot (R := ℤ) ?_
    rw [Ideal.under, RingHom.comap_ker, ← RingHom.injective_iff_ker_eq_bot]
    exact RingHom.injective_int _
  let φ : ι → E →+* L := fun i => IsFractionRing.lift (hinj i)
  have hφσ : ∀ i (a : 𝓞 E), φ i a = algebraMap S L (σ i a) := fun i a =>
    IsFractionRing.lift_algebraMap (hinj i) a
  have hφ : Function.Injective φ := fun i j hij => hσ (RingHom.ext fun a => hL (by
    rw [← hφσ, ← hφσ, hij]))
  have := det_sq_eq_discr_of_field hφ b
  apply hL
  rw [map_pow, RingHom.map_det, map_intCast, ← this]
  congr 2
  ext i j
  simp [hφσ]


theorem isSplitting_of_isUnit_discr {σ : ι → 𝓞 E →+* R} (b : Module.Basis ι ℤ (𝓞 E))
    (hd : (Matrix.of fun i j => σ i (b j)).det ^ 2 = (NumberField.discr E : R))
    (hu : IsUnit (NumberField.discr E : R)) : IsSplitting σ :=
  (isSplitting_iff_isUnit_det σ b).2 ((isUnit_pow_iff two_ne_zero).1 (hd ▸ hu))



omit [DecidableEq ι] in
theorem isSplitting_of_isDomain {S : Type*} [CommRing S] [IsDomain S] [CharZero S]
    {σ : ι → 𝓞 E →+* S} (hσ : Function.Injective σ) (hc : Fintype.card ι = Module.finrank ℚ E)
    (f : S →+* R) (hu : IsUnit (NumberField.discr E : R)) :
    IsSplitting fun i => f.comp (σ i) := by
  classical
  obtain ⟨b⟩ := nonempty_basis hc
  exact isSplitting_of_isUnit_discr b
    (det_sq_eq_discr_map (det_sq_eq_discr_of_isDomain hσ b) f) hu

theorem isSplitting_complex (E : Type*) [Field E] [NumberField E] :
    IsSplitting fun φ : E →+* ℂ => φ.comp (algebraMap (𝓞 E) E) := by
  classical
  obtain ⟨b⟩ := nonempty_basis (E := E) (NumberField.Embeddings.card E ℂ)
  exact isSplitting_of_isUnit_discr b (det_sq_eq_discr_of_field Function.injective_id b)
    (by simpa using NumberField.discr_ne_zero E)

end Discr

end EigenSplit


end GlobalTheory
