module

public import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.TensFactor
public import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.CommPrj
public import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.FinTens
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.LocEmb
public import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.TensFactorAlt
public import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.OpBasics
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

noncomputable section

open MeasureTheory NumberField IsDedekindDomain
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Global GroundTheory.Global.SemiLocal
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C
open scoped ComplexConjugate InnerProductSpace Classical

namespace UpperTheory.ConvolutionTheory.L1.TY

theorem eigIn_closed {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {W : Submodule ℂ H} (hW : IsClosed (W : Set H)) (A : H →L[ℂ] H) (x : ℝ) :
    IsClosed (eigIn W A x : Set H) := by
  have : (eigIn W A x : Set H) = (W : Set H) ∩ {v | A v = (x : ℂ) • v} := by
    ext v
    simp [eigIn]
  rw [this]
  exact hW.inter (isClosed_eq A.continuous (continuous_const_smul _))

section Hil
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem prj_mem {V : Submodule ℂ H} (hV : IsClosed (V : Set H)) (v : H) : prj V v ∈ V := by
  have h : prj V v ∈ V.topologicalClosure := Submodule.starProjection_apply_mem V.topologicalClosure v
  rwa [hV.submodule_topologicalClosure_eq] at h

theorem prj_self {V : Submodule ℂ H} {v : H} (hv : v ∈ V) : prj V v = v :=
  Submodule.starProjection_eq_self_iff.2 (Submodule.le_topologicalClosure _ hv)

theorem prj_inner {V : Submodule ℂ H} (v : H) {w : H} (hw : w ∈ V) : ⟪v - prj V v, w⟫_ℂ = 0 :=
  Submodule.starProjection_inner_eq_zero v w (Submodule.le_topologicalClosure _ hw)

theorem prj_eq_of {V : Submodule ℂ H} (hV : IsClosed (V : Set H)) (x y : H) (hy : y ∈ V)
    (h : ∀ w ∈ V, ⟪x - y, w⟫_ℂ = 0) : prj V x = y :=
  Submodule.eq_starProjection_of_mem_of_inner_eq_zero (Submodule.le_topologicalClosure _ hy)
    fun w hw => h w (by rwa [hV.submodule_topologicalClosure_eq] at hw)

theorem prj_star (V : Submodule ℂ H) : IsStarProjection (prj V) := isStarProjection_starProjection

theorem prj_mul {E G : Submodule ℂ H} (hE : IsClosed (E : Set H)) (hG : IsClosed (G : Set H))
    (hc : Commute (prj E) (prj G)) : prj E * prj G = prj (E ⊓ G) := by
  have hEG : IsClosed ((E ⊓ G : Submodule ℂ H) : Set H) := by
    rw [Submodule.coe_inf]; exact hE.inter hG
  refine ContinuousLinearMap.ext fun x => (prj_eq_of hEG x ((prj E * prj G) x) ⟨prj_mem hE (prj G x), ?_⟩ fun w hw => ?_).symm
  · show (prj E * prj G) x ∈ G
    rw [hc.eq]; exact prj_mem hG _
  · have : x - (prj E * prj G) x = (x - prj G x) + (prj G x - prj E (prj G x)) := by simp
    rw [this, inner_add_left, prj_inner x hw.2, prj_inner _ hw.1, add_zero]

theorem prj_commute {V : Submodule ℂ H} (hV : IsClosed (V : Set H)) (T : H →L[ℂ] H) (h1 : ∀ v ∈ V, T v ∈ V)
    (h2 : ∀ v ∈ V, ContinuousLinearMap.adjoint T v ∈ V) : Commute T (prj V) := by
  refine ContinuousLinearMap.ext fun v => (prj_eq_of hV (T v) (T (prj V v)) (h1 _ (prj_mem hV v)) fun w hw => ?_).symm
  rw [← map_sub, ← ContinuousLinearMap.adjoint_inner_right]
  exact prj_inner v (h2 w hw)

theorem prj_equiv {W W' : Submodule ℂ H} (hW : IsClosed (W : Set H)) (hW' : IsClosed (W' : Set H)) (U : H ≃ₗᵢ[ℂ] H)
    (h : ∀ v, U v ∈ W' ↔ v ∈ W) (v : H) : U (prj W v) = prj W' (U v) := by
  refine (prj_eq_of hW' _ _ ((h _).2 (prj_mem hW v)) fun w hw => ?_).symm
  obtain ⟨u, rfl⟩ := U.surjective w
  rw [← map_sub, U.inner_map_map]
  exact prj_inner v ((h u).1 hw)

theorem mem_eigIn {W : Submodule ℂ H} {A : H →L[ℂ] H} {x : ℝ} {v : H} : v ∈ eigIn W A x ↔ v ∈ W ∧ A v = (x : ℂ) • v := by
  simp only [eigIn, Submodule.mem_inf, Module.End.mem_eigenspace_iff, ContinuousLinearMap.coe_coe]

theorem prj_eigIn_comp_prj (Ty Fx V : Submodule ℂ H) (hTy : IsClosed (Ty : Set H)) (hFx : IsClosed (Fx : Set H))
    (hV : IsClosed (V : Set H)) (hle : Ty ≤ Fx) (Oa : H →L[ℂ] H) (hOa : ContinuousLinearMap.adjoint Oa = Oa)
    (hOT : ∀ v ∈ Ty, Oa v ∈ Ty) (hOF : ∀ v ∈ Fx, Oa v ∈ Fx) (hVT : ∀ v ∈ Ty, prj V v ∈ Ty) (x : ℝ) :
    prj (eigIn V (Oa ∘L prj Fx) x) * prj Ty = prj (eigIn (V ⊓ Ty) Oa x) ∧
    prj Ty * prj (eigIn V (Oa ∘L prj Fx) x) = prj (eigIn (V ⊓ Ty) Oa x) ∧
    prj (eigIn V (Oa ∘L prj Fx) x) * (Oa ∘L prj Fx) = (x : ℂ) • prj (eigIn V (Oa ∘L prj Fx) x) := by
  set A := Oa ∘L prj Fx
  set X := eigIn V A x with hXd
  have hXc : IsClosed (X : Set H) := eigIn_closed hV A x
  have hadj : ∀ Q : Submodule ℂ H, ContinuousLinearMap.adjoint (prj Q) = prj Q := fun Q =>
    (prj_star Q).isSelfAdjoint.adjoint_eq
  have hOP : Oa * prj Ty = prj Ty * Oa := (prj_commute hTy Oa hOT (hOa.symm ▸ hOT)).eq
  have hOFx : Oa * prj Fx = prj Fx * Oa := (prj_commute hFx Oa hOF (hOa.symm ▸ hOF)).eq
  have hVP : prj V * prj Ty = prj Ty * prj V := (prj_commute hTy (prj V) hVT ((hadj V).symm ▸ hVT)).eq
  have hFP : prj Fx * prj Ty = prj Ty := ContinuousLinearMap.ext fun v => prj_self (hle (prj_mem hTy v))
  have hPF : prj Ty * prj Fx = prj Ty :=
    ((prj_commute hFx (prj Ty) (fun _ _ => hle (prj_mem hTy _))
      ((hadj Ty).symm ▸ fun _ _ => hle (prj_mem hTy _))).eq).trans hFP
  have hAP : A * prj Ty = prj Ty * A := by
    show Oa * prj Fx * prj Ty = prj Ty * (Oa * prj Fx)
    rw [mul_assoc, hFP, hOP, ← mul_assoc, ← hOP, mul_assoc, hPF, hOP]
  have hAadj : star A = A := by
    show star (Oa * prj Fx) = Oa * prj Fx
    rw [star_mul, ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.star_eq_adjoint, hOa, hadj, hOFx]
  have heq : X ⊓ Ty = eigIn (V ⊓ Ty) Oa x := by
    ext v
    simp only [Submodule.mem_inf, mem_eigIn, hXd]
    have hA1 : v ∈ Ty → A v = Oa v := fun hv => by
      show Oa (prj Fx v) = Oa v
      rw [prj_self (hle hv)]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨⟨h1, h3⟩, by rwa [← hA1 h3]⟩
    · rintro ⟨⟨h1, h3⟩, h2⟩; exact ⟨⟨h1, by rwa [hA1 h3]⟩, h3⟩
  have hPX : ∀ v ∈ X, prj Ty v ∈ X := fun v hv => by
    obtain ⟨h1, h2⟩ := mem_eigIn.1 hv
    refine mem_eigIn.2 ⟨?_, ?_⟩
    · have := congrArg (fun S : H →L[ℂ] H => S v) hVP
      simp only [mul_apply_eq_comp, prj_self h1] at this
      rw [← this]; exact prj_mem hV _
    · have := congrArg (fun S : H →L[ℂ] H => S v) hAP
      simp only [mul_apply_eq_comp] at this
      rw [this, h2, map_smul]
  have hc : Commute (prj Ty) (prj X) := prj_commute hXc (prj Ty) hPX ((hadj Ty).symm ▸ hPX)
  have k1 : prj X * prj Ty = prj (eigIn (V ⊓ Ty) Oa x) := heq ▸ prj_mul hXc hTy hc.symm
  refine ⟨k1, hc.eq.trans k1, ?_⟩
  have hAX : A * prj X = (x : ℂ) • prj X := ContinuousLinearMap.ext fun v => (mem_eigIn.1 (prj_mem hXc v)).2
  have := congrArg star hAX
  rwa [star_mul, star_smul, hAadj, (prj_star X).isSelfAdjoint.star_eq, RCLike.star_def, Complex.conj_ofReal] at this

theorem isHS_prj (E : Submodule ℂ H) [FiniteDimensional ℂ E] : IsHilbertSchmidt (prj E) := by
  have hcl : E.topologicalClosure = E :=
    (Submodule.isClosed_of_finiteDimensional E).submodule_topologicalClosure_eq
  have : FiniteDimensional ℂ E.topologicalClosure := by rw [hcl]; infer_instance
  have h1 : IsHilbertSchmidt (E.topologicalClosure.subtypeL) := by
    rw [isHilbertSchmidt_iff (stdOrthonormalBasis ℂ E.topologicalClosure).toHilbertBasis, tsum_fintype]
    exact ENNReal.sum_lt_top.2 fun i _ => ENNReal.pow_lt_top eNorm_lt_top
  exact h1.comp_right E.topologicalClosure.orthogonalProjectionOnto

theorem trace_sm (c : ℂ) (S : H →L[ℂ] H) : trace (c • S) = c * trace S := by
  simp only [trace, smul_apply, inner_smul_right, tsum_mul_left]

theorem eig_mul {W : Submodule ℂ H} (hW : IsClosed (W : Set H)) {O : H →L[ℂ] H} (hc : Commute O (prj W)) {x : ℝ} (hx : x ≠ 0)
    (v : H) : (O * prj W) v = (x : ℂ) • v ↔ v ∈ W ∧ O v = (x : ℂ) • v := by
  constructor
  · intro h
    have hv : v ∈ W := by
      have h1 : (x : ℂ) • v ∈ W := by rw [← h, hc.eq]; exact prj_mem hW _
      exact (W.smul_mem_iff (Complex.ofReal_ne_zero.2 hx)).1 h1
    exact ⟨hv, by rw [← h, ContinuousLinearMap.mul_apply, prj_self hv]⟩
  · rintro ⟨hv, h⟩
    rw [ContinuousLinearMap.mul_apply, prj_self hv, h]

variable {Γ : Type*} [Group Γ] [TopologicalSpace Γ]

theorem lift_int {X : Type*} (π : UnitaryRep Γ H) (A : H → H) (f f' : X → Γ) (h : ∀ x v, A (π (f x) v) = π (f' x) (A v))
    (g : FreeGroup X) : ∀ v, A (π (FreeGroup.lift f g) v) = π (FreeGroup.lift f' g) (A v) := by
  induction g using FreeGroup.induction_on with
  | one => intro v; simp only [map_one, UnitaryRep.map_one_apply]
  | of x => simpa using h x
  | inv_of x ih =>
    intro v
    have h1 := ih (π (FreeGroup.lift f (FreeGroup.of x))⁻¹ v)
    rw [← UnitaryRep.map_mul_apply, mul_inv_cancel, UnitaryRep.map_one_apply] at h1
    rw [map_inv, map_inv, h1, ← UnitaryRep.map_mul_apply, inv_mul_cancel, UnitaryRep.map_one_apply]
  | mul a b iha ihb => intro v; simp only [map_mul, UnitaryRep.map_mul_apply, iha, ihb]

theorem inv_commute (π : UnitaryRep Γ H) {V : Submodule ℂ H} (hV : IsClosed (V : Set H)) (hi : π.IsInvariant V) (g : Γ) (v : H) :
    prj V (π g v) = π g (prj V v) := by
  refine prj_eq_of hV _ _ (hi _ _ (prj_mem hV v)) fun w hw => ?_
  have h1 : w = π g (π g⁻¹ w) := by rw [← UnitaryRep.map_mul_apply, mul_inv_cancel, UnitaryRep.map_one_apply]
  rw [← map_sub, h1, UnitaryRep.inner_map_map]
  exact prj_inner v (hi _ _ hw)

end Hil

theorem lift_commute {X Γ : Type*} [Group Γ] (f f' : X → Γ) (h : ∀ x y, Commute (f x) (f' y)) (a b : FreeGroup X) :
    Commute (FreeGroup.lift f a) (FreeGroup.lift f' b) := by
  induction a using FreeGroup.induction_on with
  | one => simp
  | of x =>
    induction b using FreeGroup.induction_on with
    | one => simp
    | of y => simpa using h x y
    | inv_of y ih => rw [map_inv]; exact ih.inv_right
    | mul c d ihc ihd => rw [map_mul]; exact ihc.mul_right ihd
  | inv_of x ih => rw [map_inv]; exact ih.inv_left
  | mul c d ihc ihd => rw [map_mul]; exact ihc.mul_left ihd

section Alg
variable {M : Type*} [Monoid M]

theorem ofFn_mul : ∀ (r : ℕ) (T P : Fin r → M), (∀ i j, i ≠ j → Commute (P i) (T j)) →
    (List.ofFn fun i => T i * P i).prod = (List.ofFn T).prod * (List.ofFn P).prod := by
  intro r
  induction r with
  | zero => intro T P _; simp
  | succ r ih =>
    intro T P h1
    have h3 := ih (fun i => T i.succ) (fun i => P i.succ) fun i j hij => h1 _ _ fun h => hij (Fin.succ_injective _ h)
    have h4 : Commute (P 0) (List.ofFn fun i : Fin r => T i.succ).prod := by
      refine Commute.list_prod_right _ _ fun x hx => ?_
      obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).1 hx
      exact h1 _ _ (Fin.succ_ne_zero i).symm
    simp only [List.ofFn_succ, List.prod_cons]
    rw [h3, mul_assoc, mul_assoc, ← mul_assoc (P 0), h4.eq, mul_assoc]

theorem ofFn_single : ∀ (r : ℕ) (T : Fin r → M) (j : Fin r), (∀ i, i ≠ j → T i = 1) → (List.ofFn T).prod = T j := by
  intro r
  induction r with
  | zero => intro T j; exact j.elim0
  | succ r ih =>
    intro T j h
    rw [List.ofFn_succ, List.prod_cons]
    refine Fin.cases (fun h => ?_) (fun j h => ?_) j h
    · rw [List.prod_eq_one, mul_one]
      intro x hx
      obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).1 hx
      exact h _ (Fin.succ_ne_zero i)
    · rw [h 0 (Fin.succ_ne_zero j).symm, one_mul]
      exact ih (fun i => T i.succ) j fun i hi => h _ fun e => hi (Fin.succ_injective _ e)

end Alg

def prodM {G Γ : Type*} [Group G] [Group Γ] {r : ℕ} (ι : Fin r → G →* Γ) (h : ∀ i j, i ≠ j → ∀ a b, Commute (ι i a) (ι j b)) :
    Submonoid Γ where
  carrier := {x | ∃ g : Fin r → G, x = (List.ofFn fun i => ι i (g i)).prod}
  one_mem' := ⟨1, (List.prod_eq_one fun x hx => by
    obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).1 hx
    simp).symm⟩
  mul_mem' := by
    rintro _ _ ⟨g, rfl⟩ ⟨g', rfl⟩
    refine ⟨g * g', ?_⟩
    rw [← ofFn_mul r _ _ fun i j hij => h i j hij _ _]
    simp only [Pi.mul_apply, map_mul]

theorem mem_prodM {G Γ : Type*} [Group G] [Group Γ] {r : ℕ} (ι : Fin r → G →* Γ)
    (h : ∀ i j, i ≠ j → ∀ a b, Commute (ι i a) (ι j b)) (j : Fin r) (a : G) : ι j a ∈ prodM ι h :=
  ⟨Pi.mulSingle j a, by
    rw [ofFn_single r _ j fun i hi => by simp [Pi.mulSingle_eq_of_ne hi]]
    simp⟩

theorem ofFn_mulSingle {G : Type*} [Group G] {r : ℕ} (g : Fin r → G) :
    (List.ofFn fun i => (Pi.mulSingle i (g i) : Fin r → G)).prod = g := by
  funext j
  have := map_list_prod (Pi.evalMonoidHom (fun _ : Fin r => G) j) (List.ofFn fun i => (Pi.mulSingle i (g i) : Fin r → G))
  rw [List.map_ofFn, ofFn_single r (_ ∘ _) j fun i hi => by simp [Pi.mulSingle_eq_of_ne' hi]] at this
  exact this.trans (by simp)

theorem cyc_le {α : Type*} [Preorder α] {m : ℕ} (J : Fin (m + 1) → α) (h : ∀ i, J (i + 1) ≤ J i) (i : Fin (m + 1)) :
    J i ≤ J (i + 1) := by
  have h1 : ∀ (k : ℕ) j, J ((fun x => x + 1)^[k] j) ≤ J j := fun k => by
    induction k with
    | zero => exact fun _ => le_rfl
    | succ k ih => exact fun j => by rw [Function.iterate_succ_apply']; exact (h _).trans (ih j)
  obtain ⟨k, hk, hp⟩ := Function.mem_periodicPts.1 ((add_left_injective (1 : Fin (m + 1))).mem_periodicPts i)
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
  have h2 : (fun x => x + 1)^[k] (i + 1) = i := hp
  simpa [h2] using h1 k (i + 1)

section Loc
variable {K : Type} [Field K] [NumberField K] {n : ℕ} (μ : Measure (normOneGL (K := K) (n := n))) [μ.IsHaarMeasure]

theorem rhoL_adj (w : Pl K) (g : Gw n w) : ContinuousLinearMap.adjoint (rhoL μ w g) = rhoL μ w g⁻¹ := by
  exact UpperTheory.ConvolutionTheory.L1.rhoL_adj μ w g

theorem rhoL_comm {v w : Pl K} (h : v ≠ w) (g : Gw n v) (x : Gw n w) : Commute (rhoL μ v g) (rhoL μ w x) := by
  have hm := (UpperTheory.ConvolutionTheory.Tf.commPrj K n μ ⊥).2.2.2.2.2.1
  have hc := (UpperTheory.ConvolutionTheory.Tf.locEmb K n v).2.2.2.1 w h.symm g x
  show rhoL μ v g ∘L rhoL μ w x = rhoL μ w x ∘L rhoL μ v g
  simp only [rhoL]
  rw [← hm, ← hm, hc]

theorem arch_fin (a : archGroup K n) (h : AdelicGLn.FiniteAdelicGL K n) :
    Commute (archP K n a) (MultiplicityOne.finProj K n h) := (MultiplicityOne.finProj_mul_archProj_comm h a).symm

theorem mem_eigL {w : Pl K} {J' : Subgroup (Gw n w)} {χ' : Gw n w → ℂ} {x : LL μ} :
    x ∈ eigL μ w J' χ' ↔ ∀ y ∈ J', rhoL μ w y x = χ' y • x := by
  simp [eigL, Submodule.mem_iInf, LinearMap.mem_eqLocus]

def GA (J : ∀ w : Pl K, Subgroup (Gw n w)) (χ : ∀ w : Pl K, Gw n w → ℂ) (A : Set (Pl K)) : Submodule ℂ (LL μ) :=
  ⨅ u ∈ A, eigL μ u (J u) (χ u)

variable {J : ∀ w : Pl K, Subgroup (Gw n w)} {χ : ∀ w : Pl K, Gw n w → ℂ}

theorem mem_GA {A : Set (Pl K)} {x : LL μ} : x ∈ GA μ J χ A ↔ ∀ u ∈ A, ∀ y ∈ J u, rhoL μ u y x = χ u y • x := by
  simp only [GA, Submodule.mem_iInf, mem_eigL]

theorem GA_closed (A : Set (Pl K)) : IsClosed (GA μ J χ A : Set (LL μ)) := by
  have : (GA μ J χ A : Set (LL μ)) = ⋂ u ∈ A, ⋂ y ∈ J u, {x | rhoL μ u y x = χ u y • x} := by
    ext x
    simp [mem_GA]
  rw [this]
  exact isClosed_biInter fun u _ => isClosed_biInter fun y _ => isClosed_eq (rhoL μ u y).continuous (continuous_const_smul _)

theorem GA_commute {A : Set (Pl K)} (B : LL μ →L[ℂ] LL μ) (hB : ∀ u ∈ A, ∀ x, Commute B (rhoL μ u x)) :
    Commute B (prj (GA μ J χ A)) := by
  have key : ∀ B : LL μ →L[ℂ] LL μ, (∀ u ∈ A, ∀ x, Commute B (rhoL μ u x)) → ∀ v ∈ GA μ J χ A, B v ∈ GA μ J χ A :=
    fun B hB v hv => (mem_GA μ).2 fun u hu y hy => by
      rw [← ContinuousLinearMap.mul_apply, ← (hB u hu y).eq, ContinuousLinearMap.mul_apply, (mem_GA μ).1 hv u hu y hy, map_smul]
  refine prj_commute (GA_closed μ A) B (key B hB) (key _ fun u hu x => ?_)
  have h := (hB u hu x⁻¹).star_star
  rwa [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.star_eq_adjoint, rhoL_adj, inv_inv] at h

theorem GA_rhoL {A : Set (Pl K)} {v : Pl K} (hv : v ∉ A) (g : Gw n v) : Commute (rhoL μ v g) (prj (GA μ J χ A)) :=
  GA_commute μ _ fun u hu x => rhoL_comm μ (fun h : v = u => hv (h ▸ hu)) g x

theorem GA_GA {A A' : Set (Pl K)} (h : Disjoint A A') : Commute (prj (GA μ J χ A)) (prj (GA μ J χ A')) :=
  GA_commute μ _ fun _ hu x => (GA_rhoL μ (Set.disjoint_right.1 h hu) x).symm

theorem GA_union (A A' : Set (Pl K)) : GA μ J χ (A ∪ A') = GA μ J χ A ⊓ GA μ J χ A' := iInf_union

theorem GA_prod : ∀ (r : ℕ) (R : Fin r → Set (Pl K)), (∀ i j, i ≠ j → Disjoint (R i) (R j)) →
    (List.ofFn fun i => prj (GA μ J χ (R i))).prod = prj (GA μ J χ (⋃ i, R i)) := by
  intro r
  induction r with
  | zero =>
    intro R _
    refine ContinuousLinearMap.ext fun v => ?_
    rw [prj_self ((mem_GA μ).2 fun u hu => by simp at hu)]
    simp
  | succ r ih =>
    intro R h
    rw [List.ofFn_succ, List.prod_cons, ih (fun i => R i.succ) fun i j hij => h _ _ fun e => hij (Fin.succ_injective _ e),
      prj_mul (GA_closed μ _) (GA_closed μ _)
        (GA_GA μ (Set.disjoint_iUnion_right.2 fun i => h _ _ (Fin.succ_ne_zero i).symm)), ← GA_union]
    congr 2
    ext u
    simp [Fin.exists_fin_succ]

theorem GA_mem {V : Submodule ℂ (LL μ)} (hV : IsSummand μ V) (A : Set (Pl K)) {v : LL μ} (hv : v ∈ V) :
    prj (GA μ J χ A) v ∈ V := by
  have h := GA_commute μ (J := J) (χ := χ) (A := A) (prj V) fun u _ x =>
    ContinuousLinearMap.ext fun y => inv_commute _ hV.closed hV.inv _ y
  rw [← prj_self hv, ← ContinuousLinearMap.mul_apply, ← h.eq]
  exact prj_mem hV.closed _

theorem GA_arch (A : Set (Pl K)) (a : archGroup K n) :
    Commute (rightRegularRep (rationalGLOne (K := K) (n := n)) μ (archP K n a)) (prj (GA μ J χ A)) :=
  GA_commute μ _ fun u _ x => ContinuousLinearMap.ext fun y => by
    simp only [ContinuousLinearMap.mul_apply, rhoL, rhoF]
    rw [← UnitaryRep.map_mul_apply, ← UnitaryRep.map_mul_apply, (arch_fin _ _).eq]

theorem test_ind {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {J : Subgroup G} (hJ : CO J)
    {χ : G → ℂ} (hχ : IsChr J χ) : Test ((J : Set G).indicator fun x => conj (χ x)) := by
  refine ⟨(IsLocallyConstant.iff_eventually_eq _).2 fun x => ?_,
    HasCompactSupport.intro hJ.1 fun x hx => Set.indicator_of_notMem hx _⟩
  by_cases hx : x ∈ (J : Set G)
  · filter_upwards [hJ.2.mem_nhds hx, (IsLocallyConstant.iff_eventually_eq _).1 hχ.1 x] with y hy hy2
    rw [Set.indicator_of_mem hy, Set.indicator_of_mem hx, hy2]
  · filter_upwards [(Subgroup.isClosed_of_isOpen J hJ.2).isOpen_compl.mem_nhds hx] with y hy
    rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hx]

theorem compact_typed (hn : 0 < n) (ν : Measure (archGroup K n)) [ν.IsHaarMeasure] (hco : ∀ w, CO (J w) ∧ IsChr (J w) (χ w))
    (hcof : ∀ᶠ w in Filter.cofinite, J w = GLnLocal.integralGL (w.adicCompletion K) n ∧ χ w = 1) (β : TI K n) :
    IsCompactOperator (Oinf μ ν β ∘L prj (GA μ J χ Set.univ) ∘L prj (cuspidalL2 μ)) := by
  obtain ⟨κ, hκ, H⟩ := tensFactor K n hn μ ν J χ hco hcof
  have hB := Filter.eventually_cofinite.1 hcof
  obtain ⟨e, he, -⟩ := UpperTheory.ConvolutionTheory.Tf.finTens K n μ Measure.haar _ (fun j => (hB.toFinset.equivFin.symm j).1)
    (fun i j h => hB.toFinset.equivFin.symm.injective (Subtype.ext h))
    (fun v => (J v : Set (Gw n v)).indicator fun g => conj (χ v g)) (fun i => test_ind (hco _).1 (hco _).2) fun v hv => by
      have h : J v = GLnLocal.integralGL (v.adicCompletion K) n ∧ χ v = 1 := by
        by_contra h
        exact hv ⟨hB.toFinset.equivFin ⟨v, hB.mem_toFinset.2 h⟩, by simp⟩
      rw [h.1, h.2]
      exact Set.indicator_congr fun x _ => by simp
  have h1 := @H β 0 Fin.elim0 (fun i => i.elim0) (fun i => i.elim0) (fun i => i.elim0) (fun i => i.elim0) (fun i => i.elim0)
    (fun i => i.elim0) (fun i => i.elim0) (fun i => i.elim0) e fun x => by rw [he]; simp
  have h2 := ((UpperTheory.ConvolutionTheory.C.opBasics K n μ (tens β e)).2.2).smul ((κ : ℂ)⁻¹)
  refine cast (congrArg _ (funext fun v => Eq.symm ?_)) h2
  have h3 : GA μ J χ Set.univ = ⨅ u, eigL μ u (J u) (χ u) := by simp [GA]
  simp only [h1, h3, ContinuousLinearMap.comp_apply, Pi.smul_apply, ContinuousLinearMap.smul_apply, List.ofFn_zero,
    List.prod_nil, ContinuousLinearMap.one_apply]
  rw [inv_smul_smul₀ (Complex.ofReal_ne_zero.2 hκ.ne')]

theorem split_fin (M : Submonoid (normOneGL (K := K) (n := n))) (B : Finset (Pl K))
    (hM : ∀ b ∈ B, ∀ y, MultiplicityOne.finProj K n (AdelicGLn.localEmbedding b y) ∈ M) (h : AdelicGLn.FiniteAdelicGL K n) :
    ∃ x ∈ M, ∃ h', MultiplicityOne.finProj K n h = x * MultiplicityOne.finProj K n h' ∧
      ∀ w ∈ B, finAt w (finEmb K n h') = 1 := by
  induction B using Finset.induction_on with
  | empty => exact ⟨1, M.one_mem, h, (one_mul _).symm, by simp⟩
  | insert b B hb ih =>
    obtain ⟨x, hx, h', e, h1⟩ := ih fun c hc => hM c (Finset.mem_insert_of_mem hc)
    refine ⟨_, M.mul_mem hx (hM b (Finset.mem_insert_self _ _) (finAt b (finEmb K n h'))),
      (AdelicGLn.localEmbedding b (finAt b (finEmb K n h')))⁻¹ * h', ?_, fun w hw => ?_⟩
    · rw [e, map_mul, map_inv, mul_assoc, mul_inv_cancel_left]
    · rw [map_mul, map_inv, finAt_mul, finAt_inv]
      rcases Finset.mem_insert.1 hw with rfl | hw
      · rw [(UpperTheory.ConvolutionTheory.Tf.locEmb K n w).2.1, inv_mul_cancel]
      · rw [(UpperTheory.ConvolutionTheory.Tf.locEmb K n b).2.2.1 w (fun e => hb (e ▸ hw)), h1 w hw, inv_one, one_mul]

theorem rhoL_mul (w : Pl K) (g h : Gw n w) : rhoL μ w (g * h) = rhoL μ w g ∘L rhoL μ w h := by
  exact UpperTheory.ConvolutionTheory.L1.rhoL_mul μ w g h

theorem arch_comm (a : archGroup K n) (w : Pl K) (g : Gw n w) :
    Commute (rightRegularRep (rationalGLOne (K := K) (n := n)) μ (archP K n a)) (rhoL μ w g) := by
  show rightRegularRep (rationalGLOne (K := K) (n := n)) μ (archP K n a) *
      rightRegularRep (rationalGLOne (K := K) (n := n)) μ (MultiplicityOne.finProj K n (AdelicGLn.localEmbedding w g)) =
    rightRegularRep (rationalGLOne (K := K) (n := n)) μ (MultiplicityOne.finProj K n (AdelicGLn.localEmbedding w g)) *
      rightRegularRep (rationalGLOne (K := K) (n := n)) μ (archP K n a)
  rw [← UnitaryRep.map_mul, ← UnitaryRep.map_mul, (arch_fin a _).eq]

theorem oloc_comm {w : Pl K} [MeasurableSpace (Gw n w)] {m : Measure (Gw n w)} {ψ : Gw n w → ℂ}
    {Bo : LL μ →L[ℂ] LL μ} (h : IsOloc μ w m ψ Bo) (R : LL μ →L[ℂ] LL μ) (hR : ∀ g, Commute R (rhoL μ w g)) :
    Commute R Bo := by
  refine ContinuousLinearMap.ext fun v => ext_inner_left ℂ fun u => ?_
  show ⟪u, R (Bo v)⟫_ℂ = ⟪u, Bo (R v)⟫_ℂ
  rw [← ContinuousLinearMap.adjoint_inner_left R, h, h]
  refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
  show ψ g * _ = ψ g * _
  congr 1
  rw [ContinuousLinearMap.adjoint_inner_left]
  have := congrArg (fun S : LL μ →L[ℂ] LL μ => S v) (hR g).eq
  simp only [mul_apply_eq_comp] at this
  rw [this]

theorem oloc_fix {w : Pl K} [MeasurableSpace (Gw n w)] [BorelSpace (Gw n w)] {m : Measure (Gw n w)} [m.IsHaarMeasure]
    {ψ : Gw n w → ℂ} {Bo : LL μ →L[ℂ] LL μ} (h : IsOloc μ w m ψ Bo) (J : Subgroup (Gw n w))
    (hJ : ∀ u ∈ J, ∀ g, ψ (u * g) = ψ g) (v : LL μ) : Bo v ∈ fixL μ w J := by
  refine ((UpperTheory.ConvolutionTheory.Tf.commPrj K n μ _).2.1 _).2 ?_
  rintro _ ⟨u, hu, rfl⟩
  refine ext_inner_left ℂ fun a => ?_
  show ⟪a, rhoL μ w u (Bo v)⟫_ℂ = ⟪a, Bo v⟫_ℂ
  rw [← ContinuousLinearMap.adjoint_inner_left (rhoL μ w u), h, h,
    ← integral_mul_left_eq_self (μ := m) (fun g => ψ g * ⟪a, rhoL μ w g v⟫_ℂ) u]
  refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
  show ψ g * _ = ψ (u * g) * _
  rw [hJ u hu, rhoL_mul, ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_left]

theorem mem_fixL {w : Pl K} {J : Subgroup (Gw n w)} {v : LL μ} :
    v ∈ fixL μ w J ↔ ∀ x ∈ J, rhoL μ w x v = v := by
  refine ((UpperTheory.ConvolutionTheory.Tf.commPrj K n μ _).2.1 v).trans ⟨fun h x hx => h _ ⟨x, hx, rfl⟩, ?_⟩
  rintro h _ ⟨x, hx, rfl⟩
  exact h x hx

theorem oinf_congr {ν₁ ν₂ : Measure (archGroup K n)} [ν₁.IsHaarMeasure] [ν₂.IsHaarMeasure] (h : ν₁ = ν₂) (β : TI K n) :
    Oinf μ ν₁ β = Oinf μ ν₂ β := by
  subst h; rfl

theorem rho_typed (J : ∀ w : Pl K, Subgroup (Gw n w)) (χ : ∀ w : Pl K, Gw n w → ℂ) (f : LL μ)
    (hf : ∀ w, f ∈ eigL μ w (J w) (χ w)) (P : Finset (Pl K))
    (hP : ∀ w ∉ P, J w = GLnLocal.integralGL (w.adicCompletion K) n ∧ χ w = 1) (R : Finset (Pl K)) :
    ∀ g : AdelicGLn.FiniteAdelicGL K n, (∀ w ∈ R, finAt w (finEmb K n g) ∈ J w) →
      (∀ w ∈ P, w ∉ R → finAt w (finEmb K n g) = 1) →
      (∀ w ∉ P, finAt w (finEmb K n g) ∈ GLnLocal.integralGL (w.adicCompletion K) n) →
      rhoF μ g f = (∏ w ∈ R, χ w (finAt w (finEmb K n g))) • f := by
  obtain ⟨-, -, -, -, -, hmul, hone, -⟩ := UpperTheory.ConvolutionTheory.Tf.commPrj K n μ ⊥
  have heig : ∀ w, ∀ x ∈ J w, rhoF μ (AdelicGLn.localEmbedding w x) f = χ w x • f := fun w x hx =>
    (mem_eigL μ).1 (hf w) x hx
  induction R using Finset.induction_on with
  | empty =>
    intro g _ h1 h2
    have hfix : f ∈ fixF μ (levOn P fun _ => ⊥) := by
      rw [UpperTheory.ConvolutionTheory.C.fixLev K n μ P]
      refine Submodule.mem_inf.2 ⟨?_, ?_⟩
      · refine Submodule.mem_iInf _ |>.2 fun v => Submodule.mem_iInf _ |>.2 fun hv => ?_
        refine ((UpperTheory.ConvolutionTheory.Tf.commPrj K n μ _).2.1 f).2 ?_
        rintro _ ⟨x, hx, rfl⟩
        obtain ⟨e1, e2⟩ := hP v hv
        have := heig v x (by rw [e1]; exact hx)
        rw [this, e2]
        simp
      · refine Submodule.mem_iInf _ |>.2 fun v => Submodule.mem_iInf _ |>.2 fun hv => ?_
        refine ((UpperTheory.ConvolutionTheory.Tf.commPrj K n μ _).2.1 f).2 ?_
        rintro _ ⟨x, hx, rfl⟩
        rw [Subgroup.mem_bot.1 hx, map_one, hone]
        rfl
    have hg : g ∈ levOn P (fun _ => ⊥) := fun v => by
      by_cases hv : v ∈ P
      · simp only [hv, ite_true]
        exact Subgroup.mem_bot.2 (h1 v hv (Finset.notMem_empty v))
      · simp only [hv, ite_false]
        exact h2 v hv
    simpa using ((UpperTheory.ConvolutionTheory.Tf.commPrj K n μ _).2.1 f).1 hfix g hg
  | insert a R ha ih =>
    intro g h0 h1 h2
    obtain ⟨-, e1, e2, -, -⟩ := UpperTheory.ConvolutionTheory.Tf.locEmb K n a
    set x := finAt a (finEmb K n g) with hx
    set g' := (AdelicGLn.localEmbedding a x)⁻¹ * g with hg'
    have hc : ∀ w, w ≠ a → finAt w (finEmb K n g') = finAt w (finEmb K n g) := fun w hw => by
      rw [hg', map_mul, finAt_mul, map_inv, finAt_inv, e2 w hw]
      simp
    have hca : finAt a (finEmb K n g') = 1 := by
      rw [hg', map_mul, finAt_mul, map_inv, finAt_inv, e1]
      simp [hx]
    have key := ih g' (fun w hw => by
        have hwa : w ≠ a := fun h => ha (h ▸ hw)
        rw [hc w hwa]
        exact h0 w (Finset.mem_insert_of_mem hw))
      (fun w hw hwR => by
        by_cases hwa : w = a
        · subst hwa; exact hca
        · rw [hc w hwa]
          exact h1 w hw (by simp [hwa, hwR]))
      (fun w hw => by
        by_cases hwa : w = a
        · subst hwa; rw [hca]; exact one_mem _
        · rw [hc w hwa]; exact h2 w hw)
    have hgg : g = AdelicGLn.localEmbedding a x * g' := by simp [hg']
    have hprod : ∏ w ∈ R, χ w (finAt w (finEmb K n g')) = ∏ w ∈ R, χ w (finAt w (finEmb K n g)) :=
      Finset.prod_congr rfl fun w hw => by rw [hc w fun h => ha (h ▸ hw)]
    have hstep : rhoF μ g f = rhoF μ (AdelicGLn.localEmbedding a x) (rhoF μ g' f) := by
      conv_lhs => rw [hgg, hmul]
      rfl
    rw [hstep, key, hprod, map_smul, heig a x (h0 a (Finset.mem_insert_self a R)), smul_smul,
      Finset.prod_insert ha, mul_comm]

end Loc

section Two
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
  (μ : Measure (normOneGL (K := E) (n := n))) [μ.IsHaarMeasure]

theorem operatorAt_int {s s' : archGroup F n →* archGroup E n} (hs : Continuous s) (hs' : Continuous s')
    (ν : Measure (archGroup F n)) [ν.IsHaarMeasure] (a : TI F n) (T : LL μ →L[ℂ] LL μ)
    (h : ∀ x u, T (rightRegularRep (rationalGLOne (K := E) (n := n)) μ (archP E n (s x)) u) =
      rightRegularRep (rationalGLOne (K := E) (n := n)) μ (archP E n (s' x)) (T u)) (v : LL μ) :
    T (OComponent μ s hs ν a v) = OComponent μ s' hs' ν a (T v) := by
  have key : T ∘L OComponent μ s hs ν a = OComponent μ s' hs' ν a ∘L T := by
    refine UnitaryRep.comp_integrated_of_mem_intertwiners _ _ ?_ _
    intro x u
    exact h x u
  exact DFunLike.congr_fun key v

theorem under_of_over {v : Pl F} (u : PlacesOver E v) : u.1.under (𝓞 F) = v := by
  ext1
  exact (Ideal.over_def u.1.asIdeal v.asIdeal).symm

theorem finite_over (v : Pl F) : {w : Pl E | w.under (𝓞 F) = v}.Finite := by
  refine (Set.finite_range fun u : PlacesOver E v => u.1).subset fun w hw => ?_
  subst hw
  exact ⟨⟨w, ⟨rfl⟩⟩, rfl⟩

end Two

theorem cmp_atFin {F E : Type} [Field F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
    {v : Pl F} (w : PlacesOver E v) (g : AdelicGLn.AdelicGL E n) :
    GM.cmp w (mapGL n (atFin v) g) = finAt w.1 g := by
  ext i j
  rfl

end UpperTheory.ConvolutionTheory.L1.TY
