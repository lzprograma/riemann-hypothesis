module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlkEquivInl
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExpoConjOfIsCsd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteModuleGradedQuantumDet
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open NumberField Matrix GlobalTheory.CuspRep Topology
open scoped ContDiff

namespace GlobalTheory.GLSlice

section Ring

variable {R S : Type} [CommRing R] [CommRing S] {a b : ℕ}


variable (R) in
def incl (f : Fin b ↪ Fin a) : Matrix (Fin a) (Fin b) R := Matrix.of fun i p => if f p = i then 1 else 0

theorem transpose_mul_incl (f : Fin b ↪ Fin a) : (incl R f)ᵀ * incl R f = 1 := by
  ext p q
  simp only [Matrix.mul_apply, incl, Matrix.transpose_apply, Matrix.of_apply, Matrix.one_apply]
  rw [Finset.sum_eq_single (f p)]
  · simp [eq_comm]
  · intro i _ hi
    rw [ite_eq_right (Ne.symm hi), zero_mul]
  · simp


variable (R) in
def extN (f : Fin b ↪ Fin a) : Matrix (Fin b) (Fin b) R →ₙ+* Matrix (Fin a) (Fin a) R where
  toFun X := incl R f * X * (incl R f)ᵀ
  map_mul' X Y := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (incl R f)ᵀ, transpose_mul_incl, Matrix.one_mul]
  map_zero' := by simp
  map_add' X Y := by simp [Matrix.mul_add, Matrix.add_mul]

theorem extN_apply (f : Fin b ↪ Fin a) (X : Matrix (Fin b) (Fin b) R) :
    extN R f X = incl R f * X * (incl R f)ᵀ := rfl

theorem extN_apply_apply (f : Fin b ↪ Fin a) (X : Matrix (Fin b) (Fin b) R) (p q : Fin b) :
    extN R f X (f p) (f q) = X p q := by
  simp [extN_apply, Matrix.mul_apply, incl]

theorem extN_apply_left (f : Fin b ↪ Fin a) (X : Matrix (Fin b) (Fin b) R) {i : Fin a} (hi : ∀ p, f p ≠ i)
    (j : Fin a) : extN R f X i j = 0 := by
  simp [extN_apply, Matrix.mul_apply, incl, hi]

theorem extN_apply_right (f : Fin b ↪ Fin a) (X : Matrix (Fin b) (Fin b) R) (i : Fin a) {j : Fin a}
    (hj : ∀ p, f p ≠ j) : extN R f X i j = 0 := by
  simp [extN_apply, Matrix.mul_apply, incl, hj]

theorem extN_single (f : Fin b ↪ Fin a) (p q : Fin b) (x : R) :
    extN R f (Matrix.single p q x) = Matrix.single (f p) (f q) x := by
  ext i j
  by_cases hi : ∃ p', f p' = i
  · obtain ⟨p', rfl⟩ := hi
    by_cases hj : ∃ q', f q' = j
    · obtain ⟨q', rfl⟩ := hj
      simp [extN_apply_apply, Matrix.single_apply]
    · push Not at hj
      rw [extN_apply_right f _ _ hj, Matrix.single_apply, ite_eq_right fun h => hj q h.2]
  · push Not at hi
    rw [extN_apply_left f _ hi, Matrix.single_apply, ite_eq_right fun h => hi p h.1]

theorem map_extN (f : Fin b ↪ Fin a) (φ : R →+* S) (X : Matrix (Fin b) (Fin b) R) :
    (extN R f X).map φ = extN S f (X.map φ) := by
  have h : (incl R f).map φ = incl S f := by
    ext i p; simp [incl, apply_ite φ]
  rw [extN_apply, extN_apply, Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map, h]

def embGL (f : Fin b ↪ Fin a) : GL (Fin b) R →* GL (Fin a) R := Units.map (corner (extN R f))

theorem embGL_val (f : Fin b ↪ Fin a) (y : GL (Fin b) R) :
    (embGL f y : Matrix (Fin a) (Fin a) R) = 1 - extN R f 1 + extN R f y := rfl

theorem map_embGL (f : Fin b ↪ Fin a) (φ : R →+* S) (y : GL (Fin b) R) :
    GeneralLinearGroup.map φ (embGL f y) = embGL f (GeneralLinearGroup.map φ y) := by
  apply Units.ext
  change φ.mapMatrix (1 - extN R f 1 + extN R f y) = 1 - extN S f 1 + extN S f ((y : Matrix _ _ R).map φ)
  rw [map_add (f := _), map_sub, map_one, RingHom.mapMatrix_apply, RingHom.mapMatrix_apply, map_extN, map_extN,
    Matrix.map_one _ (map_zero φ) (map_one φ)]

theorem continuous_embGL [TopologicalSpace R] [IsTopologicalRing R] (f : Fin b ↪ Fin a) :
    Continuous (embGL f : GL (Fin b) R → GL (Fin a) R) :=
  Continuous.units_map _ (continuous_const.add ((continuous_const.matrix_mul continuous_id).matrix_mul continuous_const :
    Continuous fun X : Matrix (Fin b) (Fin b) R => incl R f * X * (incl R f)ᵀ))

open GlobalTheory.LeviGA

end Ring

section Rel

variable {M N : Type} [AddCommGroup M] [Module ℂ M] [AddCommGroup N] [Module ℂ N]

theorem rel_aeval_qdet (Γ : Submodule ℂ (M × N)) {n : ℕ} (A : Fin n → Fin n → Module.End ℂ M)
    (B : Fin n → Fin n → Module.End ℂ N) (h : ∀ i j, ∀ x ∈ Γ, (A i j x.1, B i j x.2) ∈ Γ) (u : ℂ)
    (P : Polynomial ℂ) : ∀ x ∈ Γ, (Polynomial.aeval (Formalism.REAL.qdet A u) P x.1,
      Polynomial.aeval (Formalism.REAL.qdet B u) P x.2) ∈ Γ := by
  let T : Subalgebra ℂ (Module.End ℂ M × Module.End ℂ N) :=
    { carrier := {z | ∀ x ∈ Γ, (z.1 x.1, z.2 x.2) ∈ Γ}
      mul_mem' := fun hz hw x hx => hz _ (hw x hx)
      add_mem' := fun hz hw x hx => Γ.add_mem (hz x hx) (hw x hx)
      algebraMap_mem' := fun c x hx => Γ.smul_mem c hx }
  have h1 : Formalism.REAL.qdet (fun i j => (A i j, B i j)) u ∈ T := GlobalTheory.LeviHC.MidBlock.qdet_mem T h u
  have h2 : Polynomial.aeval (Formalism.REAL.qdet (fun i j => (A i j, B i j)) u) P ∈ T :=
    Algebra.adjoin_le (Set.singleton_subset_iff.2 h1) (Polynomial.aeval_mem_adjoin_singleton ℂ _)
  have e1 := Polynomial.aeval_algHom_apply (AlgHom.fst ℂ (Module.End ℂ M) (Module.End ℂ N))
    (Formalism.REAL.qdet (fun i j => (A i j, B i j)) u) P
  have e2 := Polynomial.aeval_algHom_apply (AlgHom.snd ℂ (Module.End ℂ M) (Module.End ℂ N))
    (Formalism.REAL.qdet (fun i j => (A i j, B i j)) u) P
  rw [map_qdet] at e1 e2
  intro x hx
  have h3 := h2 x hx
  change ((AlgHom.fst ℂ _ _ _ : Module.End ℂ M) x.1, (AlgHom.snd ℂ _ _ _ : Module.End ℂ N) x.2) ∈ Γ at h3
  rw [← e1, ← e2] at h3
  exact h3

end Rel

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a b : ℕ} (f : Fin b ↪ Fin a)

theorem embGL_infGL (y : GL (Fin b) (Cinf E)) : embGL f (infGL E b y) = infGL E a (embGL f y) :=
  ga_ext (by simp [map_embGL]) (by simp [map_embGL])

theorem embGL_finGL (k : GL (Fin b) (Af E)) : embGL f (finGL E b k) = finGL E a (embGL f k) :=
  ga_ext (by simp [map_embGL]) (by simp [map_embGL])



omit [_root_.NumberField.IsTotallyComplex E] in
variable (E) in
def extL : Lie E b →L[ℝ] Lie E a :=
  LinearMap.toContinuousLinearMap
    { toFun := fun X => toL (extN (Cinf E) f (Matrix.of X))
      map_add' := fun X Y => map_add (extN (Cinf E) f) (Matrix.of X) (Matrix.of Y)
      map_smul' := fun c X => by
        change extN (Cinf E) f (c • Matrix.of X) = c • extN (Cinf E) f (Matrix.of X)
        rw [extN_apply, extN_apply, Matrix.mul_smul, Matrix.smul_mul] }

omit [_root_.NumberField.IsTotallyComplex E] in
theorem toL_embGL (y : GL (Fin b) (Cinf E)) :
    toL (embGL f y).val = toL (1 - extN (Cinf E) f 1) + extL E f (toL y.val) := rfl

theorem chart_slice (ψ : GA E a → ℂ) (g : GA E a) (m : GA E b) {x : Lie E b} (hx : x ∈ invSet E b) :
    toL (1 - extN (Cinf E) f 1) + extL E f x ∈ invSet E a ∧
      chart (fun m => ψ (g * embGL f m)) m x = chart ψ (g * embGL f m) (toL (1 - extN (Cinf E) f 1) + extL E f x) := by
  obtain ⟨u, hu⟩ := id hx
  have e : x = toL u.val := hu.symm
  subst e
  rw [← toL_embGL, chart_val, chart_val, map_mul, embGL_infGL, mul_assoc]
  exact ⟨val_mem_invSet _, rfl⟩

def slice (g : GA E a) : Sm E a →ₗ[ℂ] Sm E b where
  toFun ψ := ⟨fun m => ψ.1 (g * embGL f m), fun m =>
    ((ψ.2 (g * embGL f m)).comp (contDiff_const.add (extL E f).contDiff).contDiffOn
      fun _ hx => (chart_slice f ψ.1 g m hx).1).congr fun _ hx => (chart_slice f ψ.1 g m hx).2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem slice_apply (g : GA E a) (ψ : Sm E a) (m : GA E b) : (slice f g ψ).1 m = ψ.1 (g * embGL f m) := rfl

theorem lie_slice (g : GA E a) (ψ : Sm E a) (X : Lie E b) :
    lie E b X (slice f g ψ) = slice f g (lie E a (extL E f X) ψ) := by
  refine Subtype.ext (funext fun m => ?_)
  have e : chart (slice f g ψ).1 m =ᶠ[𝓝 (oneL E b)]
      chart ψ.1 (g * embGL f m) ∘ fun x => toL (1 - extN (Cinf E) f 1) + extL E f x :=
    Filter.eventually_of_mem (isOpen_invSet.mem_nhds isUnit_one) fun x hx => (chart_slice f ψ.1 g m hx).2
  have e1 : toL (1 - extN (Cinf E) f 1) + extL E f (oneL E b) = oneL E a := sub_add_cancel _ _
  have h1 : HasFDerivAt (chart ψ.1 (g * embGL f m)) (fderiv ℝ (chart ψ.1 (g * embGL f m)) (oneL E a))
      (toL (1 - extN (Cinf E) f 1) + extL E f (oneL E b)) := by
    rw [e1]; exact (differentiableAt_chart ψ.2 _).hasFDerivAt
  have h2 := h1.comp (oneL E b) ((extL E f).hasFDerivAt.const_add (toL (1 - extN (Cinf E) f 1)))
  change fderiv ℝ (chart (slice f g ψ).1 m) (oneL E b) X = _
  rw [e.fderiv_eq, h2.fderiv]
  rfl

theorem Eop_slice (g : GA E a) (ψ : Sm E a) (τ : E →+* ℂ) (p q : Fin b) :
    Eop τ p q (slice f g ψ) = slice f g (Eop τ (f p) (f q) ψ) := by
  have e : ∀ x : Cinf E, extL E f (toL (Matrix.single p q x)) = toL (Matrix.single (f p) (f q) x) := fun x =>
    congrArg toL (extN_single f p q x)
  have h1 := lie_slice f g ψ (toL (Matrix.single p q (atEmb τ 1)))
  have h2 := lie_slice f g ψ (toL (Matrix.single p q (atEmb τ Complex.I)))
  rw [e] at h1 h2
  refine Subtype.ext (funext fun m => ?_)
  exact congrArg₂ (fun s t : ℂ => (1 / 2 : ℂ) * (s - Complex.I * t)) (congrFun (congrArg Subtype.val h1) m)
    (congrFun (congrArg Subtype.val h2) m)

theorem aeval_qdet_slice (g : GA E a) (ψ : Sm E a) (τ : E →+* ℂ) (u : ℂ) (P : Polynomial ℂ) :
    Polynomial.aeval (Formalism.REAL.qdet (Eop (a := b) τ) u) P (slice f g ψ) =
      slice f g (Polynomial.aeval (Formalism.REAL.qdet (fun p q : Fin b => Eop (a := a) τ (f p) (f q)) u) P ψ) :=
  rel_aeval_qdet (LinearMap.graph (slice f g)) (fun p q => Eop τ (f p) (f q)) (Eop τ)
    (fun p q x hx => by
      have hx' : x.2 = slice f g x.1 := hx
      change Eop τ p q x.2 = _
      rw [hx', Eop_slice]) u P (ψ, slice f g ψ) rfl

end GlobalTheory.GLSlice

end
