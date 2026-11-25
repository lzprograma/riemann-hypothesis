module

public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMulEqMulDiagonal
public import Mathlib.RingTheory.Localization.Module
public import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IrreducibleOfValued
import Mathlib.Tactic.Linter.HaveILetI
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ElementaryDivisorsInvHeckeElementSplitPlace

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LatticeElementaryDivisors, Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCoordLattice

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LatticeElementaryDivisors =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LatticeElementaryDivisors", "h": "module\n\npublic import Mathlib.LinearAlgebra.Matrix.Determinant.Basic\npublic import Mathlib.RingTheory.DiscreteValuationRing.Basic\npublic import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMulEqMulDiagonal\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Henselian\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.RingTheory.RegularLocalRing.Defs\nimport Mathlib.RingTheory.SimpleRing.Principal\nimport Mathlib.RingTheory.WittVector.IsPoly\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.ENatToNat\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.HaveILetI\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.Polynomial.Basic\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Topology.Sheaves.Init\npublic import Mathlib.RingTheory.Localization.Module\n\n"}
section -- clump:auto
@[expose] public section

open IsDedekindDomain NumberField

namespace GlobalTheory.LatticeMinuscule

open Matrix

variable {R K : Type} [CommRing R] [Field K] [Algebra R K] {n : ℕ}

open IsDedekindDomain NumberField in
open Matrix in
variable {R K : Type} [CommRing R] [Field K] [Algebra R K] {n : ℕ} in
theorem _root_.GlobalTheory.LatticeMinuscule.lattice_elementary_divisors (R K : Type) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K] (ϖ : R)
    (hϖ : Irreducible ϖ) (n k : ℕ) (hk : k ≤ n) (Λ : Submodule R (Fin n → K)) (hfg : Λ.FG)
    (hsp : Submodule.span K (Λ : Set (Fin n → K)) = ⊤) (a a' : Matrix (Fin n) (Fin n) K)
    (haa : a * a' = 1) (h1 : ∀ y ∈ Λ, a.mulVec y ∈ Λ)
    (h2 : ∀ y ∈ Λ, ∃ z ∈ Λ, algebraMap R K ϖ • y = a.mulVec z) (u : Rˣ)
    (hdet : a.det = algebraMap R K ϖ ^ k * algebraMap R K (u : R)) :
    ∃ B : Matrix (Fin n) (Fin n) K,
      (∀ y, y ∈ Λ ↔ ∃ z : Fin n → R, y = B.mulVec (fun i => algebraMap R K (z i))) ∧
      (∀ y, (∃ x ∈ Λ, y = a'.mulVec x) ↔ ∃ z : Fin n → R, y = B.mulVec (fun i =>
        algebraMap R K ϖ ^ (if i.1 < n - k then (0 : ℤ) else -1) * algebraMap R K (z i))) := by
  classical
  have hinj : Function.Injective (algebraMap R K) := IsFractionRing.injective R K
  have hϖ0 : algebraMap R K ϖ ≠ 0 := (map_ne_zero_iff _ hinj).mpr hϖ.ne_zero
  haveI : Module.Finite R Λ := Module.Finite.iff_fg.mpr hfg
  haveI : Module.Free R Λ := Module.free_of_finite_type_torsion_free'
  let b := Module.Free.chooseBasis R Λ
  have hli : LinearIndependent K (fun i => (b i : Fin n → K)) :=
    (LinearIndependent.iff_fractionRing R K).mp
      (b.linearIndependent.map' Λ.subtype (Submodule.ker_subtype Λ))
  have hcard : Fintype.card (Module.Free.ChooseBasisIndex R Λ) = n := by
    have hspan : ⊤ ≤ Submodule.span K (Set.range fun i => (b i : Fin n → K)) := by
      rw [← hsp, Submodule.span_le]
      intro x hx
      rw [← show ((⟨x, hx⟩ : Λ) : Fin n → K) = x from rfl, ← b.sum_repr ⟨x, hx⟩,
        Submodule.coe_sum]
      refine Submodule.sum_mem _ fun i _ => ?_
      rw [Submodule.coe_smul, ← algebraMap_smul K]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    have h := Module.finrank_eq_card_basis (Module.Basis.mk hli hspan)
    rw [Module.finrank_fin_fun] at h
    exact h.symm
  let b' := b.reindex (Fintype.equivFinOfCardEq hcard)
  let B0 : Matrix (Fin n) (Fin n) K := Matrix.of fun i j => (b' j : Fin n → K) i
  have key : ∀ z : Fin n → R, B0 *ᵥ (fun i => algebraMap R K (z i)) =
      ((b'.equivFun.symm z : Λ) : Fin n → K) := by
    intro z; ext i
    simp [B0, Matrix.mulVec, dotProduct, Module.Basis.equivFun_symm_apply, Finset.sum_apply, Algebra.smul_def, mul_comm]
  have memL : ∀ y, y ∈ Λ ↔ ∃ z : Fin n → R, y = B0 *ᵥ (fun i => algebraMap R K (z i)) := by
    intro y; constructor
    · intro hy; refine ⟨b'.equivFun ⟨y, hy⟩, ?_⟩; rw [key, LinearEquiv.symm_apply_apply]
    · rintro ⟨z, rfl⟩; rw [key]; exact Subtype.prop _
  have keyinj : ∀ z w : Fin n → R, B0 *ᵥ (fun i => algebraMap R K (z i)) =
      B0 *ᵥ (fun i => algebraMap R K (w i)) → z = w := by
    intro z w h; rw [key, key] at h; exact b'.equivFun.symm.injective (Subtype.coe_injective h)
  have hmap : ∀ (N : Matrix (Fin n) (Fin n) R) (z : Fin n → R),
      N.map (algebraMap R K) *ᵥ (fun i => algebraMap R K (z i)) =
        fun i => algebraMap R K ((N *ᵥ z) i) := by
    intro N z; funext i; exact (RingHom.map_mulVec (algebraMap R K) N z i).symm
  have h1' : ∀ j, ∃ z : Fin n → R,
      a *ᵥ (b' j : Fin n → K) = B0 *ᵥ (fun i => algebraMap R K (z i)) :=
    fun j => (memL _).1 (h1 _ (b' j).2)
  choose zM hzM using h1'
  let M : Matrix (Fin n) (Fin n) R := Matrix.of fun i j => zM j i
  have haB : a * B0 = B0 * M.map (algebraMap R K) := by
    ext i j
    have := congrFun (hzM j) i
    simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct, B0, M] using this
  have h2' : ∀ j, ∃ z : Fin n → R, algebraMap R K ϖ • (b' j : Fin n → K) =
      a *ᵥ (B0 *ᵥ (fun i => algebraMap R K (z i))) := by
    intro j
    obtain ⟨x, hx, hxe⟩ := h2 _ (b' j).2
    obtain ⟨z, rfl⟩ := (memL x).1 hx
    exact ⟨z, hxe⟩
  choose zM' hzM' using h2'
  let M' : Matrix (Fin n) (Fin n) R := Matrix.of fun i j => zM' j i
  have hMM : M * M' = ϖ • (1 : Matrix (Fin n) (Fin n) R) := by
    ext i j
    have h := hzM' j
    rw [Matrix.mulVec_mulVec, haB, ← Matrix.mulVec_mulVec, hmap] at h
    have hl : algebraMap R K ϖ • (b' j : Fin n → K) =
        B0 *ᵥ (fun i => algebraMap R K ((ϖ • Pi.single j (1 : R) : Fin n → R) i)) := by
      rw [key, map_smul, Module.Basis.equivFun_symm_apply]
      simp [Pi.single_apply, algebraMap_smul]
    have h3 := congrFun (keyinj _ _ (hl.symm.trans h)) i
    rw [show (M * M') i j = (M *ᵥ zM' j) i from rfl, ← h3]
    simp [Matrix.one_apply, Pi.single_apply]
  have hsurj : Function.Surjective B0.mulVec := by
    intro y
    have hy : y ∈ Submodule.span K (Λ : Set (Fin n → K)) := hsp ▸ Submodule.mem_top
    have hle : Submodule.span K (Λ : Set (Fin n → K)) ≤ LinearMap.range (Matrix.mulVecLin B0) := by
      rw [Submodule.span_le]
      intro x hx
      obtain ⟨z, rfl⟩ := (memL x).1 hx
      exact ⟨_, rfl⟩
    obtain ⟨w, hw⟩ := hle hy
    exact ⟨w, hw⟩
  have hB0 : B0.det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det B0).mp (Matrix.mulVec_surjective_iff_isUnit.mp hsurj)).ne_zero
  have hdetM : Associated M.det (ϖ ^ k) := by
    have h := congrArg Matrix.det haB
    have hdm : (M.map (algebraMap R K)).det = algebraMap R K M.det := (RingHom.map_det _ _).symm
    rw [Matrix.det_mul, Matrix.det_mul, mul_comm, hdet, hdm, ← map_pow, ← map_mul] at h
    have h' := hinj (mul_left_cancel₀ hB0 h)
    exact ⟨u⁻¹, by rw [← h', mul_assoc, Units.mul_inv, mul_one]⟩
  obtain ⟨P, Q, hP, hQ, hMQ⟩ :=
    _root_.GlobalTheory.SmithBetween.smith_between R ϖ hϖ n k hk M M' hMM hdetM
  have haa' : a' * a = 1 := mul_eq_one_comm.mp haa
  have hE : ∀ z : Fin n → R, a *ᵥ ((B0 * Q.map (algebraMap R K)) *ᵥ (fun i =>
      algebraMap R K ϖ ^ (if i.1 < n - k then (0 : ℤ) else -1) * algebraMap R K (z i))) =
        B0 *ᵥ (fun i => algebraMap R K ((P *ᵥ z) i)) := by
    intro z
    have hdw : ((Matrix.diagonal fun i : Fin n => if i.1 < n - k then (1 : R) else ϖ).map
        (algebraMap R K)) *ᵥ (fun i =>
          algebraMap R K ϖ ^ (if i.1 < n - k then (0 : ℤ) else -1) * algebraMap R K (z i)) =
        fun i => algebraMap R K (z i) := by
      rw [Matrix.diagonal_map (map_zero _)]
      funext i
      rw [Matrix.mulVec_diagonal]
      by_cases hi : i.1 < n - k <;> simp [hi, hϖ0]
    rw [Matrix.mulVec_mulVec, ← Matrix.mul_assoc, haB, Matrix.mul_assoc, ← Matrix.map_mul, hMQ,
      Matrix.map_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hdw, hmap]
  refine ⟨B0 * Q.map (algebraMap R K), fun y => ?_, fun y => ?_⟩
  · rw [memL]
    constructor
    · rintro ⟨z, rfl⟩
      refine ⟨Q⁻¹ *ᵥ z, ?_⟩
      rw [← Matrix.mulVec_mulVec, hmap, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv Q hQ,
        Matrix.one_mulVec]
    · rintro ⟨z, rfl⟩
      exact ⟨Q *ᵥ z, by rw [← Matrix.mulVec_mulVec, hmap]⟩
  · constructor
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨z, rfl⟩ := (memL x).1 hx
      refine ⟨P⁻¹ *ᵥ z, ?_⟩
      have h := hE (P⁻¹ *ᵥ z)
      have hz : P *ᵥ (P⁻¹ *ᵥ z) = z := by
        rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv P hP, Matrix.one_mulVec]
      rw [hz] at h
      rw [← h, Matrix.mulVec_mulVec, haa', Matrix.one_mulVec]
    · rintro ⟨z, rfl⟩
      refine ⟨_, (memL _).2 ⟨P *ᵥ z, rfl⟩, ?_⟩
      rw [← hE z, Matrix.mulVec_mulVec, haa', Matrix.one_mulVec]

end GlobalTheory.LatticeMinuscule
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LatticeElementaryDivisors =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCoordLattice =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCoordLattice", "h": "module\n\npublic import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull\npublic import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IrreducibleOfValued\npublic import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LatticeElementaryDivisors\nimport Mathlib.Algebra.Module.StablyFree.Basic\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.LinearAlgebra.Matrix.FiniteDimensional\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Coalgebra.IsFrobenius\nimport Mathlib.RingTheory.HopfAlgebra.Basic\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.ENatToNat\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.Polynomial.Basic\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Topology.Sheaves.Init\nimport Development.AbelianVarietyTheory.Proofs.SatakeParameters.ElementaryDivisorsInvHeckeElementSplitPlace\nimport Mathlib.RingTheory.PicardGroup\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField Matrix Formalism.L2.Theta
  Formalism.IndefR.Mult
open scoped TensorProduct NumberField.AdeleRing

namespace GlobalTheory.SplitHeckeLabel

section Generic

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem evalV_singleV_same (v : HeightOneSpectrum (𝓞 F)) (y : Fv F v) : evalV F v (singleV F v y) = y := by
  classical
  exact RestrictedProduct.single_eq_same (fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletionIntegers F) v y

theorem evalV_singleV_ne (v : HeightOneSpectrum (𝓞 F)) (y : Fv F v) {w : HeightOneSpectrum (𝓞 F)} (hw : w ≠ v) :
    evalV F w (singleV F v y) = 0 := by
  classical
  exact RestrictedProduct.single_eq_of_ne (fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletionIntegers F) y hw

theorem af_ext {a b : 𝔸ᶠ[F]} (h : ∀ w, evalV F w a = evalV F w b) : a = b :=
  RestrictedProduct.ext _ _ h

theorem singleV_mem_intAf (v : HeightOneSpectrum (𝓞 F)) (y : v.adicCompletionIntegers F) :
    singleV F v (y : Fv F v) ∈ intAf F := fun w => by
  by_cases hw : w = v
  · subst hw; rw [evalV_singleV_same]; exact y.2
  · rw [evalV_singleV_ne v _ hw]; exact zero_mem _


variable (F E) in
def intA : AddSubgroup (𝔸ᶠ[F] ⊗[F] E) :=
  AddSubgroup.closure {y | ∃ a ∈ intAf F, ∃ x : 𝓞 E, y = a ⊗ₜ[F] (x : E)}

theorem mul_mem_intAf {a b : 𝔸ᶠ[F]} (ha : a ∈ intAf F) (hb : b ∈ intAf F) : a * b ∈ intAf F := fun w => by
  rw [map_mul]; exact mul_mem (ha w) (hb w)

theorem one_mem_intAf : (1 : 𝔸ᶠ[F]) ∈ intAf F := fun w => by rw [map_one]; exact one_mem _

theorem tmul_mem_intA {a : 𝔸ᶠ[F]} (ha : a ∈ intAf F) (x : 𝓞 E) : a ⊗ₜ[F] (x : E) ∈ intA F E :=
  AddSubgroup.subset_closure ⟨a, ha, x, rfl⟩

theorem mul_mem_intA {x y : 𝔸ᶠ[F] ⊗[F] E} (hx : x ∈ intA F E) (hy : y ∈ intA F E) : x * y ∈ intA F E := by
  refine AddSubgroup.closure_induction₂ (p := fun x y _ _ => x * y ∈ intA F E) ?_ ?_ ?_ ?_ ?_ ?_ ?_ hx hy
  · rintro _ _ ⟨a, ha, u, rfl⟩ ⟨b, hb, v, rfl⟩
    rw [Algebra.TensorProduct.tmul_mul_tmul]
    exact tmul_mem_intA (mul_mem_intAf ha hb) (u * v)
  · intro x _; rw [zero_mul]; exact zero_mem _
  · intro x _; rw [mul_zero]; exact zero_mem _
  · intro x y z _ _ _ h1 h2; rw [add_mul]; exact add_mem h1 h2
  · intro x y z _ _ _ h1 h2; rw [mul_add]; exact add_mem h1 h2
  · intro x y _ _ h; rw [neg_mul]; exact neg_mem h
  · intro x y _ _ h; rw [mul_neg]; exact neg_mem h

theorem smul_mem_latHat {n : ℕ} (L : Submodule (𝓞 E) (Fin n → E)) {x : 𝔸ᶠ[F] ⊗[F] E} {y : Fin n → 𝔸ᶠ[F] ⊗[F] E}
    (hx : x ∈ intA F E) (hy : y ∈ latHat F E (L : Set (Fin n → E))) :
    x • y ∈ latHat F E (L : Set (Fin n → E)) := by
  induction hx using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨a, ha, u, rfl⟩ := hx
    induction hy using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨b, hb, w, hw, rfl⟩ := hy
      refine AddSubgroup.subset_closure ⟨a * b, mul_mem_intAf ha hb, u • w, L.smul_mem u hw, ?_⟩
      funext i
      rw [Pi.smul_apply, smul_eq_mul, Algebra.TensorProduct.tmul_mul_tmul]
      rfl
    | zero => rw [smul_zero]; exact zero_mem _
    | add y z _ _ h1 h2 => rw [smul_add]; exact add_mem h1 h2
    | neg y _ h => rw [smul_neg]; exact neg_mem h
  | zero => rw [zero_smul]; exact zero_mem _
  | add y z _ _ h1 h2 => rw [add_smul]; exact add_mem h1 h2
  | neg y _ h => rw [neg_smul]; exact neg_mem h

theorem trace_tmul (R : Type) [CommRing R] [Algebra F R] (a : R) (e : E) :
    Algebra.trace R (R ⊗[F] E) (a ⊗ₜ[F] e) = a * algebraMap F R (Algebra.trace F E e) := by
  have h1 : a ⊗ₜ[F] e = a • ((1 : R) ⊗ₜ[F] e) := by
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  rw [h1, map_smul, Algebra.trace_apply, Algebra.trace_apply, ← Algebra.baseChange_lmul,
    LinearMap.trace_baseChange, smul_eq_mul]

theorem trace_mem_intAf {z : 𝔸ᶠ[F] ⊗[F] E} (hz : z ∈ intA F E) (v : HeightOneSpectrum (𝓞 F)) :
    evalV F v (Algebra.trace 𝔸ᶠ[F] (𝔸ᶠ[F] ⊗[F] E) z) ∈ v.adicCompletionIntegers F := by
  induction hz using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨a, ha, u, rfl⟩ := hx
    rw [trace_tmul, map_mul, AlgHom.commutes]
    refine mul_mem (ha v) ?_
    have hi : IsIntegral ℤ (Algebra.trace F E (u : E)) := Algebra.isIntegral_trace u.isIntegral_coe
    exact HeightOneSpectrum.coe_mem_adicCompletionIntegers v (⟨_, hi⟩ : 𝓞 F)
  | zero => rw [map_zero, map_zero]; exact zero_mem _
  | add y z _ _ h1 h2 => rw [map_add (f := _), map_add (f := _)]; exact add_mem h1 h2
  | neg y _ h => rw [map_neg, map_neg]; exact neg_mem h

theorem exists_local_lattice {n : ℕ} (L : Submodule (𝓞 E) (Fin n → E)) (hfg : L.FG)
    (hsp : Submodule.span E (L : Set (Fin n → E)) = ⊤) (v : HeightOneSpectrum (𝓞 F))
    (φ : 𝔸ᶠ[F] ⊗[F] E →+* Fv F v) (hφa : ∀ a : 𝔸ᶠ[F], φ (algebraMap 𝔸ᶠ[F] _ a) = evalV F v a)
    (hφi : ∀ x ∈ intA F E, φ x ∈ v.adicCompletionIntegers F) :
    ∃ Λ : Submodule (v.adicCompletionIntegers F) (Fin n → Fv F v), Λ.FG ∧
      Submodule.span (Fv F v) (Λ : Set (Fin n → Fv F v)) = ⊤ ∧
      ∀ w, w ∈ Λ ↔ ∃ y ∈ latHat F E (L : Set (Fin n → E)), w = φ ∘ y := by
  classical
  set ψ : E →+* Fv F v := φ.comp (inclR 𝔸ᶠ[F]) with hψ
  have hψi : ∀ x : 𝓞 E, ψ (x : E) ∈ v.adicCompletionIntegers F := fun x => hφi _ (tmul_mem_intA one_mem_intAf x)
  have htm : ∀ (a : 𝔸ᶠ[F]) (x : E), φ (a ⊗ₜ[F] x) = evalV F v a * ψ x := fun a x => by
    rw [← hφa]
    change _ = φ (a ⊗ₜ[F] 1) * φ (1 ⊗ₜ[F] x)
    rw [← map_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  obtain ⟨T, hT⟩ := hfg
  set Λ := Submodule.span (v.adicCompletionIntegers F) ((fun x : Fin n → E => ψ ∘ x) '' (T : Set (Fin n → E)))
    with hΛ
  have hL : ∀ x ∈ L, ψ ∘ x ∈ Λ := by
    intro x hx
    rw [← hT] at hx
    induction hx using Submodule.span_induction with
    | mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩
    | zero =>
      have : ψ ∘ (0 : Fin n → E) = 0 := funext fun i => map_zero ψ
      rw [this]; exact zero_mem _
    | add x y _ _ h1 h2 =>
      have : ψ ∘ (x + y) = ψ ∘ x + ψ ∘ y := funext fun i => map_add ψ _ _
      rw [this]; exact add_mem h1 h2
    | smul r x _ h =>
      have : ψ ∘ (r • x) = (⟨ψ r, hψi r⟩ : v.adicCompletionIntegers F) • (ψ ∘ x) := funext fun i => map_mul ψ _ _
      rw [this]; exact Λ.smul_mem _ h
  refine ⟨Λ, Submodule.fg_span (T.finite_toSet.image _), ?_, fun w => ⟨fun hw => ?_, ?_⟩⟩
  · have key : ∀ x : Fin n → E, ψ ∘ x ∈ Submodule.span (Fv F v) (Λ : Set (Fin n → Fv F v)) := by
      intro x
      have hx : x ∈ Submodule.span E (L : Set (Fin n → E)) := hsp ▸ Submodule.mem_top
      induction hx using Submodule.span_induction with
      | mem x hx => exact Submodule.subset_span (hL x hx)
      | zero =>
        have : ψ ∘ (0 : Fin n → E) = 0 := funext fun i => map_zero ψ
        rw [this]; exact zero_mem _
      | add x y _ _ h1 h2 =>
        have : ψ ∘ (x + y) = ψ ∘ x + ψ ∘ y := funext fun i => map_add ψ _ _
        rw [this]; exact add_mem h1 h2
      | smul r x _ h =>
        have : ψ ∘ (r • x) = ψ r • (ψ ∘ x) := funext fun i => map_mul ψ _ _
        rw [this]; exact Submodule.smul_mem _ _ h
    rw [eq_top_iff, ← (Pi.basisFun (Fv F v) (Fin n)).span_eq, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    have : Pi.basisFun (Fv F v) (Fin n) i = ψ ∘ (Pi.single i 1 : Fin n → E) := by
      funext j
      by_cases hj : j = i
      · subst hj; simp
      · simp [hj]
    rw [this]
    exact key _
  · induction hw using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨x, hx, rfl⟩ := hw
      exact ⟨fun i => (1 : 𝔸ᶠ[F]) ⊗ₜ[F] x i,
        AddSubgroup.subset_closure ⟨1, one_mem_intAf, x, hT ▸ Submodule.subset_span hx, rfl⟩, rfl⟩
    | zero => exact ⟨0, zero_mem _, funext fun i => (map_zero φ).symm⟩
    | add x y _ _ h1 h2 =>
      obtain ⟨x', hx', rfl⟩ := h1
      obtain ⟨y', hy', rfl⟩ := h2
      exact ⟨x' + y', add_mem hx' hy', funext fun i => (map_add φ _ _).symm⟩
    | smul r x _ h =>
      obtain ⟨x', hx', rfl⟩ := h
      refine ⟨(singleV F v (r : Fv F v) ⊗ₜ[F] ((1 : 𝓞 E) : E)) • x',
        smul_mem_latHat L (tmul_mem_intA (singleV_mem_intAf v r) 1) hx', funext fun i => ?_⟩
      change (r : Fv F v) * φ (x' i) = φ ((singleV F v (r : Fv F v) ⊗ₜ[F] (1 : E)) * x' i)
      rw [map_mul, htm, map_one, mul_one, evalV_singleV_same]
  · rintro ⟨y, hy, rfl⟩
    induction hy using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨a, ha, x, hx, rfl⟩ := hy
      have : (φ ∘ fun i => a ⊗ₜ[F] x i) = (⟨evalV F v a, ha v⟩ : v.adicCompletionIntegers F) • (ψ ∘ x) :=
        funext fun i => htm a (x i)
      rw [this]; exact Λ.smul_mem _ (hL x hx)
    | zero =>
      have : φ ∘ (0 : Fin n → 𝔸ᶠ[F] ⊗[F] E) = 0 := funext fun i => map_zero φ
      rw [this]; exact zero_mem _
    | add x y _ _ h1 h2 =>
      have : φ ∘ (x + y) = φ ∘ x + φ ∘ y := funext fun i => map_add φ _ _
      rw [this]; exact add_mem h1 h2
    | neg x _ h =>
      have : φ ∘ (-x) = -(φ ∘ x) := funext fun i => map_neg φ _
      rw [this]; exact neg_mem h

end Generic

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem splitLab_getD {n k i : ℕ} (hk : k ≤ n) (hi : i < n) :
    (splitLab n k).getD i 0 = if i < n - k then 0 else -1 := by
  unfold splitLab
  split_ifs with h
  · rw [List.getD_append _ _ _ _ (by simpa using h)]
    simp [h]
  · rw [List.getD_append_right _ _ _ _ (by simpa using h)]
    have : i - (n - k) < k := by omega
    simp [this]

theorem finPart_cA (D : D7) (x : Formalism.L2.Theta.AE D) :
    finPart D (cA D x) = sigR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig (finPart D x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add a b ha hb => simp only [RingHom.map_add (f := _), ha, hb]
  | tmul a e => rfl

theorem finPart_det {D : D7} (V : HSp D) (α : GA D V) (e u : Formalism.L2.Theta.AE D) (p : D.host.E) (k : ℕ)
    (h : e * (mt V α).det = e * incA D p ^ k * u) :
    finPart D e * (finMat D.sp.cm.sig V.gram α).det =
      finPart D e * inclR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) p ^ k * finPart D u := by
  have hinc : finPart D (incA D p) = inclR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) p := rfl
  have hd : finPart D (mt V α).det = (finMat D.sp.cm.sig V.gram α).det := RingHom.map_det (finPart D) (mt V α)
  rw [← hd, ← hinc, ← RingHom.map_pow, ← RingHom.map_mul, ← RingHom.map_mul, ← RingHom.map_mul, h]

theorem divAt_inv {D : D7} (V : HSp D) (e : Formalism.L2.Theta.AE D) (P : HeightOneSpectrum (𝓞 D.host.E))
    (he : Formalism.L2.NTheta.IsIdemAt e P) (ϖ : 𝓞 D.host.E) (hϖ : ϖ ∈ P.asIdeal) (hϖ2 : ϖ ∉ P.asIdeal ^ 2) (k : ℕ)
    (hk : k ≤ V.rank) (α : GA D V) (hα : Formalism.L2.NTheta.IsHeckeElt V e (ϖ : D.host.E) k α) :
    DivAt V e (ϖ : D.host.E) (splitLab V.rank k) α⁻¹ :=
  GlobalTheory.SplitDivisors.divAt_inv_of_isHeckeElt V P e ϖ k α he hϖ hϖ2 hk hα

end GlobalTheory.SplitHeckeLabel
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCoordLattice =====
