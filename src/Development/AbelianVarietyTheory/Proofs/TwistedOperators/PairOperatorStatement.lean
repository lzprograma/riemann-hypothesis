module

public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.AdjointOperatorIdentities
public import Mathlib.RingTheory.Etale.Weakly
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.TotallySplit
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsFFNeZeroThree
import Mathlib.Algebra.Module.StablyFree.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
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
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Topology.Sheaves.Init
public import Mathlib.NumberTheory.LegendreSymbol.AddCharacter

@[expose] public section

open ValuativeRel Matrix IsLocalRing
open GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.AdjointOperatorIdentities

noncomputable section
namespace GlobalTheory.PairOp

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : Type}
  {M : Type} [AddCommGroup M] [Module ℂ M]

theorem vanishing [Fintype n] [DecidableEq n] (q : Unif k) : Vanishing k n M q := by
  exact {
    invariant_eq_zero π P v hv M' _ _ θ hθ := by
      classical
      letI : Fintype 𝓀[k]ˣ := Fintype.ofFinite _

      have scal : ∀ s : 𝒪[k]ˣ, ∃ g : GL n k, ∀ x : n → k, g • x = (s : 𝒪[k]) • x := by
        intro s
        refine ⟨Units.map (Matrix.scalar n : k →+* Matrix n n k).toMonoidHom
          (Units.map (algebraMap 𝒪[k] k).toMonoidHom s), fun x => ?_⟩
        ext i
        simp [Units.smul_def, Matrix.scalar_apply, Matrix.mulVec_diagonal, Algebra.smul_def]

      have stab : ∀ (g : GL n k) (s : 𝒪[k]ˣ), (∀ x : n → k, g • x = (s : 𝒪[k]) • x) →
          ∀ L : Submodule 𝒪[k] (n → k), g ∈ latStab L := by
        intro g s hg L
        open Pointwise in rw [MulAction.mem_stabilizer_iff]
        ext x
        rw [mem_smul_iff]
        have e : x = (s : 𝒪[k]) • (g⁻¹ • x) := by rw [← hg, smul_inv_smul]
        constructor
        · intro h
          rw [e]
          exact L.smul_mem _ h
        · intro h
          have e' : g⁻¹ • x = ((s⁻¹ : 𝒪[k]ˣ) : 𝒪[k]) • x := by
            conv_rhs => rw [e]
            rw [smul_smul, Units.inv_mul, one_smul]
          rw [e']
          exact L.smul_mem _ h

      have lift : ∀ c : 𝓀[k]ˣ, ∃ s : 𝒪[k]ˣ, (Units.map (residue 𝒪[k]).toMonoidHom s)⁻¹ = c := by
        intro c
        obtain ⟨t, ht⟩ := IsLocalRing.residue_surjective ((c⁻¹ : 𝓀[k]ˣ) : 𝓀[k])
        have hu : IsUnit t := by
          by_contra hnu
          have h0 : residue 𝒪[k] t = 0 :=
            (IsLocalRing.residue_eq_zero_iff t).mpr ((IsLocalRing.mem_maximalIdeal t).mpr hnu)
          rw [ht] at h0
          exact (c⁻¹).ne_zero h0
        refine ⟨hu.unit, ?_⟩
        rw [inv_eq_iff_eq_inv]
        ext
        simp [ht]
      have hθc : ∀ c : 𝓀[k]ˣ, θ (formOf π P v (c • P)) = θ v := by
        intro c
        obtain ⟨s, hs⟩ := lift c
        obtain ⟨g, hg⟩ := scal s
        have hgP : g • P = c • P := by rw [scalar_smul_eq g s hg P, hs]
        rw [← hgP, formOf_smul]
        rcases hθ with h | h
        · exact h g (stab g s hg P.lat) v
        · exact h g (stab g s hg P.ker) v
      have hsum : ∑ c : 𝓀[k]ˣ, formOf π P v (c • P) = 0 := (mem_Mram _).mp hv P
      have h0 := congrArg θ hsum

      rw [map_sum, map_zero] at h0
      simp only [hθc, Finset.sum_const, Finset.card_univ] at h0
      have hcard : (Fintype.card 𝓀[k]ˣ : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
      rw [← Nat.cast_smul_eq_nsmul ℂ] at h0
      exact (smul_eq_zero.mp h0).resolve_left hcard
  }

theorem cross_dia (q : Unif k) {P₁ P : Pair k n} (h : P.lat = P₁.ker) (c : 𝓀[k]ˣ) :
    cross q (c • P₁) (c • P) = cross q P₁ P := by
  rw [cross_dia_left q (by rw [Pair.dia_lat]; exact h), cross_dia_right q h]
  simp

theorem sumOp_dia (S : Pair k n → Finset (Pair k n)) (w : Pair k n → Pair k n → ℂ) (c : 𝓀[k]ˣ)
    (hS : ∀ P Q, Q ∈ S P ↔ c • Q ∈ S (c • P)) (hw : ∀ P, ∀ Q ∈ S P, w (c • P) (c • Q) = w P Q) :
    (sumOp S w * dia c : Module.End ℂ (Form k n M)) = dia c * sumOp S w := by
  refine LinearMap.ext fun φ => funext fun P => ?_
  simp only [Module.End.mul_apply, sumOp_apply, dia_apply]
  refine Finset.sum_nbij' (fun Q => c • Q) (fun Q => c⁻¹ • Q) (fun Q hQ => (hS P Q).mp hQ)
    (fun Q hQ => (hS P (c⁻¹ • Q)).mpr (by rwa [smul_inv_smul])) (fun Q _ => inv_smul_smul c Q)
    (fun Q _ => smul_inv_smul c Q) fun Q hQ => ?_
  rw [hw P Q hQ]

variable (q : Unif k) (χ : AddChar 𝓀[k] ℂ)

theorem FF_dia (c : 𝓀[k]ˣ) : (FF q χ * dia c : Module.End ℂ (Form k n M)) = dia c * FF q χ := by
  unfold FF
  refine sumOp_dia _ _ c (fun P Q => by simp) fun P Q hQ => ?_
  rw [cross_dia q (mem_withLat.mp hQ)]

theorem FFStar_dia (c : 𝓀[k]ˣ) : (FFStar q χ * dia c : Module.End ℂ (Form k n M)) = dia c * FFStar q χ := by
  unfold FFStar
  refine sumOp_dia _ _ c (fun P Q => by simp) fun P Q hQ => ?_
  rw [cross_dia q (mem_withKer.mp hQ).symm]

theorem dia_dia (d c : 𝓀[k]ˣ) : (dia d * dia c : Module.End ℂ (Form k n M)) = dia c * dia d := by
  rw [← map_mul, ← map_mul, mul_comm]

theorem mem_ram {A : Module.End ℂ (Form k n M)} (h : ∀ c : 𝓀[k]ˣ, A * dia c = dia c * A) {φ : Form k n M}
    (hφ : φ ∈ Mram k n M) : A φ ∈ Mram k n M := by
  simp only [Mram, LinearMap.mem_ker] at hφ ⊢
  have hc : (Nm : Module.End ℂ (Form k n M)) * A = A * Nm := by
    unfold Nm
    rw [Finset.sum_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun c _ => (h c).symm
  rw [← Module.End.mul_apply, hc, Module.End.mul_apply, hφ, map_zero]

variable {χ}

private theorem sum_subtype_ne_zero_eq_sum_sub_zero {V : Type} [Zero V] [Fintype V] [DecidableEq V] [Fintype {v : V // v ≠ 0}]
    (g : V → ℂ) : ∑ v : {v : V // v ≠ 0}, g v.1 = ∑ v, g v - g 0 := by
  rw [eq_sub_iff_add_eq, ← Finset.sum_erase_add _ _ (Finset.mem_univ (0 : V))]
  congr 1
  exact Finset.sum_bij' (fun v _ => v.1) (fun v hv => ⟨v, Finset.ne_of_mem_erase hv⟩)
    (fun v _ => Finset.mem_erase.mpr ⟨v.2, Finset.mem_univ _⟩) (fun v _ => Finset.mem_univ _)
    (fun v _ => rfl) (fun v _ => rfl) (fun v _ => rfl)

theorem FF_FFStar [Fintype n] (hχ : χ ≠ 1) (φ : Form k n M) :
    FF q χ (FFStar q χ φ) = (resCard k ^ Fintype.card n : ℂ) • φ - tr' φ := by
  classical
  funext P₁
  rw [FF_apply, Pi.sub_apply, Pi.smul_apply, tr'_apply]
  set L := P₁.ker with hL
  have : L.IsFullLattice k := by rw [hL]; infer_instance
  letI : Fintype {f : Module.Dual 𝓀[k] (Red L) // f ≠ 0} := Fintype.ofFinite _
  letI : Fintype {x : Red L // x ≠ 0} := Fintype.ofFinite _
  letI : Fintype (Module.Dual 𝓀[k] (Red L)) := Fintype.ofFinite _
  letI : Fintype (Red L) := Fintype.ofFinite _
  letI : Fintype 𝓀[k] := Fintype.ofFinite _
  obtain ⟨x₁, hx₁⟩ : ∃ x₁ : {x : Red L // x ≠ 0}, up L q x₁ = P₁ :=
    ⟨_, congrArg Subtype.val ((kerEquiv L q).apply_symm_apply ⟨P₁, hL.symm⟩)⟩
  rw [← hx₁, sum_withLat L, sum_withKer L q]
  simp only [FFStar_ofDual, cross_up_ofDual, Finset.smul_sum, smul_smul, ← AddChar.map_add_eq_mul]
  rw [Finset.sum_comm]
  simp only [← Finset.sum_smul]
  have hinner : ∀ x : {x : Red L // x ≠ 0}, ∑ f : {f : Module.Dual 𝓀[k] (Red L) // f ≠ 0},
      χ (f.1 x₁.1 + -f.1 x.1) = (if x = x₁ then (resCard k : ℂ) ^ Fintype.card n else 0) - 1 := by
    intro x
    rw [sum_subtype_ne_zero_eq_sum_sub_zero (fun f : Module.Dual 𝓀[k] (Red L) => χ (f x₁.1 + -f x.1))]
    simp only [LinearMap.zero_apply, neg_zero, add_zero, AddChar.map_zero_eq_one]
    congr 1
    have e : ∀ f : Module.Dual 𝓀[k] (Red L),
        f x₁.1 + -f x.1 = Module.Dual.eval 𝓀[k] (Red L) (x₁.1 - x.1) f := by
      intro f
      simp [sub_eq_add_neg]
    simp only [e]
    rw [Model.sum_char hχ]
    have hiff : Module.Dual.eval 𝓀[k] (Red L) (x₁.1 - x.1) = 0 ↔ x = x₁ := by
      constructor
      · intro h0
        have h1 : x₁.1 - x.1 = 0 := (Module.forall_dual_apply_eq_zero_iff 𝓀[k] _).mp fun f => by
          simpa using LinearMap.congr_fun h0 f
        exact (Subtype.ext (sub_eq_zero.mp h1)).symm
      · rintro rfl
        simp
    have hcard : (Fintype.card (Module.Dual 𝓀[k] (Red L)) : ℂ) = (resCard k : ℂ) ^ Fintype.card n := by
      rw [Module.card_eq_pow_finrank (K := 𝓀[k]), Subspace.dual_finrank_eq, Red.finrank_eq]
      simp [resCard, Nat.card_eq_fintype_card]
    simp only [hiff, hcard]
  simp only [hinner, sub_smul, ite_smul, zero_smul, one_smul, Finset.sum_sub_distrib, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true]


variable (χ) in
theorem FFStar_eq_U_GsStar {φ : Form k n M} (h : φ ∈ Mram k n M) : FFStar q χ φ = U q (GsStar χ φ) := by
  classical
  letI : Fintype 𝓀[k]ˣ := Fintype.ofFinite _
  funext P
  rw [FFStar_apply, U_apply]
  simp only [GsStar_apply]

  have h0 : ∑ P₁ ∈ withKer P.lat with cross q P₁ P = 0, χ (-cross q P₁ P) • φ P₁ = 0 := by
    rw [Finset.sum_congr rfl fun P₁ hP₁ => by
      rw [(Finset.mem_filter.mp hP₁).2, neg_zero, AddChar.map_zero_eq_one, one_smul]]
    refine Model.sum_stable_eq_zero h _ fun c P₁ => ?_
    simp only [Finset.mem_filter, mem_withKer, Pair.dia_ker]
    constructor
    · rintro ⟨hk, hc⟩
      refine ⟨hk, ?_⟩
      rwa [cross_dia_left q hk.symm, mul_eq_zero, or_iff_right (Units.ne_zero _)] at hc
    · rintro ⟨hk, hc⟩
      exact ⟨hk, by rw [cross_dia_left q hk.symm, hc, mul_zero]⟩
  rw [← Finset.sum_filter_add_sum_filter_not (withKer P.lat) (fun P₁ => cross q P₁ P = 0), h0, zero_add,
    ← Finset.sum_product']
  refine Finset.sum_bij'
    (fun P₁ hP₁ => (Units.mk0 (cross q P₁ P) (Finset.mem_filter.mp hP₁).2 • P₁,
      Units.mk0 (cross q P₁ P) (Finset.mem_filter.mp hP₁).2))
    (fun x _ => x.2⁻¹ • x.1) (fun P₁ hP₁ => ?_) (fun x hx => ?_) (fun P₁ _ => inv_smul_smul _ _)
    (fun x hx => ?_) (fun P₁ _ => by simp)
  · obtain ⟨hk, hc⟩ := Finset.mem_filter.mp hP₁
    refine Finset.mem_product.mpr ⟨Finset.mem_filter.mpr ⟨?_, ?_⟩, Finset.mem_univ _⟩
    · rw [mem_withKer, Pair.dia_ker]
      exact mem_withKer.mp hk
    · rw [cross_dia_left q (mem_withKer.mp hk).symm]
      simp [hc]
  · obtain ⟨h1, -⟩ := Finset.mem_product.mp hx
    obtain ⟨hk, hc⟩ := Finset.mem_filter.mp h1
    refine Finset.mem_filter.mpr ⟨?_, ?_⟩
    · rw [mem_withKer, Pair.dia_ker]
      exact mem_withKer.mp hk
    · rw [cross_dia_left q (mem_withKer.mp hk).symm, hc, inv_inv, mul_one]
      exact x.2.ne_zero
  · obtain ⟨h1, -⟩ := Finset.mem_product.mp hx
    obtain ⟨hk, hc⟩ := Finset.mem_filter.mp h1
    have e : cross q (x.2⁻¹ • x.1) P = x.2 := by
      rw [cross_dia_left q (mem_withKer.mp hk).symm, hc, inv_inv, mul_one]
    have eu : ∀ h', Units.mk0 (cross q (x.2⁻¹ • x.1) P) h' = x.2 := fun h' => Units.ext (by simpa using e)
    rw [eu]
    exact Prod.ext (smul_inv_smul _ _) rfl

theorem resCard_ne_zero : (resCard k : ℂ) ≠ 0 := by
  unfold resCard
  exact_mod_cast (Nat.card_pos (α := 𝓀[k])).ne'

theorem FFStar_FF_ram [Fintype n] (hχ : χ ≠ 1) {φ : Form k n M} (h : φ ∈ Mram k n M) :
    FFStar q χ (FF q χ φ) = ((resCard k : ℂ) ^ Fintype.card n) • φ := by
  rw [Model.FFStar_FF q hχ φ, (Model.tr_eq_zero h).1, sub_zero]

theorem FF_FFStar_ram [Fintype n] (hχ : χ ≠ 1) {φ : Form k n M} (h : φ ∈ Mram k n M) :
    FF q χ (FFStar q χ φ) = ((resCard k : ℂ) ^ Fintype.card n) • φ := by
  rw [FF_FFStar q hχ φ, (Model.tr_eq_zero h).2, sub_zero]

theorem operatorIdentities [Fintype n] (hχ : χ ≠ 1) : OperatorIdentities k n M q χ := by
  exact {
    FFStar_FF_ram φ h := FFStar_FF_ram q hχ h
    FF_FFStar_ram φ h := FF_FFStar_ram q hχ h
    FF_mem_ram φ h := mem_ram (fun c => FF_dia q χ c) h
    FFStar_mem_ram φ h := mem_ram (fun c => FFStar_dia q χ c) h
    dia_mem_ram c φ h := mem_ram (fun d => dia_dia c d) h
  }

theorem pairOperatorStatement : PairOperatorStatement := by
  intro k _ _ _ _ ϖ ψ hψ n _ _
  exact fun M _ _ => ⟨vanishing ϖ, operatorIdentities ϖ (resChar_ne_one hψ ϖ)⟩

end GlobalTheory.PairOp
