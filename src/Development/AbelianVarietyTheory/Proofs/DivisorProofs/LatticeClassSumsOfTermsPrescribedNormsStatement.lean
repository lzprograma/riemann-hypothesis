module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Mathlib.Tactic.Linter.Style
import Mathlib.Topology.Algebra.InfiniteSum.Nonarchimedean
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsGenLab

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeClassSumsOfTermsPrescribedNorms, Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeClassSumsOfTermsPrescribedNormsStatement

@[expose] public noncomputable section

open GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc.USum Filter Topology

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeClassSumsOfTermsPrescribedNorms =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeClassSumsOfTermsPrescribedNorms", "h": "module\n\npublic import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.Style\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Algebra.InfiniteSum.Nonarchimedean\nimport Mathlib.Topology.Connected.Separation\nimport Mathlib.Topology.MetricSpace.Ultra.TotallySeparated\nimport Std.Tactic.BVDecide.Normalize.Prop\nimport Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsGenLab\n\n"}
namespace GlobalTheory.UPoinc.USum.ClassTerms

theorem summable_of_mem_fd {p : ℕ} [Fact p.Prime] {I : Type} (M : Submodule ℚ_[p] (PadicAlgCl p))
    [FiniteDimensional ℚ_[p] M] (f : I → PadicAlgCl p) (hf : ∀ i, f i ∈ M)
    (h0 : Tendsto (fun i => ‖f i‖) cofinite (𝓝 0)) : Summable f :=
  have : CompleteSpace M := FiniteDimensional.completeSpace ℚ_[p] M
  (NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero (f := fun i => (⟨f i, hf i⟩ : M))
    (tendsto_zero_iff_norm_tendsto_zero.2 (by simpa using h0))).hasSum.map M.subtype continuous_subtypeVal |>.summable

theorem exists_unit_sub_one_unit (p : ℕ) [Fact p.Prime] :
    ∃ u : PadicAlgCl p, ‖u‖ = 1 ∧ ‖u - 1‖ = 1 := by
  obtain ⟨u, hu⟩ := IsAlgClosed.exists_root (Polynomial.X ^ 2 - Polynomial.X - 1 : Polynomial (PadicAlgCl p))
    (by have hd : (Polynomial.X ^ 2 - Polynomial.X - 1 : Polynomial (PadicAlgCl p)).degree = 2 := by compute_degree!
        rw [hd]; decide)
  have h2 : u ^ 2 = u + 1 := by simp [Polynomial.IsRoot] at hu; linear_combination hu
  have hle : ‖u‖ ≤ 1 := by
    by_contra h
    push Not at h
    have h3 : ‖u‖ ^ 2 ≤ max ‖u‖ ‖(1 : PadicAlgCl p)‖ := by rw [← norm_pow, h2]; exact IsUltrametricDist.norm_add_le_max _ _
    rw [norm_one, max_eq_left h.le] at h3; nlinarith
  have hle' : ‖u - 1‖ ≤ 1 := by
    have := IsUltrametricDist.norm_add_le_max u (-1)
    rw [← sub_eq_add_neg, norm_neg, norm_one] at this; exact this.trans (max_le hle le_rfl)
  have hprod : ‖u‖ * ‖u - 1‖ = 1 := by rw [← norm_mul, show u * (u - 1) = 1 by linear_combination h2, norm_one]
  have h1 : 1 ≤ ‖u - 1‖ := by nlinarith [norm_nonneg (u - 1)]
  have h1' : 1 ≤ ‖u‖ := by nlinarith [norm_nonneg u]
  exact ⟨u, le_antisymm hle h1', le_antisymm hle' h1⟩

theorem one_class {p : ℕ} [Fact p.Prime] {Y K : Type} [Nonempty Y] [Nonempty K] (q : Y → ℝ) (s : PadicAlgCl p)
    (n : Y → ℕ) (hq : Tendsto q cofinite atTop) (hs : ∀ χ, ‖s‖ ^ n χ = Real.exp (-q χ))
    (C : Set Y) (χ₀ : Y) (h0 : χ₀ ∈ C) (hmin : ∀ χ ∈ C, q χ₀ ≤ q χ) (G : K → PadicAlgCl p)
    (hG : ∀ κ, ‖G κ‖ ≤ Real.exp (-q χ₀))
    (hG' : (∀ χ ∈ C, χ ≠ χ₀ → q χ₀ < q χ) → ∃ κ, ‖G κ‖ = Real.exp (-q χ₀)) :
    ∃ t : Y → K → PadicAlgCl p, (∀ χ ∈ C, ∀ κ, ‖t χ κ‖ ≤ Real.exp (-q χ)) ∧
      (∀ χ ∈ C, ∃ κ, ‖t χ κ‖ = Real.exp (-q χ)) ∧ ∀ κ, HasSum (fun χ : C => t χ κ) (G κ) := by
  classical
  obtain ⟨u₀, hu1, hu2⟩ := exists_unit_sub_one_unit p
  set D : Set Y := C \ {χ₀}
  set A : Subalgebra ℚ_[p] (PadicAlgCl p) := Algebra.adjoin ℚ_[p] ({s, u₀} : Set (PadicAlgCl p))
  let M : Submodule ℚ_[p] (PadicAlgCl p) := Subalgebra.toSubmodule A
  have : FiniteDimensional ℚ_[p] M :=
    Algebra.finite_adjoin_of_finite_of_isIntegral (by simp) fun x _ => Algebra.IsIntegral.isIntegral x
  have hsA : s ∈ A := Algebra.subset_adjoin (by simp)
  have huA : u₀ ∈ A := Algebra.subset_adjoin (by simp)
  have hsumm : ∀ w : Y → PadicAlgCl p, (∀ χ, w χ ∈ A) → (∀ χ, ‖w χ‖ = Real.exp (-q χ)) → Summable (D.indicator w) :=
    fun w hwA hw => summable_of_mem_fd M _
      (fun χ => if h : χ ∈ D then by rw [Set.indicator_of_mem h]; exact hwA χ else by rw [Set.indicator_of_notMem h]; exact M.zero_mem)
      (squeeze_zero (fun _ => norm_nonneg _)
        (fun χ => by by_cases h : χ ∈ D <;> simp [Set.indicator_of_mem, Set.indicator_of_notMem, h, hw]; positivity)
        (Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp hq)))
  have hSle : ∀ w : Y → PadicAlgCl p, (∀ χ, ‖w χ‖ = Real.exp (-q χ)) → ‖∑' χ, D.indicator w χ‖ ≤ Real.exp (-q χ₀) :=
    fun w hw => IsUltrametricDist.norm_tsum_le_of_forall_le fun χ =>
      if h : χ ∈ D then by rw [Set.indicator_of_mem h, hw]; exact Real.exp_le_exp.mpr (neg_le_neg (hmin χ h.1))
      else by rw [Set.indicator_of_notMem h, norm_zero]; positivity
  have key : ∀ w : Y → PadicAlgCl p, (∀ χ, w χ ∈ A) → (∀ χ, ‖w χ‖ = Real.exp (-q χ)) →
      (∃ κ, ‖G κ - ∑' χ, D.indicator w χ‖ = Real.exp (-q χ₀)) →
      ∃ t : Y → K → PadicAlgCl p, (∀ χ ∈ C, ∀ κ, ‖t χ κ‖ ≤ Real.exp (-q χ)) ∧
      (∀ χ ∈ C, ∃ κ, ‖t χ κ‖ = Real.exp (-q χ)) ∧ ∀ κ, HasSum (fun χ : C => t χ κ) (G κ) := by
    intro w hwA hw ⟨κ₀, hκ₀⟩
    set S := ∑' χ, D.indicator w χ
    refine ⟨fun χ κ => if χ = χ₀ then G κ - S else w χ, fun χ _ κ => ?_, fun χ _ => ?_, fun κ => ?_⟩
    · by_cases h : χ = χ₀
      · subst h; simp only [ite_true, sub_eq_add_neg]
        exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hG κ) (by rw [norm_neg]; exact hSle w hw))
      · simp only [h, ite_false, hw, le_refl]
    · by_cases h : χ = χ₀
      · subst h; exact ⟨κ₀, by simpa using hκ₀⟩
      · exact ⟨Classical.arbitrary K, by simp only [h, ite_false, hw]⟩
    · have h2 := (hasSum_ite_eq χ₀ (G κ - S)).add (hsumm w hwA hw).hasSum
      rw [sub_add_cancel] at h2
      refine (hasSum_subtype_iff_indicator (f := fun χ => if χ = χ₀ then G κ - S else w χ)).mpr ?_
      convert h2 using 1; funext χ
      by_cases h : χ = χ₀
      · subst h; simp [Set.indicator_of_mem h0, Set.indicator_of_notMem (fun hh => hh.2 rfl : χ ∉ D)]
      · by_cases hc : χ ∈ C
        · simp [Set.indicator_of_mem hc, Set.indicator_of_mem (show χ ∈ D from ⟨hc, h⟩), h]
        · simp [Set.indicator_of_notMem hc, Set.indicator_of_notMem (fun hh => hc hh.1 : χ ∉ D), h]
  set rr : Y → PadicAlgCl p := fun χ => s ^ n χ
  have hrA : ∀ χ, rr χ ∈ A := fun χ => A.pow_mem hsA _
  have hrn : ∀ χ, ‖rr χ‖ = Real.exp (-q χ) := fun χ => by simp [rr, norm_pow, hs]
  by_cases hstrict : ∀ χ ∈ C, χ ≠ χ₀ → q χ₀ < q χ
  · obtain ⟨κ, hκ⟩ := hG' hstrict
    refine key rr hrA hrn ⟨κ, ?_⟩
    have hlt : ‖∑' χ, D.indicator rr χ‖ < Real.exp (-q χ₀) := by
      by_cases hDe : D.Nonempty
      · have : Nonempty D := hDe.to_subtype
        obtain ⟨a₁, ha₁⟩ := (hq.comp (Subtype.val_injective (p := (· ∈ D))).tendsto_cofinite).exists_forall_le
        have ha₁' : (a₁ : Y) ∈ C ∧ (a₁ : Y) ≠ χ₀ := a₁.2
        refine lt_of_le_of_lt (IsUltrametricDist.norm_tsum_le_of_forall_le (C := Real.exp (-q a₁)) fun χ => ?_)
          (Real.exp_lt_exp.mpr (neg_lt_neg (hstrict a₁ ha₁'.1 ha₁'.2)))
        by_cases h : χ ∈ D
        · rw [Set.indicator_of_mem h, hrn]; exact Real.exp_le_exp.mpr (neg_le_neg (ha₁ ⟨χ, h⟩))
        · rw [Set.indicator_of_notMem h, norm_zero]; positivity
      · have hz : D.indicator rr = 0 := funext fun χ => Set.indicator_of_notMem (fun h => hDe ⟨χ, h⟩) _
        simp only [hz, Pi.zero_apply, tsum_zero, norm_zero]; positivity
    rw [sub_eq_add_neg, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm
      (by rw [norm_neg, hκ]; exact hlt.ne'), norm_neg, hκ, max_eq_left hlt.le]
  · push Not at hstrict
    obtain ⟨χ₁, hχ₁C, hχ₁ne, hχ₁le⟩ := hstrict
    have hq₁ : q χ₁ = q χ₀ := le_antisymm hχ₁le (hmin χ₁ hχ₁C)
    set κ₀ : K := Classical.arbitrary K
    by_cases hc : ‖G κ₀ - ∑' χ, D.indicator rr χ‖ = Real.exp (-q χ₀)
    · exact key rr hrA hrn ⟨κ₀, hc⟩
    · set w := Function.update rr χ₁ (u₀ * rr χ₁)
      refine key w (fun χ => by by_cases h : χ = χ₁ <;> simp [w, h, A.mul_mem, huA, hrA])
        (fun χ => by by_cases h : χ = χ₁ <;> simp [w, h, norm_mul, hu1, hrn]) ⟨κ₀, ?_⟩
      have hind : D.indicator w = Function.update (D.indicator rr) χ₁ (u₀ * rr χ₁) := by
        funext χ; by_cases h : χ = χ₁
        · subst h; simp [w, Set.indicator_of_mem (show χ ∈ D from ⟨hχ₁C, hχ₁ne⟩)]
        · by_cases hd : χ ∈ D <;> simp [w, h, hd, Set.indicator_of_mem, Set.indicator_of_notMem]
      have hS' : ∑' χ, D.indicator w χ = u₀ * rr χ₁ - rr χ₁ + ∑' χ, D.indicator rr χ := by
        rw [hind]; have := (hsumm rr hrA hrn).hasSum.update χ₁ (u₀ * rr χ₁)
        rw [Set.indicator_of_mem (⟨hχ₁C, hχ₁ne⟩ : χ₁ ∈ D)] at this; exact this.tsum_eq
      have hle : ‖G κ₀ - ∑' χ, D.indicator rr χ‖ < Real.exp (-q χ₀) := lt_of_le_of_ne (by
        rw [sub_eq_add_neg]; exact (IsUltrametricDist.norm_add_le_max _ _).trans
          (max_le (hG κ₀) (by rw [norm_neg]; exact hSle rr hrn))) hc
      have hn1 : ‖-((u₀ - 1) * rr χ₁)‖ = Real.exp (-q χ₀) := by
        rw [norm_neg, norm_mul, hu2, _root_.one_mul, hrn, hq₁]
      rw [show G κ₀ - ∑' χ, D.indicator w χ = (G κ₀ - ∑' χ, D.indicator rr χ) + -((u₀ - 1) * rr χ₁) by rw [hS']; ring,
        IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by rw [hn1]; exact hle.ne), hn1, max_eq_right hle.le]

end GlobalTheory.UPoinc.USum.ClassTerms

namespace GlobalTheory.UPoinc.USum

open GlobalTheory.UPoinc.USum.ClassTerms in
theorem classSum_of_terms : ∀ (p : ℕ) [Fact p.Prime] (Y K : Type) [AddCommGroup Y] [Nonempty K] (m : ℕ) (q : Y → ℝ) (s : PadicAlgCl p) (n : Y → ℕ), Filter.Tendsto q Filter.cofinite Filter.atTop → (∀ χ, ‖s‖ ^ n χ = Real.exp (-q χ)) → ∀ F : Y → K → PadicAlgCl p, (∀ ν ν' κ, CongMod m ν ν' → F ν κ = F ν' κ) → (∀ ν κ, (∀ χ, CongMod m χ ν → q ν ≤ q χ) → ‖F ν κ‖ ≤ Real.exp (-q ν)) → (∀ ν, (∀ χ, CongMod m χ ν → χ ≠ ν → q ν < q χ) → ∃ κ, ‖F ν κ‖ = Real.exp (-q ν)) → ∃ t : Y → K → PadicAlgCl p, (∀ χ κ, ‖t χ κ‖ ≤ Real.exp (-q χ)) ∧ (∀ χ, ∃ κ, ‖t χ κ‖ = Real.exp (-q χ)) ∧ ∀ ν κ (δ : ℝ), 0 < δ → ∃ S₀ : Finset Y, ∀ S : Finset Y, (∀ χ ∈ S, CongMod m χ ν) → (∀ χ ∈ S₀, CongMod m χ ν → χ ∈ S) → ‖F ν κ - ∑ χ ∈ S, t χ κ‖ ≤ δ := by
  intro p _ Y K _ _ m q s n hq hs F hF hle heq
  classical
  let R : Setoid Y := ⟨CongMod m, ⟨fun _ => ⟨0, by simp⟩,
    fun ⟨w, hw⟩ => ⟨-w, by rw [hw]; simp⟩,
    fun ⟨w, hw⟩ ⟨w', hw'⟩ => ⟨w' + w, by rw [hw, hw', smul_add]; abel⟩⟩⟩
  have hR : ∀ x y : Y, Quotient.mk R x = Quotient.mk R y ↔ CongMod m x y :=
    fun _ _ => Quotient.eq
  have hmin : ∀ c : Quotient R, ∃ χ₀, Quotient.mk R χ₀ = c ∧ ∀ χ, Quotient.mk R χ = c → q χ₀ ≤ q χ := fun c => by
    obtain ⟨x, rfl⟩ := Quotient.exists_rep c
    let Cs : Set Y := {χ | Quotient.mk R χ = Quotient.mk R x}
    have : Nonempty Cs := ⟨⟨x, rfl⟩⟩
    obtain ⟨a, ha⟩ := (hq.comp (Subtype.val_injective (p := (· ∈ Cs))).tendsto_cofinite).exists_forall_le
    exact ⟨a, a.2, fun χ hχ => ha ⟨χ, hχ⟩⟩
  choose z hzc hzmin using hmin
  choose tc htc1 htc2 htc3 using fun c : Quotient R =>
    one_class q s n hq hs {χ | Quotient.mk R χ = c} (z c) (hzc c) (hzmin c) (F (z c))
      (fun κ => hle _ κ fun χ hχ => hzmin c χ (((hR _ _).2 hχ).trans (hzc c)))
      (fun H => heq (z c) fun χ hχ hne => H χ (((hR _ _).2 hχ).trans (hzc c)) hne)
  refine ⟨fun χ κ => tc (Quotient.mk R χ) χ κ, fun χ κ => htc1 _ χ rfl κ, fun χ => htc2 _ χ rfl, fun ν κ δ hδ => ?_⟩
  set c := Quotient.mk R ν
  have hFz : F (z c) κ = F ν κ := hF _ _ κ ((hR _ _).1 (hzc c))
  obtain ⟨T₀, hT₀⟩ := Metric.tendsto_atTop.1 (hFz ▸ htc3 c κ : Tendsto (fun T : Finset {χ | Quotient.mk R χ = c} => ∑ χ ∈ T, tc c χ κ) atTop (𝓝 (F ν κ))) δ hδ
  refine ⟨T₀.map (Function.Embedding.subtype _), fun S hSc hS₀ => ?_⟩
  have h1 := hT₀ _ fun x hx => Finset.mem_subtype.2 (hS₀ x (Finset.mem_map_of_mem _ hx) ((hR _ _).1 x.2))
  change dist (∑ χ ∈ S.subtype (fun χ => Quotient.mk R χ = c), tc c χ κ) (F ν κ) < δ at h1
  rw [Finset.sum_subtype_eq_sum_filter (fun χ => tc c χ κ),
    Finset.filter_true_of_mem fun χ hχ => (hR _ _).2 (hSc χ hχ)] at h1
  show ‖F ν κ - ∑ χ ∈ S, tc (Quotient.mk R χ) χ κ‖ ≤ δ
  rw [Finset.sum_congr rfl fun χ hχ => by rw [(hR _ _).2 (hSc χ hχ)], ← dist_eq_norm, dist_comm]
  exact h1.le

end GlobalTheory.UPoinc.USum
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeClassSumsOfTermsPrescribedNorms =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeClassSumsOfTermsPrescribedNormsStatement =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeClassSumsOfTermsPrescribedNormsStatement", "h": "module\n\npublic import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeClassSumsOfTermsPrescribedNorms\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsGenLab\n\n"}
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeClassSumsOfTermsPrescribedNormsStatement =====
