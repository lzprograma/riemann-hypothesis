module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsLocIsoRefl
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MeasurePreservingPiCurry
public import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PartialColumnFourierMemSchwartzBruhat
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
import Aesop.Main
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierTransformInversionLocalFieldPi
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Std.Tactic.BVDecide.Normalize.Prop
import Mathlib.Tactic.TypeStar

section
@[expose] public section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.ColFourier

noncomputable section
namespace GlobalTheory.ColFourier

theorem fourier_pi_inversion_at {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] {n : Type*} [Fintype n] [DecidableEq n]
    {ψ : AddChar k Circle} {c : kˣ} {ν : Measure k} (h : HasConductor ψ c) (hν : IsSelfDual ψ ν)
    {g : (n → k) → ℂ} (hg : g ∈ SB (n → k)) (a : n → k) :
    ∫ y : n → k, (∫ x, g x * (ψ (x ⬝ᵥ y) : ℂ) ∂(Measure.pi fun _ => ν)) * (ψ⁻¹ (y ⬝ᵥ a) : ℂ)
      ∂(Measure.pi fun _ => ν) = g a := by
  haveI := hν.1
  haveI := secondCountable k
  haveI := t2Space k
  have hh : (fun x => g (x + a)) ∈ SB (n → k) :=
    ⟨hg.1.comp_continuous (by fun_prop), hg.2.comp_homeomorph (Homeomorph.addRight a)⟩
  have h1 := (FourierPi.fourier_pi_of_conductor h hν hh).2
  simp only [zero_add] at h1
  rw [← h1]
  congr 1
  funext y
  rw [← integral_mul_const,
    ← integral_add_right_eq_self (fun x => g x * (ψ (x ⬝ᵥ y) : ℂ) * (ψ⁻¹ (y ⬝ᵥ a) : ℂ)) a]
  congr 1
  funext x
  rw [add_dotProduct, AddChar.map_add_eq_mul, AddChar.inv_apply', dotProduct_comm y a, mul_assoc,
    ← Circle.coe_mul, mul_inv_cancel_right]

theorem fourierInt_inv_fourierInt : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (A C : Type) [Fintype A] [DecidableEq A] [DecidableEq C] (ψ : AddChar k Circle) (m : Measure k), HasConductor ψ 1 → IsUnitVol m → ∀ (P : Finset C), ∀ Ξ ∈ SB (Matrix A C k), fourierInt ψ⁻¹ m P (fourierInt ψ m P Ξ) = Ξ := by
  intro k _ _ _ _ _ _ A C _ _ _ ψ m hψ hm P Ξ hΞ
  have hν : IsSelfDual ψ m := isSelfDual_of_isUnitVol m hψ hm
  haveI := hν.1
  haveI := secondCountable k
  haveI := t2Space k
  funext X
  have h0 := comp_setCols_mem_SB hΞ P X
  have hg : (fun x : (_ : A) × P → k => Ξ (setCols P X (Matrix.of fun i j => x ⟨i, j⟩))) ∈
      SB ((_ : A) × P → k) :=
    ⟨h0.1.comp_continuous (f := fun x : (_ : A) × P → k => (Matrix.of fun i j => x ⟨i, j⟩ : Matrix A P k))
        (continuous_pi fun i => continuous_pi fun j => continuous_apply _),
      HasCompactSupport.intro (h0.2.image (f := fun (U : Matrix A P k) (p : (_ : A) × P) => U p.1 p.2)
        (continuous_pi fun p => (continuous_apply p.2).comp (continuous_apply p.1)))
        fun x hx => image_eq_zero_of_notMem_tsupport (f := fun U => Ξ (setCols P X U)) fun h => hx ⟨_, h, rfl⟩⟩
  have h1 := fourier_pi_inversion_at hψ hν hg (fun p => X p.1 p.2)
  have h2 : setCols P X (Matrix.of fun i (j : P) => X i j) = X := setCols_restrictCols P X
  simp only [h2] at h1
  rw [← h1, fourierInt_eq_pi]
  congr 1
  funext y
  rw [fourierInt_eq_pi]
  have h3 : (fun p : (_ : A) × P => setCols P X (Matrix.of fun i j => y ⟨i, j⟩) p.1 p.2) = y := by
    funext p
    simp [setCols, p.2.2]
  simp only [setCols_setCols, h3]

end GlobalTheory.ColFourier
end
end
end


section
@[expose] public section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.ColFourier
open scoped Pointwise

noncomputable section
namespace GlobalTheory.ColFourier

section Lemmas
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {A C : Type} [Fintype A] [DecidableEq C]

theorem mem_maxIdeal_pow_iff {ϖ : kˣ} (hϖ : IsUnif ϖ) (n : ℕ) (r : 𝒪[k]) :
    r ∈ IsLocalRing.maximalIdeal 𝒪[k] ^ n ↔ valuation k (r : k) ≤ valuation k ((ϖ ^ n : kˣ) : k) := by
  rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton,
    ← (Valuation.integer.integers (valuation k)).le_iff_dvd]
  rfl

theorem natDatum_setCols_eq {ϖ : kˣ} {n : ℕ} {Φ : Matrix A C k → ℂ} (hΦ : IsNatDatum ϖ n Φ) (P : Finset C)
    (Y : Matrix A C k) {U V : Matrix A P k} (h : ∀ i j, U i j - V i j ∈ cball (ϖ ^ n)) :
    Φ (setCols P Y U) = Φ (setCols P Y V) := by
  have h0 : 0 < valuation k ((ϖ ^ n : kˣ) : k) := zero_lt_iff.2 (by simp)
  have hZ : setCols P 0 (U - V) ∈ matLat A ((ϖ ^ n) • stdLat k C) := by
    rw [mem_matLat]
    intro i
    rw [mem_smul_lat, mem_stdLat]
    intro j
    by_cases hj : j ∈ P
    · have h1 := h i ⟨j, hj⟩
      simp only [cball, Set.mem_setOf_eq] at h1
      simp only [Pi.smul_apply, Matrix.row, setCols, of_apply, dif_pos hj, Matrix.sub_apply, Units.smul_def,
        smul_eq_mul]
      rw [Valuation.mem_integer_iff, map_mul, Units.val_inv_eq_inv_val, map_inv₀, inv_mul_le_iff₀ h0, mul_one]
      exact h1
    · simp [Matrix.row, setCols, hj]
  have := hΦ.2 (setCols P Y V) _ hZ
  rw [← this]
  congr 1
  ext i j
  by_cases hj : j ∈ P <;> simp [setCols, hj]

theorem psi_pairCols_eq {ψ : AddChar k Circle} (hψ : HasConductor ψ 1) {ϖ : kˣ} {n : ℕ} (P : Finset C)
    {Y : Matrix A C k} (hY : ∀ i, ∀ j ∈ P, ((ϖ ^ n : kˣ) : k) * Y i j ∈ 𝒪[k]) {U V : Matrix A P k}
    (h : ∀ i j, U i j - V i j ∈ cball (ϖ ^ n)) : ψ (pairCols P Y U) = ψ (pairCols P Y V) := by
  have h1 : pairCols P Y U = pairCols P Y V + pairCols P Y (U - V) := by
    simp only [pairCols, ← Finset.sum_add_distrib, Matrix.sub_apply]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  rw [h1, AddChar.map_add_eq_mul, hψ.eq_one (y := pairCols P Y (U - V)) ?_, mul_one]
  show valuation k _ ≤ valuation k ((1 : kˣ) : k)
  rw [Units.val_one, map_one]
  refine Valuation.map_sum_le _ fun i _ => Valuation.map_sum_le _ fun j _ => ?_
  have h2 := h i j
  have h3 := hY i j j.2
  rw [cball, Set.mem_setOf_eq] at h2
  rw [Valuation.mem_integer_iff, map_mul] at h3
  rw [map_mul, Matrix.sub_apply]
  exact (mul_le_mul' h2 le_rfl).trans (by rw [mul_comm] at h3 ⊢; exact h3)

end Lemmas

theorem fourierInt_eq_fourierSum : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (A C : Type) [Fintype A] [DecidableEq A]
    [DecidableEq C] (ψ : AddChar k Circle) (m : Measure k) (ϖ : kˣ), IsUnif ϖ → HasConductor ψ 1 → IsUnitVol m →
    ∀ (P : Finset C) (n : ℕ) (Φ : Matrix A C k → ℂ), IsNatDatum ϖ n Φ →
      fourierInt ψ m P Φ = fourierSum ψ ϖ n P Φ := by
  intro k _ _ _ _ _ _ A C _ _ _ ψ m ϖ hϖ hψ hm P n Φ hΦ
  haveI := secondCountable k
  haveI := t2Space k
  haveI := hm.1
  have h0 : 0 < valuation k ((ϖ ^ n : kˣ) : k) := zero_lt_iff.2 (by simp)
  funext Y
  rw [fourierSum_apply]
  split_ifs with hY
  · rw [fourierInt]
    set F : Matrix A P k → ℂ := fun U => Φ (setCols P Y U) * (ψ (pairCols P Y U) : ℂ) with hF
    let S : (A → P → Res k n) → Set (Matrix A P k) := fun T =>
      Set.univ.pi fun i => Set.univ.pi fun j => (fun x => x + -liftRes T i j) ⁻¹' cball (ϖ ^ n)
    have hmemS : ∀ T U, U ∈ S T ↔ ∀ i j, U i j - liftRes T i j ∈ cball (ϖ ^ n) := by
      intro T U
      exact ⟨fun h i j => by simpa [sub_eq_add_neg] using h i trivial j trivial,
        fun h i _ j _ => by simpa [sub_eq_add_neg] using h i j⟩
    have hS : ∀ T, MeasurableSet (S T) := fun T =>
      MeasurableSet.univ_pi fun i => MeasurableSet.univ_pi fun j =>
        (isOpen_cball _).measurableSet.preimage (measurable_add_const _)
    have hcb : m (cball (ϖ ^ n)) = (distribHaarChar k (ϖ ^ n) : ENNReal) := by
      rw [measure_cball, hm.2, mul_one]
    have hvolE : ∀ T, (volM m A P) (S T) = (distribHaarChar k (ϖ ^ n) : ENNReal) ^ (Fintype.card A * P.card) := by
      intro T
      simp only [volM, S]
      refine (Measure.pi_pi (fun _ : A => Measure.pi fun _ : P => m)
        (fun i => Set.univ.pi fun j => (fun x => x + -liftRes T i j) ⁻¹' cball (ϖ ^ n))).trans ?_
      simp only [Measure.pi_pi, measure_preimage_add_right, hcb, Finset.prod_const, Finset.card_univ,
        Fintype.card_coe, ← pow_mul]
      rw [mul_comm]
    have hnabs : nabs k (ϖ ^ n) = ((resCard k : ℝ) ^ n)⁻¹ := by
      have h1 : ∀ l : ℕ, nabs k (ϖ ^ l) = nabs k ϖ ^ l := by
        intro l; induction l with
        | zero => simp [nabs_one]
        | succ l ih => rw [pow_succ, nabs_mul, ih, pow_succ]
      rw [h1, nabs_uniformiser hϖ.irreducible (x := ϖ) rfl, inv_pow]
    have hvol : ∀ T, (volM m A P).real (S T) = ((resCard k : ℝ) ^ (n * Fintype.card A * P.card))⁻¹ := by
      intro T
      rw [Measure.real, hvolE, ENNReal.toReal_pow, ENNReal.coe_toReal]
      have : ((distribHaarChar k (ϖ ^ n) : NNReal) : ℝ) = nabs k (ϖ ^ n) := rfl
      rw [this, hnabs, inv_pow, ← pow_mul, mul_assoc]
    have hfin : ∀ T, (volM m A P) (S T) ≠ ⊤ := fun T => by
      rw [hvolE]; exact ENNReal.pow_ne_top ENNReal.coe_ne_top
    have hpt : ∀ U, F U = ∑ T, (S T).indicator (fun _ => F (liftRes T)) U := by
      intro U
      by_cases hU : ∀ i j, U i j ∈ 𝒪[k]
      · let T0 : A → P → Res k n := fun i j => Ideal.Quotient.mk _ ⟨U i j, hU i j⟩
        have key1 : ∀ T i j, U i j - liftRes T i j ∈ cball (ϖ ^ n) ↔ T i j = T0 i j := by
          intro T i j
          have e : T i j = T0 i j ↔ (⟨U i j, hU i j⟩ - Quotient.out (T i j) : 𝒪[k]) ∈
              IsLocalRing.maximalIdeal 𝒪[k] ^ n := by
            conv_lhs => rw [← Ideal.Quotient.mk_out (T i j)]
            rw [eq_comm]
            exact Ideal.Quotient.eq
          rw [e, mem_maxIdeal_pow_iff hϖ]
          rfl
        have key : ∀ T, U ∈ S T ↔ T = T0 := by
          intro T
          rw [hmemS]
          simp only [key1]
          exact ⟨fun h => funext fun i => funext fun j => h i j, fun h i j => by rw [h]⟩
        rw [Finset.sum_eq_single T0 (fun T _ hT => Set.indicator_of_notMem (fun h => hT ((key T).1 h)) _)
          (by simp), Set.indicator_of_mem ((key T0).2 rfl)]
        have hd := (hmemS T0 U).1 ((key T0).2 rfl)
        simp only [hF]
        rw [natDatum_setCols_eq hΦ P Y hd, psi_pairCols_eq hψ P hY hd]
      · push_neg at hU
        obtain ⟨i, j, hij⟩ := hU
        have hz : F U = 0 := by
          simp only [hF]
          rw [hΦ.1 _ ?_, zero_mul]
          intro hm'
          apply hij
          have := mem_matLat_stdLat.1 hm' i j
          simpa [setCols, j.2] using this
        rw [hz]
        symm
        refine Finset.sum_eq_zero fun T _ => Set.indicator_of_notMem (fun h => hij ?_) _
        have h1 : valuation k (U i j - liftRes T i j) ≤ valuation k ((ϖ ^ n : kˣ) : k) := (hmemS T U).1 h i j
        have h2 : U i j - liftRes T i j ∈ 𝒪[k] := by
          rw [Valuation.mem_integer_iff]
          refine le_trans h1 ?_
          rw [Units.val_pow_eq_pow_val, map_pow]
          exact pow_le_one' (hϖ.mem) n
        simpa using add_mem h2 (liftRes_mem T i j)
    rw [show F = fun U => ∑ T, (S T).indicator (fun _ => F (liftRes T)) U from funext hpt]
    rw [integral_finsetSum _ (fun T _ => (integrable_indicator_iff (hS T)).2
      (integrableOn_const (lt_top_iff_ne_top.2 (hfin T)).ne)), Finset.mul_sum]
    refine Finset.sum_congr rfl fun T _ => ?_
    rw [integral_indicator_const _ (hS T), hvol, Complex.real_smul]
    push_cast
    rfl
  · rw [fourierInt_eq_pi]
    refine GlobalTheory.SplitWeil.FourierPi.fourier_eq_zero_pi _ hψ (s := ϖ ^ n) (fun t ht x => ?_) ?_
    · exact natDatum_setCols_eq hΦ P Y fun i j => by simpa using ht ⟨i, j⟩ trivial
    · intro hmem
      apply hY
      intro i j hj
      have h1 : valuation k (Y i j) ≤ valuation k ((((1 : kˣ) * (ϖ ^ n)⁻¹ : kˣ)) : k) := hmem ⟨i, ⟨j, hj⟩⟩ trivial
      rw [one_mul, Units.val_inv_eq_inv_val, map_inv₀] at h1
      rw [Valuation.mem_integer_iff, map_mul]
      calc valuation k ((ϖ ^ n : kˣ) : k) * valuation k (Y i j)
          ≤ valuation k ((ϖ ^ n : kˣ) : k) * (valuation k ((ϖ ^ n : kˣ) : k))⁻¹ := mul_le_mul' le_rfl h1
        _ = 1 := mul_inv_cancel₀ h0.ne'

end GlobalTheory.ColFourier
end
end
end


@[expose] public section

namespace GlobalTheory.ColFourier
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitFlip
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [MeasurableSpace k] [BorelSpace k]
variable {A C : Type} [Fintype A] [DecidableEq C]

theorem fourierInt_add (ψ : AddChar k Circle) (m : Measure k) (hψ : HasConductor ψ 1) (hm : IsUnitVol m)
    (P : Finset C) {Ξ₁ Ξ₂ : Matrix A C k → ℂ} (h₁ : Ξ₁ ∈ SB (Matrix A C k)) (h₂ : Ξ₂ ∈ SB (Matrix A C k)) :
    fourierInt ψ m P (Ξ₁ + Ξ₂) = fourierInt ψ m P Ξ₁ + fourierInt ψ m P Ξ₂ := by
  haveI := hm.1
  haveI := secondCountable k
  haveI := isAddHaarMeasure_volM m (A := A) P
  haveI : BorelSpace (Matrix A P k) := inferInstanceAs (BorelSpace (A → P → k))
  have hi : ∀ Ξ ∈ SB (Matrix A C k), ∀ Y : Matrix A C k,
      Integrable (fun U => Ξ (setCols P Y U) * (ψ (pairCols P Y U) : ℂ)) (volM m A P) := by
    intro Ξ hΞ Y
    have hg := comp_setCols_mem_SB hΞ P Y
    have hc : Continuous fun U : Matrix A P k => pairCols P Y U := by unfold pairCols; fun_prop
    exact (hg.1.continuous.integrable_of_hasCompactSupport hg.2).mul_bdd (c := 1)
      ((continuous_subtype_val.comp (hψ.continuous.comp hc)).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun U => (Circle.norm_coe _).le)
  funext Y
  simp only [fourierInt, Pi.add_apply, add_mul]
  exact integral_add (hi _ h₁ Y) (hi _ h₂ Y)

theorem fourierInt_shift [Fintype C] (ψ : AddChar k Circle) (m : Measure k) (hm : IsUnitVol m) (P : Finset C)
    (Ξ : Matrix A C k → ℂ) (T R : Matrix A C k) (hT : ∀ r, ∀ s ∉ P, T r s = 0) (hR : ∀ r, ∀ s ∈ P, R r s = 0) :
    fourierInt ψ m P (fun S => (ψ (GlobalTheory.FlipMatch.pairM S R) : ℂ) * Ξ (S + T)) =
      fun Z => (ψ (GlobalTheory.FlipMatch.pairM Z R - GlobalTheory.FlipMatch.pairM Z T) : ℂ) * fourierInt ψ m P Ξ Z := by
  haveI := hm.1
  haveI := isAddHaarMeasure_volM m (A := A) P
  haveI : MeasurableAdd (Matrix A P k) := inferInstanceAs (MeasurableAdd (A → P → k))
  funext Z
  unfold fourierInt
  set Tp := restrictCols P T
  rw [← integral_add_right_eq_self (μ := volM m A P)
    (fun U => Ξ (setCols P Z U) * (ψ (pairCols P Z U) : ℂ)) Tp, ← integral_const_mul]
  congr 1
  funext U
  have ea : GlobalTheory.FlipMatch.pairM (setCols P Z U) R = GlobalTheory.FlipMatch.pairM Z R := by
    simp only [GlobalTheory.FlipMatch.pairM]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    by_cases h : j ∈ P
    · simp [setCols, h, hR i j h]
    · simp [setCols, h]
  have eb : setCols P Z U + T = setCols P Z (U + Tp) := by
    ext i j
    by_cases h : j ∈ P
    · simp [setCols, h, Tp, restrictCols]
    · simp [setCols, h, hT i j h]
  have ec : pairCols P Z (U + Tp) = pairCols P Z U + GlobalTheory.FlipMatch.pairM Z T := by
    simp only [pairCols, GlobalTheory.FlipMatch.pairM, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_subset (Finset.subset_univ P) (fun j _ hj => by simp [hT i j hj]),
      ← Finset.sum_coe_sort P, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp [Tp, restrictCols]
    ring
  have key : (ψ (GlobalTheory.FlipMatch.pairM Z R - GlobalTheory.FlipMatch.pairM Z T) : ℂ) *
      ψ (pairCols P Z U + GlobalTheory.FlipMatch.pairM Z T) = ψ (GlobalTheory.FlipMatch.pairM Z R) * ψ (pairCols P Z U) := by
    rw [← Circle.coe_mul, ← Circle.coe_mul, ← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul]
    congr 2; ring
  dsimp only
  rw [ea, eb, ec]
  linear_combination (Ξ (setCols P Z (U + Tp))) * key.symm

end GlobalTheory.ColFourier

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA IsDatumB mulG colV adjV₁)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple Acts SInf At piW psiLoc chrW)

open GlobalTheory.FlipMatch

theorem GlobalTheory.ColFourier.exists_blockFourier : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (A : Type) [Fintype A] [DecidableEq A] (C : Type) [Fintype C] [DecidableEq C] (ψ : AddChar k Circle) (ϖ : kˣ) (P : Finset C), IsUnif ϖ → HasConductor ψ 1 →
    ∃ 𝓕 : (Matrix A C k → ℂ) →ₗ[ℂ] (Matrix A C k → ℂ), Set.BijOn 𝓕 (GlobalTheory.WeilM.SB (Matrix A C k) : Set _) (GlobalTheory.WeilM.SB (Matrix A C k) : Set _) ∧
      (∀ Ξ ∈ GlobalTheory.WeilM.SB (Matrix A C k), ∀ T R : Matrix A C k, (∀ r, ∀ s ∈ P, T r s = 0) → (∀ r, ∀ s ∉ P, R r s = 0) →
        𝓕 (fun S => (ψ (pairM S R) : ℂ) * Ξ (S + T)) = fun Z => 𝓕 Ξ (Z + (T + R))) ∧
      (∀ Ξ ∈ GlobalTheory.WeilM.SB (Matrix A C k), ∀ T R : Matrix A C k, (∀ r, ∀ s ∉ P, T r s = 0) → (∀ r, ∀ s ∈ P, R r s = 0) →
        𝓕 (fun S => (ψ (pairM S R) : ℂ) * Ξ (S + T)) = fun Z => (ψ (pairM Z R - pairM Z T) : ℂ) * 𝓕 Ξ Z) ∧
      ∀ Ξ ∈ GlobalTheory.WeilM.SB (Matrix A C k), ∀ n, IsNatDatum ϖ n (𝓕 Ξ) → fourierSum ψ⁻¹ ϖ n P (𝓕 Ξ) = Ξ := by
  intro k _ _ _ _ A _ _ C _ _ ψ ϖ P hϖ hψ
  borelize k
  obtain ⟨m, hm⟩ := exists_isUnitVol k
  haveI := hm.1
  have hψ' : HasConductor ψ⁻¹ 1 := GlobalTheory.ColFourier.hasConductor_inv hψ
  have hSB := fun (χ : AddChar k Circle) (hχ : HasConductor χ 1) (Ξ : Matrix A C k → ℂ)
    (h : Ξ ∈ SB (Matrix A C k)) => _root_.GlobalTheory.ColFourier.fourierInt_mem_SB k A C χ m hχ hm P Ξ h
  have hInv := fun (χ : AddChar k Circle) (hχ : HasConductor χ 1) (Ξ : Matrix A C k → ℂ)
    (h : Ξ ∈ SB (Matrix A C k)) => _root_.GlobalTheory.ColFourier.fourierInt_inv_fourierInt k A C χ m hχ hm P Ξ h
  let L : SB (Matrix A C k) →ₗ[ℂ] (Matrix A C k → ℂ) :=
    { toFun := fun Ξ => fourierInt ψ m P Ξ
      map_add' := fun a b => GlobalTheory.ColFourier.fourierInt_add ψ m hψ hm P a.2 b.2
      map_smul' := fun c a => by
        funext Y
        simp only [SetLike.val_smul, RingHom.id_apply, Pi.smul_apply, smul_eq_mul, fourierInt]
        rw [← integral_const_mul]
        congr 1; funext U; ring }
  obtain ⟨F, hF⟩ := LinearMap.exists_extend L
  have hFe : ∀ Ξ ∈ SB (Matrix A C k), F Ξ = fourierInt ψ m P Ξ := fun Ξ h => LinearMap.congr_fun hF ⟨Ξ, h⟩
  have hmod : ∀ Ξ ∈ SB (Matrix A C k), ∀ T R : Matrix A C k,
      (fun S => (ψ (pairM S R) : ℂ) * Ξ (S + T)) ∈ SB (Matrix A C k) := by
    intro Ξ hΞ T R
    have hc : Continuous fun S : Matrix A C k => pairM S R := by unfold pairM; fun_prop
    refine ⟨((hψ.isLocallyConstant.comp_continuous hc).comp (fun z : Circle => (z : ℂ))).mul
      (hΞ.1.comp_continuous (continuous_add_const T)), ?_⟩
    exact (hΞ.2.comp_homeomorph (Homeomorph.addRight T)).mul_left
  refine ⟨F, ⟨fun Ξ h => ?_, fun Ξ₁ h₁ Ξ₂ h₂ he => ?_, fun Ψ hΨ => ?_⟩, fun Ξ hΞ T R hT hR => ?_,
    fun Ξ hΞ T R hT hR => ?_, fun Ξ hΞ n hn => ?_⟩
  · show F Ξ ∈ SB (Matrix A C k)
    rw [hFe Ξ h]; exact hSB ψ hψ Ξ h
  · rw [hFe _ h₁, hFe _ h₂] at he
    rw [← hInv ψ hψ Ξ₁ h₁, ← hInv ψ hψ Ξ₂ h₂, he]
  · have h1 := hSB ψ⁻¹ hψ' Ψ hΨ
    refine ⟨_, h1, ?_⟩
    rw [hFe _ h1]
    simpa only [inv_inv] using hInv ψ⁻¹ hψ' Ψ hΨ
  · rw [hFe _ (hmod Ξ hΞ T R), hFe _ hΞ]
    funext Z
    unfold fourierInt
    congr 1
    funext U
    have e1 : setCols P Z U + T = setCols P (Z + (T + R)) U := by
      ext i j
      by_cases h : j ∈ P
      · simp [setCols, h, hT i j h]
      · simp [setCols, h, hR i j h]
    have e2 : pairM (setCols P Z U) R + pairCols P Z U = pairCols P (Z + (T + R)) U := by
      simp only [pairM, pairCols, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Finset.sum_subset (Finset.subset_univ P) (fun j _ hj => by simp [setCols, hj, hR i j hj]),
        ← Finset.sum_coe_sort P, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp [setCols, j.2, hT i j j.2]
      ring
    dsimp only
    rw [e1, ← e2, AddChar.map_add_eq_mul, Circle.coe_mul]
    ring
  · rw [hFe _ (hmod Ξ hΞ T R), hFe _ hΞ]
    exact GlobalTheory.ColFourier.fourierInt_shift ψ m hm P Ξ T R hT hR
  · rw [hFe _ hΞ] at hn ⊢
    rw [← GlobalTheory.ColFourier.fourierInt_eq_fourierSum k A C ψ⁻¹ m ϖ hϖ hψ' hm P n _ hn]
    exact hInv ψ hψ Ξ hΞ
