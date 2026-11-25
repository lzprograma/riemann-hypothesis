module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CombAtSingleZero
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSelfDualCLatFrame
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.AddNsmulResidueAssoc
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ThetaAtEqSumHeisOfFourierSum
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsNatMulSplitHalfLatticeCoordinatesIntegral
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsNsmulMemHomLatticeOfIntegralFrameCoords
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemHomLatticeCompletionIffSupportedMaps
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PlacewiseToAdelicDecompositionForall
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SchwartzBruhatMatrixUniformlyLocallyConstantBoun
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasWeil
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
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceBaseVacuumDatumExistsUnique

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing
open scoped TensorProduct Pointwise

namespace GlobalTheory.FinPl.CombProof

open GlobalTheory.PlaceModel GlobalTheory.PlaceDatum

section Comb

variable {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D)

theorem comb_eq_sum (c : WO S T →₀ ℂ) (f : WO S T → ℂ) :
    comb ψ S T c f = c.sum fun u a => a • heisO ψ S T u f := rfl

theorem comb_zero_left (f : WO S T → ℂ) : comb ψ S T 0 f = 0 := by
  rw [comb_eq_sum, Finsupp.sum_zero_index]

theorem comb_add_left (c₁ c₂ : WO S T →₀ ℂ) (f : WO S T → ℂ) :
    comb ψ S T (c₁ + c₂) f = comb ψ S T c₁ f + comb ψ S T c₂ f := by
  rw [comb_eq_sum, comb_eq_sum, comb_eq_sum]
  exact Finsupp.sum_add_index' (fun i => zero_smul ℂ (heisO ψ S T i f)) fun i a b => add_smul a b (heisO ψ S T i f)

theorem comb_smul_left (a : ℂ) (c : WO S T →₀ ℂ) (f : WO S T → ℂ) :
    comb ψ S T (a • c) f = a • comb ψ S T c f := by
  rw [comb_eq_sum, comb_eq_sum, Finsupp.sum_smul_index' (fun i => zero_smul ℂ (heisO ψ S T i f)), Finsupp.smul_sum]
  simp only [smul_smul, smul_eq_mul]

theorem comb_single (u : WO S T) (a : ℂ) (f : WO S T → ℂ) :
    comb ψ S T (Finsupp.single u a) f = a • heisO ψ S T u f := by
  rw [comb_eq_sum, Finsupp.sum_single_index (zero_smul ℂ (heisO ψ S T u f))]

variable {S T} {P : Pl D → Prop}

theorem combAt_zero : CombAt P (0 : WO S T →₀ ℂ) := fun u hu => by simp at hu

open Classical in
theorem combAt_add {c₁ c₂ : WO S T →₀ ℂ} (h₁ : CombAt P c₁) (h₂ : CombAt P c₂) : CombAt P (c₁ + c₂) :=
  fun u hu => (Finset.mem_union.1 (Finsupp.support_add hu)).elim (h₁ u) (h₂ u)

theorem combAt_smul (a : ℂ) {c : WO S T →₀ ℂ} (h : CombAt P c) : CombAt P (a • c) :=
  fun u hu => h u (Finsupp.support_smul hu)

theorem combAt_single {u : WO S T} (hu : MxAt P u) (a : ℂ) : CombAt P (Finsupp.single u a) := fun u' hu' => by
  rw [Finset.mem_singleton.1 (Finsupp.support_single_subset hu')]
  exact hu

end Comb

section Rd
variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {p : SplitPt D k} {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {S T : HSp D}

theorem rd_add (α : Frame p S n') (β : Frame p T n) (t s : WO S T) : rd α β (t + s) = rd α β t + rd α β s := by
  unfold rd
  rw [Matrix.map_add p.pr (map_add p.pr), Matrix.mul_add, Matrix.add_mul]

theorem rd_nsmul (α : Frame p S n') (β : Frame p T n) (N : ℕ) (t : WO S T) : rd α β (N • t) = (N : k) • rd α β t := by
  unfold rd
  have : (N • t).map p.pr = (N : k) • t.map p.pr := by
    ext i j
    simp [Matrix.map_apply, nsmul_eq_mul, map_mul, map_natCast]
  rw [this, Matrix.mul_smul, Matrix.smul_mul]

end Rd

theorem isSBHalf_extFun : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : SplitPt D k) (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (S T : HSp D)
    (α : Frame p S n') (β : Frame p T n) (LS : Lat S) (LT : Lat T), IsSelfDualC S LS → IsSelfDualC T LT →
    ∀ Ψ ∈ SB (Matrix n n' k), IsSBHalf p.e (latO S T (LS : Set _) (LT : Set _) (· = p.v)) (extFun α β Ψ) := by
  apply _root_.GlobalTheory.FinPl.OverProof.isSBHalf_extFun <;> assumption

variable {D : D7}

theorem dualPair {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {S T : HSp D} {LS : Lat S} {LT : Lat T}
    (hS : IsSelfDualC S LS) (hT : IsSelfDualC T LT) {e : AE D} {v : Pl D} (hs : IsSplitIdem D e) {ε : AF D.host.F}
    (hε : IsPlaceIdem D v ε) (heq : e + cA D e = algebraMap (AF D.host.F) (AE D) ε) :
    let Λ := latO S T (LS : Set _) (LT : Set _) (· = v)
    (∀ u ∈ Λ ⊓ half S T e, ∀ y ∈ Λ ⊓ half S T (cA D e), ψ (symplO S T u y) = 1) ∧
    (∀ x ∈ half S T e, (∀ y ∈ Λ ⊓ half S T (cA D e), ψ (symplO S T x y) = 1) → x ∈ Λ ⊓ half S T e) ∧
    (∀ y ∈ half S T (cA D e), (∀ u ∈ Λ ⊓ half S T e, ψ (symplO S T u y) = 1) → y ∈ Λ ⊓ half S T (cA D e)) ∧
    (∀ k : ℕ, 0 < k → ∃ R : Set (WO S T), R.Finite ∧ ∀ t ∈ Λ ⊓ half S T e, ∃ r ∈ R, ∃ u ∈ Λ ⊓ half S T e, t = r + k • u) ∧
    (∀ y ∈ half S T (cA D e), ∃ k : ℕ, 0 < k ∧ k • y ∈ Λ) := by
  apply _root_.GlobalTheory.FinPl.OverProof.dualPair <;> assumption

theorem extFun_comb : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (α : Frame p S n') (β : Frame p T n) (LS : Lat S) (LT : Lat T), IsSelfDualC S LS → IsSelfDualC T LT → ∀ Ψ ∈ SB (Matrix n n' k), ∃ c : WO S T →₀ ℂ, CombAt (· = p.v) c ∧ ∀ (f₀ : WO S T → ℂ) (Tm : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ)), IsPlaceModel ψ (symplO S T) (heisO ψ S T) p.e (latO S T (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) (· = p.v)) 1 f₀ Tm → Tm (extFun α β Ψ) = comb ψ S T c f₀ := by
  classical
  intro D k _ _ _ _ p n n' _ _ _ _ ψ hψ S T α β LS LT hS hT Ψ hΨ
  obtain ⟨ε, hε, heq⟩ := p.above
  have hs := p.split
  have he := hs.1
  have hec := hs.2.1
  have he' : cA D p.e * cA D p.e = cA D p.e := by rw [← map_mul, he]
  have heε : algebraMap (AF D.host.F) (AE D) ε * p.e = p.e := by rw [← heq]; linear_combination he + hec
  have heε' : algebraMap (AF D.host.F) (AE D) ε * cA D p.e = cA D p.e := by
    rw [← heq]; linear_combination he' + hec
  obtain ⟨hLL', hX, -, hfin, hden⟩ := dualPair hψ hS hT hs hε heq
  set Λ := latO S T (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) (· = p.v) with hΛ
  have hΦ := isSBHalf_extFun D k p n n' S T α β LS LT hS hT Ψ hΨ
  have tf : ∀ k : ℕ, 0 < k → Function.Injective fun t : WO S T => k • t := fun k hk a b hab => by
    rw [← inv_smul_nsmul S T hk a, ← inv_smul_nsmul S T hk b]
    exact congrArg _ hab
  have hb : IsBichar (fun x y : WO S T => ψ (symplO S T x y)) := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro a b y; rw [symplO_add_left, AddChar.map_add_eq_mul]
    · intro a b y; rw [symplO_add_right, AddChar.map_add_eq_mul]
    · intro y; rw [symplO_zero_left, AddChar.map_zero_eq_one]
    · intro y; rw [symplO_zero_right, AddChar.map_zero_eq_one]
  have hm : extFun α β Ψ ∈
      waveSpan (fun x y : WO S T => ψ (symplO S T x y)) (half S T p.e) (half S T (cA D p.e)) (Λ ⊓ half S T p.e) := by
    obtain ⟨h1, k, hk, h2, h3⟩ := hΦ
    exact mem_waveSpan hb inf_le_right inf_le_right hLL' hX (half_div S T p.e) (half_div S T _) tf hfin _
      (fun t ht => (isHalf_iff S T).1 (h1 t ht)) k hk (fun u hu => h2 u hu.1 ((isHalf_iff S T).2 hu.2))
      fun t ht => ⟨h3 t ht, (half S T p.e).nsmul_mem ((isHalf_iff S T).1 (h1 t ht)) _⟩

  have hεid : algebraMap (AF D.host.F) (AE D) ε ∈ idAt D (· = p.v) := by
    obtain ⟨a, rfl, -, h0⟩ := id hε
    exact LatMem.tmul_mem_idAt (fun w hw => h0 w hw) 1
  have hsupp : ∀ {e' : AE D}, algebraMap (AF D.host.F) (AE D) ε * e' = e' → ∀ x ∈ half S T e', ∀ i j,
      x i j ∈ idAt D (· = p.v) := fun {e'} h x hx i j => by
    have h1 := (isHalf_iff S T).2 hx i j
    have : x i j = algebraMap (AF D.host.F) (AE D) ε * x i j := by
      linear_combination (algebraMap (AF D.host.F) (AE D) ε - 1) * h1 - x i j * h
    rw [this]
    exact Ideal.mul_mem_right _ _ hεid
  have hmx : ∀ x ∈ half S T p.e, ∀ y ∈ half S T (cA D p.e), MxAt (· = p.v) (x + y) := fun x hx y hy i j => by
    rw [Matrix.add_apply]
    exact add_mem (hsupp heε x hx i j) (hsupp heε' y hy i j)
  generalize extFun α β Ψ = Φ at hm
  induction hm using Submodule.span_induction with
  | mem _ hh =>
    obtain ⟨x, hx, y, hy, rfl⟩ := hh
    refine ⟨Finsupp.single (x + y) (ψ (symplOH S T x y)), combAt_single (hmx x hx y hy) _, fun f₀ Tm h => ?_⟩
    have s0 := GlobalTheory.isSBHalf_halfInd p.e Λ
    have s1 : IsSBHalf p.e Λ fun t => ψ (symplO S T t y) * halfInd p.e Λ t := by
      obtain ⟨k, hk, hk'⟩ := hden y hy
      obtain ⟨a1, k', hk1, a2, a3⟩ := s0
      refine ⟨fun t ht => a1 t (right_ne_zero_of_mul ht), k * k', Nat.mul_pos hk hk1, fun u hu hh t => ?_,
        fun t ht => ?_⟩
      · have e1 : halfInd p.e Λ (t + (k * k') • u) = halfInd p.e Λ t := by
          rw [mul_nsmul]
          exact a2 _ (nsmul_mem hu k) ((isHalf_iff S T).2 (nsmul_mem ((isHalf_iff S T).1 hh) k)) t
        have e2 : ψ (symplO S T ((k * k') • u) y) = 1 := by
          rw [mul_nsmul']
          exact (hb.nsmul k _ y).trans
            (hLL' _ (nsmul_mem (AddSubgroup.mem_inf.2 ⟨hu, (isHalf_iff S T).1 hh⟩) k') _ ⟨hk', nsmul_mem hy k⟩)
        simp only [e1, symplO_add_left, AddChar.map_add_eq_mul, e2, mul_one]
      · rw [mul_nsmul']
        exact nsmul_mem (a3 t (right_ne_zero_of_mul ht)) k
    have e1 : wave (fun x y : WO S T => ψ (symplO S T x y)) (Λ ⊓ half S T p.e) x y =
        fun t => (fun t => ψ (symplO S T t y) * halfInd p.e Λ t) (t + x) := by
      rw [halfInd_eq_ind]; rfl
    have v1 := h.vac
    rw [one_smul] at v1
    rw [e1, h.trans _ s1 x ((isHalf_iff S T).2 hx), h.modul _ s0 y ((isHalf_iff S T).2 hy), v1, comb_single]
    exact heisL_heisL S T ψ x y f₀
  | zero => exact ⟨0, combAt_zero, fun f₀ Tm _ => by rw [LinearMap.map_zero, comb_zero_left]⟩
  | add f g _ _ hf hg =>
    obtain ⟨c₁, hc₁, h₁⟩ := hf
    obtain ⟨c₂, hc₂, h₂⟩ := hg
    exact ⟨c₁ + c₂, combAt_add hc₁ hc₂, fun f₀ Tm h => by
      rw [LinearMap.map_add (f := _), h₁ f₀ Tm h, h₂ f₀ Tm h, comb_add_left]⟩
  | smul a f _ hf =>
    obtain ⟨c, hc, h₁⟩ := hf
    exact ⟨a • c, combAt_smul a hc, fun f₀ Tm h => by rw [LinearMap.map_smul, h₁ f₀ Tm h, comb_smul_left]⟩

end GlobalTheory.FinPl.CombProof
