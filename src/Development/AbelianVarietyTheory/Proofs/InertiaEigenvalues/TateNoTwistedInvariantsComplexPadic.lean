module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfTateTwistInvariantFiniteExtension
public import Formalism.SharpRestriction.LevelLetterCocycles.NormOfVOne
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.CrystallinePeriods.RingBasics
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AxSenTateComplexPadicFixedClosure
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N
open scoped Formalism.Per

noncomputable section
namespace GlobalTheory.TateChiQ
open GlobalTheory.MemLoc
open GlobalTheory.MemLoc.TateTwist (Fz Vz bound decomp Vz_stable le_natDegree pow_mem_Fz σC_algebraMap)
variable {l : ℕ} [Fact l.Prime]

theorem zeta_pow (ζ : ℕ → Om l) (χ : GQ l →* ℤ_[l]ˣ) (cZ0 : ζ 0 = 1) (cZs : ∀ m, ζ (m + 1) ^ l = ζ m) (cZ1 : ζ 1 ≠ 1)
    (cχ : ∀ (g : GQ l) (m : ℕ) (x : Om l), x ^ (l ^ m) = 1 → g x = x ^ (PadicInt.toZModPow m (χ g : ℤ_[l])).val) (n m : ℕ) : ζ (n + m) ^ l ^ m = ζ n :=
  GlobalTheory.MemLoc.TateTwist.zeta_pow_of ⟨ζ, χ, cZ0, cZs, cZ1, cχ⟩ n m

theorem zeta_prim (ζ : ℕ → Om l) (χ : GQ l →* ℤ_[l]ˣ) (cZ0 : ζ 0 = 1) (cZs : ∀ m, ζ (m + 1) ^ l = ζ m) (cZ1 : ζ 1 ≠ 1)
    (cχ : ∀ (g : GQ l) (m : ℕ) (x : Om l), x ^ (l ^ m) = 1 → g x = x ^ (PadicInt.toZModPow m (χ g : ℤ_[l])).val) (n : ℕ) : IsPrimitiveRoot (ζ n) (l ^ n) :=
  GlobalTheory.MemLoc.TateTwist.zeta_prim_of ⟨ζ, χ, cZ0, cZs, cZ1, cχ⟩ n

theorem Fz_mono (ζ : ℕ → Om l) (χ : GQ l →* ℤ_[l]ˣ) (cZ0 : ζ 0 = 1) (cZs : ∀ m, ζ (m + 1) ^ l = ζ m) (cZ1 : ζ 1 ≠ 1)
    (cχ : ∀ (g : GQ l) (m : ℕ) (x : Om l), x ^ (l ^ m) = 1 → g x = x ^ (PadicInt.toZModPow m (χ g : ℤ_[l])).val) : Monotone fun n => Fz (ζ n) :=
  GlobalTheory.MemLoc.TateTwist.Fz_mono_of ⟨ζ, χ, cZ0, cZs, cZ1, cχ⟩

theorem chi_eq_one (ζ : ℕ → Om l) (χ : GQ l →* ℤ_[l]ˣ) (cZ0 : ζ 0 = 1) (cZs : ∀ m, ζ (m + 1) ^ l = ζ m) (cZ1 : ζ 1 ≠ 1)
    (cχ : ∀ (g : GQ l) (m : ℕ) (x : Om l), x ^ (l ^ m) = 1 → g x = x ^ (PadicInt.toZModPow m (χ g : ℤ_[l])).val) (g : GQ l) (hg : g ∈ (⨆ n, Fz (ζ n)).fixingSubgroup) : χ g = 1 :=
  GlobalTheory.MemLoc.TateTwist.chi_eq_one_of ⟨ζ, χ, cZ0, cZs, cZ1, cχ⟩ g hg

theorem exists_gamma (ζ : ℕ → Om l) (χ : GQ l →* ℤ_[l]ˣ) (cZ0 : ζ 0 = 1) (cZs : ∀ m, ζ (m + 1) ^ l = ζ m) (cZ1 : ζ 1 ≠ 1)
    (cχ : ∀ (g : GQ l) (m : ℕ) (x : Om l), x ^ (l ^ m) = 1 → g x = x ^ (PadicInt.toZModPow m (χ g : ℤ_[l])).val) (n : ℕ) (hn : 1 ≤ n) (j : ℕ) (hj : j ≠ 0) :
    ∃ g ∈ (Fz (ζ n)).fixingSubgroup, (χ g : ℤ_[l]) ^ j ≠ 1 :=
  GlobalTheory.MemLoc.TateTwist.exists_gamma_of ⟨ζ, χ, cZ0, cZs, cZ1, cχ⟩ n hn j hj

theorem estimate (ζ : ℕ → Om l) (χ : GQ l →* ℤ_[l]ˣ) (cZ0 : ζ 0 = 1) (cZs : ∀ m, ζ (m + 1) ^ l = ζ m) (cZ1 : ζ 1 ≠ 1)
    (cχ : ∀ (g : GQ l) (m : ℕ) (x : Om l), x ^ (l ^ m) = 1 → g x = x ^ (PadicInt.toZModPow m (χ g : ℤ_[l])).val) (n : ℕ) (hn : 1 ≤ n) (g : GQ l) (hg : g ∈ (Fz (ζ n)).fixingSubgroup)
    (c : ℚ_[l]) (y₀ y : Om l) (h₀ : y₀ ∈ Fz (ζ n)) (hy : y ∈ ⨆ k, Fz (ζ k)) :
    ∃ b : Om l, ‖(l : Om l)‖ * ‖b - y₀‖ ≤ ‖y - y₀‖ ∧
      ‖(l : Om l)‖ * (‖c - 1‖ * ‖b‖) ≤ ‖g y * algebraMap _ _ c - y‖ :=
  GlobalTheory.MemLoc.TateTwist.estimate_of ⟨ζ, χ, cZ0, cZs, cZ1, cχ⟩ n hn g hg c y₀ y h₀ hy

theorem full (ζ : ℕ → Om l) (χ : GQ l →* ℤ_[l]ˣ) (cZ0 : ζ 0 = 1) (cZs : ∀ m, ζ (m + 1) ^ l = ζ m) (cZ1 : ζ 1 ≠ 1)
    (cχ : ∀ (g : GQ l) (m : ℕ) (x : Om l), x ^ (l ^ m) = 1 → g x = x ^ (PadicInt.toZModPow m (χ g : ℤ_[l])).val) (i : ℤ) (x : ℂ_[l]) (hi : i ≠ 0)
    (hx : ∀ g : GQ l, Per.σC g x * (algebraMap ℚ_[l] ℂ_[l] ((χ g : ℤ_[l]) : ℚ_[l])) ^ i = x) : x = 0 :=
  GlobalTheory.MemLoc.TateTwist.full_of ⟨ζ, χ, cZ0, cZs, cZ1, cχ⟩ i x hi hx

def chiZ (P : LocPrime l) : GQ l →* ℤ_[l]ˣ where
  toFun g := PadicInt.mkUnits (Formalism.MainNotions.InvariantsGenerators.InvariantsFromGenerators.chiQ_norm P g)
  map_one' := Units.ext (Subtype.ext (by simp [PadicInt.mkUnits]))
  map_mul' g h := Units.ext (Subtype.ext (by simp [PadicInt.mkUnits]; rfl))

theorem chiZ_coe (P : LocPrime l) (g : GQ l) :
    (((chiZ P g : ℤ_[l]ˣ) : ℤ_[l]) : ℚ_[l]) = ((P.χQ g : ℚ_[l]ˣ) : ℚ_[l]) := by
  simp [chiZ, PadicInt.mkUnits]

theorem chiZ_cyc (P : LocPrime l) (g : GQ l) (m : ℕ) (x : Om l) (hx : x ^ (l ^ m) = 1) :
    g x = x ^ (PadicInt.toZModPow m (chiZ P g : ℤ_[l])).val := by
  obtain ⟨a, ha, hga⟩ := P.χQ_cyc g m x hx
  have h1 : ‖(chiZ P g : ℤ_[l]) - (a : ℤ_[l])‖ ≤ (l : ℝ) ^ (-(m : ℤ)) := by
    rw [PadicInt.norm_def, PadicInt.coe_sub, chiZ_coe, PadicInt.coe_natCast]
    exact ha
  have h2 := (PadicInt.norm_le_pow_iff_mem_span_pow _ _).1 h1
  rw [← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub, sub_eq_zero, map_natCast] at h2
  rw [h2, ZMod.val_natCast, hga, ← pow_eq_pow_mod a hx]

theorem twist_fin (ζ : ℕ → Om l) (χ : GQ l →* ℤ_[l]ˣ) (cZ0 : ζ 0 = 1) (cZs : ∀ m, ζ (m + 1) ^ l = ζ m) (cZ1 : ζ 1 ≠ 1)
    (cχ : ∀ (g : GQ l) (m : ℕ) (x : Om l), x ^ (l ^ m) = 1 → g x = x ^ (PadicInt.toZModPow m (χ g : ℤ_[l])).val) :
    ∀ (K : FinExt l) (i : ℤ) (x : ℂ_[l]), i ≠ 0 → (∀ g ∈ GK K, Per.σC g x * (algebraMap ℚ_[l] ℂ_[l] ((χ g : ℤ_[l]) : ℚ_[l])) ^ i = x) → x = 0 :=
  GlobalTheory.MemLoc.TateTwist.tate_twist_invariants_of ⟨ζ, χ, cZ0, cZs, cZ1, cχ⟩

end GlobalTheory.TateChiQ

namespace GlobalTheory.TateChiQ
open GlobalTheory.MemLoc.TateTwist (σC_algebraMap)

theorem tate_chiQ : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K : FinExt l) (m : ℤ), m ≠ 0 → ∀ x : ℂ_[l], (∀ g : ↥(GK K), Per.σC (g : GQ l) x = ((((P.χQ (g : GQ l)) ^ m : ℚ_[l]ˣ) : ℚ_[l]) : ℂ_[l]) * x) → x = 0 := by
  intro l _ P AI _ K m hm x hx
  refine twist_fin P.ζQ (chiZ P) P.ζQ_zero P.ζQ_succ P.ζQ_one (chiZ_cyc P) K (-m) x (neg_ne_zero.2 hm) fun g hg => ?_
  have h1 := hx ⟨g, hg⟩
  have e : ((((P.χQ g) ^ m : ℚ_[l]ˣ) : ℚ_[l]) : ℂ_[l]) = (algebraMap ℚ_[l] ℂ_[l] ((P.χQ g : ℚ_[l]ˣ) : ℚ_[l])) ^ m := by
    have e0 : ((((P.χQ g) ^ m : ℚ_[l]ˣ) : ℚ_[l]) : ℂ_[l]) = algebraMap ℚ_[l] ℂ_[l] ((((P.χQ g) ^ m : ℚ_[l]ˣ) : ℚ_[l])) := rfl
    rw [e0, Units.val_zpow_eq_zpow_val, map_zpow₀]
  have hne : algebraMap ℚ_[l] ℂ_[l] ((P.χQ g : ℚ_[l]ˣ) : ℚ_[l]) ≠ 0 :=
    (map_ne_zero _).2 (Units.ne_zero _)
  change Per.σC g x = _ at h1
  rw [chiZ_coe, h1, e, zpow_neg, mul_assoc, mul_comm x, ← mul_assoc, mul_inv_cancel₀ (zpow_ne_zero _ hne), one_mul]

end GlobalTheory.TateChiQ
