module

public import Development.AbelianVarietyTheory.Definitions.Foundations.FinalTheorems
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.KatoUse
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.RhoKApply
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.ClsFacts
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.DecCyc
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.ClassFieldRamification.KwAbs
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Places
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.CoboundaryLemmaNoColumn
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.DatFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.DatLoc
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.DiagonalOnSubgroupOfConjugate
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.ExistsIsDiagOnOfIsDiagOnInfKerSign
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.ExistsIsFlagOnOfEigenvectorNormalSubgroup
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.ExistsUnitPowNe
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.MemGalOfQuadraticOfFixesDiscrRootsOfUnity
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.PtIneL
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.PtInertiaAway
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Basic
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
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

namespace GlobalTheory.KillsComp

theorem proj_pow_eq_one (l : ℕ) [hl : Fact l.Prime] (N : ℕ) [NeZero N] (u : (ZMod N)ˣ)
    (hu : l ∣ N → (l : ℤ) ∣ ((u : ZMod N).val : ℤ) - 1) :
    proj l N u ^ l ^ (N.factorization l - 1) = 1 := by
  set a := N.factorization l
  set m := l ^ (a - 1)
  set U : ℤ := ((u : ZMod N).val : ℤ)
  set e : ℕ := ordCompl[l] N ^ Nat.totient (ordProj[l] N)
  set V : ℤ := (e : ℤ) * U + (1 - (e : ℤ))
  have hV : ((V : ℤ) : ZMod N) = (proj l N u : ZMod N) := by
    simp only [V, proj, projZ, idem, Units.coe_map, MonoidHom.coe_mk, OneHom.coe_mk, U]
    rw [Int.cast_add, Int.cast_mul, Int.cast_sub, Int.cast_one, Int.cast_natCast, Int.cast_natCast, ZMod.natCast_zmod_val]
  have hV1 : V - 1 = (e : ℤ) * (U - 1) := by ring
  have htot : 0 < Nat.totient (ordProj[l] N) := Nat.totient_pos.2 (pow_pos hl.out.pos _)
  have hcompl : ((ordCompl[l] N : ℕ) : ℤ) ∣ V ^ m - 1 := by
    have h1 : ((ordCompl[l] N : ℕ) : ℤ) ∣ V - 1 := by
      rw [hV1]
      refine Dvd.dvd.mul_right ?_ _
      exact_mod_cast dvd_pow_self _ htot.ne'
    have h2 : V - 1 ∣ V ^ m - 1 := by simpa using sub_dvd_pow_sub_pow V 1 m
    exact h1.trans h2
  have hproj : ((ordProj[l] N : ℕ) : ℤ) ∣ V ^ m - 1 := by
    rcases Nat.eq_zero_or_pos a with ha | ha
    · show ((l ^ a : ℕ) : ℤ) ∣ _
      rw [ha]; simp
    · have hlN : l ∣ N := by
        by_contra h
        have : a = 0 := Nat.factorization_eq_zero_of_not_dvd h
        omega
      have h1 : (l : ℤ) ∣ V - 1 := by
        rw [hV1]; exact Dvd.dvd.mul_left (hu hlN) _
      have := dvd_sub_pow_of_dvd_sub (p := l) (k := a - 1) (by simpa using h1)
      rw [one_pow, Nat.sub_add_cancel ha] at this
      exact_mod_cast this
  have hN : (N : ℤ) ∣ V ^ m - 1 := by
    have hc : IsCoprime ((ordProj[l] N : ℕ) : ℤ) ((ordCompl[l] N : ℕ) : ℤ) :=
      Nat.isCoprime_iff_coprime.2 (coprime_ordProj_ordCompl l N)
    have := hc.mul_dvd hproj hcompl
    rwa [← Nat.cast_mul, Nat.ordProj_mul_ordCompl_eq_self] at this
  refine Units.ext ?_
  rw [Units.val_pow_eq_pow_val, Units.val_one, ← hV]
  have := (ZMod.intCast_zmod_eq_zero_iff_dvd _ N).2 hN
  push_cast at this
  exact sub_eq_zero.1 this

end GlobalTheory.KillsComp

open GlobalTheory.KillsComp in
theorem GlobalTheory.killsMu_comp_of_sq_eq_one : ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] {N : ℕ} [NeZero N] (ψ : DirichletCharacter O N), l ≠ 2 → HV.comp l ψ ^ 2 = 1 → Af.KillsMu (F := ℚ) l (Chr.dirG ℚ Ω (HV.comp l ψ)) := by
  intro Ω _ _ _ l hl O _ N _ ψ hl2 hsq s hs
  set c := Chr.cls ℚ Ω N s
  have hu : l ∣ N → (l : ℤ) ∣ (((c : ZMod N)).val : ℤ) - 1 := by
    intro hlN
    have h1 : Chr.cls ℚ Ω l s = 1 := (Chr.clsFacts ℚ Ω l).2.2.1 s 1 fun ζ hζ => by
      rw [hs ζ hζ, Units.val_one, ZMod.val_one, pow_one]
    have h2 := DFunLike.congr_fun ((Chr.clsFacts ℚ Ω N).2.1 l hlN) s
    rw [MonoidHom.comp_apply, h1] at h2
    have h3 := congrArg (fun x : (ZMod l)ˣ => (x : ZMod l)) h2
    simp only [ZMod.unitsMap_val, Units.val_one, ZMod.cast_eq_val] at h3
    have h4 : (((((c : ZMod N)).val : ℤ) - 1 : ℤ) : ZMod l) = 0 := by push_cast; rw [h3]; ring
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ l).1 h4
  have hm := proj_pow_eq_one l N c hu
  set m := l ^ (N.factorization l - 1)
  refine Units.ext ?_
  simp only [Chr.dirG, MonoidHom.comp_apply, MulChar.coe_toUnitHom, Units.val_one]
  have hval : (HV.comp l ψ) (c : ZMod N) = ψ (proj l N c : ZMod N) := by
    simp only [HV.comp, MulChar.ofUnitHom_coe, MonoidHom.comp_apply, MulChar.coe_toUnitHom]
  have y2 : ψ (proj l N c : ZMod N) ^ 2 = 1 := by
    have := congrArg (fun χ : DirichletCharacter O N => χ (c : ZMod N)) hsq
    simp only [MulChar.pow_apply_coe, MulChar.one_apply_coe] at this
    rwa [hval] at this
  have ym : ψ (proj l N c : ZMod N) ^ m = 1 := by
    rw [← map_pow, ← Units.val_pow_eq_pow_val, hm, Units.val_one, map_one]
  have hcop : Nat.Coprime 2 m := by
    refine Nat.Coprime.pow_right _ ?_
    exact (Nat.coprime_primes Nat.prime_two Fact.out).2 (Ne.symm hl2)
  rw [hval]
  have := (pow_gcd_eq_one).2 ⟨y2, ym⟩
  rwa [hcop.gcd_eq_one, pow_one] at this

end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

namespace GlobalTheory.Ord2.IrrTransfer

theorem isIrr_of_range {Γ Γ' k : Type} [Group Γ] [Group Γ'] [Field k] {n : ℕ} (r : Γ →* GL (Fin n) k)
    (r' : Γ' →* GL (Fin n) k) (h : ∀ g', ∃ g, r g = r' g') (hr' : Af.IsIrr r') : Af.IsIrr r := by
  unfold Af.IsIrr IsIrrSub at *
  obtain ⟨h1, h2, h3⟩ := hr'
  refine ⟨h1, fun g v _ => Submodule.mem_top, fun W' hle hW => h3 W' hle ?_⟩
  intro g' v hv
  obtain ⟨g, hg⟩ := h g'
  rw [← hg]
  exact hW g v hv

end GlobalTheory.Ord2.IrrTransfer

end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

namespace GlobalTheory.Ord2

open UpperTheory.V.Base UpperTheory.V.U3 in
theorem psi_ine {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {K : Type} [Field K] [NumberField K] [Algebra K Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} {N : ℕ} [NeZero N] {e : ℕ} {ψ : DirichletCharacter c.O N} (D : U3.Dat Ω K c e ψ) :
    ∀ g ∈ Loc.Iq l, Chr.dirG ℚ Ω ψ (D.ι g) = Chr.dirG ℚ Ω (HV.comp l ψ) (D.ι g) := by
  intro g hg
  obtain ⟨-, -, -, -, -, -, hcyc, -⟩ := dat_loc D
  have h1 := D.Ψ_I g hg
  have h2 : Chr.Psi l e (Chr.dirG ℚ Ω ψ) (D.ι g) = chiO ℚ Ω l c.O (D.ι g) ^ (e : ℤ) * Chr.dirG ℚ Ω ψ (D.ι g) := rfl
  have h3 : chiO ℚ Ω l c.O (D.ι g) = Loc.cycA l l c.O g := by
    show Units.map _ (cycZ ℚ Ω l (D.ι g)) = _
    rw [hcyc]
    rfl
  rw [h2, h3, zpow_natCast] at h1
  exact mul_left_cancel h1


end GlobalTheory.Ord2

end

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

namespace GlobalTheory.Ord2.TwDet

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {l : ℕ} [Fact l.Prime]

theorem tw_coe (W : R2 Ω l) (χ : G ℚ Ω →* (Qbar l)ˣ) (s : G ℚ Ω) :
    mat (tw W χ) s = (χ s : Qbar l) • mat W s := tw_val W χ s

theorem dt_coe (W : R2 Ω l) (s : G ℚ Ω) : (dt W s : Qbar l) = (mat W s).det := by
  simp [dt, mat]

theorem dt_tw (W : R2 Ω l) (χ : G ℚ Ω →* (Qbar l)ˣ) : dt (tw W χ) = χ ^ 2 * dt W := by
  ext s
  simp only [MonoidHom.mul_apply, MonoidHom.pow_apply, Units.val_mul, Units.val_pow_eq_pow_val]
  rw [dt_coe, dt_coe, tw_coe, Matrix.det_smul]
  simp

theorem killsMu_dvd {M N : ℕ} {C : Type} [Monoid C] {χ : G ℚ Ω →* C} (h : KillsMu M χ) (hMN : M ∣ N) :
    KillsMu N χ := by
  intro s hs
  apply h s
  intro ζ hζ
  obtain ⟨k, rfl⟩ := hMN
  exact hs ζ (by rw [pow_mul, hζ, one_pow])

theorem killsMu_mul {M : ℕ} {C : Type} [CommMonoid C] {χ ψ : G ℚ Ω →* C} (h : KillsMu M χ) (h' : KillsMu M ψ) :
    KillsMu M (χ * ψ) := by
  intro s hs
  simp [h s hs, h' s hs]

end GlobalTheory.Ord2.TwDet

namespace GlobalTheory.Ord2.TwDet

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {l : ℕ} [Fact l.Prime]

theorem cont_val {W : R2 Ω l} (h : Continuous W) : Continuous fun s => mat W s :=
  Units.continuous_val.comp h

theorem dt_cont {W : R2 Ω l} (h : Continuous W) : Continuous fun s => (dt W s : Qbar l) := by
  simp_rw [dt_coe]
  exact (cont_val h).matrix_det

theorem tw_cont {W : R2 Ω l} {χ : G ℚ Ω →* (Qbar l)ˣ} (h : Continuous W)
    (hχ : Continuous fun s => (χ s : Qbar l)) : Continuous (tw W χ) := by
  rw [Units.continuous_iff]
  constructor
  · change Continuous fun s => mat (tw W χ) s
    simp_rw [tw_coe]
    exact hχ.smul (cont_val h)
  · have e : ∀ s, (((tw W χ s)⁻¹ : GL (Fin 2) (Qbar l)) : Matrix (Fin 2) (Fin 2) (Qbar l)) = mat (tw W χ) s⁻¹ := by
      intro s; simp only [mat, map_inv]
    simp_rw [e, tw_coe]
    exact (hχ.comp continuous_inv).smul ((cont_val h).comp continuous_inv)

theorem ker_open {W : R2 Ω l} (h : Continuous W) (h2 : dt W ^ 2 = 1) : IsOpen ((dt W).ker : Set (G ℚ Ω)) := by
  have hs : ((dt W).ker : Set (G ℚ Ω)) = {s | (dt W s : Qbar l) = -1}ᶜ := by
    ext s
    have hsq : (dt W s : Qbar l) * (dt W s : Qbar l) = 1 := by
      have := congrArg (fun f : G ℚ Ω →* (Qbar l)ˣ => ((f s : (Qbar l)ˣ) : Qbar l)) h2
      simpa [pow_two] using this
    simp only [SetLike.mem_coe, MonoidHom.mem_ker, Set.mem_compl_iff, Set.mem_setOf_eq]
    constructor
    · intro h1 h2
      rw [h1] at h2
      have : (1 : Qbar l) = -1 := by simpa using h2
      have h2' : (2 : Qbar l) = 0 := by linear_combination this
      exact two_ne_zero h2'
    · intro hne
      rcases mul_self_eq_one_iff.mp hsq with h1 | h1
      · exact Units.val_eq_one.mp h1
      · exact absurd h1 hne
  rw [hs, isOpen_compl_iff]
  exact isClosed_eq (dt_cont h) continuous_const

end GlobalTheory.Ord2.TwDet

namespace GlobalTheory.Ord2.TwDet

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {l : ℕ} [Fact l.Prime]

theorem tw_tw (W : R2 Ω l) (a b : G ℚ Ω →* (Qbar l)ˣ) : tw (tw W a) b = tw W (b * a) := by
  ext s i j
  change mat (tw (tw W a) b) s i j = mat (tw W (b * a)) s i j
  rw [tw_coe, tw_coe, tw_coe]
  simp [mul_assoc]

theorem conj_tw (W : R2 Ω l) (χ : G ℚ Ω →* (Qbar l)ˣ) (g : GL (Fin 2) (Qbar l)) (s : G ℚ Ω) :
    ((g * tw W χ s * g⁻¹ : GL (Fin 2) (Qbar l)) : Matrix (Fin 2) (Fin 2) (Qbar l)) =
      (χ s : Qbar l) • ((g * W s * g⁻¹ : GL (Fin 2) (Qbar l)) : Matrix (Fin 2) (Fin 2) (Qbar l)) := by
  simp only [Units.val_mul]
  change (g : Matrix (Fin 2) (Fin 2) (Qbar l)) * mat (tw W χ) s * _ = _
  rw [tw_coe, Matrix.mul_smul, Matrix.smul_mul]

theorem dt_conj (W : R2 Ω l) (g : GL (Fin 2) (Qbar l)) (s : G ℚ Ω) :
    (dt W s : Qbar l) = ((g * W s * g⁻¹ : GL (Fin 2) (Qbar l)) : Matrix (Fin 2) (Fin 2) (Qbar l)).det := by
  rw [← Matrix.GeneralLinearGroup.val_det_apply, map_mul, map_mul, mul_comm, ← mul_assoc, map_inv, inv_mul_cancel, one_mul]
  rfl

theorem diag_tw {W : R2 Ω l} {H : Subgroup (G ℚ Ω)} {χ : Fin 2 → G ℚ Ω →* (Qbar l)ˣ} (h : IsDiagOn W H χ) :
    IsDiagOn (tw W (dt W)) H (fun i => χ i * χ 0 * χ 1) := by
  obtain ⟨g, hg⟩ := h
  refine ⟨g, fun s hs => ?_⟩
  have hd : (dt W s : Qbar l) = (χ 0 s : Qbar l) * (χ 1 s : Qbar l) := by
    rw [dt_conj W g s, hg s hs, Matrix.det_diagonal, Fin.prod_univ_two]
  rw [conj_tw, hg s hs, hd]
  ext i j
  by_cases hij : i = j
  · subst hij; simp; ring
  · simp [hij]

theorem flag_tw {W : R2 Ω l} {H : Subgroup (G ℚ Ω)} {κ : Fin 2 → ↥H →* (Qbar l)ˣ} (h : IsFlagOn W H κ) :
    IsFlagOn (tw W (dt W)) H (fun i => κ i * (dt W).comp H.subtype) := by
  obtain ⟨g, hg⟩ := h
  refine ⟨g, fun s => ⟨fun i j hij => ?_, fun i => ?_⟩⟩
  · rw [conj_tw, Matrix.smul_apply, (hg s).1 i j hij, smul_zero]
  · rw [conj_tw, Matrix.smul_apply, (hg s).2 i]
    simp [mul_comm]

end GlobalTheory.Ord2.TwDet

namespace GlobalTheory.Ord2

open TwDet

theorem admissible_twist_by_det : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ι : Qbar l ≃+* ℂ)
    (e : ℕ) (W : R2 Ω l), admitted ι e W → admitted ι e (tw W (dt W)) := by
  intro l _ Ω _ _ _ ι e W h
  have hdt : dt (tw W (dt W)) = dt W := by rw [dt_tw, h.det2, one_mul]
  obtain ⟨N, hN, hNk⟩ := UpperTheory.V.CF.kwAbs Ω (dt W).ker (ker_open h.cont h.det2)
    (Abelianization.commutator_subset_ker (dt W))
  have hθN : KillsMu N (dt W) := fun s hs => hNk s hs
  refine ⟨tw_cont h.cont (dt_cont h.cont), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hdt]; exact h.det2
  · intro s hs; rw [hdt]; exact h.odd s hs
  · have hH : H0g (tw W (dt W)) = H0g W := by unfold H0g; rw [hdt]
    rw [hH]
    have : (tw W (dt W)).comp (H0g W).subtype = W.comp (H0g W).subtype := by
      ext s i j
      change mat (tw W (dt W)) s i j = mat W s i j
      have h1 : dt W (s : G ℚ Ω) = 1 := MonoidHom.mem_ker.mp (Subgroup.mem_inf.mp s.2).2
      rw [tw_coe, h1]
      simp
    rw [this]; exact h.irr
  · obtain ⟨M, hM, hl⟩ := h.away
    refine ⟨M, hM, fun w hw => ?_⟩
    obtain ⟨A, hA, χ, hχ, hd⟩ := hl w hw
    exact ⟨A, hA, fun i => χ i * χ 0 * χ 1,
      fun i => killsMu_mul (killsMu_mul (hχ i) (hχ 0)) (hχ 1), diag_tw hd⟩
  · obtain ⟨f, M, φ, hM, hφ, hf⟩ := h.modular
    refine ⟨f, M * N, φ * dt W, Nat.mul_pos hM hN,
      killsMu_mul (killsMu_dvd hφ (dvd_mul_right M N)) (killsMu_dvd hθN (dvd_mul_left N M)), ?_⟩
    rw [tw_tw, mul_assoc, mul_assoc, ← pow_two, h.det2, mul_one]
    exact hf
  · obtain ⟨A, χ, κ, hA, hχ, hfl, hine, hk⟩ := h.flag
    refine ⟨A, χ, fun i => κ i * (dt W).comp (Dec (F := ℚ) A).subtype, hA, hχ, flag_tw hfl, ?_, ?_⟩
    · rw [hdt]; exact hine
    · intro s hs
      have h1 : dt W (s : G ℚ Ω) = 1 := hine hs
      obtain ⟨h0, h1'⟩ := hk s hs
      refine ⟨?_, ?_⟩ <;>
        simp only [MonoidHom.mul_apply, MonoidHom.comp_apply, Subgroup.coe_subtype, h1, mul_one] <;>
        assumption

end GlobalTheory.Ord2

end
