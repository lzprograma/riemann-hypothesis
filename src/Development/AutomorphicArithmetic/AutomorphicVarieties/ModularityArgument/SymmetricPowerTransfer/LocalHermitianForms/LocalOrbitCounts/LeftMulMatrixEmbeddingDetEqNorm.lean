module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.NormOneIsCoboundaryUnramifiedQuadratic
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.FzkLaw
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.GConj
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.FinD
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.WTrans
public import Mathlib.Algebra.Module.Lattice.Full
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
import Mathlib.RingTheory.Henselian
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
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Algebra.Module.Lattice.Basic
public import Mathlib.LinearAlgebra.Matrix.Basis

@[expose] public section

open QuadraticAlgebra UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Loc.GL Matrix

noncomputable section

section Main

variable {O : Type} [CommRing O] {K : Type} [Field K] [Algebra O K] {τ : K}

private theorem cls_mul (t : Etau K τ) (S : Set (Etau K τ)) :
    cls τ ((t * ·) '' S) = (fun S => (t * ·) '' S) '' cls τ S := by
  ext T
  constructor
  · rintro ⟨r, rfl⟩
    exact ⟨_, ⟨r, rfl⟩, by simp [← Set.image_comp]⟩
  · rintro ⟨_, ⟨r, rfl⟩, rfl⟩
    exact ⟨r, by simp [← Set.image_comp]⟩

private theorem stab_iff (u : (Etau K τ)ˣ) (g : GL (Fin 2) K) :
    (∃ S, IsLat O τ S ∧ (∀ y ∈ S, (u : Etau K τ) * y ∈ S) ∧ cls τ (LL O τ g) = cls τ S) →
      Ent O (g⁻¹ * (jU (j0 τ) u * g)) := by
  rintro ⟨S, -, hs, e⟩
  obtain ⟨s, hs'⟩ : LL O τ g ∈ cls τ S := e ▸ cls_self _
  rw [← lat_le (τ := τ), lat_mul, hs']
  rintro _ ⟨_, ⟨y, hy, rfl⟩, rfl⟩
  exact ⟨_, hs y hy, by simp⟩

open Classical in
private theorem val_eq [IsDomain O] [IsDiscreteValuationRing O] {Δ : K} (hL : IsLoc O Δ) (χ : Kˣ →* ℂˣ) (hχ : Unr O χ)
    (u : (Etau K τ)ˣ) (s : Kˣ) (ε : Oˣ) (hu : QuadraticAlgebra.norm (u : Etau K τ) = algebraMap O K ε) (g : GL (Fin 2) K) :
    fZK O χ (g⁻¹ * jU (j0 τ) (su τ s * u) * g) = (((χ s)⁻¹ : ℂˣ) : ℂ) *
      if ∃ S, IsLat O τ S ∧ (∀ y ∈ S, (u : Etau K τ) * y ∈ S) ∧ cls τ (LL O τ g) = cls τ S then 1 else 0 := by
  haveI := hL.frac
  obtain ⟨h0, h1⟩ := fzkLaw O K Δ hL χ hχ
  have e : g⁻¹ * jU (j0 τ) (su τ s * u) * g = sc s * (g⁻¹ * (jU (j0 τ) u * g)) := by
    rw [map_mul, jU_su, ← mul_assoc, ← GeneralLinearGroup.scalar_commute]
    group
  have hd : ((g⁻¹ * (jU (j0 τ) u * g) : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).det = algebraMap O K ε := by
    rw [Units.val_mul, Units.val_mul, ← mul_assoc, det_units_conj', ← hu, ← leftMulMatrixEmbedding_det_eq_norm]
    rfl
  rw [e]
  split_ifs with h
  · rw [h1 s _ (kg_of_det (stab_iff u g h) ε hd), mul_one]
  · rw [mul_zero]
    refine h0 _ fun hz => h ⟨_, lat_isLat g, fun y hy => ?_, rfl⟩
    have hz' : g⁻¹ * (jU (j0 τ) u * g) ∈ ZK O K :=
      ((ZK O K).mul_mem_cancel_left (zk_iff.2 ⟨s, 1, one_mem _, (mul_one _).symm⟩)).1 hz
    have := (lat_le (τ := τ)).2 (ent_of_zk ε hd hz')
    rw [lat_mul] at this
    exact this ⟨y, hy, rfl⟩

private theorem wcount_mul {T Y : Type} [Group T] [MulAction T Y] (C : Subgroup T) (c : ℂ) (k : Y → ℂ) :
    c * wcount C k = wcount C fun y => c * k y := by
  unfold wcount
  rw [mul_finsum]
  exact finsum_congr fun o => by ring

private theorem q_mul (t : (Etau K τ)ˣ) (x : Etau K τ) [IsDomain O] [IsDiscreteValuationRing O] [IsFractionRing O K]
    (X : Set (Set (Etau K τ))) (h : ∃ S, IsLat O τ S ∧ (∀ y ∈ S, x * y ∈ S) ∧ X = cls τ S) :
    ∃ S, IsLat O τ S ∧ (∀ y ∈ S, x * y ∈ S) ∧ (fun S => ((t : Etau K τ) * ·) '' S) '' X = cls τ S := by
  obtain ⟨S, hS, hs, rfl⟩ := h
  refine ⟨_, ?_, ?_, (cls_mul _ S).symm⟩
  · obtain ⟨g, rfl⟩ := isLat_lat hS
    rw [← lat_mul]
    exact lat_isLat _
  · rintro _ ⟨y, hy, rfl⟩
    exact ⟨_, hs y hy, mul_left_comm _ _ _⟩

end Main

end

theorem UpperTheory.V.Z.Sym.Loc.gLat :
    UpperTheory.V.Z.Sym.Loc.GLat := by
  classical
  intro O K _ _ _ _ _ Δ τ hL hτ j χ hj hχ z s ε hz
  haveI := hL.frac
  rw [(gConj O K Δ τ hL hτ j (j0 τ) hj leftMulMatrixEmbedding_omega_trace).2 χ hχ z]
  obtain ⟨u, rfl⟩ : ∃ u, z = su τ s * u := ⟨(su τ s)⁻¹ * z, by simp⟩
  have hx : ((s⁻¹ : Kˣ) : K) • ((su τ s * u : (Etau K τ)ˣ) : Etau K τ) = u := by
    rw [Units.val_mul, su_mul, smul_smul, Units.inv_mul, one_smul]
  have hu : QuadraticAlgebra.norm (u : Etau K τ) = algebraMap O K ε := by
    rw [Units.val_mul, su_mul, ← leftMulMatrixEmbedding_det_eq_norm, map_smul, det_smul, leftMulMatrixEmbedding_det_eq_norm, Fintype.card_fin, mul_comm] at hz
    exact mul_right_cancel₀ (pow_ne_zero 2 s.ne_zero) hz
  rw [hx]
  unfold gOrb orb vcount
  letI := mulAct (K := K) τ
  letI : MulAction (Etau K τ)ˣ (GL (Fin 2) K ⧸ ZK O K) := MulAction.compHom _ (jU (j0 τ))
  rw [wcount_mul]
  have hmk : ∀ g : GL (Fin 2) K, cls τ (LL O τ (QuotientGroup.mk g : GL (Fin 2) K ⧸ ZK O K).out) = cls τ (LL O τ g) :=
    fun g => cls_lat.2 (QuotientGroup.eq.1 (QuotientGroup.out_eq' _))
  have heq : ∀ (t : (Etau K τ)ˣ) (y : GL (Fin 2) K ⧸ ZK O K), cls τ (LL O τ (t • y).out) = t • cls τ (LL O τ y.out) := by
    intro t y
    have : t • y = QuotientGroup.mk (jU (j0 τ) t * y.out) := by
      conv_lhs => rw [← QuotientGroup.out_eq' y]
      rfl
    rw [this, hmk, lat_mul, cls_mul]
    rfl
  have hq : ∀ (t : (Etau K τ)ˣ) (X : Set (Set (Etau K τ))),
      (∃ S, IsLat O τ S ∧ (∀ y ∈ S, (u : Etau K τ) * y ∈ S) ∧ t • X = cls τ S) ↔
        ∃ S, IsLat O τ S ∧ (∀ y ∈ S, (u : Etau K τ) * y ∈ S) ∧ X = cls τ S := by
    intro t X
    refine ⟨fun h => ?_, q_mul t _ X⟩
    have := q_mul t⁻¹ _ _ h
    change ∃ S, _ ∧ _ ∧ t⁻¹ • t • X = _ at this
    rwa [inv_smul_smul] at this
  simp only [MonoidHom.id_apply]
  refine wTrans _ _ _ _ _ _ (fun y X => X = cls τ (LL O τ y.out)) ?_ ?_ ?_ ?_ ?_ ?_
  · intro t y
    rw [val_eq hL χ hχ u s ε hu, val_eq hL χ hχ u s ε hu, heq, if_congr (hq _ _) rfl rfl]
  · intro t X
    rw [if_congr (hq _ _) rfl rfl]
  · rintro t y _ rfl
    exact (heq t y).symm
  · rintro y _ rfl
    exact val_eq hL χ hχ u s ε hu _
  · exact fun y _ => ⟨_, rfl, fun _ h => h⟩
  · intro X hX
    have h : ∃ S, IsLat O τ S ∧ (∀ y ∈ S, (u : Etau K τ) * y ∈ S) ∧ X = cls τ S := by
      by_contra h
      exact hX (by rw [ite_eq_right h, mul_zero])
    obtain ⟨S, hS, -, rfl⟩ := h
    obtain ⟨g, rfl⟩ := isLat_lat hS
    refine ⟨QuotientGroup.mk g, (hmk g).symm, fun y hy => ?_⟩
    rw [← QuotientGroup.out_eq' y]
    exact QuotientGroup.eq.2 (cls_lat.1 hy.symm)
