module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.TraceFormulaEigenvalues.FormsFin
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.TraceFormulaEigenvalues.FinD
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open UpperTheory.V.Z.Sym in
theorem UpperTheory.V.Z.Sym.Tf.centFin :
    UpperTheory.V.Z.Sym.Tf.CentFin := by
  intro Γ G V _ _ _ _ B hB tw f hf δ
  classical
  obtain ⟨S₀, hS₀⟩ := hB.cls
  choose D hD using fun g : G => UpperTheory.V.Z.Sym.Tf.finD B hB tw f hf g g
  let rep : G → Γ → Γ := fun g d =>
    if h : ∃ γ : Γ, ∃ z ∈ B.Γ₀, γ⁻¹ * δ * tw.θΓ γ = d * z then h.choose else 1
  have rep_spec : ∀ g d, (∃ γ : Γ, ∃ z ∈ B.Γ₀, γ⁻¹ * δ * tw.θΓ γ = d * z) →
      ∃ z ∈ B.Γ₀, (rep g d)⁻¹ * δ * tw.θΓ (rep g d) = d * z := by
    intro g d h
    simp only [rep, dite_eq_left h]
    exact h.choose_spec
  refine ⟨S₀.biUnion (fun g => (D g).image (fun d => B.ι (rep g d) * g)), ?_⟩
  intro y hy
  obtain ⟨γ, g, hg, u, hu, rfl⟩ := hS₀ y
  have hcomm : ∀ c : Γ, tw.θ (B.ι c) = B.ι (tw.θΓ c) := tw.comm
  have expand : (B.ι γ * g * u)⁻¹ * B.ι δ * tw.θ (B.ι γ * g * u) =
      u⁻¹ * (g⁻¹ * B.ι (γ⁻¹ * δ * tw.θΓ γ) * tw.θ g) * tw.θ u := by
    simp only [map_mul, map_inv, hcomm]
    group
  have hne : f (g⁻¹ * B.ι (γ⁻¹ * δ * tw.θΓ γ) * tw.θ g) ≠ 0 := by
    intro h0
    apply hy
    show f ((B.ι γ * g * u)⁻¹ * B.ι δ * tw.θ (B.ι γ * g * u)) = 0
    rw [expand]
    have e1 := hf.right ⟨u, hu⟩ (u⁻¹ * (g⁻¹ * B.ι (γ⁻¹ * δ * tw.θΓ γ) * tw.θ g))
    have e2 := hf.left ⟨u⁻¹, B.U.inv_mem hu⟩ (g⁻¹ * B.ι (γ⁻¹ * δ * tw.θΓ γ) * tw.θ g)
    simp only at e1 e2
    rw [e1, e2, h0, mul_zero, mul_zero]
  obtain ⟨d, hd, z₂, hz₂, hγ⟩ := hD g (γ⁻¹ * δ * tw.θΓ γ) hne
  obtain ⟨z₁, hz₁, hr⟩ := rep_spec g d ⟨γ, z₂, hz₂, hγ⟩
  set r := rep g d with hr_def
  have hdr : d = r⁻¹ * δ * tw.θΓ r * z₁⁻¹ := eq_mul_inv_of_mul_eq hr.symm
  have hc : z₁⁻¹ * z₂ ∈ Subgroup.center Γ :=
    B.cenΓ (B.Γ₀.mul_mem (B.Γ₀.inv_mem hz₁) hz₂)
  have hx : γ * r⁻¹ ∈ tw.Cent δ := by
    refine ⟨z₁⁻¹ * z₂, B.Γ₀.mul_mem (B.Γ₀.inv_mem hz₁) hz₂, ?_⟩
    calc (γ * r⁻¹)⁻¹ * δ * tw.θΓ (γ * r⁻¹)
        = r * (γ⁻¹ * δ * tw.θΓ γ) * (tw.θΓ r)⁻¹ := by
          simp only [map_mul, map_inv]
          group
      _ = r * (d * z₂) * (tw.θΓ r)⁻¹ := by rw [hγ]
      _ = δ * (tw.θΓ r * (z₁⁻¹ * z₂)) * (tw.θΓ r)⁻¹ := by
          rw [hdr]
          group
      _ = δ * ((z₁⁻¹ * z₂) * tw.θΓ r) * (tw.θΓ r)⁻¹ := by
          rw [(Subgroup.mem_center_iff.mp hc (tw.θΓ r)).symm]
      _ = δ * (z₁⁻¹ * z₂) := by group
  refine ⟨⟨γ * r⁻¹, hx⟩, B.ι r * g, ?_, u, hu, ?_⟩
  · exact Finset.mem_biUnion.mpr ⟨g, hg, Finset.mem_image.mpr ⟨d, hd, rfl⟩⟩
  · show B.ι γ * g * u = B.ι (γ * r⁻¹) * (B.ι r * g) * u
    rw [map_mul, map_inv]
    group
