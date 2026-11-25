module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalWeilOperators.LocForm
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalWeilOperators.LocJJA
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalWeilOperators.OppositeUnipotentWeylConj

@[expose] public section

noncomputable section

open scoped TensorProduct NNReal Matrix SchwartzMap Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula

def locFT {m n : ℕ} (C s : ℂ) (g : (Fin m → Fin n → ℂ) → ℂ) : (Fin m → Fin n → ℂ) → ℂ :=
  fun u => C * ∫ v : Fin m → Fin n → ℂ,
    Complex.exp (2 * Real.pi * Complex.I * ((s * Matrix.trace ((Matrix.of u)ᴴ * Matrix.of v)).re : ℂ)) * g v

def chirp {m n : ℕ} (k : ℂ) (x : Matrix (Fin n) (Fin n) ℂ) (g : (Fin m → Fin n → ℂ) → ℂ) :
    (Fin m → Fin n → ℂ) → ℂ :=
  fun u => Complex.exp (2 * Real.pi * Complex.I * k * Matrix.trace (x * ((Matrix.of u)ᴴ * Matrix.of u))) * g u

theorem locFT_zero {m n : ℕ} (C s : ℂ) : locFT (m := m) (n := n) C s 0 = 0 := by
  funext u
  simp [locFT]

theorem chirp_zero {m n : ℕ} (k : ℂ) (x : Matrix (Fin n) (Fin n) ℂ) : chirp (m := m) k x 0 = 0 := by
  funext u
  simp [chirp]

theorem locFT_smul {m n : ℕ} (C s a : ℂ) (g : (Fin m → Fin n → ℂ) → ℂ) :
    locFT C s (a • g) = a • locFT C s g := by
  funext u
  simp only [locFT, Pi.smul_apply, smul_eq_mul]
  rw [show (fun v : Fin m → Fin n → ℂ => Complex.exp (2 * Real.pi * Complex.I *
      ((s * Matrix.trace ((Matrix.of u)ᴴ * Matrix.of v)).re : ℂ)) * (a * g v)) = fun v => a * (Complex.exp
      (2 * Real.pi * Complex.I * ((s * Matrix.trace ((Matrix.of u)ᴴ * Matrix.of v)).re : ℂ)) * g v) from
    funext fun v => by ring, integral_const_mul]
  ring

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

end PositivityTheory.SiegelWeilFormula

end
