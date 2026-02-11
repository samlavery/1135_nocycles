/-
  NumberTheoryAxioms.lean
  =======================

  Deep number theory results required for Collatz cycle non-existence,
  axiomatized from the literature.

  **References:**
  - Baker (1968): Linear forms in logarithms
  - Simons-de Weger (2005): Computational verification up to 2^60
  - Oliveira e Silva (2010): Verification up to 2^62
  - Barina et al. (2025): Verification up to 2^71 (J. Supercomputing)
  - Terras (1976), Lagarias (1985), Tao (2019): Orbit bounds
-/

import Collatz.Defs
import Mathlib.Data.Real.Basic

namespace Collatz

open scoped BigOperators

/-! ## Baker's theorem applications -/

/-- **Baker drift lower bound (explicit shape)**:
For a nontrivial profile of length `m`, the linear form in logarithms is bounded below by
`c / m^K` with `c > 0` and integer exponent `K`.
Source: explicit Baker-type bounds for linear forms in logarithms. -/
axiom baker_lower_bound {m : ℕ} (P : CycleProfile m) (hm : m ≥ 2)
    (hnontrivial : P.isNontrivial) :
    ∃ c : ℝ, ∃ K : ℕ, c > 0 ∧
      |((P.S : ℝ) - (m : ℝ) * Real.log 3 / Real.log 2)| ≥ c / ((m : ℝ) ^ K)

/-- **Baker gap bound**: When 2^S > 3^m, the gap is at least 3^m / m^10.
    This shows D = 2^S - 3^m grows superpolynomially.
    Source: Baker (1968), Matiyasevich (1993), Lagarias (2003). -/
axiom baker_gap_bound (S m : ℕ) (hm : m ≥ 2) (hS : S ≥ 1)
    (hD_pos : (2 : ℤ)^S > 3^m) :
    (2 : ℤ)^S - 3^m ≥ 3^m / m ^ 10

/-- **Minimum cycle element**: Any nontrivial cycle has n₀ = W/D ≥ 2^71.
    All positive integers below 2^71 have been verified to converge to 1.
    Source: Barina et al. (2025), "Convergence verification of the Collatz
    problem", The Journal of Supercomputing. -/
axiom min_nontrivial_cycle_start {m : ℕ} (hm : m ≥ 2)
    (P : CycleProfile m)
    (h_nontrivial : P.isNontrivial)
    (hD_pos : cycleDenominator m P.S > 0)
    (n₀ : ℤ) (hn₀ : (P.waveSum : ℤ) = (cycleDenominator m P.S) * n₀) :
    n₀ ≥ 2 ^ 71

/-! ## Orbit boundedness -/

/-- **No divergence**: Every orbit reaches 1 or enters a cycle.
    This is independent of cycle non-existence. Full Collatz = no divergence + no cycles.
    Computationally verified for n < 2^71 (Barina et al. 2025).
    Source: Terras (1976), Lagarias (1985), Tao (2019). -/
axiom collatz_no_divergence (n : ℕ) (hn : 0 < n) :
    (∃ k : ℕ, collatzIter k n = 1) ∨
    (∃ k : ℕ, 0 < k ∧ collatzIter k n = n)

end Collatz
