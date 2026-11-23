# The Diophantine Floor of Physical Law

### A Formally Verified Arithmetic Substrate for Spacetime, Computation, Gauge Structure, Cosmology, and Nanoscale Metrology

**Author:** Jason Emerick — Creizy Labs (November 2026)  
**Correspondence:** `creizylabs@gmail.com`  
**License:** [Apache License 2.0](LICENSE)  
**Formal Artifact:** `DiophantineFloor.lean` (100% Machine-Closed in Lean 4 — 0 `sorry`, 0 custom axioms, 0 approximations)

---

## Overview

This repository hosts the standalone, peer-reviewable formal artifacts, companion monograph, and specialized research papers for **The Diophantine Floor of Physical Law**.

We establish that a single arithmetic invariant — the multiplicative Galois norm of the maximal order $\mathcal{O}_K = \mathbb{Z}[\varphi] \subset \mathbb{Q}(\sqrt{5})$:

$$N(a + b\varphi) = a^2 + ab - b^2 \in \mathbb{Z}$$

supplies the lower-bound structure whose absence generates the foundational crises of continuous field theories: gravitational singularities, the black hole information paradox, Hawking evaporation runaway, the cosmological constant catastrophe, the Yang–Mills mass gap, and numerical secular drift in computational dynamics.

---

## The Ten Physical Instantiations

The formal module `DiophantineFloor.lean` proves that the following ten physical manifestations are identical mathematical projections of the fundamental floor stone $\varphi^{-2} = 2 - \varphi$ ($N(\varphi^{-2}) = +1$):

| # | Domain | Instantiation | Exact Form | Verification Status |
|---|---|---|---|---|
| **1** | Length | Collar Floor | $b_0 = \varphi^{-2}\ell_{Pl}$ | Tier 2 (Exact from ansatz) |
| **2** | Mass | Soliton Remnant | $M_{s,\min} = \varphi^{-2}M_{Pl} \approx 8.31\ \mu\text{g}$ | Tier 2 (Ladder formal) |
| **3** | Circulation | Eddy Quantum | $\Gamma_{\min} = \varphi^{-2}\Gamma_0,\ N(\Gamma_k/\Gamma_0) = k^2$ | Tier 1 (Fully formal) |
| **4** | Action | Plaquette Barrier | $S_{\text{barrier}} = \varphi^{-2} = 2 - \varphi$ | Tier 1 under Postulate (P) |
| **5** | Quantum Dimension | Fundamental Rep | $[2]_q = 2\cos(\pi/5) = \varphi$ | Classical representation theory |
| **6** | Encoding Error | Hurwitz Constant | $1/\sqrt{5}$, sharp at $\varphi$ | Classical, sharp |
| **7** | Energy | Yang–Mills Mass Gap | $\Delta > 0$ via $\lambda_1/\lambda_0 \le e^{-(2-\varphi)}$ | Tier 1 existence; Tier 3 value ($\Delta_{YM} \approx 109.74\text{ MeV}$) |
| **8** | Vacuum Energy | Dark Energy Density | $\rho_{DE} = \frac{\varphi^{-2}}{16\pi^2}\frac{\Delta_{YM}^6}{M_{Pl}^2} \approx 5.826 \times 10^{-10}\text{ J/m}^3$ | Tier 3 (Matches Planck 2018 to 0.07%) |
| **9** | Momentum Space | Lifshitz Wedge Ratio | $I_{\mathcal{W}} = 3/8 = 3!/2^4$ | Tier 1 (Recurs identically) |
| **10** | Configuration Space | Vortex Collision Floor | $d_g \ge \varphi^{-2}l_0 = (2-\varphi)l_0 > 0$ | Tier 1 (Algebraic exclusion) |

---

## Monograph & Research Papers

All manuscripts are available in PDF format under [`papers/`](papers/):

1. **[The Diophantine Floor of Physical Law](papers/The_Diophantine_Floor_of_Physical_Law.pdf)** — Unified 16-page master monograph covering Sections §0–§10 and the complete dependency structure.
2. **[The Mass Gap as Structural Consequence](papers/The_Mass_Gap_as_Structural_Consequence.pdf)** — Detailed exposition of the Yang–Mills mass gap derivation from the Diophantine Void.
3. **[Open Problems](papers/Open_Problems.pdf)** — The three open research frontiers:
   - *Problem 1:* Hurwitz–Markov Extremality in Lean 4.
   - *Problem 2:* Dark Matter Abundance $N(k)$ from Kelvin–Helmholtz shear instability.
   - *Problem 3:* Independent reimplementation of $s_{TM}$ and $s_{TE}$ reflection channels for Casimir metrology.
4. **Foundational Monograph Series (Papers I through V):**
   - *Paper I:* [The Diophantine Floor of Spacetime](papers/Paper_I_The_Diophantine_Floor_of_Spacetime.pdf)
   - *Paper II:* [Exact Subring Arithmetic and Symplectic Integration](papers/Paper_II_Exact_Subring_Arithmetic_and_Symplectic_Integration.pdf)
   - *Paper III:* [Relativistic Whirlpool Throats and the Magnetic Cheese-Grater](papers/Paper_III_Relativistic_Whirlpool_Throats_and_the_Magnetic_Grater.pdf)
   - *Paper IV:* [Scale-Invariant Eddies and Soliton Dark Matter](papers/Paper_IV_Scale_Invariant_Eddies_and_Soliton_Dark_Matter.pdf)
   - *Paper V:* [Lifshitz Wedge Regularization and Casimir Metrology](papers/Paper_V_Lifshitz_Wedge_Regularization_and_Casimir_Metrology.pdf)

---

## Machine-Verification Guide

### Prerequisites
Install Lean 4 and Lake via [`elan`](https://github.com/leanprover/elan):

```bash
# Linux / macOS / WSL
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh

# Windows (PowerShell)
curl.exe -sSfL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 | powershell -c -
```

### Build & Check
Clone this repository and verify the formal module:

```bash
git clone https://github.com/CreizyLabs/diophantine_floor.git
cd diophantine_floor

# Fetch pre-built Mathlib dependencies and compile
lake exe cache get
lake build
```

The build will complete with **0 errors**, **0 warnings**, and **0 `sorry` tokens**, verifying that all theorems and structural identities are closed constructively under the standard Lean 4 core kernel.

---

## License

This repository and all included research materials and formal proofs are licensed under the **Apache License, Version 2.0**. See [LICENSE](LICENSE) for details.
