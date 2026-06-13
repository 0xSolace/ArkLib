# Papers to fetch manually (IACR Cloudflare-blocked + paywalled) — 2026-06-13

The automated network here is **fully Cloudflare-403'd against `eprint.iacr.org`**, and the
following journal items are paywalled. Please grab these and drop the PDFs into
`~/papers/arklib/` with the suggested filename. Ordered by importance to the δ* / prize attack.

## TIER ★★★ — prize-critical, get first

| # | Paper | Identifier / DOI | URL | save as |
|---|-------|------------------|-----|---------|
| 1 | **ABF26** — Arnon, Boneh, Fenzi, *Open Problems in List Decoding and Correlated Agreement* (the prize paper; need §4.3 ε_ca/ε_mca capacity bounds + §5 LD⇒MCA collapse verbatim) | IACR ePrint **2026/680** | https://eprint.iacr.org/2026/680.pdf | `eprint-2026-680-ABF26.pdf` |
| 2 | **Okamoto** — *The Syndrome-Space Lens: A Complete Resolution of Proximity Gaps for RS* (claims resolution UP TO CAPACITY — must read adversarially to find the flaw; if correct it closes the prize) | IACR ePrint **2025/1712** | https://eprint.iacr.org/2025/1712.pdf | `eprint-2025-1712-SyndromeSpaceLens.pdf` |

## TIER ★★ — directly feeds the open core

| # | Paper | Identifier / DOI | URL | save as |
|---|-------|------------------|-----|---------|
| 3 | **Hab25** — Haböck, *A note on mutual correlated agreement for RS* (Johnson lane; the residual now supplied by BCHKS25) | IACR ePrint **2025/2110** | https://eprint.iacr.org/2025/2110.pdf | `eprint-2025-2110-Hab25.pdf` |
| 4 | **Diamond–Gruen** — `n^τ` proximity gap refuted ∀τ (char-2 capacity barrier) | IACR ePrint **2025/2010** | https://eprint.iacr.org/2025/2010.pdf | `eprint-2025-2010-DiamondGruen.pdf` |
| 5 | **Li–Wan** — *k-subset sum over finite fields of characteristic 2* (char-2-native `C(n,k)/q` + Weil error — strongest char-2 ℓ-word supply lever for `CubicSupplyCountermodel`) | DOI **10.1016/j.ffa.2019.06.004** (Finite Fields Appl. 59 (2019), S1071579719300462) | https://doi.org/10.1016/j.ffa.2019.06.004 | `LiWan-char2-ksubsetsum.pdf` |
| 6 | **Heath-Brown–Konyagin** — *New bounds for Gauss sums derived from k-th powers* (the `E⁺(G) ≪ \|G\|^{5/2}` source) | DOI **10.1093/qjmath/51.2.221** (Q. J. Math. 51 (2000) 221–235) | https://doi.org/10.1093/qjmath/51.2.221 | `HeathBrownKonyagin-2000-gausssums.pdf` |

## TIER ★ — completeness / transfer

| # | Paper | Identifier / DOI | URL | save as |
|---|-------|------------------|-----|---------|
| 7 | **"a small multiplicative subgroup is not a sumset"** (superpoly evidence for ℓ-fold subset-sumset) | Finite Fields Appl. (S1071579720300149); DOI **10.1016/j.ffa.2020.101724** | https://doi.org/10.1016/j.ffa.2020.101724 | `subgroup-not-a-sumset.pdf` |
| 8 | **Cilleruelo–Garaev** — *Concentration of points on curves over prime fields* (GAFA 2011 journal version; have the arXiv 1803.02165 cousin, want the GAFA original) | DOI **10.1007/s00039-011-0127-6** | https://doi.org/10.1007/s00039-011-0127-6 | `CillerueloGaraev-GAFA2011.pdf` |
| 9 | **Bordage et al.** | IACR ePrint **2025/2051** | https://eprint.iacr.org/2025/2051.pdf | `eprint-2025-2051-Bordage.pdf` |
| 10 | **Mohnblatt–Wagner** — MCA ⇒ FRIDA opening-consistency | IACR ePrint **2026/1055** | https://eprint.iacr.org/2026/1055.pdf | `eprint-2026-1055-MohnblattWagner.pdf` |
| 11 | **Garreta–Mohnblatt–Wagner** — Lean4 round-by-round FRI soundness (formal substrate; also check for a GitHub repo) | IACR ePrint **2025/1993** | https://eprint.iacr.org/2025/1993.pdf | `eprint-2025-1993-GMW.pdf` |
| 12 | **Fenzi–Sanso** — small-field hash-based SNARGs less sound than conjectured | IACR ePrint **2025/2197** | https://eprint.iacr.org/2025/2197.pdf | `eprint-2025-2197-FenziSanso.pdf` |

---
**Already acquired (no action needed):** 74 PDFs in `~/papers/arklib/`; full index in
`docs/kb/deltastar-acquisition-2026-06-13.md`. BCHKS25 is on disk as `eccc-tr25-169.pdf`
(= ePrint 2025/2055); GG25 as `late2025/goyal_guruswami_eccc166.pdf` + `arxiv-2601.10047`.
