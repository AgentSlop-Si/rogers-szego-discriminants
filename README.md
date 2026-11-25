# Paper 3: Moving-Root Splitting, 2-Adic Wronskians, and Ordinary z-Discriminants of Rogers-Szegő Polynomials at Roots of Unity

## Files
- `main.tex` — Submission-ready `amsart` LaTeX manuscript.
- `references.bib` — Clean BibTeX bibliography.
- `certify_composite_orders.cpp` + `composite_witnesses.csv` — Standalone C++17 (stdlib only) dual-witness verifier certifying all 76 odd composite orders (`d <= 255` plus `d=289, 343`; 10,860 nonconstant residuals; 21,720 exact finite-field checks).
- `verify_rogers_szego.py` — Standalone Python 3 (stdlib only) verifier checking the 2-adic Newton polygons of parity-Hermite Wronskians, characteristic-$p$ Wronskian identity and $\tau=2$ triple zero, exact augmented contents $c_s^+$ for $s\in\{3,7,11,15,19\}$, exact small $\mathbb{Z}[q]$ discriminants $D_2$--$D_6$, and Hermite degeneration constants.

## How to Compile PDF
1. Upload `main.tex` and `references.bib` to Overleaf (or compile locally with `latexmk -pdf main.tex`).
2. Edit `\author`, `\email`, and `\address` at the top of `main.tex` if desired.
3. Optional before journal submission: inspect the 6-page paywalled paper Zhedanov (1997), *Int. J. Mod. Phys. A* 12(1), 289–294, via a university library or author copy, and remove the abstract-only caveat in Section 9.

## Suggested Submission Metadata
- **arXiv primary / secondary:** `math.CA` (Classical Analysis and ODEs) / `math.NT` (Number Theory)
- **MSC 2020:** Primary `33D45`, `11R18`; Secondary `11C08`, `11S05`, `33C45`
- **Target journals (zero-fee):** *SIGMA* (diamond OA, fast turnaround, ideal fit), *The Ramanujan Journal*, *Journal of Approximation Theory*.

## Verify Computations
```bash
python3 verify_rogers_szego.py
c++ -O3 -std=c++17 certify_composite_orders.cpp -o /tmp/certify_composite_orders
/tmp/certify_composite_orders composite_witnesses.csv
```
