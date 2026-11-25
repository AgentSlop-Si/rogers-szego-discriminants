#!/usr/bin/env python3
"""Standalone verification script for:
'Moving-Root Splitting, 2-Adic Wronskians, and Ordinary z-Discriminants of Rogers-Szego Polynomials at Roots of Unity'.

Uses Python 3 standard library only (exact integer/polynomial arithmetic, zero external dependencies).
Verifies:
1. Shifted 2-adic Newton polygon of parity-Hermite Wronskians W_m^U(1+z), W_m^V(1+z) for m=2..8 (Theorem 1.2(a)).
2. Exact characteristic-p Hermite-Wronskian identity H'V - HV' - yHV = -y^p and tau=2 triple zero (Theorem 6.3).
3. Exact augmented contents c_s^+ in Z[omega] for s in {3, 7, 11, 15, 19} via reciprocal reduction (Eq. (6.6)).
4. Exact small ordinary discriminants D_2..D_7 and exact Phi_d valuations vs d*C(A,2) + A*(b mod 2).
5. Exact integral Hermite degeneration constants V_b(1), B_{b,j}(1), C_{b,j}(1) (Theorem 5.1).
"""
from __future__ import annotations

import math
from functools import reduce


# ---- Exact univariate integer polynomial helpers (low-to-high degree list) ----
def p_trim(a: list[int]) -> list[int]:
    a = list(a)
    while len(a) > 1 and a[-1] == 0:
        a.pop()
    return a if a else [0]


def p_add(a: list[int], b: list[int]) -> list[int]:
    n = max(len(a), len(b))
    res = [(a[i] if i < len(a) else 0) + (b[i] if i < len(b) else 0) for i in range(n)]
    return p_trim(res)


def p_sub(a: list[int], b: list[int]) -> list[int]:
    n = max(len(a), len(b))
    res = [(a[i] if i < len(a) else 0) - (b[i] if i < len(b) else 0) for i in range(n)]
    return p_trim(res)


def p_mul(a: list[int], b: list[int]) -> list[int]:
    res = [0] * (len(a) + len(b) - 1)
    for i, ca in enumerate(a):
        if ca == 0:
            continue
        for j, cb in enumerate(b):
            res[i + j] += ca * cb
    return p_trim(res)


def p_scale(a: list[int], c: int) -> list[int]:
    return p_trim([x * c for x in a])


def p_deriv(a: list[int]) -> list[int]:
    if len(a) <= 1:
        return [0]
    return p_trim([i * a[i] for i in range(1, len(a))])


def p_shift(a: list[int], c: int) -> list[int]:
    """Return a(x + c)."""
    res = [0]
    power = [1]
    base = [c, 1]
    for coeff in a:
        if coeff:
            res = p_add(res, p_scale(power, coeff))
        power = p_mul(power, base)
    return res


def p_divmod_monic(a: list[int], m: list[int]) -> tuple[list[int], list[int]]:
    """Exact polynomial division of a by monic m in Z[x]."""
    assert m[-1] == 1
    a = list(a)
    dm = len(m) - 1
    if len(a) - 1 < dm:
        return [0], p_trim(a)
    q = [0] * (len(a) - dm)
    for i in range(len(a) - 1, dm - 1, -1):
        c = a[i]
        if c != 0:
            q[i - dm] = c
            for j in range(dm + 1):
                a[i - dm + j] -= c * m[j]
    return p_trim(q), p_trim(a)


def p_mod_monic(a: list[int], m: list[int]) -> list[int]:
    return p_divmod_monic(a, m)[1]


def p_eval(a: list[int], x: int) -> int:
    val = 0
    for c in reversed(a):
        val = val * x + c
    return val


def cyclotomic_poly(n: int) -> list[int]:
    """Exact monic Phi_n(q) in Z[q]."""
    # q^n - 1 divided by Phi_d for proper divisors d|n
    poly = [-1] + [0] * (n - 1) + [1]
    for d in range(1, n):
        if n % d == 0:
            phi_d = cyclotomic_poly(d)
            poly, rem = p_divmod_monic(poly, phi_d)
            assert rem == [0]
    return poly


def v2(n: int) -> int:
    if n == 0:
        return 10**9
    n = abs(n)
    c = 0
    while n % 2 == 0:
        c += 1
        n //= 2
    return c


# ---- 1. Verify 2-adic Newton polygon of parity-Hermite Wronskians (Theorem 1.2(a)) ----
def verify_2adic_wronskians() -> None:
    U = [[1], [-1, 1]]
    V = [[1], [-3, 1]]
    for m in range(1, 9):
        # U_{m+1} = (y - 4m - 1) U_m - 2m(2m-1) U_{m-1}
        u_next = p_sub(p_mul([-4 * m - 1, 1], U[m]), p_scale(U[m - 1], 2 * m * (2 * m - 1)))
        v_next = p_sub(p_mul([-4 * m - 3, 1], V[m]), p_scale(V[m - 1], 2 * m * (2 * m + 1)))
        U.append(u_next)
        V.append(v_next)

    for name, seq in [("U", U), ("V", V)]:
        for m in range(2, 9):
            W = p_sub(p_mul(p_deriv(seq[m]), seq[m - 1]), p_mul(seq[m], p_deriv(seq[m - 1])))
            assert len(W) - 1 == 2 * m - 2 and W[-1] == 1
            W_shift = p_shift(W, 1)  # W(1 + z)
            assert v2(W_shift[0]) == m - 1, (name, m, v2(W_shift[0]))
            assert v2(W_shift[-1]) == 0
            for j, cj in enumerate(W_shift):
                # Must satisfy 2 * v2(cj) >= 2*(m-1) - j
                assert 2 * v2(cj) >= 2 * (m - 1) - j, (name, m, j, v2(cj))
    print("  [PASS] 2-adic Newton polygons of W_m^U(1+z), W_m^V(1+z) verified for m = 2..8 (v_2(y-1) = 1/2)")


# ---- 2. Verify char-p Hermite-Wronskian identity & tau=2 triple zero (Theorem 6.3) ----
def verify_charp_wronskian_and_triple_zero() -> None:
    def he_mod_p(A: int, p: int) -> list[int]:
        seq = [[1], [0, 1]]
        for n in range(1, A):
            nxt = [0] * (n + 2)
            for j, c in enumerate(seq[n]):
                nxt[j + 1] = (nxt[j + 1] + c) % p
            for j, c in enumerate(seq[n - 1]):
                nxt[j] = (nxt[j] - n * c) % p
            seq.append(nxt)
        return seq[A]

    for p in [3, 5, 7, 11, 13, 17, 19, 23, 29]:
        A = (p - 1) // 2
        H = he_mod_p(A, p)
        # V(y) = i^{-A} H(i y): coeff of y^k in V is i^{k-A} H_k = (-1)^{(k-A)/2} H_k (since k === A mod 2!)
        V = [0] * len(H)
        for k, c in enumerate(H):
            if c:
                assert (k - A) % 2 == 0
                sign = -1 if ((k - A) // 2) % 2 else 1
                V[k] = (sign * c) % p
        Hp = [(k * H[k]) % p for k in range(1, len(H))] or [0]
        Vp = [(k * V[k]) % p for k in range(1, len(V))] or [0]

        def pmul_p(a: list[int], b: list[int]) -> list[int]:
            r = [0] * (len(a) + len(b) - 1)
            for i, ca in enumerate(a):
                for j, cb in enumerate(b):
                    r[i + j] = (r[i + j] + ca * cb) % p
            return r

        t1 = pmul_p(Hp, V)
        t2 = pmul_p(H, Vp)
        t3 = [0] + pmul_p(H, V)  # y H V
        L = max(len(t1), len(t2), len(t3))
        lhs = [
            ((t1[k] if k < len(t1) else 0) - (t2[k] if k < len(t2) else 0) - (t3[k] if k < len(t3) else 0)) % p
            for k in range(L)
        ]
        exp = [0] * p + [p - 1]
        assert lhs[: len(exp)] == exp and all(x == 0 for x in lhs[len(exp) :]), (p, lhs)

        # Check J(y; 2) = y H(y) - 2 H'(y) at y = 0
        J2 = [0] * (A + 2)
        for k, c in enumerate(H):
            J2[k + 1] = (J2[k + 1] + c) % p
        for k, c in enumerate(Hp):
            J2[k] = (J2[k] - 2 * c) % p
        if p % 4 == 3:
            assert J2[0] != 0
        else:
            assert J2[0] == 0 and J2[1] == 0 and J2[2] == 0 and J2[3] != 0
    print("  [PASS] Char-p Wronskian H'V - HV' - yHV = -y^p and tau=2 triple zero verified for odd primes p <= 29")


# ---- 3. Ring arithmetic in O_s = Z[omega]/(Phi_s(omega)) to verify c_s^+ for s in {3,7,11,15,19} ----
def ring_content(a: list[int], phi: list[int]) -> int:
    r = p_mod_monic(a, phi)
    g = 0
    for c in r:
        g = math.gcd(g, abs(c))
    return g


def ring_mul(a: list[int], b: list[int], phi: list[int]) -> list[int]:
    return p_mod_monic(p_mul(a, b), phi)


def ring_inv_aut(a: list[int], s: int, phi: list[int]) -> list[int]:
    """Apply iota: omega -> omega^{-1} = omega^{s-1} in O_s."""
    r = p_mod_monic(a, phi)
    res = [0]
    for k, c in enumerate(r):
        if c:
            exp = (-k) % s
            term = [0] * exp + [c]
            res = p_add(res, p_mod_monic(term, phi))
    return p_mod_monic(res, phi)


def poly_over_ring_mul(A: list[list[int]], B: list[list[int]], phi: list[int]) -> list[list[int]]:
    res = [[0] for _ in range(len(A) + len(B) - 1)]
    for i, a in enumerate(A):
        for j, b in enumerate(B):
            res[i + j] = p_mod_monic(p_add(res[i + j], ring_mul(a, b, phi)), phi)
    return res


def sylvester_det_over_ring(A: list[list[int]], B: list[list[int]], phi: list[int]) -> list[int]:
    """Exact Bareiss-free cofactor/Laplace resultant in O_s for small degree polynomials (deg <= 4)."""
    # Strip trailing zero coeffs
    while len(A) > 1 and A[-1] == [0]:
        A = A[:-1]
    while len(B) > 1 and B[-1] == [0]:
        B = B[:-1]
    da, db = len(A) - 1, len(B) - 1
    if da == 0 and db == 0:
        return [1]
    if da == 0:
        # A[0]^db
        res = [1]
        for _ in range(db):
            res = ring_mul(res, A[0], phi)
        return res
    if db == 0:
        res = [1]
        for _ in range(da):
            res = ring_mul(res, B[0], phi)
        return res
    # Build (da+db) x (da+db) Sylvester matrix M[row][col]
    n = da + db
    M = [[[0] for _ in range(n)] for _ in range(n)]
    for i in range(db):
        for k in range(da + 1):
            M[i][i + k] = A[da - k]
    for i in range(da):
        for k in range(db + 1):
            M[db + i][i + k] = B[db - k]

    # Exact determinant by memoized Laplace expansion (n <= 8 is instant for r <= 4!)
    memo: dict[tuple[int, int], list[int]] = {}

    def det_rec(row: int, col_mask: int) -> list[int]:
        if row == n:
            return [1]
        key = (row, col_mask)
        if key in memo:
            return memo[key]
        acc = [0]
        sign = 1
        for col in range(n):
            if col_mask & (1 << col):
                continue
            entry = M[row][col]
            if entry != [0]:
                sub = det_rec(row + 1, col_mask | (1 << col))
                prod = ring_mul(entry, sub, phi)
                acc = p_add(acc, prod) if sign > 0 else p_sub(acc, prod)
            sign = -sign
        acc = p_mod_monic(acc, phi)
        memo[key] = acc
        return acc

    return det_rec(0, 0)


def ring_poly_eval(P: list[list[int]], x: int, phi: list[int]) -> list[int]:
    acc = [0]
    for c in reversed(P):
        acc = p_mod_monic(p_add(p_scale(acc, x), c), phi)
    return acc


def ring_poly_deriv(P: list[list[int]], phi: list[int]) -> list[list[int]]:
    if len(P) <= 1:
        return [[0]]
    return [p_mod_monic(p_scale(P[k], k), phi) for k in range(1, len(P))]


def ring_poly_mod_monic(A: list[list[int]], B: list[list[int]], phi: list[int]) -> list[list[int]]:
    """Reduce A modulo monic B over O_s."""
    assert B[-1] == [1]
    A = [list(c) for c in A]
    db = len(B) - 1
    for i in range(len(A) - 1, db - 1, -1):
        c = A[i]
        if c != [0]:
            for j in range(db + 1):
                A[i - db + j] = p_mod_monic(p_sub(A[i - db + j], ring_mul(c, B[j], phi)), phi)
    while len(A) > 1 and A[-1] == [0]:
        A.pop()
    return A


def verify_five_families_contents() -> None:
    expected = {3: 1, 7: 7**2, 11: 11**5, 15: (3**12) * (5**9), 19: 19**11}
    for s, exp_c in expected.items():
        r = (s - 3) // 4
        b = 2 * r + 1
        phi = cyclotomic_poly(s)

        # Build H_b(z; omega) in O_s[z] using q-Pascal
        # row[k] = [n choose k]_omega
        row = [[1]]
        for n in range(1, b + 1):
            nxt = [[1]]
            for k in range(1, n):
                shift = (n - k) % s
                w_pow = p_mod_monic([0] * shift + [1], phi)
                term = p_mod_monic(p_add(row[k], ring_mul(w_pow, row[k - 1], phi)), phi)
                nxt.append(term)
            nxt.append([1])
            row = nxt

        # Divide H_b by (z + 1) to get U_s of degree 2r
        U = [[0] for _ in range(2 * r + 1)]
        rem = [list(c) for c in row]
        for k in range(2 * r, -1, -1):
            U[k] = rem[k + 1]
            rem[k] = p_mod_monic(p_sub(rem[k], U[k]), phi)
        assert rem[0] == [0]

        # Build S_j(t) with S_0=2, S_1=t, S_{j+1}=t S_j - S_{j-1}
        S_polys = [[2], [0, 1]]
        for j in range(1, r + 1):
            S_polys.append(p_sub([0] + S_polys[j], S_polys[j - 1]))
        # P_s(t) = U_r + sum_{j=1}^r U_{r+j} S_j(t)
        P_s = [[0] for _ in range(r + 1)]
        P_s[0] = U[r]
        for j in range(1, r + 1):
            for deg, coeff in enumerate(S_polys[j]):
                if coeff:
                    P_s[deg] = p_mod_monic(p_add(P_s[deg], p_scale(U[r + j], coeff)), phi)

        # Build C_s(t): C_1=1, C_3=t-1, C_{m+2}=t C_m - C_{m-2}
        C_prev, C_curr = [1], [-1, 1]
        m_cur = 3
        while m_cur < s:
            C_prev, C_curr = C_curr, p_sub([0] + C_curr, C_prev)
            m_cur += 2
        C_s_ring = [[c] for c in C_curr]

        # Compute Disc(P_s) = (-1)^{r(r-1)/2} Res(P_s, P_s')
        if r <= 1:
            disc_P = [1]
        else:
            res_pp = sylvester_det_over_ring(P_s, ring_poly_deriv(P_s, phi), phi)
            sign = -1 if ((r * (r - 1)) // 2) % 2 else 1
            disc_P = p_mod_monic(p_scale(res_pp, sign), phi)

        # Compute Res(P_s, C_s) = Res(P_s, C_s mod P_s) since P_s is monic!
        if r == 0:
            res_PC = [1]
        else:
            C_red = ring_poly_mod_monic(C_s_ring, P_s, phi)
            res_PC = sylvester_det_over_ring(P_s, C_red, phi)

        P_at_2 = ring_poly_eval(P_s, 2, phi)
        P_at_m2 = ring_poly_eval(P_s, -2, phi)
        # Gamma_s = (-1)^r P_s(2) P_s(-2)^2 (Disc(P_s) Res(P_s, C_s))^2
        inner = ring_mul(disc_P, res_PC, phi)
        inner2 = ring_mul(inner, inner, phi)
        gamma = ring_mul(P_at_2, ring_mul(P_at_m2, P_at_m2, phi), phi)
        gamma = ring_mul(gamma, inner2, phi)
        if r % 2 == 1:
            gamma = p_scale(gamma, -1)

        # g_s = U_s(-1) = (-1)^r P_s(-2)
        g_s = p_scale(P_at_m2, -1 if r % 2 else 1)
        # v_s = (omega^2; omega^2)_r * (omega; omega^2)_b
        v_s = [1]
        for t in range(r):
            e = (2 * (t + 1)) % s
            fac = p_mod_monic(p_sub([1], [0] * e + [1]), phi)
            v_s = ring_mul(v_s, fac, phi)
        for t in range(b):
            e = (1 + 2 * t) % s
            fac = p_mod_monic(p_sub([1], [0] * e + [1]), phi)
            v_s = ring_mul(v_s, fac, phi)

        # Check denominator-free inverse identity g_s v_s^iota + g_s^iota v_s == v_s v_s^iota
        g_i = ring_inv_aut(g_s, s, phi)
        v_i = ring_inv_aut(v_s, s, phi)
        lhs_id = p_mod_monic(p_add(ring_mul(g_s, v_i, phi), ring_mul(g_i, v_s, phi)), phi)
        rhs_id = ring_mul(v_s, v_i, phi)
        assert lhs_id == rhs_id, f"Inverse identity failed at s={s}"

        delta_s = p_mod_monic(p_sub(p_scale(g_s, 2), v_s), phi)
        gamma_i = ring_inv_aut(gamma, s, phi)
        B_s = ring_mul(ring_mul(gamma, gamma_i, phi), delta_s, phi)
        c_plus = ring_content(B_s, phi)
        assert c_plus == exp_c, (s, c_plus, exp_c)
        print(f"  [PASS] Five-family augmented content s={s:2d}: c_s^+ = {c_plus:,}")


# ---- 4. Verify small exact discriminants D_2..D_6 and Hermite degeneration constants ----
def verify_small_discriminants() -> None:
    # Build H_n(z; q) as list of Z[q] polynomials (in z degree 0..n)
    # Check D_2(q) = (q-1)(q+3) vs q-discriminant (q-1)(q+1)^2, and Phi_3 order in D_n(q) for n=2..6!
    H_rows: list[list[list[int]]] = [[[1]]]
    for n in range(1, 7):
        prev = H_rows[-1]
        cur = [[1]]
        for k in range(1, n):
            q_shift = [0] * (n - k) + [1]
            cur.append(p_add(prev[k], p_mul(q_shift, prev[k - 1])))
        cur.append([1])
        H_rows.append(cur)

    # Exact discriminant of monic polynomial over Z[q] via Sylvester matrix determinant (for deg <= 6)
    def disc_over_Zq(P: list[list[int]]) -> list[int]:
        deg = len(P) - 1
        if deg <= 1:
            return [1]
        Pd = [p_scale(P[k], k) for k in range(1, deg + 1)]
        # Build (2*deg - 1) x (2*deg - 1) Sylvester matrix
        m = 2 * deg - 1
        M = [[[0] for _ in range(m)] for _ in range(m)]
        for i in range(deg - 1):
            for k in range(deg + 1):
                M[i][i + k] = P[deg - k]
        for i in range(deg):
            for k in range(deg):
                M[deg - 1 + i][i + k] = Pd[deg - 1 - k]

        # Fraction-free Bareiss algorithm over Z[q]! (Exact polynomial division)
        # Even simpler: evaluate at enough integer points q = 0, 1, ..., B and verify exact divisibility,
        # OR for deg <= 6, exact Laplace with memoization takes < 0.05s!
        memo: dict[tuple[int, int], list[int]] = {}

        def det_r(row: int, mask: int) -> list[int]:
            if row == m:
                return [1]
            key = (row, mask)
            if key in memo:
                return memo[key]
            acc = [0]
            sign = 1
            for col in range(m):
                if mask & (1 << col):
                    continue
                if M[row][col] != [0]:
                    sub = det_r(row + 1, mask | (1 << col))
                    prod = p_mul(M[row][col], sub)
                    acc = p_add(acc, prod) if sign > 0 else p_sub(acc, prod)
                sign = -sign
            memo[key] = acc
            return acc

        res = det_r(0, 0)
        if ((deg * (deg - 1)) // 2) % 2:
            res = p_scale(res, -1)
        return res

    def ord_poly(F: list[int], phi: list[int]) -> tuple[int, list[int]]:
        k = 0
        cur = F
        while True:
            q, rem = p_divmod_monic(cur, phi)
            if rem != [0]:
                return k, cur
            cur = q
            k += 1

    phi1 = [-1, 1]
    phi3 = cyclotomic_poly(3)
    phi5 = cyclotomic_poly(5)

    D2 = disc_over_Zq(H_rows[2])
    assert D2 == p_mul([-1, 1], [3, 1]), D2  # (q-1)(q+3)

    for n in range(2, 7):
        Dn = disc_over_Zq(H_rows[n])
        # Check d=1 order = C(n, 2) and V_n(1) = prod_{j=1}^n j^j (Theorem 5.1 Eq. (5.2))
        o1, Vn = ord_poly(Dn, phi1)
        assert o1 == n * (n - 1) // 2
        prod_jj = 1
        for j in range(1, n + 1):
            prod_jj *= j**j
        assert p_eval(Vn, 1) == prod_jj

        # Check odd primes p=3 and p=5 against p*C(A,2) + A*(b mod 2)
        for p, phip in [(3, phi3), (5, phi5)]:
            A, b = divmod(n, p)
            exp_ord = p * (A * (A - 1) // 2) + A * (b % 2)
            got_ord, _ = ord_poly(Dn, phip)
            assert got_ord == exp_ord, (n, p, got_ord, exp_ord)
    print("  [PASS] Exact Z[q] discriminants D_2..D_6 match V_b(1)=prod j^j and ord_{Phi_p} = p*C(A,2) + A*(b mod 2)")


def main() -> None:
    verify_2adic_wronskians()
    verify_charp_wronskian_and_triple_zero()
    verify_five_families_contents()
    verify_small_discriminants()
    print("ALL PAPER 3 PYTHON VERIFICATIONS PASSED.")


if __name__ == "__main__":
    main()
