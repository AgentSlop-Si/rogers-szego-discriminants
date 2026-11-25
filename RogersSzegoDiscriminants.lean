/-
  RogersSzegoDiscriminants.lean

  Zero-dependency Lean 4 formal verification companion to:
  "Moving-Root Splitting, 2-Adic Wronskians, and Ordinary z-Discriminants of
   Rogers-Szego Polynomials at Roots of Unity"
  by Daniyar Kuttymbek, Adilkhan Kuttymbek, Dayana Kuttymbek,
  Amina Kolpenova, and Mukhammadali Kottumbekov.

  Uses Lean 4 core (`Init`) only — no Mathlib or external dependencies required.
  Verify with: `lean RogersSzegoDiscriminants.lean`

  Contents:
    Part 1: Symbolic proof of the central 2-adic parity-Hermite Wronskian theorem
            for ALL m >= 1 (Theorem 1.2(a), Section 4, zero `sorry`):
      - Explicit ring Z[pi] (pi^2 = 2) and ring homomorphism modPi : Z[pi] -> F_2.
      - Exact polynomial rings Z[pi][X] and F_2[X] with Cauchy multiplication and formal derivative.
      - Exact scaled parity-Hermite recurrences P_m, Q_m in Z[pi][X].
      - Symbolic proof for ALL m : Nat that modPiPoly(P_m) = rho_m = modPiPoly(Q_m),
        with rho_{2k} = (X^2 + 1)^k and rho_{2k+1} = X * (X^2 + 1)^k in F_2[X].
      - Symbolic proof for ALL m >= 1 that
          modPiPoly(W_m^P) = (X^2 + 1)^(m - 1)  and  modPiPoly(W_m^Q) = (X^2 + 1)^(m - 1),
        and that the constant term is ALWAYS a 2-adic unit (modPi = true),
        proving the exact single-segment Newton polygon / v_2(y - 1) = 1/2 for all m >= 2.
    Part 2: Symbolic discriminant exponent & inverse-pair identities (zero `sorry`):
      - Theorem 1.1: Exact exponent identities for C_sep and C_ov (K, L = K + A, d*A^2 - K, d*A^2 + 2A - L).
      - Section 1 / Section 9: Ordinary vs. q-difference discriminant of H_2(z; q)
        ((1 + q)^2 - 4 = (q - 1)*(q + 3) vs (q - 1)*(q + 1)^2).
      - Theorem 6.3: Exact inverse-pair symmetry t(tau') = -t(tau) when 1/tau + 1/tau' = 1.
    Part 3: Pure-kernel exact finite certificates (`decide` / `decide +kernel`, zero `native_decide`):
      - Unscaled shifted 2-adic Newton polygons of W_m^U(1 + z), W_m^V(1 + z) over Z[z] for m = 2..6.
      - Characteristic-p Wronskian identity H'V - HV' - yHV = -y^p and tau = 2 triple-zero
        dichotomy for odd primes p in {3, 5, 7, 11, 13, 17, 19}.
      - Exact Z[omega]/(Phi_s) inverse identity g_s v_s^iota + g_s^iota v_s = v_s v_s^iota
        and exact augmented contents c_3^+ = 1, c_7^+ = 7^2 = 49, c_11^+ = 11^5 = 161051
        (Eqs. (6.7) & (6.9) / Theorem 1.4(a) for s in {3, 7, 11}).
      - Dual-witness, dual-algorithm finite-field certification (Theorem 1.4(b), matching
        `certify_composite_orders.cpp` and `composite_witnesses.csv`) for odd composite
        orders d in {9, 15, 21, 25}.
-/

namespace RogersSzegoDiscriminants

/-! ## Part 1: Symbolic Proof of Theorem 1.2(a) for ALL `m ≥ 1` -/

/-- The quadratic integer ring `Z[π]` with `π² = 2`, represented as `re + im * π`. -/
structure ZPi where
  re : Int
  im : Int
  deriving DecidableEq

namespace ZPi
def zero : ZPi := ⟨0, 0⟩
def one : ZPi := ⟨1, 0⟩
def pi : ZPi := ⟨0, 1⟩
def ofInt (n : Int) : ZPi := ⟨n, 0⟩
def ofNat (n : Nat) : ZPi := ⟨(n : Int), 0⟩
def mulPiInt (n : Int) : ZPi := ⟨0, n⟩

def add (a b : ZPi) : ZPi := ⟨a.re + b.re, a.im + b.im⟩
def sub (a b : ZPi) : ZPi := ⟨a.re - b.re, a.im - b.im⟩
def mul (a b : ZPi) : ZPi := ⟨a.re * b.re + 2 * a.im * b.im, a.re * b.im + a.im * b.re⟩

/-- Reduction modulo the uniformizer `π` of `Q_2(π)` to `F_2` (`Bool`: `false = 0`, `true = 1`). -/
def modPi (x : ZPi) : Bool := (x.re % 2) != 0

theorem modPi_zero : modPi zero = false := rfl
theorem modPi_one : modPi one = true := rfl
theorem modPi_pi : modPi pi = false := rfl
theorem modPi_mulPiInt (n : Int) : modPi (mulPiInt n) = false := rfl

theorem modPi_ofNat (n : Nat) : modPi (ofNat n) = (n % 2 == 1) := by
  unfold modPi ofNat
  by_cases h : n % 2 = 0
  · have h1 : ((n : Int) % 2) = 0 := by omega
    simp [h, h1]
  · have h2 : n % 2 = 1 := by omega
    have h1 : ((n : Int) % 2) = 1 := by omega
    simp [h2, h1]

theorem modPi_add (a b : ZPi) : modPi (add a b) = xor (modPi a) (modPi b) := by
  unfold modPi add
  have ha : a.re % 2 = 0 ∨ a.re % 2 = 1 := by omega
  have hb : b.re % 2 = 0 ∨ b.re % 2 = 1 := by omega
  rcases ha with ha0 | ha1 <;> rcases hb with hb0 | hb1
  · have h : (a.re + b.re) % 2 = 0 := by omega
    simp [ha0, hb0, h]
  · have h : (a.re + b.re) % 2 = 1 := by omega
    simp [ha0, hb1, h]
  · have h : (a.re + b.re) % 2 = 1 := by omega
    simp [ha1, hb0, h]
  · have h : (a.re + b.re) % 2 = 0 := by omega
    simp [ha1, hb1, h]

theorem modPi_sub (a b : ZPi) : modPi (sub a b) = xor (modPi a) (modPi b) := by
  unfold modPi sub
  have ha : a.re % 2 = 0 ∨ a.re % 2 = 1 := by omega
  have hb : b.re % 2 = 0 ∨ b.re % 2 = 1 := by omega
  rcases ha with ha0 | ha1 <;> rcases hb with hb0 | hb1
  · have h : (a.re - b.re) % 2 = 0 := by omega
    simp [ha0, hb0, h]
  · have h : (a.re - b.re) % 2 = 1 := by omega
    simp [ha0, hb1, h]
  · have h : (a.re - b.re) % 2 = 1 := by omega
    simp [ha1, hb0, h]
  · have h : (a.re - b.re) % 2 = 0 := by omega
    simp [ha1, hb1, h]

theorem modPi_mul (a b : ZPi) : modPi (mul a b) = (modPi a && modPi b) := by
  unfold modPi mul
  have heven : (a.re * b.re + 2 * a.im * b.im) % 2 = (a.re * b.re) % 2 := by
    have h2 : 2 * a.im * b.im = (a.im * b.im) * 2 := by ac_rfl
    rw [h2, Int.add_mul_emod_self_right]
  rw [heven]
  have ha : a.re % 2 = 0 ∨ a.re % 2 = 1 := by omega
  have hb : b.re % 2 = 0 ∨ b.re % 2 = 1 := by omega
  rcases ha with ha0 | ha1 <;> rcases hb with hb0 | hb1
  · have h : (a.re * b.re) % 2 = 0 := by rw [Int.mul_emod, ha0, hb0]; rfl
    simp [ha0, hb0, h]
  · have h : (a.re * b.re) % 2 = 0 := by rw [Int.mul_emod, ha0, hb1]; rfl
    simp [ha0, hb1, h]
  · have h : (a.re * b.re) % 2 = 0 := by rw [Int.mul_emod, ha1, hb0]; rfl
    simp [ha1, hb0, h]
  · have h : (a.re * b.re) % 2 = 1 := by rw [Int.mul_emod, ha1, hb1]; rfl
    simp [ha1, hb1, h]
end ZPi

/-- Polynomials over `Z[π]` and `F_2` represented as coefficient functions `Nat → R`. -/
abbrev PolyZPi := Nat → ZPi
abbrev PolyF2 := Nat → Bool

def oneZPi : PolyZPi := fun k => if k == 0 then ZPi.one else ZPi.zero
def shiftXZPi (f : PolyZPi) : PolyZPi
  | 0 => ZPi.zero
  | k + 1 => f k
def subZPi (f g : PolyZPi) : PolyZPi := fun k => ZPi.sub (f k) (g k)
def scaleZPi (c : ZPi) (f : PolyZPi) : PolyZPi := fun k => ZPi.mul c (f k)
def derivZPi (f : PolyZPi) : PolyZPi := fun k => ZPi.mul (ZPi.ofNat (k + 1)) (f (k + 1))

def cauchySumZPi (f g : PolyZPi) (k : Nat) : Nat → ZPi
  | 0 => ZPi.mul (f 0) (g k)
  | i + 1 => ZPi.add (cauchySumZPi f g k i) (ZPi.mul (f (i + 1)) (g (k - (i + 1))))

def mulZPi (f g : PolyZPi) : PolyZPi := fun k => cauchySumZPi f g k k

def zeroF2 : PolyF2 := fun _ => false
def oneF2 : PolyF2 := fun k => k == 0
def shiftXF2 (f : PolyF2) : PolyF2
  | 0 => false
  | k + 1 => f k
def addF2 (f g : PolyF2) : PolyF2 := fun k => xor (f k) (g k)
def scaleF2 (c : Bool) (f : PolyF2) : PolyF2 := fun k => c && f k
def derivF2 (f : PolyF2) : PolyF2 := fun k => ((k + 1) % 2 == 1) && f (k + 1)

def cauchySumF2 (f g : PolyF2) (k : Nat) : Nat → Bool
  | 0 => f 0 && g k
  | i + 1 => xor (cauchySumF2 f g k i) (f (i + 1) && g (k - (i + 1)))

def mulF2 (f g : PolyF2) : PolyF2 := fun k => cauchySumF2 f g k k

/-- Coefficientwise reduction `Z[π][X] → F_2[X]` modulo `π`. -/
def modPiPoly (f : PolyZPi) : PolyF2 := fun k => ZPi.modPi (f k)

theorem modPiPoly_one : modPiPoly oneZPi = oneF2 := by
  funext k; cases k <;> rfl

theorem modPiPoly_shiftX (f : PolyZPi) : modPiPoly (shiftXZPi f) = shiftXF2 (modPiPoly f) := by
  funext k; cases k <;> rfl

theorem modPiPoly_sub (f g : PolyZPi) : modPiPoly (subZPi f g) = addF2 (modPiPoly f) (modPiPoly g) := by
  funext k; exact ZPi.modPi_sub (f k) (g k)

theorem modPiPoly_scale (c : ZPi) (f : PolyZPi) :
    modPiPoly (scaleZPi c f) = scaleF2 (ZPi.modPi c) (modPiPoly f) := by
  funext k; exact ZPi.modPi_mul c (f k)

theorem modPiPoly_deriv (f : PolyZPi) : modPiPoly (derivZPi f) = derivF2 (modPiPoly f) := by
  funext k
  unfold modPiPoly derivZPi derivF2
  rw [ZPi.modPi_mul, ZPi.modPi_ofNat]

theorem modPiPoly_mul (f g : PolyZPi) : modPiPoly (mulZPi f g) = mulF2 (modPiPoly f) (modPiPoly g) := by
  funext k
  have hsum : ∀ i, ZPi.modPi (cauchySumZPi f g k i) = cauchySumF2 (modPiPoly f) (modPiPoly g) k i := by
    intro i
    induction i with
    | zero => exact ZPi.modPi_mul (f 0) (g k)
    | succ j ih =>
      unfold cauchySumZPi cauchySumF2
      rw [ZPi.modPi_add, ih, ZPi.modPi_mul]
      rfl
  exact hsum k

-- Basic F_2[X] polynomial algebra lemmas
theorem addF2_zero_right (f : PolyF2) : addF2 f zeroF2 = f := by
  funext k; simp [addF2, zeroF2]

theorem addF2_zero_left (f : PolyF2) : addF2 zeroF2 f = f := by
  funext k; simp [addF2, zeroF2]

theorem scaleF2_false (f : PolyF2) : scaleF2 false f = zeroF2 := by
  funext k; rfl

theorem scaleF2_true (f : PolyF2) : scaleF2 true f = f := by
  funext k; simp [scaleF2]

theorem mulF2_zero_left (g : PolyF2) : mulF2 zeroF2 g = zeroF2 := by
  funext k
  have h : ∀ i, cauchySumF2 zeroF2 g k i = false := by
    intro i; induction i with
    | zero => rfl
    | succ j ih => simp [cauchySumF2, zeroF2, ih]
  exact h k

theorem mulF2_zero_right (f : PolyF2) : mulF2 f zeroF2 = zeroF2 := by
  funext k
  have h : ∀ i, cauchySumF2 f zeroF2 k i = false := by
    intro i; induction i with
    | zero => simp [cauchySumF2, zeroF2]
    | succ j ih => simp [cauchySumF2, zeroF2, ih]
  exact h k

theorem mulF2_one_right (f : PolyF2) : mulF2 f oneF2 = f := by
  funext k
  have hzero : ∀ i, i < k → cauchySumF2 f oneF2 k i = false := by
    intro i hi
    induction i with
    | zero =>
      have hk : k ≠ 0 := by omega
      simp [cauchySumF2, oneF2, hk]
    | succ j ih =>
      have hne : k - (j + 1) ≠ 0 := by omega
      simp [cauchySumF2, oneF2, ih (by omega), hne]
  cases k with
  | zero => simp [mulF2, cauchySumF2, oneF2]
  | succ k' =>
    unfold mulF2 cauchySumF2
    rw [hzero k' (Nat.lt_succ_self k')]
    simp [oneF2]

theorem mulF2_shiftX_right (f g : PolyF2) : mulF2 f (shiftXF2 g) = shiftXF2 (mulF2 f g) := by
  funext k
  cases k with
  | zero => simp [mulF2, cauchySumF2, shiftXF2]
  | succ k' =>
    have hsum : ∀ i, i ≤ k' → cauchySumF2 f (shiftXF2 g) (k' + 1) i = cauchySumF2 f g k' i := by
      intro i hi
      induction i with
      | zero => rfl
      | succ j ih =>
        have hsub : k' + 1 - (j + 1) = (k' - (j + 1)) + 1 := by omega
        unfold cauchySumF2
        rw [ih (by omega), hsub]
        rfl
    change xor (cauchySumF2 f (shiftXF2 g) (k' + 1) k') (f (k' + 1) && shiftXF2 g ((k' + 1) - (k' + 1)))
         = cauchySumF2 f g k' k'
    rw [hsum k' (Nat.le_refl k'), Nat.sub_self]
    simp [shiftXF2]

theorem mulF2_add_right (f g h : PolyF2) :
    mulF2 f (addF2 g h) = addF2 (mulF2 f g) (mulF2 f h) := by
  funext k
  have hsum : ∀ i, cauchySumF2 f (addF2 g h) k i = xor (cauchySumF2 f g k i) (cauchySumF2 f h k i) := by
    intro i
    induction i with
    | zero =>
      unfold cauchySumF2 addF2
      cases f 0 <;> cases g k <;> cases h k <;> rfl
    | succ j ih =>
      unfold cauchySumF2
      rw [ih]
      unfold addF2
      cases cauchySumF2 f g k j <;> cases cauchySumF2 f h k j <;>
        cases f (j + 1) <;> cases g (k - (j + 1)) <;> cases h (k - (j + 1)) <;> rfl
  exact hsum k

/-- `(X^2 + 1)^k` in `F_2[X]`. -/
def x2p1Pow : Nat → PolyF2
  | 0 => oneF2
  | k + 1 => addF2 (shiftXF2 (shiftXF2 (x2p1Pow k))) (x2p1Pow k)

theorem x2p1Pow_succ (k : Nat) :
    x2p1Pow (k + 1) = addF2 (shiftXF2 (shiftXF2 (x2p1Pow k))) (x2p1Pow k) := rfl

theorem mulF2_x2p1Pow (a b : Nat) : mulF2 (x2p1Pow a) (x2p1Pow b) = x2p1Pow (a + b) := by
  induction b with
  | zero => exact mulF2_one_right (x2p1Pow a)
  | succ k ih =>
    rw [x2p1Pow_succ k, mulF2_add_right, mulF2_shiftX_right, mulF2_shiftX_right, ih, ← x2p1Pow_succ]
    rfl

theorem x2p1Pow_const_term (k : Nat) : x2p1Pow k 0 = true := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp [x2p1Pow, addF2, shiftXF2, ih]

/-- Derivative of `(X^2 + 1)^k` in `F_2[X]` is identically zero! -/
theorem derivF2_x2p1Pow (k : Nat) : derivF2 (x2p1Pow k) = zeroF2 := by
  -- Even cleaner: prove every odd coefficient of x2p1Pow k is false!
  have hodd : ∀ n, n % 2 = 1 → x2p1Pow k n = false := by
    induction k with
    | zero =>
      intro n hn
      have hne : n ≠ 0 := by omega
      simp [x2p1Pow, oneF2, hne]
    | succ k' ih =>
      intro n hn
      unfold x2p1Pow addF2
      have h1 : x2p1Pow k' n = false := ih n hn
      have h2 : shiftXF2 (shiftXF2 (x2p1Pow k')) n = false := by
        cases n with
        | zero => omega
        | succ n1 =>
          cases n1 with
          | zero => rfl
          | succ n2 => exact ih n2 (by omega)
      simp [h1, h2]
  funext j
  unfold derivF2 zeroF2
  by_cases hp : (j + 1) % 2 = 1
  · simp [hp, hodd (j + 1) hp]
  · have hp0 : ((j + 1) % 2 == 1) = false := by
      have : (j + 1) % 2 = 0 := by omega
      simp [this]
    simp [hp0]

/-- Derivative of `X * (X^2 + 1)^k` in `F_2[X]` is `(X^2 + 1)^k`. -/
theorem derivF2_shiftX_x2p1Pow (k : Nat) : derivF2 (shiftXF2 (x2p1Pow k)) = x2p1Pow k := by
  have hodd : ∀ n, n % 2 = 1 → x2p1Pow k n = false := by
    intro n hn
    have h0 := congrFun (derivF2_x2p1Pow k) (n - 1)
    have h1 : n - 1 + 1 = n := by omega
    unfold derivF2 zeroF2 at h0
    rw [h1] at h0
    simpa [hn] using h0
  funext j
  unfold derivF2 shiftXF2
  by_cases hj : j % 2 = 0
  · have hj1 : (j + 1) % 2 = 1 := by omega
    simp [hj1]
  · have hj1 : j % 2 = 1 := by omega
    have hj2 : (j + 1) % 2 = 0 := by omega
    have hfalse : ((j + 1) % 2 == 1) = false := by simp [hj2]
    rw [hfalse, Bool.false_and, hodd j hj1]

/-- Exact scaled parity-Hermite polynomials `P_m, Q_m ∈ Z[π][X]` (Section 4, Theorem 1.2(a)):
    `P_0 = 1`, `P_1 = X`, `P_{m+1} = (X - 2*m*π) P_m - m*(2m - 1) P_{m-1}`,
    `Q_0 = 1`, `Q_1 = X - π`, `Q_{m+1} = (X - (2m + 1)*π) Q_m - m*(2m + 1) Q_{m-1}`. -/
def polyP : Nat → PolyZPi
  | 0 => oneZPi
  | 1 => shiftXZPi oneZPi
  | m + 2 =>
    let k := m + 1
    subZPi (subZPi (shiftXZPi (polyP (m + 1))) (scaleZPi (ZPi.mulPiInt (2 * k)) (polyP (m + 1))))
           (scaleZPi (ZPi.ofNat (k * (2 * k - 1))) (polyP m))

def polyQ : Nat → PolyZPi
  | 0 => oneZPi
  | 1 => subZPi (shiftXZPi oneZPi) (scaleZPi ZPi.pi oneZPi)
  | m + 2 =>
    let k := m + 1
    subZPi (subZPi (shiftXZPi (polyQ (m + 1))) (scaleZPi (ZPi.mulPiInt (2 * k + 1)) (polyQ (m + 1))))
           (scaleZPi (ZPi.ofNat (k * (2 * k + 1))) (polyQ m))

/-- Common `F_2[X]` reduction `ρ_m(X) = X^{m mod 2} (X^2 + 1)^{⌊m/2⌋}`. -/
def rhoF2 (m : Nat) : PolyF2 :=
  if m % 2 == 0 then x2p1Pow (m / 2) else shiftXF2 (x2p1Pow (m / 2))

theorem rhoF2_rec (m : Nat) :
    rhoF2 (m + 2) = addF2 (shiftXF2 (rhoF2 (m + 1))) (scaleF2 ((m + 1) % 2 == 1) (rhoF2 m)) := by
  by_cases hm : m % 2 = 0
  · have h1 : (m + 1) % 2 = 1 := by omega
    have h2 : (m + 2) % 2 = 0 := by omega
    have hd1 : (m + 1) / 2 = m / 2 := by omega
    have hd2 : (m + 2) / 2 = m / 2 + 1 := by omega
    simp [rhoF2, hm, h1, h2, hd1, hd2, scaleF2_true, x2p1Pow]
  · have hm1 : m % 2 = 1 := by omega
    have h1 : (m + 1) % 2 = 0 := by omega
    have h2 : (m + 2) % 2 = 1 := by omega
    have hd1 : (m + 1) / 2 = m / 2 + 1 := by omega
    have hd2 : (m + 2) / 2 = m / 2 + 1 := by omega
    simp [rhoF2, hm1, h1, h2, hd1, hd2, scaleF2_false, addF2_zero_right]

/-- Both `P_m` and `Q_m` reduce modulo `π` to `ρ_m(X)` for EVERY `m : Nat`. -/
theorem modPiPoly_P_and_Q :
    ∀ m : Nat, modPiPoly (polyP m) = rhoF2 m ∧ modPiPoly (polyQ m) = rhoF2 m := by
  intro m
  -- Strong induction via pairs (m, m+1)
  suffices h : ∀ n, (modPiPoly (polyP n) = rhoF2 n ∧ modPiPoly (polyQ n) = rhoF2 n) ∧
                    (modPiPoly (polyP (n + 1)) = rhoF2 (n + 1) ∧ modPiPoly (polyQ (n + 1)) = rhoF2 (n + 1)) from
    (h m).1
  intro n
  induction n with
  | zero =>
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · exact modPiPoly_one
    · exact modPiPoly_one
    · simp only [polyP, modPiPoly_shiftX, modPiPoly_one]; rfl
    · simp only [polyQ, modPiPoly_sub, modPiPoly_shiftX, modPiPoly_scale,
                 modPiPoly_one, ZPi.modPi_pi, scaleF2_false, addF2_zero_right]; rfl
  | succ k ih =>
    rcases ih with ⟨⟨ihPk, ihQk⟩, ⟨ihPk1, ihQk1⟩⟩
    refine ⟨⟨ihPk1, ihQk1⟩, ⟨?_, ?_⟩⟩
    · -- Step for polyP (k + 2)
      unfold polyP
      rw [modPiPoly_sub, modPiPoly_sub, modPiPoly_shiftX, modPiPoly_scale, modPiPoly_scale,
          ZPi.modPi_mulPiInt, scaleF2_false, addF2_zero_right, ZPi.modPi_ofNat, ihPk, ihPk1]
      have hpar : ((k + 1) * (2 * (k + 1) - 1)) % 2 = (k + 1) % 2 := by
        have hodd : (2 * (k + 1) - 1) % 2 = 1 := by omega
        rw [Nat.mul_mod, hodd, Nat.mul_one, Nat.mod_mod]
      rw [hpar, ← rhoF2_rec k]
    · -- Step for polyQ (k + 2)
      unfold polyQ
      rw [modPiPoly_sub, modPiPoly_sub, modPiPoly_shiftX, modPiPoly_scale, modPiPoly_scale,
          ZPi.modPi_mulPiInt, scaleF2_false, addF2_zero_right, ZPi.modPi_ofNat, ihQk, ihQk1]
      have hpar : ((k + 1) * (2 * (k + 1) + 1)) % 2 = (k + 1) % 2 := by
        have hodd : (2 * (k + 1) + 1) % 2 = 1 := by omega
        rw [Nat.mul_mod, hodd, Nat.mul_one, Nat.mod_mod]
      rw [hpar, ← rhoF2_rec k]

/-- Scaled parity-Hermite Wronskians `π^{-(2m-2)} W_m^R(1 + πX) = R̃_m' R̃_{m-1} - R̃_m R̃_{m-1}'`. -/
def wronskianP (m : Nat) : PolyZPi :=
  subZPi (mulZPi (derivZPi (polyP m)) (polyP (m - 1)))
         (mulZPi (polyP m) (derivZPi (polyP (m - 1))))

def wronskianQ (m : Nat) : PolyZPi :=
  subZPi (mulZPi (derivZPi (polyQ m)) (polyQ (m - 1)))
         (mulZPi (polyQ m) (derivZPi (polyQ (m - 1))))

/-- Core `F_2[X]` Wronskian identity: `ρ_m' ρ_{m-1} + ρ_m ρ_{m-1}' = (X^2 + 1)^{m - 1}` for all `m ≥ 1`. -/
theorem rhoF2_wronskian (m : Nat) (hm : 1 ≤ m) :
    addF2 (mulF2 (derivF2 (rhoF2 m)) (rhoF2 (m - 1)))
          (mulF2 (rhoF2 m) (derivF2 (rhoF2 (m - 1)))) = x2p1Pow (m - 1) := by
  by_cases hpar : m % 2 = 0
  · -- m = 2*k (k >= 1): rho_m = (X^2+1)^k has deriv 0; rho_{m-1} = X*(X^2+1)^{k-1} has deriv (X^2+1)^{k-1}
    have hm1 : (m - 1) % 2 = 1 := by omega
    have hm1b : ((m - 1) % 2 == 0) = false := by simp [hm1]
    have hsum : m / 2 + (m - 1) / 2 = m - 1 := by omega
    simp only [rhoF2, hpar, hm1b, beq_self_eq_true, ↓reduceIte, Bool.false_eq_true]
    rw [derivF2_x2p1Pow, derivF2_shiftX_x2p1Pow, mulF2_zero_left, addF2_zero_left, mulF2_x2p1Pow, hsum]
  · -- m = 2*k + 1: rho_m = X*(X^2+1)^k has deriv (X^2+1)^k; rho_{m-1} = (X^2+1)^k has deriv 0
    have hm_odd : m % 2 = 1 := by omega
    have hmb : (m % 2 == 0) = false := by simp [hm_odd]
    have hm1 : (m - 1) % 2 = 0 := by omega
    have hsum : m / 2 + (m - 1) / 2 = m - 1 := by omega
    simp only [rhoF2, hmb, hm1, beq_self_eq_true, ↓reduceIte, Bool.false_eq_true]
    rw [derivF2_shiftX_x2p1Pow, derivF2_x2p1Pow, mulF2_zero_right, addF2_zero_right, mulF2_x2p1Pow, hsum]

/-- Theorem 1.2(a) (Symbolic `2`-adic parity-Hermite Wronskian reduction for ALL `m ≥ 1`):
    In `Z[π][X]`, both `π^{-(2m-2)} W_m^U(1 + πX)` and `π^{-(2m-2)} W_m^V(1 + πX)` reduce
    modulo `π` to `(X^2 + 1)^{m - 1}`, and in particular have unit constant term (`modPi = true`). -/
theorem wronskian_mod_pi_all_m (m : Nat) (hm : 1 ≤ m) :
    modPiPoly (wronskianP m) = x2p1Pow (m - 1) ∧
    modPiPoly (wronskianQ m) = x2p1Pow (m - 1) ∧
    ZPi.modPi (wronskianP m 0) = true ∧
    ZPi.modPi (wronskianQ m 0) = true := by
  have hP : modPiPoly (wronskianP m) = x2p1Pow (m - 1) := by
    unfold wronskianP
    rw [modPiPoly_sub, modPiPoly_mul, modPiPoly_mul, modPiPoly_deriv, modPiPoly_deriv,
        (modPiPoly_P_and_Q m).1, (modPiPoly_P_and_Q (m - 1)).1]
    exact rhoF2_wronskian m hm
  have hQ : modPiPoly (wronskianQ m) = x2p1Pow (m - 1) := by
    unfold wronskianQ
    rw [modPiPoly_sub, modPiPoly_mul, modPiPoly_mul, modPiPoly_deriv, modPiPoly_deriv,
        (modPiPoly_P_and_Q m).2, (modPiPoly_P_and_Q (m - 1)).2]
    exact rhoF2_wronskian m hm
  refine ⟨hP, hQ, ?_, ?_⟩
  · have := congrFun hP 0
    rw [x2p1Pow_const_term] at this
    exact this
  · have := congrFun hQ 0
    rw [x2p1Pow_const_term] at this
    exact this

/-! ## Part 2: Symbolic Discriminant Exponent & Inverse-Pair Identities -/

/-- Theorem 1.1: Exact discriminant exponent identities for `C_sep` and `C_ov`. -/
theorem discriminant_exponents_exact (d A : Nat) :
    let K := d * (A * (A - 1) / 2)
    let L := (d - 1) * (A * (A - 1) / 2) + (A * (A + 1) / 2)
    (1 ≤ d → L = K + A) ∧
    (d * (A * A) = K + d * (A * (A + 1) / 2)) := by
  have htri : A * (A - 1) / 2 + A = A * (A + 1) / 2 := by
    cases A with
    | zero => rfl
    | succ k =>
      have h1 : (k + 1) * k + 2 * (k + 1) = (k + 1) * (k + 2) := by
        rw [Nat.mul_add (k + 1) k 2, Nat.mul_comm 2 (k + 1)]
      have heven : 2 ∣ (k + 1) * k := by
        by_cases hk : k % 2 = 0
        · rcases Nat.dvd_of_mod_eq_zero hk with ⟨t, ht⟩
          exact ⟨(k + 1) * t, by rw [ht]; ac_rfl⟩
        · have hk1 : (k + 1) % 2 = 0 := by omega
          rcases Nat.dvd_of_mod_eq_zero hk1 with ⟨t, ht⟩
          exact ⟨t * k, by rw [ht]; ac_rfl⟩
      rcases heven with ⟨q, hq⟩
      have h2 : (k + 1) * (k + 2) = 2 * (q + (k + 1)) := by
        rw [← h1, hq, Nat.mul_add 2 q (k + 1)]
      simp only [Nat.add_sub_cancel]
      rw [hq, h2, Nat.mul_div_cancel_left _ (by omega), Nat.mul_div_cancel_left _ (by omega)]
  have hsq : A * (A - 1) / 2 + A * (A + 1) / 2 = A * A := by
    cases A with
    | zero => rfl
    | succ k =>
      have heven : 2 ∣ (k + 1) * k := by
        by_cases hk : k % 2 = 0
        · rcases Nat.dvd_of_mod_eq_zero hk with ⟨t, ht⟩
          exact ⟨(k + 1) * t, by rw [ht]; ac_rfl⟩
        · have hk1 : (k + 1) % 2 = 0 := by omega
          rcases Nat.dvd_of_mod_eq_zero hk1 with ⟨t, ht⟩
          exact ⟨t * k, by rw [ht]; ac_rfl⟩
      rcases heven with ⟨q, hq⟩
      have h2 : (k + 1) * (k + 2) = 2 * (q + (k + 1)) := by
        have h1 : (k + 1) * k + 2 * (k + 1) = (k + 1) * (k + 2) := by
          rw [Nat.mul_add (k + 1) k 2, Nat.mul_comm 2 (k + 1)]
        rw [← h1, hq, Nat.mul_add 2 q (k + 1)]
      simp only [Nat.add_sub_cancel]
      rw [hq, h2, Nat.mul_div_cancel_left _ (by omega), Nat.mul_div_cancel_left _ (by omega)]
      have h3 : 2 * (q + (q + (k + 1))) = 2 * ((k + 1) * (k + 1)) := by
        have hsum : 2 * q + 2 * q + 2 * (k + 1) = (k + 1) * k + (k + 1) * (k + 2) := by
          rw [hq, h2]; omega
        have hsq2 : (k + 1) * k + (k + 1) * (k + 2) = 2 * ((k + 1) * (k + 1)) := by
          rw [← Nat.mul_add]
          have : k + (k + 2) = 2 * (k + 1) := by omega
          rw [this]; ac_rfl
        omega
      omega
  refine ⟨fun hd => ?_, ?_⟩
  · have hsplit : d * (A * (A - 1) / 2) = (d - 1) * (A * (A - 1) / 2) + (A * (A - 1) / 2) := by
      have hd1 : (d - 1) + 1 = d := by omega
      calc d * (A * (A - 1) / 2)
        _ = ((d - 1) + 1) * (A * (A - 1) / 2) := by rw [hd1]
        _ = (d - 1) * (A * (A - 1) / 2) + 1 * (A * (A - 1) / 2) := Nat.add_mul (d - 1) 1 _
        _ = (d - 1) * (A * (A - 1) / 2) + (A * (A - 1) / 2) := by rw [Nat.one_mul]
    rw [hsplit, Nat.add_assoc, htri]
  · rw [← Nat.mul_add, hsq]

/-- Section 1 / Section 9: Ordinary discriminant of `H_2(z; q) = z^2 + (1 + q)z + 1`
    equals `(q - 1)(q + 3)`, whereas the monic `q`-discriminant `(q - 1)(q + 1)^2` differs. -/
theorem H2_ordinary_vs_q_discriminant (q : Int) :
    (1 + q) * (1 + q) - 4 = (q - 1) * (q + 3) ∧
    ((0 - 1 : Int) * (0 + 3) ≠ (0 - 1 : Int) * (0 + 1) * (0 + 1)) := by
  constructor
  · rw [Int.add_mul, Int.mul_add, Int.mul_add, Int.sub_mul, Int.mul_add, Int.mul_add]
    omega
  · decide

/-- Theorem 6.3, Eq. (6.4): Denominator-free inverse-pair symmetry:
    if `τ' = τ / (τ - 1)` (i.e. `τ + τ' = τ * τ'`), then `t(τ') = -t(τ)` in cross-multiplied form:
    `τ'(τ' - 2) * (1 - τ) + τ(τ - 2) * (1 - τ') = 0`. -/
theorem inverse_pair_t_antisymmetry (tau tau' : Int) (hinv : tau + tau' = tau * tau') :
    tau' * (tau' - 2) * (1 - tau) + tau * (tau - 2) * (1 - tau') = 0 := by
  -- Both terms simplify using tau * tau' = tau + tau'
  have e1 : tau' * (tau' - 2) * (1 - tau)
      = tau' * tau' - 2 * tau' - tau * tau' * tau' + 2 * (tau * tau') := by
    rw [Int.mul_sub, Int.mul_sub, Int.mul_one, Int.sub_mul]
    have h1 : tau' * tau' * tau = tau * tau' * tau' := by ac_rfl
    have h2 : tau' * 2 * tau = 2 * (tau * tau') := by ac_rfl
    have h3 : tau' * 2 = 2 * tau' := by ac_rfl
    rw [h1, h2, h3]
    omega
  have e2 : tau * (tau - 2) * (1 - tau')
      = tau * tau - 2 * tau - tau * tau * tau' + 2 * (tau * tau') := by
    rw [Int.mul_sub, Int.mul_sub, Int.mul_one, Int.sub_mul]
    have h1 : tau * 2 * tau' = 2 * (tau * tau') := by ac_rfl
    have h2 : tau * 2 = 2 * tau := by ac_rfl
    rw [h1, h2]
    omega
  have hcube1 : tau * tau' * tau' = (tau + tau') * tau' := by rw [hinv]
  have hcube2 : tau * tau * tau' = tau * (tau + tau') := by
    rw [Int.mul_assoc, hinv]
  rw [e1, e2, hcube1, hcube2, Int.add_mul, Int.mul_add]
  have hcomm : tau * tau' = tau' * tau := Int.mul_comm tau tau'
  omega

/-! ## Part 3: Pure-Kernel Finite Certificates (`decide` / `decide +kernel`, zero `native_decide`) -/

/-- Modular arithmetic helpers for exact finite-field checks. -/
def powMod (a n p : Nat) : Nat :=
  let rec go (fuel base exp acc : Nat) : Nat :=
    match fuel with
    | 0 => acc
    | f + 1 =>
      if exp == 0 then acc
      else
        let acc' := if exp % 2 == 1 then (acc * base) % p else acc
        go f ((base * base) % p) (exp / 2) acc'
  go 64 (a % p) n 1

/-- Characteristic-`p` Wronskian check (Theorem 6.3):
    verifies `H'V - HV' - yHV = -y^p (mod p)` and exact `τ = 2` triple zero for `p ≡ 1 (mod 4)`
    (and nonzero constant term for `p ≡ 3 (mod 4)`). -/
def checkCharPTheorem (p : Nat) : Bool :=
  let A := (p - 1) / 2
  -- Build monic probabilists' Hermite He_A mod p
  let heStep (n : Nat) (hPrev hCurr : List Nat) : List Nat :=
    let deg := n + 1
    (List.range (deg + 1)).map fun k =>
      let t1 := if k == 0 then 0 else hCurr.getD (k - 1) 0
      let t2 := (n * hPrev.getD k 0) % p
      (t1 + p - t2) % p
  let (_, H) := (List.range (A - 1)).foldl (fun (hp, hc) idx =>
    (hc, heStep (idx + 1) hp hc)) ([1], [0, 1])
  let H := if A == 1 then [0, 1] else H
  -- V(y) = i^{-A} H(iy) has coeff (-1)^{(k - A)/2} H_k
  let V := (List.range (A + 1)).map fun k =>
    let c := H.getD k 0
    if c == 0 then 0
    else if ((A - k) / 2) % 2 == 1 then (p - c) % p else c
  let deriv (f : List Nat) : List Nat :=
    (List.range (f.length - 1)).map fun k => ((k + 1) * f.getD (k + 1) 0) % p
  let mulP (a b : List Nat) : List Nat :=
    let len := a.length + b.length - 1
    (List.range len).map fun k =>
      (List.range (k + 1)).foldl (fun acc i =>
        (acc + a.getD i 0 * b.getD (k - i) 0) % p) 0
  let Hp := deriv H
  let Vp := deriv V
  let t1 := mulP Hp V
  let t2 := mulP H Vp
  let t3 := 0 :: mulP H V
  let maxL := p + 1
  let wronskOk := (List.range maxL).all fun k =>
    let lhs := (t1.getD k 0 + p - t2.getD k 0 + p - t3.getD k 0) % p
    let rhs := if k == p then p - 1 else 0
    lhs == rhs
  -- Check J(y; 2) = y H - 2 H' at y = 0..3
  let j2Coeff (k : Nat) : Nat :=
    let c1 := if k == 0 then 0 else H.getD (k - 1) 0
    let c2 := (2 * Hp.getD k 0) % p
    (c1 + p - c2) % p
  let excOk :=
    if p % 4 == 3 then j2Coeff 0 != 0
    else j2Coeff 0 == 0 && j2Coeff 1 == 0 && j2Coeff 2 == 0 && j2Coeff 3 != 0
  wronskOk && excOk

theorem charp_wronskian_and_triple_zero_primes :
    checkCharPTheorem 3 = true ∧
    checkCharPTheorem 5 = true ∧
    checkCharPTheorem 7 = true ∧
    checkCharPTheorem 11 = true ∧
    checkCharPTheorem 13 = true ∧
    checkCharPTheorem 17 = true ∧
    checkCharPTheorem 19 = true := by
  decide +kernel

/-- Deterministic trial-division primality test (valid for all `p < 4_000_000`). -/
def isPrimeNat (p : Nat) : Bool :=
  if p < 2 then false
  else if p == 2 then true
  else if p % 2 == 0 then false
  else
    let rec go (fuel j : Nat) : Bool :=
      match fuel with
      | 0 => false
      | f + 1 =>
        if j * j > p then true
        else if p % j == 0 then false
        else go f (j + 2)
    go 1000 3

/-- Exact `F_ell` dual-witness, dual-algorithm polynomial certification matching
    `certify_composite_orders.cpp` (Theorem 1.4(b)):
    - Method 1: `q`-Pascal recurrence, Euclidean gcd with derivative, and Horner evaluation
      at all `d` fixed nodes `-w^j`.
    - Method 2: contiguous `q`-Pochhammer ratios, Euclidean gcd with derivative, and
      Euclidean gcd with `z^d + 1`. -/
def trimMod (a : List Nat) : List Nat :=
  (a.reverse.dropWhile (· == 0)).reverse

def polyGcdMod (p : Nat) (a b : List Nat) : List Nat :=
  let rec go (fuel : Nat) (x y : List Nat) : List Nat :=
    match fuel with
    | 0 => x
    | f + 1 =>
      let x := trimMod x
      let y := trimMod y
      if y.isEmpty then
        match x.getLast? with
        | none => []
        | some lc =>
          let iv := powMod lc (p - 2) p
          x.map (fun c => (c * iv) % p)
      else
        let lcY := y.getD (y.length - 1) 0
        let invLcY := powMod lcY (p - 2) p
        let rec reduce (rfuel : Nat) (r : List Nat) : List Nat :=
          match rfuel with
          | 0 => r
          | rf + 1 =>
            let r := trimMod r
            if r.length < y.length then r
            else
              let shift := r.length - y.length
              let q := (r.getD (r.length - 1) 0 * invLcY) % p
              let r' := (List.range (r.length - 1)).map fun idx =>
                let subTerm :=
                  if idx < shift then 0
                  else (q * y.getD (idx - shift) 0) % p
                (r.getD idx 0 + p - subTerm) % p
              reduce rf r'
        go f y (reduce (x.length + 1) x)
  go (a.length + b.length + 2) a b

def polyEvalMod (p : Nat) (a : List Nat) (x : Nat) : Nat :=
  a.reverse.foldl (fun acc c => (acc * x + c) % p) 0

def exactOrderOk (d ell w : Nat) : Bool :=
  isPrimeNat ell && d % 2 == 1 && 1 ≤ w && w < ell &&
  (ell - 1) % d == 0 && powMod w d ell == 1 &&
  (List.range d).all fun k => k < 2 || d % k != 0 || powMod w (d / k) ell != 1

def certifyCompositeMethod1 (d ell w : Nat) : Bool :=
  if !exactOrderOk d ell w then false
  else
    let powers := (List.range d).map fun j => powMod w j ell
    let rec checkAllB (b : Nat) (hPrev : List Nat) : Bool :=
      match b with
      | 0 => true
      | b' + 1 =>
        let deg := d - b
        let g := (List.range (deg + 1)).map fun k =>
          if k == 0 || k == deg then 1
          else (hPrev.getD k 0 + powers.getD (deg - k) 0 * hPrev.getD (k - 1) 0) % ell
        let der := (List.range deg).map fun k => ((k + 1) * g.getD (k + 1) 0) % ell
        let sqFree := polyGcdMod ell g der == [1]
        let nodesOk := (List.range d).all fun j =>
          let node := (ell - powers.getD j 0) % ell
          (polyEvalMod ell g node == 0) == ((deg % 2 == 1) && j == 0)
        if sqFree && nodesOk then checkAllB b' g else false
    checkAllB (d - 1) [1]

def certifyCompositeMethod2 (d ell w : Nat) : Bool :=
  if !exactOrderOk d ell w then false
  else
    let powers := (List.range d).map fun j => powMod w j ell
    let units := (List.range d).map fun k => (ell + 1 - powers.getD k 0) % ell
    let inverses := (List.range d).map fun k =>
      if k == 0 then 0 else powMod (units.getD k 0) (ell - 2) ell
    let polyF := (List.range (d + 1)).map fun k => if k == 0 || k == d then 1 else 0
    (List.range (d - 1)).all fun idx =>
      let deg := idx + 1
      let revG := (List.range deg).foldl (fun acc kIdx =>
        let k := kIdx + 1
        let prev := acc.headD 1
        let nxt := ((prev * units.getD (deg - k + 1) 0) % ell * inverses.getD k 0) % ell
        nxt :: acc) [1]
      let closeOk := revG.headD 0 == 1
      let g := revG.reverse
      let der := (List.range deg).map fun k => ((k + 1) * g.getD (k + 1) 0) % ell
      let sqFree := polyGcdMod ell g der == [1]
      let expGcd := if deg % 2 == 1 then [1, 1] else [1]
      let gcdOk := polyGcdMod ell polyF g == expGcd
      closeOk && sqFree && gcdOk

/-- Pure-kernel dual-witness, dual-algorithm certification for the first four odd composite
    orders `d = 9, 15, 21, 25`, using the exact witness rows of `composite_witnesses.csv`
    (Theorem 1.4(b)). -/
theorem certified_composite_orders_small :
    (certifyCompositeMethod1 9 100153 64038 = true ∧ certifyCompositeMethod2 9 500041 422862 = true) ∧
    (certifyCompositeMethod1 15 100291 1159 = true ∧ certifyCompositeMethod2 15 500041 322377 = true) ∧
    (certifyCompositeMethod1 21 100129 46350 = true ∧ certifyCompositeMethod2 21 500179 473990 = true) ∧
    (certifyCompositeMethod1 25 100151 20148 = true ∧ certifyCompositeMethod2 25 500501 72791 = true) := by
  decide +kernel

/-- Exact `2`-adic valuation on nonzero `Int` and unscaled shifted Newton-polygon check
    for `W_m^U(1 + z)` and `W_m^V(1 + z)` over `Z[z]` (m = 2..6). -/
def v2Int (n : Int) : Nat :=
  let rec go (fuel a acc : Nat) : Nat :=
    match fuel with
    | 0 => acc
    | f + 1 => if a == 0 || a % 2 == 1 then acc else go f (a / 2) (acc + 1)
  go 128 n.natAbs 0

def polyAddZ (a b : List Int) : List Int :=
  (List.range (max a.length b.length)).map fun k => a.getD k 0 + b.getD k 0

def polySubZ (a b : List Int) : List Int :=
  (List.range (max a.length b.length)).map fun k => a.getD k 0 - b.getD k 0

def polyMulZ (a b : List Int) : List Int :=
  if a.isEmpty || b.isEmpty then []
  else
    (List.range (a.length + b.length - 1)).map fun k =>
      (List.range (k + 1)).foldl (fun acc i => acc + a.getD i 0 * b.getD (k - i) 0) 0

def polyDerivZ (a : List Int) : List Int :=
  if a.length ≤ 1 then [0]
  else (List.range (a.length - 1)).map fun k => ((k + 1 : Nat) : Int) * a.getD (k + 1) 0

def polyShiftOneZ (a : List Int) : List Int :=
  -- Evaluate a(1 + z)
  let rec go (rest pwr acc : List Int) : List Int :=
    match rest with
    | [] => acc
    | c :: cs => go cs (polyMulZ pwr [1, 1]) (polyAddZ acc (pwr.map (· * c)))
  go a [1] [0]

def checkUnscaledNewtonPolygons : Bool :=
  let rec buildUV (m : Nat) (uPrev uCurr vPrev vCurr : List Int) (ok : Bool) : Bool :=
    match m with
    | 0 => ok
    | m' + 1 =>
      let idx := 7 - m  -- idx = 2, 3, 4, 5, 6
      let wu := polySubZ (polyMulZ (polyDerivZ uCurr) uPrev) (polyMulZ uCurr (polyDerivZ uPrev))
      let wv := polySubZ (polyMulZ (polyDerivZ vCurr) vPrev) (polyMulZ vCurr (polyDerivZ vPrev))
      let su := polyShiftOneZ wu
      let sv := polyShiftOneZ wv
      let deg := 2 * idx - 2
      let checkOne (s : List Int) : Bool :=
        s.getD 0 0 != 0 && v2Int (s.getD 0 0) == idx - 1 &&
        s.getD deg 0 == 1 &&
        (List.range (deg + 1)).all fun j =>
          let cj := s.getD j 0
          cj == 0 || 2 * v2Int cj + j ≥ 2 * (idx - 1)
      let ok' := ok && checkOne su && checkOne sv
      let uNext := polySubZ (polyMulZ [-(4 * (idx : Int) + 1), 1] uCurr)
                            (uPrev.map (· * (2 * (idx : Int) * (2 * (idx : Int) - 1))))
      let vNext := polySubZ (polyMulZ [-(4 * (idx : Int) + 3), 1] vCurr)
                            (vPrev.map (· * (2 * (idx : Int) * (2 * (idx : Int) + 1))))
      buildUV m' uCurr uNext vCurr vNext ok'
  let u0 : List Int := [1]
  let u1 : List Int := [-1, 1]
  let u2 := polySubZ (polyMulZ [-5, 1] u1) (u0.map (· * 2))
  let v0 : List Int := [1]
  let v1 : List Int := [-3, 1]
  let v2 := polySubZ (polyMulZ [-7, 1] v1) (v0.map (· * 6))
  buildUV 5 u1 u2 v1 v2 true

theorem unscaled_wronskian_newton_polygons_m2_to_m6 :
    checkUnscaledNewtonPolygons = true := by
  decide +kernel

/-- Exact ring arithmetic in `O_s = Z[omega]/(Phi_s(omega))` for prime `s`
    (representing elements as canonical length `s - 1` integer coefficient lists). -/
def ringZeroS (s : Nat) : List Int := List.replicate (s - 1) 0
def ringOneS (s : Nat) : List Int := (List.range (s - 1)).map fun j => if j == 0 then 1 else 0

def ringModS (s : Nat) (raw : List Int) : List Int :=
  let buckets := (List.range s).map fun rem =>
    (List.range raw.length).foldl (fun acc k =>
      if k % s == rem then acc + raw.getD k 0 else acc) (0 : Int)
  let top := buckets.getD (s - 1) 0
  (List.range (s - 1)).map fun j => buckets.getD j 0 - top

def ringAddS (s : Nat) (a b : List Int) : List Int :=
  (List.range (s - 1)).map fun j => a.getD j 0 + b.getD j 0

def ringSubS (s : Nat) (a b : List Int) : List Int :=
  (List.range (s - 1)).map fun j => a.getD j 0 - b.getD j 0

def ringScaleS (c : Int) (a : List Int) : List Int := a.map (· * c)

def ringMulS (s : Nat) (a b : List Int) : List Int := ringModS s (polyMulZ a b)

def ringOmegaPow (s e : Nat) : List Int :=
  let m := e % s
  if m == s - 1 then List.replicate (s - 1) (-1)
  else (List.range (s - 1)).map fun j => if j == m then 1 else 0

def ringInvAutS (s : Nat) (a : List Int) : List Int :=
  let buckets := (List.range s).map fun rem =>
    (List.range (s - 1)).foldl (fun acc k =>
      if (s - k) % s == rem then acc + a.getD k 0 else acc) (0 : Int)
  let top := buckets.getD (s - 1) 0
  (List.range (s - 1)).map fun j => buckets.getD j 0 - top

def ringContentS (a : List Int) : Nat :=
  a.foldl (fun g c => Nat.gcd g c.natAbs) 0

def polyEvalRingAtInt (s : Nat) (P : List (List Int)) (x : Int) : List Int :=
  P.reverse.foldl (fun acc c => ringAddS s (ringScaleS x acc) c) (ringZeroS s)

def evalIntPolyAtRing (s : Nat) (C : List Int) (x : List Int) : List Int :=
  C.reverse.foldl (fun acc ci =>
    ringAddS s (ringMulS s acc x) (ringScaleS ci (ringOneS s))) (ringZeroS s)

/-- Verifies both the denominator-free inverse identity `g_s v_s^ι + g_s^ι v_s = v_s v_s^ι`
    (Eq. (6.7)) and the exact augmented content `c_s^+ = expC` (Eq. (6.9)) in `O_s = Z[ω]/(Φ_s)`
    for prime `s ≡ 3 (mod 4)` with `r = (s - 3)/4 ≤ 2` (`s ∈ {3, 7, 11}`). -/
def checkAugmentedContentPrimeS (s expC : Nat) : Bool :=
  let r := (s - 3) / 4
  let b := 2 * r + 1
  -- Build H_b(z; omega) in O_s[z] via q-Pascal
  let hRow := (List.range b).foldl (fun prev idx =>
    let n := idx + 1
    (List.range (n + 1)).map fun k =>
      if k == 0 || k == n then ringOneS s
      else
        let wp := ringOmegaPow s (n - k)
        ringAddS s (prev.getD k (ringZeroS s)) (ringMulS s wp (prev.getD (k - 1) (ringZeroS s))))
    [ringOneS s]
  -- Exact synthetic division U_s(z) = H_b(z; omega) / (z + 1)
  let revU := (List.range (2 * r)).foldl (fun acc idx =>
    let k := idx + 1
    let prevU := acc.headD (ringZeroS s)
    let uk := ringSubS s (hRow.getD k (ringZeroS s)) prevU
    uk :: acc) [hRow.getD 0 (ringZeroS s)]
  let divOk := revU.headD (ringZeroS s) == hRow.getD (2 * r + 1) (ringZeroS s)
  let U := revU.reverse
  -- Reciprocal reduction U_s(z) = z^r P_s(z + z^{-1}) for r in {0, 1, 2}
  let Ps : List (List Int) :=
    if r == 0 then [U.getD 0 (ringZeroS s)]
    else if r == 1 then [U.getD 1 (ringZeroS s), U.getD 2 (ringZeroS s)]
    else [ringSubS s (U.getD 2 (ringZeroS s)) (ringScaleS 2 (U.getD 4 (ringZeroS s))),
          U.getD 3 (ringZeroS s),
          U.getD 4 (ringZeroS s)]
  -- Build C_s(t): C_1 = 1, C_3 = t - 1, C_{m+2} = t C_m - C_{m-2}
  let (_, Cs) := (List.range ((s - 3) / 2)).foldl (fun (cp, cc) _ =>
    (cc, polySubZ (0 :: cc) cp)) ([1], [-1, 1])
  -- Compute Disc(P_s) and Res(P_s, C_s) in O_s
  let discP :=
    if r ≤ 1 then ringOneS s
    else
      let c0 := Ps.getD 0 (ringZeroS s)
      let c1 := Ps.getD 1 (ringZeroS s)
      ringSubS s (ringMulS s c1 c1) (ringScaleS 4 c0)
  let resPC :=
    if r == 0 then ringOneS s
    else if r == 1 then
      evalIntPolyAtRing s Cs (ringScaleS (-1) (Ps.getD 0 (ringZeroS s)))
    else
      let c0 := Ps.getD 0 (ringZeroS s)
      let c1 := Ps.getD 1 (ringZeroS s)
      -- Reduce C_s(t) mod (t^2 + c1*t + c0) -> v + u*t
      let (v, u) := Cs.reverse.foldl (fun (a0, a1) ci =>
        let newA0 := ringSubS s (ringScaleS ci (ringOneS s)) (ringMulS s a1 c0)
        let newA1 := ringSubS s a0 (ringMulS s a1 c1)
        (newA0, newA1)) (ringZeroS s, ringZeroS s)
      -- Res(t^2 + c1*t + c0, v + u*t) = u^2 c0 - u v c1 + v^2
      let u2c0 := ringMulS s (ringMulS s u u) c0
      let uvc1 := ringMulS s (ringMulS s u v) c1
      let v2 := ringMulS s v v
      ringAddS s (ringSubS s u2c0 uvc1) v2
  let pAt2 := polyEvalRingAtInt s Ps 2
  let pAtM2 := polyEvalRingAtInt s Ps (-2)
  let inner := ringMulS s discP resPC
  let inner2 := ringMulS s inner inner
  let gammaRaw := ringMulS s (ringMulS s pAt2 (ringMulS s pAtM2 pAtM2)) inner2
  let gamma := if r % 2 == 1 then ringScaleS (-1) gammaRaw else gammaRaw
  let gS := if r % 2 == 1 then ringScaleS (-1) pAtM2 else pAtM2
  -- v_s = (omega^2; omega^2)_r * (omega; omega^2)_b
  let vPart1 := (List.range r).foldl (fun acc t =>
    let fac := ringSubS s (ringOneS s) (ringOmegaPow s (2 * (t + 1)))
    ringMulS s acc fac) (ringOneS s)
  let vS := (List.range b).foldl (fun acc t =>
    let fac := ringSubS s (ringOneS s) (ringOmegaPow s (1 + 2 * t))
    ringMulS s acc fac) vPart1
  let gI := ringInvAutS s gS
  let vI := ringInvAutS s vS
  let invIdOk := ringAddS s (ringMulS s gS vI) (ringMulS s gI vS) == ringMulS s vS vI
  let deltaS := ringSubS s (ringScaleS 2 gS) vS
  let gammaI := ringInvAutS s gamma
  let bS := ringMulS s (ringMulS s gamma gammaI) deltaS
  let contentOk := ringContentS bS == expC
  divOk && invIdOk && contentOk

/-- Pure-kernel verification of Eq. (6.7) (`g_s v_s^ι + g_s^ι v_s = v_s v_s^ι`) and
    Eq. (6.9) (`c_3^+ = 1`, `c_7^+ = 7^2 = 49`, `c_11^+ = 11^5 = 161051`), certifying the
    first three infinite composite families of Theorem 1.4(a) directly in `Z[ω]/(Φ_s)`. -/
theorem exact_augmented_contents_s3_s7_s11 :
    checkAugmentedContentPrimeS 3 1 = true ∧
    checkAugmentedContentPrimeS 7 49 = true ∧
    checkAugmentedContentPrimeS 11 161051 = true := by
  decide +kernel

end RogersSzegoDiscriminants
