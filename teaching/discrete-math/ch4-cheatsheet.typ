#import "@preview/showybox:2.0.4": showybox

#let homepage = link("https://cs.shivi.io")[cs.shivi.io]
#let author = "Shivram Sambhus (Group K, HS25)"
#let title = "DM Cheatsheet - Number Theory"

#set page(
  paper: "a4",
  flipped: true,
  margin: (x: 10pt, y: 10pt),
  footer: context [
    #grid(
      columns: 1fr,
      align: (right),
      gutter: 0pt,
      [
        #counter(page).display("1 / 1", both: true)
      ],
    )
  ],
)


#set text(size: 8pt)

#set heading(numbering: "1.1")

#let color-box = (
  rgb("#268bd2"), // Blue
  rgb("#859900"), // Green
  rgb("#b58900"), // Yellow
  rgb("#cb4b16"), // Orange
  rgb("#d33682"), // Magenta
  rgb("#6c71c4"), // Violet
)

#show heading: it => {
  let index = counter(heading).at(it.location()).first()
  let hue = color-box.at(calc.rem(index - 1, color-box.len()))

  let color = hue.darken(30% * (it.depth - 1))

  let heading_size = 7.5pt
  let inset_size = 1.0mm


  set text(white, size: heading_size)
  set align(left)
  block(
    radius: 0.6mm,
    inset: inset_size,
    width: 100%,
    above: 7.5pt,
    below: 7.5pt,
    fill: color,
    it,
  )
}

#let concept-block(
  body: content,
  alignment: start,
  width: 100%,
  fill-color: white,
) = context {
  let heading-count = counter(heading).at(here()).first()
  let current-color = color-box.at(calc.rem(heading-count - 1, color-box.len()))
  block(
    breakable: true,
    stroke: 1pt + current-color,
    fill: fill-color,
    radius: 3pt,
    inset: 6pt,
    width: width,
  )[
    #align(alignment)[
      #body
    ]
  ]
}

#let inline(title) = context {
  let heading-count = counter(heading).at(here()).first()
  let current-color = color-box.at(calc.rem(heading-count - 1, color-box.len()))

  box(grid(
    columns: (1fr, auto, 1fr),
    align: horizon + center,
    column-gutter: 1em,
    line(length: 100%, stroke: 1pt + current-color),
    text(fill: current-color, weight: "bold")[#title],
    line(length: 100%, stroke: 1pt + current-color),
  ))
}

#columns(3, gutter: 6pt)[

  #text(title, weight: "bold") - #text(author)

  = Introduction: The Integers and Their Secrets
  _Number theory is the study of the integers ($ZZ$). This chapter explores the fundamental properties of divisibility, prime numbers, and modular arithmetic, culminating in powerful applications like modern cryptography._

  == TOC

  #outline(title: none)

  = Part I: Divisibility and Core Algorithms
  _The concept of one integer dividing another is the bedrock of number theory. From this simple idea, we can derive powerful algorithms for finding common divisors and solving linear equations._

  == Divisibility and Remainders
  #concept-block(body: [
    #inline[Core Concepts]
    - *Divisibility:* For integers $a, b$, we say *$a$ divides $b$*, written $a | b$, if there exists an integer $c$ such that $b = a c$. Here, $a$ is a *divisor* of $b$, and $b$ is a *multiple* of $a$.
    - *Division Theorem (Euclid):* For any integers $a$ and $d != 0$, there exist *unique* integers $q$ (quotient) and $r$ (remainder) such that:
      $a = q d + r quad "and" quad 0 <= r < |d|$
      The remainder $r$ is often denoted $a mod d$.
  ])

  == Greatest Common Divisor (GCD)
  #concept-block(body: [
    #inline[Definition]
    The *greatest common divisor* of $a$ and $b$ (not both zero), denoted $gcd(a, b)$, is the largest positive integer that divides both $a$ and $b$.
    - *Relatively Prime:* Two integers $a, b$ are *relatively prime* (or coprime) if $gcd(a, b) = 1$.

    #inline[Euclidean Algorithm]
    A fast, recursive algorithm to compute the GCD. It's based on the identity:
    $gcd(a, b) = gcd(b, a mod b)$
    
    #box(fill: luma(235), inset: 5pt, radius: 3pt)[
      *Approach: Calculating GCD with the Euclidean Algorithm*
      To find $gcd(a, b)$ for $a > b$:
      1. Let $(x, y) = (a, b)$.
      2. While $y != 0$:
         - Calculate the remainder $r = x mod y$.
         - Update the pair: $(x, y) = (y, r)$.
      3. The GCD is the last non-zero value of $y$ (which will be in the $x$ position).

      *Example: $gcd(48, 18)$*
      - $gcd(48, 18) = gcd(18, 48 mod 18) = gcd(18, 12)$
      - $gcd(18, 12) = gcd(12, 18 mod 12) = gcd(12, 6)$
      - $gcd(12, 6) = gcd(6, 12 mod 6) = gcd(6, 0)$
      - The last non-zero remainder is 6. So, $gcd(48, 18) = 6$.
    ]
  ])

  == Extended Euclidean Algorithm
  #concept-block(body: [
    #inline[Bézout's Identity]
    For any integers $a, b$ (not both zero), there exist integers $u, v$ such that:
    $u a + v b = gcd(a, b)$
    The integers $u, v$ are called *Bézout coefficients*. The Extended Euclidean Algorithm finds them.

    #box(fill: luma(235), inset: 5pt, radius: 3pt)[
      *Approach: Finding Bézout Coefficients*
      This algorithm works by running the Euclidean algorithm forward and then substituting backwards.
      1. *Forward Pass:* Find the GCD using the division algorithm, keeping track of each equation.
         - $48 = 2 * 18 + 12$
         - $18 = 1 * 12 + 6$
         - $12 = 2 * 6 + 0$
      2. *Backward Pass:* Start from the last non-zero remainder equation and solve for the GCD (which is 6).
         - $6 = 18 - 1 * 12$
      3. Substitute the previous remainder (12) upwards.
         - $6 = 18 - 1 * (48 - 2 * 18)$
      4. Group terms by $a$ and $b$.
         - $6 = 18 - 1*48 + 2*18$
         - $6 = 3 * 18 - 1 * 48$
      So, $u = -1$ and $v = 3$.
    ]
    
    *Application:* This is crucial for finding multiplicative inverses in modular arithmetic.
  ])

  = Part II: Prime Numbers & Factorization
  _Prime numbers are the "atoms" of the integers. The Fundamental Theorem of Arithmetic is one of the most important results in all of mathematics._

  == Fundamental Theorem of Arithmetic
  #concept-block(body: [
    #inline[Core Concepts]
    - *Prime:* A positive integer $p > 1$ whose only positive divisors are 1 and $p$.
    - *Composite:* An integer greater than 1 that is not prime.
    - *Fundamental Theorem:* Every integer $n > 1$ can be written as a product of primes, and this factorization is *unique* up to the order of the factors.
      $n = p_1^(e_1) p_2^(e_2) ... p_k^(e_k)$

    #inline[Euclid's Lemma]
    A key step in proving uniqueness: If a prime $p$ divides a product $a b$, then $p$ must divide $a$ or $p$ must divide $b$ ($p|a b -> p|a or p|b$).

    #inline[GCD & LCM via Prime Factorization]
    If $a = product p_i^(a_i)$ and $b = product p_i^(b_i)$:
    - $gcd(a, b) = product p_i^(min(a_i, b_i))$
    - $lcm(a, b) = product p_i^(max(a_i, b_i))$
    - A useful identity: $a * b = gcd(a, b) * lcm(a, b)$.
  ])

  == Primality Testing & Distribution
  #concept-block(body: [
    #inline[Trial Division]
    To check if an integer $n$ is prime, it is sufficient to test for divisibility by all primes up to $sqrt(n)$.
    - *Lemma:* Every composite integer $n$ has a prime divisor $p <= sqrt(n)$.
    - *Proof Idea:* If $n=a b$, then either $a <= sqrt(n)$ or $b <= sqrt(n)$, otherwise $a b > n$. This divisor either is prime or has a smaller prime factor.

    #inline[Infinitude of Primes]
    
    *Theorem (Euclid):* There are infinitely many prime numbers.
    
    *Proof by Contradiction:*
    1. Assume there is a finite list of all primes: $p_1, p_2, ..., p_n$.
    2. Construct the number $N = (p_1 * p_2 * ... * p_n) + 1$.
    3. $N$ is not divisible by any prime on our "complete" list (it always leaves a remainder of 1).
    4. This means $N$ must either be prime itself, or be divisible by a new prime not on our list.
    5. This contradicts the assumption that our list was complete.
  ])

  = Part III: Modular Arithmetic
  _Modular arithmetic deals with remainders. Instead of the infinite set of integers, we work with a finite set of "congruence classes," which simplifies many problems._

  == Congruence Relations
  #concept-block(body: [
    #inline[Definition]
    Two integers $a, b$ are *congruent modulo m* (where $m >= 1$) if they have the same remainder when divided by $m$.
    $a equiv b (mod m) quad<=>quad m | (a - b)$
    - This is an *equivalence relation*: it is reflexive, symmetric, and transitive.
    - The equivalence classes are the sets of integers with the same remainder. For modulo $m$, there are $m$ classes: $[0]_m, [1]_m, ..., [m-1]_m$.
    - The set of these classes is denoted $ZZ_m = {[0]_m, [1]_m, ..., [m-1]_m}$.

    #inline[Modular Arithmetic Rules]
    Congruence is compatible with addition and multiplication. If $a equiv b (mod m)$ and $c equiv d (mod m)$:
    - $a + c equiv b + d (mod m)$
    - $a * c equiv b * d (mod m)$
    
    *Intuition:* You can reduce intermediate results modulo $m$ at any point in a calculation without changing the final result's remainder.
    
    *Example:* Compute $7^100 mod 24$.
    $7^2 = 49 equiv 1 (mod 24)$.
    $7^100 = (7^2)^50 equiv 1^50 equiv 1 (mod 24)$.
  ])

  == Multiplicative Inverses & Groups
  #concept-block(body: [
    #inline[Definition & Existence]
    The *multiplicative inverse* of an integer $a$ modulo $m$ is an integer $x$ such that:
    $a x equiv 1 (mod m)$
    This inverse is often denoted $a^(-1)$.
    
    *Theorem:* A multiplicative inverse of $a$ modulo $m$ exists *if and only if* $gcd(a, m) = 1$. If it exists, it is unique in $ZZ_m$.

    #box(fill: luma(235), inset: 5pt, radius: 3pt)[
      *Approach: Finding the Inverse*
      Use the Extended Euclidean Algorithm to find $u, v$ such that $u a + v m = gcd(a, m)$.
      1. If $gcd(a, m) = 1$, then we have:
         $u a + v m = 1$
      2. Taking this equation modulo $m$:
         $u a + v m equiv 1 (mod m)$
         $u a + 0 equiv 1 (mod m)$
         $u a equiv 1 (mod m)$
      3. The Bézout coefficient $u$ is the inverse of $a$. If $u$ is negative, add $m$ to get the equivalent inverse in $ZZ_m$.
    ]

    #inline[The Group of Units $ZZ_m^star$]
    - The set of all integers in $ZZ_m$ that are relatively prime to $m$ is denoted $ZZ_m^star$.
    - $ZZ_m^star$ forms a *multiplicative group*. This means it's closed under multiplication, has an identity (1), and every element has an inverse within the set.
  ])

  == Key Theorems
  #concept-block(body: [
    #inline[Euler's Totient Function]
    
    *Euler's totient function*, $phi(m)$, counts the number of positive integers up to $m$ that are relatively prime to $m$.
    - In other words, $phi(m) = |ZZ_m^star|$.
    - If $p$ is prime, $phi(p) = p-1$.
    - If $p, q$ are distinct primes, $phi(p q) = (p-1)(q-1)$.
    - If $m = p_1^(k_1) ... p_r^(k_r)$, then $phi(m) = m product_(i=1)^r (1 - 1/p_i)$.

    #inline[Euler's Theorem]
    If $gcd(a, m) = 1$, then:
    $a^(phi(m)) equiv 1 (mod m)$
    
    *Intuition:* This is a deep result from group theory (Lagrange's Theorem) applied to $ZZ_m^star$. It provides a powerful way to reduce large exponents.

    #inline[Fermat's Little Theorem]
    A special case of Euler's Theorem. If $p$ is a prime and $a$ is not a multiple of $p$:
    $a^(p-1) equiv 1 (mod p)$
    An alternative form is $a^p equiv a (mod p)$ for any integer $a$.
  ])

  == Chinese Remainder Theorem (CRT)
  #concept-block(body: [
    #inline[The Theorem]
    Let $m_1, m_2, ..., m_r$ be pairwise relatively prime integers. Then for any integers $a_1, ..., a_r$, the system of simultaneous congruences:
    $x equiv a_1 (mod m_1)$
    $x equiv a_2 (mod m_2)$
    $...$
    $x equiv a_r (mod m_r)$
    has a *unique solution* for $x$ modulo $M = m_1 * m_2 * ... * m_r$.

    #box(fill: luma(235), inset: 5pt, radius: 3pt)[
      *Approach: Constructive Solution*
      1. For each $i$, calculate $M_i = M / m_i$.
      2. For each $i$, find the modular inverse of $M_i$ modulo $m_i$. Let's call it $N_i$.
         $M_i N_i equiv 1 (mod m_i)$. (Use Extended Euclidean Alg.)
      3. The solution $x$ is the sum of these parts:
         $x = sum_(i=1)^r a_i M_i N_i$
      4. The final unique solution is $x mod M$.
      *Intuition:* Each term $a_i M_i N_i$ is constructed to be congruent to $a_i$ modulo $m_i$ and congruent to 0 modulo all other $m_j$ (since $m_j | M_i$ for $j!=i$). Summing them up satisfies all congruences simultaneously.
    ]
  ])

  = Part IV: Cryptographic Applications
  _Number theory, once considered pure mathematics, is now the foundation of modern digital security._

  == Diffie-Hellman Key Exchange
  #concept-block(body: [
    #inline[The Problem & The Protocol]
    How can Alice and Bob agree on a shared secret key over a public channel?
    1. *Public Parameters:* Large prime $p$ and a generator $g$ in $ZZ_p^*$.
    2. *Alice:* Chooses secret $x_A$, sends public $y_A = g^(x_A) mod p$.
    3. *Bob:* Chooses secret $x_B$, sends public $y_B = g^(x_B) mod p$.
    4. *Shared Secret:* Alice computes $(y_B)^(x_A)$. Bob computes $(y_A)^(x_B)$. Both get $g^(x_A x_B) mod p$.

    #inline[Security]
    Based on the *Discrete Logarithm Problem*: given $g, p,$ and $y$, it is computationally hard to find the exponent $x$ such that $y = g^x mod p$.
  ])
]