#import "@preview/showybox:2.0.4": showybox

#let homepage = link("https://cs.shivi.io")[cs.shivi.io]
#let author = "Shivram Sambhus"
#let title = "Analysis 1 Cheatsheet (FS25)"

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


#set text(size: 7.5pt)

#set heading(numbering: "1.1")

#let color-box = (
  rgb("888888"),
  rgb("888888"),
)

#show heading: it => {
  let index = counter(heading).at(it.location()).first()
  let hue = color-box.at(calc.rem(index, color-box.len()))
  hue = color-box.at(calc.rem(index - 1, color-box.len()))

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
  let current-color = rgb("#000000")
  block(
    breakable: true,
    stroke: current-color,
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
  let current-color = rgb("#000000")

  box(grid(
    columns: (1fr, auto, 1fr),
    align: horizon + center,
    column-gutter: 1em,
    line(length: 100%, stroke: 1pt + current-color),
    text(fill: current-color, weight: "bold")[#title],
    line(length: 100%, stroke: 1pt + current-color),
  ))
}

#columns(4, gutter: 6pt)[

  #text(title, weight: "bold") - #text(author + " @ " + homepage)

  = Part I: Foundations
  == The Real Number System ($RR$)
  _This section lays the foundation for analysis by defining the real numbers $RR$ as a complete ordered field. The key axioms—Field, Order, and especially Completeness—are what give $RR$ its unique structure without "gaps," allowing for concepts like suprema and infima._

  === Axioms of the Real Numbers
  #concept-block(body: [
    #block(inset: (
      bottom: 4pt,
    ))[The real numbers $RR$ form a *complete ordered field* satisfying:]
    - *Field Axioms:* Define a *field*, ensuring standard arithmetic works as expected (associativity, commutativity, identities, inverses, distributivity).
    - *Order Axioms:* Define an *ordered field*, allowing comparison of numbers (reflexivity, antisymmetry, transitivity, totality) and ensuring compatibility with field operations ($x <= y => x+z <= y+z$; and $0 <= x, y => 0 <= x y$).
    - *Completeness Axiom:* This is the crucial axiom that distinguishes $RR$ from $QQ$. Every non-empty set of real numbers that is bounded above has a *least upper bound* (a supremum) in $RR$. An equivalent statement is that every non-empty set bounded below has a greatest lower bound (infimum) in $RR$.
    #box(fill: luma(200), inset: 6pt, radius: 2pt)[

      *Intuition:* If you have a set of numbers all less than, say, 2, there must be a single "best" ceiling for that set, and that ceiling is a real number itself (not true for rationals) (e.g., the set ${x in QQ | x^2 < 2}$ has an upper bound in $QQ$, like 2, but no *least* upper bound *in* $QQ$).
    ]
  ])

  === Supremum and Infimum
  An *upper bound* of a set $A$ is a number $c$ s.t. $forall a in A, a <= c$. The *supremum* ($sup(A)$) is the least upper bound. A *lower bound* is a number $d$ s.t. $forall a in A, a >= d$. The *infimum* ($inf(A)$) is the greatest lower bound.

  #concept-block(body: [
    #inline("Characterization of Supremum")
    $x = sup(A)$ if and only if:
    1. $x$ is an upper bound: $forall a in A, a <= x$.
    2. For any $epsilon > 0$, $x - epsilon$ is not an upper bound: $exists a in A$ s.t. $x - epsilon < a$.

    #inline("Properties of Supremum/Infimum")
    For non-empty, bounded sets $A, B subset RR$ and $c in RR$:
    - $sup(A union B) = max(sup(A), sup(B))$
    - $sup(A+B) = sup(A) + sup(B)$, where $A+B = {a+b | a in A, b in B}$.
    - $sup(c A) = c sup(A)$ for $c > 0$.
    - $sup(c A) = c inf(A)$ for $c < 0$.

    #inline("Key Properties from Axioms")
    - *Archimedean Property*: For any $x, y in RR$ with $x>0$, there exists an $n in NN$ such that $n x > y$.
    - *Density of Rationals*: Between any two distinct real numbers, there exists a rational number.
  ])

  === Absolute Value & Inequalities
  The *absolute value* of $x in RR$, denoted $abs(x)$, is $x$ if $x>=0$ and $-x$ if $x<0$.

  #concept-block(body: [
    #inline("Important Inequalities")
    - *Triangle Inequality*: $abs(x + y) <= abs(x) + abs(y)$
    - *Reverse Triangle Inequality*: $abs(abs(x) - abs(y)) <= abs(x - y)$
    - *Bernoulli's*: For $x > -1, n in NN$, $(1+x)^n >= 1 + n x$.
    - *AM-GM (Arithmetic-Geometric Mean)*: For non-negative $x_1, ..., x_n$:
      $ root(n, x_1 ... x_n) <= (x_1 + ... + x_n)/n $
    - *Young's Inequality*: For $x,y >= 0$ and $epsilon > 0$:
      $x y <= epsilon/2 x^2 + 1/(2epsilon) y^2$
    - *Exponential Inequality*: For all $x in RR$:
      $1 + x <= e^x$
  ])

  == Complex Numbers & $RR^n$
  _This section extends analysis from the real line to higher dimensions. Complex numbers $CC$ form an algebraically complete field, crucial for many areas of math. Euclidean space $RR^n$ provides the setting for multivariable calculus, where concepts like distance and limits are generalized using norms._

  === Complex Numbers ($CC$)
  Numbers of the form $z = a + b i$, where $a, b in RR$ and $i^2 = -1$.
  - *Conjugate*: $overline(z) = a - b i$.
  - *Modulus*: $abs(z) = sqrt(a^2 + b^2) = sqrt(z overline(z))$.
  - *Polar Form*: $z = r(cos(theta) + i sin(theta))$ where $r = abs(z)$.
  - *Exponential Form*: $z = r e^(i theta)$.
  - *Fundamental Thm. of Algebra*: Every non-constant polynomial with complex coefficients has at least one root in $CC$.

  #concept-block(body: [
    #inline("Euler's & De Moivre's Formulas")
    - *Euler's Formula*: $e^(i theta) = cos(theta) + i sin(theta)$.
    - *De Moivre's Formula*: $(cos(theta) + i sin(theta))^n = cos(n theta) + i sin(n theta)$.

    #inline("Calculating the Argument, $arg(z)$")
    #box(
      fill: luma(200),
      inset: 6pt,
      radius: 2pt,
    )[*Strategy:* Always draw the point in the complex plane to ensure your angle is correct. The $"atan2"(b,a)$ function often handles this automatically. The *principal argument* is usually taken in $(-\pi, \pi]$.]
  ])

  === Euclidean Space ($RR^n$)
  $RR^n$ is the set of vectors $x = (x_1, ..., x_n)$.
  - *Inner Product*: $x dot.c y = sum_(i=1)^n x_i y_i$.
  - *Euclidean Norm*: $||x||_2 = sqrt(x dot.c x)$.
  - *Metric (Distance)*: $d(x,y) = |abs(x-y)|_2$.

  #concept-block(body: [
    #inline("Key Inequalities & Convergence")
    - *Cauchy-Schwarz*: $abs(x dot.c y) <= ||x||_2 ||y||_2$.
    - *Triangle Inequality*: $||x+y||_2 <= ||x||_2 + ||y||_2$.
    - *Convergence*: A sequence $(x_k)$ in $RR^n$ converges to $L in RR^n$ if $lim_(k->oo) ||x_k - L||_2 = 0$. This is equivalent to component-wise convergence.
  ])

  = Part II: Sequences and Series
  == Sequences of Numbers
  _A sequence is an infinite, ordered list of numbers. The central idea is convergence: do the terms of the sequence "settle down" and approach a single finite value, called the limit? This section provides the formal definition of a limit and key theorems to prove convergence or divergence._

  A sequence $(a_n)$ converges to a limit $L$ if $forall epsilon > 0, exists N in NN$ such that for all $n >= N$, it holds that $abs(a_n - L) < epsilon$. A sequence can have at most one limit.

  === Key Convergence Theorems
  #concept-block(body: [
    #inline("Squeeze Theorem")
    If $a_n <= b_n <= c_n$ for large $n$, and $lim a_n = lim c_n = L$, then $lim b_n = L$.

    #inline("Monotone Convergence Theorem")
    Every bounded, monotonic sequence converges. This is a direct, powerful consequence of the Completeness Axiom.

    #inline("Bolzano-Weierstrass Theorem")
    Every bounded sequence in $RR$ has a convergent subsequence. This is the workhorse for compactness arguments.

    #inline("Cauchy Criterion")
    A sequence converges iff it is a *Cauchy sequence*. In a complete space like $RR$, this means the terms get arbitrarily close to *each other*. ($forall epsilon > 0, exists N$ s.t. for $m,n >= N$, $abs(a_m - a_n) < epsilon$).

    #inline("Nested Interval Theorem (Cauchy-Cantor)")
    If $I_n = [a_n, b_n]$ is a sequence of non-empty, nested, closed bounded intervals (i.e., $I_1 supset I_2 supset ...$), then their intersection is non-empty. If, in addition, the lengths of the intervals tend to zero ($lim_(n->oo) (b_n - a_n) = 0$), then the intersection contains exactly one point. This theorem is equivalent to the Completeness Axiom.

    #inline("Insight: Why Cauchy is useful")
    The Cauchy criterion lets us prove convergence *without knowing the limit's value*. This is a huge theoretical advantage.

    *Problem:* Show that if $|a_{n+1} - a_n| <= r^n$ for some $r in (0,1)$, then $(a_n)$ is Cauchy.

    *Solution:* For $m > n$, use the triangle inequality and sum a geometric series:
    $|a_m - a_n| <= sum_(j=n)^(m-1) |a_(j+1) - a_j| <= sum_(j=n)^(m-1) r^j < sum_(j=n)^oo r^j = r^n/(1-r)$.
    As $n->oo$, this tail goes to 0. For any $epsilon > 0$, we can find an $N$ such that the tail is less than $epsilon$. Thus, $(a_n)$ is Cauchy and converges.
  ])

  === Strategies & Common Limits
  #concept-block(body: [
    #inline("Proving Divergence")
    Show the sequence is unbounded, OR find two subsequences that converge to different limits (e.g., $a_n = (-1)^n$).

    #inline("Dominant Term Analysis")
    For rational functions of polynomials or exponentials, divide by the fastest-growing term. Hierarchy: Factorials > Exponentials > Polynomials > Logarithms.

    #inline("Important Limits to Know")
    - $lim_(n->oo) (1+x/n)^n = e^x$
    - $lim_(n->oo) root(n, n) = 1$
    - $lim_(n->oo) root(n, a) = 1$ for $a>0$.
      #box(
        fill: luma(200),
        inset: 6pt,
        radius: 2pt,
      )[*Proof for $a>1$:* Let $root(n, a) = 1+b_n$ for $b_n>0$. Then $a=(1+b_n)^n$. By Bernoulli's inequality, $a >= 1+n b_n$. Rearranging gives $0 < b_n <= (a-1)/n$. By Squeeze Theorem, $b_n -> 0$, so $root(n, a) -> 1$.]
    - $lim_(n->oo) n^k/a^n = 0$ for $a>1, k in RR$.

    #inline("Tricks for Evaluating Limits")
    - *Binomial Trick*: For square roots, multiply by the conjugate:
      $lim (sqrt(n^2+3n)-n) = lim ((n^2+3n)-n^2)/(sqrt(n^2+3n)+n) = lim (3n)/(n(sqrt(1+3/n)+1)) = 3/2$.
    - *Log Trick*: For limits of the form $f(x)^(g(x))$, rewrite as $e^(g(x) ln(f(x)))$ and find the limit of the exponent.
  ])

  #concept-block(body: [
    #inline("Limes Superior and Inferior")
    For a bounded sequence $(a_n)$, we define:
    - $lim inf a_n := lim_(n->oo) (inf_(k>=n) a_k)$ (largest subsequential limit)
    - $lim sup a_n := lim_(n->oo) (sup_(k>=n) a_k)$ (smallest subsequential limit)
    A sequence $(a_n)$ converges to $L$ iff it is bounded and $lim inf a_n = lim sup a_n = L$.

    #box(fill: luma(200), inset: 6pt, radius: 2pt)[
      #inline("Strategy: Recursive Sequences")
      *Problem:* For $a_1=sqrt(2), a_(n+1) = sqrt(2+a_n)$, show convergence and find the limit.
      1. *Boundedness:* Prove $a_n <= 2$ by induction. Base case $a_1 <= 2$ holds. Assume $a_k <= 2$. Then $a_(k+1) = sqrt(2+a_k) <= sqrt(2+2) = 2$.
      2. *Monotonicity:* Prove $a_(n+1) >= a_n$ by induction. $a_2 = sqrt(2+sqrt(2)) > sqrt(2) = a_1$. Assume $a_k >= a_(k-1)$. Then $a_(k+1) = sqrt(2+a_k) >= sqrt(2+a_(k-1)) = a_k$.
      3. *Convergence:* By Monotone Convergence Theorem, $(a_n)$ converges to some limit $L$.
      4. *Find Limit:* Take the limit of the recursion: $lim a_(n+1) = lim sqrt(2+a_n) => L = sqrt(2+L) => L^2 - L - 2 = 0 => (L-2)(L+1)=0$. Since $a_n>0$, the limit must be $L=2$.
    ]
  ])

  == Series of Numbers
  _A series is the sum of the terms in a sequence. We ask if this infinite sum converges to a finite value. This section covers various tests to determine convergence, distinguishes between absolute and conditional convergence, and explores how rearranging terms can affect the sum._

  A series $sum_(k=1)^oo a_k$ converges if its sequence of partial sums $S_n = sum_(k=1)^n a_k$ converges. A series with non-negative terms converges iff its partial sums are bounded.

  #concept-block(body: [
    #inline("Fundamental Series Types")
    - *Geometric Series*: $sum_(k=0)^oo a r^k$. Converges to $a/(1-r)$ if $|r| < 1$; diverges if $|r| >= 1$.
    - *p-Series*: $sum_(k=1)^oo 1/k^p$. Converges if $p > 1$; diverges if $p <= 1$.
    - *Harmonic Series*: $sum_(k=1)^oo 1/k$. A special p-series with $p=1$. It *diverges*.
    - *Alternating Harmonic Series*: $sum_(k=1)^oo (-1)^(k-1)/k$. Converges to $ln(2)$.
  ])

  === Convergence Tests
  #concept-block(body: [
    #inline("Divergence Test")
    If $lim_(k->oo) a_k != 0$ (or does not exist), the series $sum a_k$ *diverges*.

    #inline("Tests for Positive Series")
    - *Direct Comparison:* If $0 <= a_k <= b_k$ and $sum b_k$ converges, then $sum a_k$ converges.
    - *Limit Comparison:* For positive series $sum a_k, sum b_k$, let $L = lim (a_k/b_k)$. If $0 < L < oo$, then both series behave the same (both converge or both diverge).
    - *Integral Test:* If $f(x)$ is a positive, continuous, decreasing function on $[N, oo)$ and $a_k = f(k)$, then $sum a_k$ converges iff $integral_N^oo f(x) "dx"$ converges.

    #box(fill: luma(200), inset: 6pt, radius: 2pt)[
      #inline("Strategy: Boundedness for Comparison")
      If $sum a_k$ converges *absolutely* and $sum b_k$ converges, show $sum a_k b_k$ and $sum a_k^2$ converge absolutely.

      *Solution ($sum a_k b_k$):* Since $sum b_k$ converges, the sequence $(b_k)$ is bounded by some $M$. Thus, $|a_k b_k| = |a_k| |b_k| <= M |a_k|$. Since $sum M|a_k|$ converges, $sum a_k b_k$ converges absolutely by comparison.

      *Solution ($sum a_k^2$):* Since $sum |a_k|$ converges, $a_k -> 0$. For large enough $k$, $|a_k|<1$, which implies $|a_k|^2 < |a_k|$. The series $sum |a_k|^2$ converges by comparison with $sum |a_k|$.
    ]
    #box(fill: luma(200), inset: 6pt, radius: 2pt)[
      #inline("Strategy: AM-GM for Comparison")
      Given $sum a_k$ converges ($a_k >= 0$), prove $sum sqrt(a_k a_(k+1))$ converges.

      *Solution:* By AM-GM, $sqrt(a_k a_(k+1)) <= (a_k + a_(k+1))/2$. The series $sum (a_k + a_(k+1))/2 = 1/2 sum a_k + 1/2 sum a_(k+1)$ converges. By Direct Comparison, $sum sqrt(a_k a_(k+1))$ converges.
    ]
  ])

  === Absolute, Conditional, and Other Tests
  A series $sum a_k$ is *absolutely convergent* if $sum abs(a_k)$ converges. It is *conditionally convergent* if it converges but does not converge absolutely.

  #concept-block(body: [
    #inline("Key Theorems")
    - *Absolute Convergence Implies Convergence*: If a series converges absolutely, then it converges.
    - *Alternating Series Test (Leibniz)*: An alternating series $sum (-1)^k a_k$ converges if $(a_k)$ is positive, decreasing, and $lim a_k = 0$. Remainder estimate: $|S - S_n| <= a_(n+1)$.
    - *Ratio and Root Tests*: Let $L = lim abs(a_(k+1)/a_k)$ (Ratio) or $L = limsup root(k, abs(a_k))$ (Root).
      - $L < 1 =>$ Series converges absolutely.
      - $L > 1 =>$ Series diverges.
      - $L = 1 =>$ Test is inconclusive.
      #box(fill: luma(200), inset: 6pt, radius: 2pt)[
        *Root Test Logic ($L = limsup root(k, |a_k|)$)*:
        - *If $L < 1$*: Find $q$ with $L < q < 1$. For large $k$, $|a_k| < q^k$. Converges by comparison to geometric series $sum q^k$.
        - *If $L > 1$*: $|a_k| > 1$ for infinitely many $k$. Terms don't go to 0, so series diverges by Divergence Test.
      ]
    - *Dirichlet's Test*: If $(a_n)$ is a positive, decreasing sequence with $lim a_n = 0$, and the partial sums of another series $sum b_n$ are bounded, then $sum a_n b_n$ converges. (Leibniz is a special case where $b_n = (-1)^n$).
    - *Riemann Rearrangement Theorem*: A conditionally convergent series can be rearranged to sum to any real number, or to diverge. An absolutely convergent series will always sum to the same value, regardless of rearrangement.
  ])

  === Operations on Series
  #concept-block(body: [
    #inline("Swapping Double Sums")
    You can swap the order of summation in a double series $sum_m sum_n a_(m,n)$ if the series converges *absolutely*. This means the sum of all absolute values is finite.

    *Sufficient Condition:* A constant $C$ exists such that:
    $ sum_(m=0)^M sum_(n=0)^N |a_(m,n)| <= C, quad forall M, N >= 0 $
    If this holds, then:
    $ sum_(m=0)^oo (sum_(n=0)^oo a_(m,n)) = sum_(n=0)^oo (sum_(m=0)^oo a_(m,n)) $

    #inline("Pitfall: Swapping is not always allowed!")
    *Counterexample:* Let $a_(m,m) = 1$, $a_(m, m+1) = -1$, and $0$ otherwise.
    - $sum_m (sum_n a_(m,n)) = sum_m (1-1) = 0$.
    - $sum_n (sum_m a_(m,n)) = 1 + (-1+1) + ... = 1$. Since $0 != 1$, the swap is invalid.

    #inline("Cauchy Product")
    The Cauchy product of two series $sum a_n$ and $sum b_n$ is the series $sum c_n$ where $c_n = sum_(k=0)^n a_k b_(n-k)$.
    - *Mertens' Theorem:* If $sum a_n$ converges *absolutely* to $A$ and $sum b_n$ converges to $B$, their Cauchy product converges to $A B$.
    - *Abel's Theorem:* If $sum a_n -> A$, $sum b_n -> B$, and their Cauchy product $sum c_n$ converges to $C$, then $C = A B$.
    #box(fill: luma(200), inset: 6pt, radius: 2pt)[
      #inline("Pitfall: Conditional Convergence")
      The Cauchy product of two conditionally convergent series may diverge. Example: $sum_(n=0)^oo (-1)^n/sqrt(n+1)$ with itself.
    ]
  ])

  == Power Series
  _A series of the form $sum c_n (x-a)^n$. They are central to analysis, defining many important functions._

  For each power series, there is a *radius of convergence* $R in [0, oo]$.
  - Converges absolutely for $|x-a|<R$.
  - Diverges for $|x-a|>R$.
  - Behavior at the boundary $|x-a|=R$ must be tested separately.

  #concept-block(body: [
    #inline("Calculating the Radius of Convergence (R)")
    - *Root Test (Cauchy-Hadamard)*: The most general formula.
      $ R = 1 / (lim sup_(n->oo) root(n, |c_n|)) $
    - *Ratio Test*: Often easier, but only works if the limit exists.
      $ R = lim_(n->oo) abs(c_n / c_(n+1)) $
    #box(fill: luma(200), inset: 6pt, radius: 2pt)[
      #inline("Strategy: Gap Series")
      For $sum_(n=0)^oo (9i)/n^2 z^(2n)$, the coefficients $c_k$ are non-zero only for even $k$. You must use the Cauchy-Hadamard formula.
      $c_k = cases((36i)/k^2 & "if " k " is even", 0 & "if " k " is odd")$.
      $L = limsup_(k->oo) |c_k|^(1/k) = lim_(k->oo, "k even") (36/k^2)^(1/k) = (lim 36^(1/k))/(lim (k^(1/k))^2) = 1/1^2 = 1$.
      The ROC is $R = 1/L = 1$.
    ]
    #inline("Differentiation & Integration")
    A power series can be differentiated or integrated term-by-term inside its open interval of convergence.
    - *Key Fact*: Differentiating or integrating a power series *does not change its radius of convergence*.
    - *Reason*: The radius for $sum n c_n x^(n-1)$ is $1/(limsup root(n, |n c_n|))$. Since $lim root(n, n)=1$, this is the same as the original radius.
    - *Application*: We know $1/(1-x) = sum_(n=0)^oo x^n$ for $|x|<1$. Integrating gives:
      $-ln(1-x) = sum_(n=0)^oo x^(n+1)/(n+1)$ for $|x|<1$.
  ])

  #concept-block(body: [
    #inline("The Exponential Function $exp(z)$")
    Defined by its power series: $ exp(z) := sum_(n=0)^oo z^n/(n!) $ It converges for all $z in CC$.
    - *Alternative Definition (Real Line):* $e^x = exp(x) = lim_(n->oo) (1+x/n)^n$.
    #box(
      fill: luma(200),
      inset: 6pt,
      radius: 2pt,
    )[*Pitfall:* The sum must start at $n=0$ to include the leading term $z^0/0! = 1$. The sum from $n=1$ is $exp(z)-1$.]
    - *Key Property:* $exp(z+w) = exp(z) exp(w)$ for all $z, w in CC$.
    - *On the Real Line:* $exp(x)$ is strictly positive, strictly increasing, and its derivative is itself. Its range is $(0,oo)$.
    #box(fill: luma(200), inset: 6pt, radius: 2pt)[
      #inline("Limit Strategy: Use $exp$")
      *Problem:* Evaluate $lim_(n->oo) (1 + 1/n^3)^n$.

      *Solution:* Rewrite as $((1 + 1/n^3)^(n^3))^(1/n^2)$. The inner part tends to $e$. The limit becomes $lim_(n->oo) e^(1/n^2) = e^0 = 1$.
    ]
    #inline("Connection to Trigonometry")
    For real $x$, $e^(i x) = cos(x) + i sin(x)$.
    - $cos(x) = (e^(i x) + e^(-i x))/2$, $sin(x) = (e^(i x) - e^(-i x))/(2i)$
  ])


  = Part III: Functions, Limits, Continuity
  == Limits & Continuity of Functions
  _This section covers the behavior of functions. A limit describes the value a function approaches. Continuity formalizes the idea of a function having no "jumps" or "holes". Uniform convergence extends this to sequences of functions._

  A function $f$ has a limit $L$ at a cluster point $c$ of its domain $D$, written $lim_(x->c) f(x) = L$, if: $forall epsilon > 0, exists delta > 0$ s.t. for all $x in D$, $0 < |x-c| < delta => |f(x) - L| < epsilon$.
  A function $f$ is *continuous* at a point $c$ in its domain if $lim_(x->c) f(x) = f(c)$.

  #concept-block(body: [
    #inline("Sequential Criterion")
    $lim_(x->c) f(x) = L$ iff for *every* sequence $(x_n)$ in $D backslash {c}$ with $x_n -> c$, we have $f(x_n) -> L$.
    #box(fill: luma(200), inset: 6pt, radius: 2pt)[
      *Strategy: Proving Discontinuity*
      To show $f(x) = cases(x, &"if " x in QQ \ 0, &"if " x in.not QQ)$ is discontinuous at $x_0 != 0$.

      *Solution:* Let $x_0 in QQ, x_0 != 0$. Then $f(x_0)=x_0$. Find a sequence of *irrationals* $(y_n)$ converging to $x_0$. Then $f(y_n) = 0$ for all $n$. The limit $lim f(y_n) = 0 != f(x_0)$. By the sequential criterion, $f$ is not continuous at $x_0$.
    ]

    #inline("Key Theorems on Compact Sets $[a,b]$")
    - *Intermediate Value Theorem (IVT)*: If $f$ is continuous on $[a,b]$, it takes on every value between $f(a)$ and $f(b)$.
      *Application:* If $f:[0,1]->[0,1]$ is continuous, it has a fixed point. Let $g(x) = f(x)-x$. $g(0)=f(0)>=0$ and $g(1)=f(1)-1<=0$. By IVT, there's a $c$ where $g(c)=0$, so $f(c)=c$.
    - *Extreme Value Theorem (EVT)*: If $f$ is continuous on $[a,b]$, then $f$ is bounded and attains its global maximum and minimum.
    - *Heine-Cantor Theorem*: If $f$ is continuous on $[a,b]$, then it is *uniformly continuous*.
  ])

  #concept-block(body: [
    #inline("Monotonicity & Boundedness Pitfalls")
    - *Monotonicity on a non-compact interval does NOT imply boundedness*. E.g., $f(x) = 1/x$ on $(0, 1]$.
    - *Monotonicity on a COMPACT interval $[a,b]$ implies boundedness*. Its range is $[f(a), f(b)]$ (if increasing).
    - *Boundedness does NOT imply monotonicity*. E.g., $f(x) = sin(x)$ on $[0, 2pi]$.
    - *Strict monotonicity does NOT imply continuity*. It can still have jump discontinuities.
    #box(fill: luma(200), inset: 6pt, radius: 2pt)[
      #inline("Pitfall: Monotonicity vs. Differentiability")
      - *Strictly Monotonic does NOT imply Differentiable at a point:* The function $f(x) = x^3$ is strictly increasing everywhere, but its derivative is $f'(0)=0$.
    ]
  ])

  == Sequences and Series of Functions
  #concept-block(body: [
    #inline("Pointwise vs. Uniform Convergence")
    - *Pointwise*: $lim_(n->oo) f_n (x) = f(x)$ for each fixed $x$. The rate of convergence can vary with $x$.
    - *Uniform*: $lim_(n->oo) "sup"_(x in D) |f_n (x) - f(x)| = 0$. The "worst-case" error across the domain goes to zero. Uniform convergence implies pointwise convergence.

    #inline("Consequences of Uniform Convergence")
    Let $f_n -> f$ uniformly.
    - *Continuity*: If all $f_n$ are continuous, then $f$ is continuous.
    - *Integration*: $lim_(n->oo) integral_a^b f_n (x) "dx" = integral_a^b f(x) "dx"$.
    - *Differentiation*: Requires a stronger condition. If $(f_n')$ converges *uniformly* to $g$ and $(f_n)$ converges *pointwise* to $f$, then $f$ is differentiable and $f' = g$.
    #box(fill: luma(200), inset: 6pt, radius: 2pt)[
      #inline("Pitfall: Differentiability")
      Uniform convergence of differentiable functions $f_n -> f$ is *not* enough to guarantee that the limit $f$ is differentiable.
      *Counterexample:* $f_n (x) = sqrt(1/n^2 + x^2)$ on $(-1,1)$. Each $f_n$ is smooth, but $(f_n)$ converges uniformly to $f(x) = |x|$, which is not differentiable at $x=0$.
    ]

    #inline("Weierstrass M-Test (for Series)")
    If there is a convergent series of positive numbers $sum M_n$ such that $|u_n (x)| <= M_n$ for all $x$ in the domain $D$, then the series $sum u_n (x)$ converges *uniformly* on $D$.
  ])

  = Part IV: Differentiation and Integration
  == Differentiation
  _Differentiation measures the instantaneous rate of change. The derivative gives the slope of the tangent line. This section defines the derivative, details its fundamental rules, and covers the main theorems that relate it to a function's behavior._

  The derivative of $f$ at $c$ is $f'(c) = lim_(h->0) (f(c+h) - f(c))/h$. If a function is differentiable at $c$, it must be continuous at $c$. The converse is false (e.g., $f(x)=abs(x)$ at $x=0$).

  #concept-block(body: [
    #inline("Fundamental Rules of Differentiation")
    Let $f, g$ be differentiable at $x$ and $c$ be a constant.
    - *Linearity:* $(c f(x) + g(x))' = c f'(x) + g'(x)$.
    - *Product Rule:* $(f(x)g(x))' = f'(x)g(x) + f(x)g'(x)$.
    - *Quotient Rule:* $((f(x))/(g(x)))' = (f'(x)g(x) - f(x)g'(x))/(g(x)^2)$, for $g(x) != 0$.
    - *Chain Rule:* $(f(g(x)))' = f'(g(x)) dot.c g'(x)$.
    - *Logarithmic Power Rule:* $a^(log_b(c)) = c^(log_b(a))$.
  ])

  #concept-block(body: [
    #inline("Key Theorems of Differentiation")
    - *Fermat's Theorem*: If $f$ has a local extremum at an interior point $c$ and is differentiable there, then $f'(c) = 0$.
    - *Rolle's Theorem*: If $f$ is continuous on $[a,b]$, differentiable on $(a,b)$, and $f(a)=f(b)$, then there is a $c in (a,b)$ where $f'(c)=0$.
    - *Mean Value Theorem (MVT)*: If $f$ is continuous on $[a,b]$ and differentiable on $(a,b)$, there exists a $c in (a,b)$ such that $ f'(c) = (f(b) - f(a))/(b-a) $
    - *L'Hôpital's Rule*: For indeterminate forms $0/0$ or $oo/oo$: $ lim_(x->c) f(x)/g(x) = lim_(x->c) f'(x)/g'(x) $ if the second limit exists.
  ])

  #concept-block(body: [
    #inline("Higher-Order Derivatives and Applications")
    - *General Leibniz Rule (Product Rule)*:
      $ (f g)^(n)(x) = sum_(k=0)^n binom(n, k) f^((k))(x) g^((n-k))(x) $
    - *Taylor's Theorem*: Provides approximations of functions by polynomials with a remainder term.
      $f(x) = sum_(k=0)^n (f^((k))(a))/(k!) (x-a)^k + R_n (x)$
      where $R_n (x) = (f^((n+1))(c))/((n+1)!) (x-a)^(n+1)$ for some $c$ between $a$ and $x$.

    #inline("Extrema & Higher Derivatives (Second Derivative Test & Generalization)")
    Let $f'(c) = 0$.
    - If $f''(c) > 0$, $f$ has a local minimum at $c$.
    - If $f''(c) < 0$, $f$ has a local maximum at $c$.
    - If $f''(c) = 0$, the test is inconclusive.

    *Generalization:* Let $k >= 2$ be the first order for which $f^((k))(c) != 0$.
    - If $k$ is *even*: Local min if $f^((k))(c)>0$; local max if $f^((k))(c)<0$.
    - If $k$ is *odd*: Neither a max nor min (saddle/inflection point).
    #inline("Strategy: Finding the n-th Derivative")
    For many functions, the n-th derivative follows a pattern.
    1. *Compute the first few derivatives:* Calculate $f', f'', f'''$, etc.
    2. *Identify the pattern:* Look for repeating cycles (like sin/cos), factorial terms (from power rule), or alternating signs.
    3. *Formulate a hypothesis:* Write a general formula for $f^((n))(x)$.
    4. *Prove by Induction (optional but rigorous):* Verify the base case and show that if the formula holds for $n$, it holds for $n+1$.
  ])

  #concept-block(body: [
    #inline("Special Topics and Examples")
    - *Hyperbolic Functions:* $cosh(x) = (e^x+e^(-x))/2$, $sinh(x) = (e^x-e^(-x))/2$. They satisfy $(cosh(x))' = sinh(x)$, $(sinh(x))' = cosh(x)$, and $cosh^2(x) - sinh^2(x) = 1$.

    #inline("Even/Odd Derivatives")
    - The derivative of an even function is odd.
    - The derivative of an odd function is even.

    #inline("Differentiable but not Continuously")
    The function $f(x) = cases(x^2 sin(1/x), &"if " x != 0 \ 0, &"if " x=0)$ is differentiable everywhere (including at $x=0$, where $f'(0)=0$), but its derivative $f'(x)$ is not continuous at $x=0$.

    #box(fill: luma(200), inset: 6pt, radius: 2pt)[
      #inline("Smooth Functions ($C^oo$) and Analytic Functions ($C^omega$)")
      - A function is *smooth* if it has derivatives of all orders.
      - A function is *analytic* at a point $x_0$ if it is smooth and its Taylor series converges to the function in a neighborhood of $x_0$.
      - *Pitfall:* Not all smooth functions are analytic. The classic counterexample is $f(x) = cases(e^(-1/x^2), &"if " x != 0, 0, &"if " x=0)$. This function is infinitely differentiable everywhere, but all its derivatives at $x=0$ are zero. Its Taylor series at $0$ is identically zero and thus does not equal the function for any $x!=0$.
    ]
  ])

  == The Riemann Integral
  _Integration can be viewed as finding the area under a curve. The Riemann integral formalizes this with upper and lower sums. The Fundamental Theorem of Calculus provides the profound link between integration and differentiation._

  A function is *Riemann integrable* on $[a,b]$ if its upper and lower Riemann sums converge to the same value as the partition width goes to zero. Continuous functions and monotonic functions on $[a,b]$ are integrable.

  #concept-block(body: [
    #inline("Properties of the Definite Integral")
    - *Linearity*: $integral_a^b (alpha f(x) + beta g(x)) "dx" = alpha integral_a^b f(x) "dx" + beta integral_a^b g(x) "dx"$.
    - *Interval Additivity*: $integral_a^c f(x) "dx" = integral_a^b f(x) "dx" + integral_b^c f(x) "dx"$.
    - *Bounds*: $integral_a^b f(x) "dx" = - integral_b^a f(x) "dx"$ and $integral_a^a f(x) "dx" = 0$.
    - *Comparison*: If $f(x) <= g(x)$ for all $x in [a,b]$, then $integral_a^b f(x) "dx" <= integral_a^b g(x) "dx"$.
    - *Triangle Inequality for Integrals*: $|integral_a^b f(x) "dx"| <= integral_a^b |f(x)| "dx"$.
    - *Cauchy-Schwarz Inequality for Integrals*:
      $ (integral_a^b f(x)g(x) "dx")^2 <= (integral_a^b f(x)^2 "dx") (integral_a^b g(x)^2 "dx") $
  ])

  #concept-block(body: [
    #inline("Core Integration Techniques")

    *1. Substitution ($u$-sub):*
    *Goal:* Simplify the integrand by changing the variable. It is the reverse of the chain rule.
    *When to Use:* Look for a composite function $f(g(x))$ where the derivative of the "inner" function, $g'(x)$, is also present as a factor.
    *Process:*
    1. Identify a suitable inner function $u = g(x)$.
    2. Compute its differential: $"du" = g'(x)"dx"$.
    3. Substitute both $u$ and $"du"$ into the integral. All terms involving the original variable $x$ must be eliminated.
    4. Integrate the simpler function with respect to $u$.
    5. Back-substitute $u = g(x)$ to express the final answer in terms of $x$.
    *Example:* $integral x^2 cos(x^3) "dx"$.
    Let $u = x^3$. Then $"du" = 3x^2 "dx"$, so $x^2 "dx" = "du"/3$.
    $integral cos(u) ("du"/3) = 1/3 integral cos(u) "du" = 1/3 sin(u) + C = 1/3 sin(x^3) + C$.

    *2. Integration by Parts (IBP):*
    *Goal:* Transform an integral of a product into a hopefully simpler integral. It is the reverse of the product rule. Formula: $integral u "dv" = u v - integral v "du"$.
    *Strategy 1: Choosing $u$ (LIATE Heuristic):* To choose which part of the product is $u$, follow this order of preference. The remaining part is $"dv"$.
    1. Logarithmic ($ln(x)$)
    2. Inverse trigonometric ($arctan(x)$)
    3. Algebraic ($x^2, 3x$)
    4. Trigonometric ($sin(x)$)
    5. Exponential ($e^x$)
    *Strategy 2: Tabular Method (for repeated IBP):* Use when one function (the one you choose for $u$) differentiates to zero after several steps.
    1. Create two columns: one for differentiating ($D$), one for integrating ($I$).
    2. Start with your chosen $u$ in the $D$ column and $"dv"$ in the $I$ column.
    3. Repeatedly differentiate down the $D$ column until you reach zero.
    4. Repeatedly integrate down the $I$ column.
    5. The answer is the sum of the products of the diagonal terms, with alternating signs ($+,-,+,...$).
    *Example (Tabular):* $integral x^2 e^(2x) "dx"$.
    #table(
      columns: 3,
      align: center,
      table.header([*Sign*], [*Differentiate* $u$], [*Integrate* $"dv"$]),
      [$+$], [$x^2$], [$e^(2x)$],
      [$-$], [$2x$], [$1/2 e^(2x)$],
      [$+$], [$2$], [$1/4 e^(2x)$],
      [$-$], [$0$], [$1/8 e^(2x)$],
    )
    Result: $x^2(1/2 e^(2x)) - 2x(1/4 e^(2x)) + 2(1/8 e^(2x)) + C = 1/2 x^2 e^(2x) - 1/2 x e^(2x) + 1/4 e^(2x) + C$.

    *Stopping Conditions:*
    1. If D column reaches zero, stop.
    2. The integral of the last term (D column x I column) is trivial.
    3. We loop (see below) if the integral reappears

    *Strategy 3: Looping/Boomerang Integrals:* Use when integrating products of exponential and trig functions. After two rounds of IBP, the original integral reappears.

    *Example (Looping):* $I = integral e^x cos(x) "dx"$.
    1. Let $u=e^x, "dv"=cos(x)"dx"$. Then $I = e^x sin(x) - integral e^x sin(x) "dx"$.
    2. Apply IBP to the new integral: let $u=e^x, "dv"=sin(x)"dx"$.
      $integral e^x sin(x) "dx" = -e^x cos(x) + integral e^x cos(x) "dx" = -e^x cos(x) + I$.
    3. Substitute back and solve for $I$:
      $I = e^x sin(x) - (-e^x cos(x) + I) = e^x(sin(x)+cos(x)) - I$.
      $2I = e^x(sin(x)+cos(x)) => I = 1/2 e^x(sin(x)+cos(x)) + C$.

    *3. Partial Fraction Decomposition:*
    *Goal:* Break down a rational function $P(x)/Q(x)$ into a sum of simpler, integrable fractions.
    *Process:*
    1. *Long Division:* If $deg(P) >= deg(Q)$, perform polynomial long division first.
    2. *Factor Denominator:* Factor $Q(x)$ completely into linear factors $(x-a)$ and irreducible quadratic factors $(x^2+b x+c)$.
    3. *Set up Decomposition:*
      - For each factor $(x-a)^k$: $A_1/(x-a) + A_2/(x-a)^2 + ... + A_k/(x-a)^k$.
      - For each factor $(x^2+b x+c)^k$: $(B_1x+C_1)/(x^2+b x+c) + ... + (B_k x+C_k)/(x^2+b x+c)^k$.
    4. *Solve for Coefficients:* Combine the new fractions and equate the resulting numerator to the original $P(x)$. Solve the system of equations for the coefficients by either equating coefficients of like powers of $x$ or by substituting strategic values for $x$.

    *4. Trigonometric Substitution:*
    *Goal:* Eliminate square roots of quadratic expressions of the form $a^2+-x^2$ or $x^2-a^2$.
    *Process:*
    1. *Identify the Form and Substitute:* Choose the substitution for $x$ and find $"dx"$.
      #table(
        columns: 3,
        align: center,
        table.header([*Expression*], [*Substitution*], [*Identity Used*]),
        [$sqrt(a^2-x^2)$], [$x=a sin(theta)$], [$1-sin^2(theta)=cos^2(theta)$],
        [$sqrt(a^2+x^2)$], [$x=a tan(theta)$], [$1+tan^2(theta)=sec^2(theta)$],
        [$sqrt(x^2-a^2)$], [$x=a sec(theta)$], [$sec^2(theta)-1=tan^2(theta)$],
      )
    2. *Simplify and Integrate:* Substitute for $x$ and $"dx"$, then use the identity to eliminate the square root. Integrate the resulting trigonometric expression.
    3. *Convert Back to $x$ using a Reference Triangle:* Draw a right triangle based on the original substitution. For example, if $x=a tan(theta)$, then $tan(theta)=x/a$. Label the "opposite" side as $x$ and the "adjacent" side as $a$. The hypotenuse will be $sqrt(x^2+a^2)$. Use this triangle to find expressions for any remaining trig functions (like $sin(theta)$, $sec(theta)$) in terms of $x$.
    *Example:* $I = integral (sqrt(9-x^2))/x^2 "dx"$.
    1. *Substitute:* Form is $sqrt(a^2-x^2)$ with $a=3$. Let $x=3sin(theta)$, so $"dx"=3cos(theta)d(theta)$.
      $sqrt(9-x^2) = sqrt(9-9sin^2(theta)) = 3cos(theta)$.
    2. *Simplify & Integrate:*
      $I = integral (3cos(theta))/((3sin(theta))^2) (3cos(theta)d(theta)) = integral (9cos^2(theta))/(9sin^2(theta)) d(theta) = integral cot^2(theta) d(theta)$.
      Using the identity $cot^2(theta) = csc^2(theta)-1$:
      $I = integral (csc^2(theta)-1) d(theta) = -cot(theta) - theta + C$.
    3. *Convert Back:* From $x=3sin(theta)$, we have $sin(theta)=x/3$. The reference triangle has opposite=$x$, hypotenuse=3, and adjacent=$sqrt(9-x^2)$.
      So, $cot(theta) = ("adj")/("opp") = (sqrt(9-x^2))/x$, and $theta = arcsin(x/3)$.
      Final Answer: $I = -(sqrt(9-x^2))/x - arcsin(x/3) + C$.
  ])

  #concept-block(body: [
    #inline("Improper Integrals")
    - *Type 1 (Infinite Interval)*: $integral_a^oo f(x) "dx" = lim_(b->oo) integral_a^b f(x) "dx"$.
      - *p-Test*: $integral_1^oo 1/x^p "dx"$ converges if $p>1$.
    - *Type 2 (Unbounded Integrand)*: If $f$ is unbounded at $a$, $integral_a^b f(x) "dx" = lim_(c->a^+) integral_c^b f(x) "dx"$.
      - *p-Test at 0*: $integral_0^1 1/x^p "dx"$ converges if $p<1$.
    - *Comparison Test*: If $0 <= f(x) <= g(x)$ and $integral g(x) "dx"$ converges, then $integral f(x) "dx"$ converges.
  ])

  == Theoretical Connections in Calculus
  _This section explores the rigorous relationships between the core concepts of continuity, differentiability, and integrability. Understanding these implications and the counterexamples that define their boundaries is fundamental to analysis._

  #concept-block(body: [
    #inline("The Hierarchy of Function Classes on a Compact Interval $[a,b]$")
    These properties are related in a complex web of implications. The main chain is a strict, one-way hierarchy.

    *Differentiable* $arrow.r.long$ *Continuous* $arrow.r.long$ *Riemann Integrable* $arrow.r.long$ *Bounded*

    - *(D $=>$ C):* If a function is differentiable on $[a,b]$, it is continuous on $[a,b]$.
    - *(C $=>$ I):* If a function is continuous on $[a,b]$, it is Riemann integrable on $[a,b]$.
    - *(I $=>$ B):* A function must be bounded on $[a,b]$ to be Riemann integrable.

    #inline("The Role of Monotonicity")
    Monotonicity is a powerful condition that guarantees integrability, even without continuity.

    *Monotonic* $arrow.r.long$ *Riemann Integrable*

    - *(M $=>$ I):* If a function is monotonic (either non-increasing or non-decreasing) on $[a,b]$, it is Riemann integrable on $[a,b]$. A monotonic function on a compact interval is also necessarily bounded.

    #box(fill: luma(200), inset: 6pt, radius: 2pt)[
      #inline("Key Implications and Counterexamples")
      - *Continuous does NOT imply Monotonic:* $f(x) = sin(x)$ is continuous on $[0, 2pi]$ but not monotonic.
      - *Monotonic does NOT imply Continuous:* A step function, like $f(x) = cases(0, &"if " x < 1, 1, &"if " x >= 1)$, is monotonic on $[0,2]$ but not continuous at $x=1$.
      - *Monotonic does NOT imply Differentiable:* The same step function is not differentiable at the jump. Also, $f(x)=|x|$ is not monotonic on $[-1,1]$ but is composed of monotonic pieces.
      - *Differentiable does NOT imply Monotonic:* $f(x) = x^2$ is differentiable on $[-1,1]$ but not monotonic. (However, the *sign* of the derivative determines monotonicity on an interval).
      - *Bounded does NOT imply Integrable:* The Dirichlet function, $f(x) = cases(1, &"if " x in QQ, 0, &"if " x in.not QQ)$, is bounded on $[0,1]$ but not integrable.
    ]
  ])

  #concept-block(body: [
    #inline("Formal Definition of the Riemann Integral")
    Let $f$ be a bounded function on $[a,b]$. For any partition $P = {x_0, x_1, ..., x_n}$ of $[a,b]$:
    - Let $m_i = inf_(x in [x_(i-1), x_i]) f(x)$ and $M_i = sup_(x in [x_(i-1), x_i]) f(x)$.
    - The *Lower Sum* is $L(f,P) = sum_(i=1)^n m_i (x_i - x_(i-1))$.
    - The *Upper Sum* is $U(f,P) = sum_(i=1)^n M_i (x_i - x_(i-1))$.
    - The *Lower Integral* is $integral_a^(bar) b f(x) "dx" = sup_P L(f,P)$.
    - The *Upper Integral* is $integral_(bar a)^b f(x) "dx" = inf_P U(f,P)$.

    $f$ is *Riemann integrable* on $[a,b]$ if the lower and upper integrals are equal. Their common value is the Riemann integral $integral_a^b f(x) "dx"$.

    *Riemann's Criterion for Integrability:* A bounded function $f$ is integrable on $[a,b]$ if and only if for every $epsilon > 0$, there exists a partition $P$ such that $U(f,P) - L(f,P) < epsilon$.
  ])

  #concept-block(body: [
    #inline("Conditions for Riemann Integrability on $[a,b]$")
    A function $f$ is Riemann integrable on $[a,b]$ if and only if it is bounded and the set of its discontinuities has "measure zero" (a concept from higher analysis). For Analysis 1, we rely on the following sufficient conditions:
    - *Continuity:* If $f$ is continuous on $[a,b]$, it is integrable.
    - *Monotonicity:* If $f$ is monotonic (either non-increasing or non-decreasing) on $[a,b]$, it is integrable. (Note: A monotonic function can have many jump discontinuities).
    - *Finite Discontinuities:* If $f$ is bounded and has only a finite number of discontinuities on $[a,b]$, it is integrable.

    #inline("Integrability on Non-Compact Intervals")

    The standard Riemann integral is defined *only* on compact (closed and bounded) intervals $[a,b]$. To handle integration over non-compact intervals like $[a, oo)$ or $(a,b]$, we extend the concept using limits. This defines the *improper integral*. An improper integral *converges* if the corresponding limit exists and is finite; otherwise, it *diverges*.
  ])


  #concept-block(body: [
    #inline("The Substitution Rule: A Formal View")
    This rule is a powerful computational tool derived from the Chain Rule and the FTC.

    Let $g: [a,b] -> I$ be a *continuously differentiable* function ($g'$ exists and is continuous) and let $f: I -> RR$ be a *continuous* function. Then:
    $ integral_a^b f(g(x)) g'(x) "dx" = integral_(g(a))^(g(b)) f(u) "du" $
  ])

  #concept-block(body: [
    #inline("Key Theorems and Applications of Integration")

    *FTC Part 1 in Practice (Leibniz Integral Rule):*
    The FTC's power is extended with the chain rule for differentiating integrals with variable bounds.
    $ d/("dx") integral_(g(x))^(h(x)) f(t) "dt" = f(h(x))h'(x) - f(g(x))g'(x) $
    *Example:* Find the derivative of $F(x) = integral_(-2020)^(x^3) sin(pi t^2) "dt"$.
    Here, $g(x)=-2020$ (so $g'(x)=0$), $h(x)=x^3$ (so $h'(x)=3x^2$), and $f(t)=sin(pi t^2)$.
    $F'(x) = f(h(x))h'(x) - f(g(x))g'(x) = sin(pi(x^3)^2) dot.c (3x^2) - 0 = 3x^2 sin(pi x^6)$.

    *Mean Value Theorems for Integrals:*
    These theorems relate the value of an integral to the values of the function itself, generalizing the concepts of IVT and EVT to integrals.
    - *Standard MVT for Integrals:* If $f$ is continuous on $[a,b]$, there exists a $c in [a,b]$ such that:
      $ integral_a^b f(x) "dx" = f(c) (b-a) $
      This means the integral equals the area of a rectangle with height $f(c)$ (the average value of the function).
    - *Weighted MVT for Integrals:* If $f$ is continuous on $[a,b]$ and $g$ is an integrable function that does not change sign on $[a,b]$ (i.e., $g(x) >= 0$ or $g(x) <= 0$ for all $x$), then there exists a $c in [a,b]$ such that:
      $ integral_a^b f(x)g(x) "dx" = f(c) integral_a^b g(x) "dx" $
    *Example:* For a continuous $f: [0, ln 2] -> RR$, show $exists eta in [0, ln 2]$ with $f(eta) = 1/(e^2-e) integral_0^(ln 2) e^(e^x) f(x) "dx"$.
    Let the weight function be $g(x) = e^(e^x)$, which is positive. By the Weighted MVT, there exists an $eta$ such that:
    $ integral_0^(ln 2) f(x)e^(e^x) "dx" = f(eta) integral_0^(ln 2) e^(e^x) "dx" $
    The integral of the weight is $integral_0^(ln 2) e^(e^x) "dx" = [e^(e^x)]_0^(ln 2) = e^(e^(ln 2)) - e^(e^0) = e^2 - e$.
    Rearranging gives the desired result.

    *Symmetry in Integration (Even/Odd Functions):*
    Integrating over a symmetric interval $[-a, a]$ can be greatly simplified.
    - *Odd Function:* If $f$ is an odd function ($f(-x) = -f(x)$), then:
      $ integral_(-a)^a f(x) "dx" = 0 $
    - *Even Function:* If $f$ is an even function ($f(-x) = f(x)$), then:
      $ integral_(-a)^a f(x) "dx" = 2 integral_0^a f(x) "dx" $
  ])

  #concept-block(body: [
    #inline("Properties of Function Compositions")
    Let $f: A -> B$ and $g: B -> C$ be functions so the composition $g circle.small f: A -> C$ is well-defined. The properties of the composition depend critically on the properties of the individual functions.

    - *Continuity:*
      - *Rule:* The composition of continuous functions is continuous. If $f$ is continuous at a point $a in A$ and $g$ is continuous at the point $f(a) in B$, then the composition $g circle.small f$ is continuous at $a$.
      - *Implication:* This is a robust property. Continuity is well-preserved under composition. There are no common "trick" cases where composing two continuous functions results in a discontinuity.

    - *Differentiability:*
      - *Rule (Chain Rule):* The composition of differentiable functions is differentiable. If $f$ is differentiable at $a$ and $g$ is differentiable at $f(a)$, then $g circle.small f$ is differentiable at $a$, and its derivative is given by the chain rule:
        $ (g circle.small f)'(a) = g'(f(a)) f'(a) $
      - *Pitfall: Composition can be "smoother" than its parts.* A composition can be differentiable even if one of the constituent functions is not. The non-differentiable point of an "inner" function can be mapped by the "outer" function to a point where its own derivative is zero, effectively cancelling the problem.
      #box(fill: luma(240), inset: 6pt, radius: 2pt)[
        *Counterexample 1:* Let $f(x) = |x|$ (not diff. at 0) and $g(x) = x^2$ (diff. everywhere).
        The composition $h(x) = g(f(x)) = (|x|)^2 = x^2$. The function $h(x)=x^2$ is differentiable everywhere, including at $x=0$.
      ]

    - *Integrability (on a compact interval $[a,b]$):*
      - *Rule:* Integrable $circle.small$ Continuous $=>$ *Integrable*.
        If $g: [a,b] -> [c,d]$ is Riemann integrable and $f: [c,d] -> RR$ is *continuous*, then the composition $f circle.small g$ is Riemann integrable on $[a,b]$.
      - *Pitfall: The order matters!* The reverse is not true. Continuity of the inner function is not enough to guarantee integrability of the composition.
      #box(fill: luma(240), inset: 6pt, radius: 2pt)[
        *Counterexample (Level=Difficult):* Continuous $circle.small$ Integrable is *not* necessarily Integrable.
        Let $g$ be Thomae's function (integrable but discontinuous at every rational) and $f$ be a function that is 1 at non-zero values and 0 at zero (continuous everywhere except 0, but we can make it continuous). The composition $f circle.small g$ can result in the non-integrable Dirichlet function.
      ]
  ])

  #concept-block(body: [
    #inline("Interplay with Limits of Functions (Uniform Convergence)")
    How do these properties behave when we take the limit of a sequence of functions, $f_n -> f$?
    - *Continuity:* The pointwise limit of continuous functions need not be continuous. However, if the convergence is *uniform*, then the limit function $f$ of continuous functions $f_n$ is also *continuous*.
    - *Integration:* The limit of integrals may not equal the integral of the limit. However, if $f_n$ are integrable and converge *uniformly* to $f$ on $[a,b]$, we can swap the limit and the integral:
      $ lim_(n->oo) integral_a^b f_n (x) "dx" = integral_a^b (lim_(n->oo) f_n (x)) "dx" = integral_a^b f(x) "dx" $
    - *Differentiation:* This is the most restrictive case. Uniform convergence of $f_n -> f$ is not enough. We need the sequence of *derivatives* to converge uniformly. If $f_n$ are continuously differentiable, $f_n -> f$ pointwise, and $f_n' -> g$ *uniformly*, then $f$ is differentiable and $f' = g$.
  ])

  = Part V: Advanced Topics
  == Convexity
  A function $f: I -> RR$ is *convex* if for all $x,y in I$ and $lambda in [0,1]$:
  $f(lambda x + (1-lambda)y) <= lambda f(x) + (1-lambda)f(y)$
  It is *concave* if $-f$ is convex.

  #concept-block(body: [
    #inline("Tests for Convexity")
    - *Geometric:* The line segment connecting any two points on the graph lies above or on the graph.
    - *Derivatives:* If $f$ is differentiable, it's convex iff $f'$ is non-decreasing. If $f$ is twice differentiable, it's convex iff $f'' >= 0$.
    - *Jensen's Inequality:* For a convex function $f$,
      $f(sum_(i=1)^n lambda_i x_i) <= sum_(i=1)^n lambda_i f(x_i)$ for $sum lambda_i = 1$.
  ])

  == Gamma and Stirling's Formulas
  #concept-block(body: [
    #inline("Gamma Function")
    An extension of the factorial function. For $Re(s)>0$:
    $Gamma(s) = integral_0^oo x^(s-1) e^(-x) "dx"$
    - *Key Property:* $Gamma(s+1) = s Gamma(s)$.
    - *For integers n:* $Gamma(n) = (n-1)!$.
    - *Special Value:* $Gamma(1/2) = sqrt(pi)$.

    #inline("Stirling's Formula")
    An approximation for large factorials:
    $ n! approx sqrt(2 pi n) (n/e)^n $
    More precisely: $lim_(n->oo) (n!)/(sqrt(2 pi n) (n/e)^n) = 1$.
  ])

  == Partial Fraction Decomposition
  _This is a purely algebraic technique for rewriting a complex rational function $P(x)/Q(x)$ as a sum of simpler, easily integrable fractions. The structure of the sum is determined entirely by the factors of the denominator $Q(x)$._

  #concept-block(body: [
    #inline("Decomposition Rules based on Denominator Factors")

    *Case 1: Distinct Linear Factors*
    - For each factor $(a x+b)$, add a term: $A / (a x+b)$

    *Case 2: Repeated Linear Factors*
    - For each factor $(a x+b)^k$, add $k$ terms:
      $ A_1 / (a x+b) + A_2 / (a x+b)^2 + ... + A_k / (a x+b)^k $

    *Case 3: Distinct Irreducible Quadratic Factors*
    - For each factor $(a x^2+b x+c)$, add a term:
      $ (A x+B) / (a x^2+b x+c) $

    *Case 4: Repeated Irreducible Quadratic Factors*
    - For each factor $(a x^2+b x+c)^k$, add $k$ terms:
      $ (A_1x+B_1) / (a x^2+b x+c) + ... + (A_(k x)+B_k) / (a x^2+b x+c)^k $
  ])

  = Appendices
  _This section provides a comprehensive reference for key formulas, identities, and problem-solving strategies. It is designed for quick look-ups and to reinforce the algorithmic approaches to common analysis problems._

  === Appendix A: Common Limits

  #table(
    columns: (1fr, auto),
    align: (left, right),
    table.header([*Fundamental & Exponential*], [*Value*]),
    [$lim_(x -> oo) 1/x^a, quad (a > 0)$], [$0$],
    [$lim_(x -> 0^+) 1/x^a, quad (a > 0)$], [$+oo$],
    [$lim_(x -> oo) a^x, quad (a > 1)$], [$+oo$],
    [$lim_(x -> oo) a^x, quad (0 < a < 1)$], [$0$],
    [$lim_(x -> oo) ln(x)$], [$+oo$],
    [$lim_(x -> 0^+) ln(x)$], [$-oo$],
    [$lim_(x -> 0) x ln(x)$], [$0$],
    [$lim_(n -> oo) (1 + x/n)^n$], [$e^x$],
    [$lim_(n -> oo) root(n, n)$], [$1$],
    [$lim_(n -> oo) root(n, a), quad (a > 0)$], [$1$],
    [$lim_(x -> 0) sin(x)/x$], [$1$],
    [$lim_(x -> 0) (1-cos(x))/x$], [$0$],
    [$lim_(x -> 0) (1-cos(x))/x^2$], [$1/2$],
    [$lim_(x -> 0) (e^x-1)/x$], [$1$],
    [$lim_(x -> 0) (a^x-1)/x$], [$ln(a)$],
    [$lim_(x -> 0) (ln(1+x))/x$], [$1$],
    [$lim_(x -> oo) arctan(x)$], [$pi/2$],
    [$lim_(x -> -oo) arctan(x)$], [$-pi/2$],
    [$lim_(x -> oo) tanh(x)$], [$1$],
    [$lim_(x -> -oo) tanh(x)$], [$-1$],
  )

  === Appendix B: Common Series and Sums

  #table(
    columns: 3,
    table.header([*Series Type*], [*Series Notation*], [*Result / Condition*]),
    [Geometric], [$sum_(n=0)^oo a r^n$], [Converges to $a/(1-r)$ if $|r|<1$],
    [p-Series],
    [$sum_(n=1)^oo 1/n^p$],
    [Converges if $p>1$; Diverges if $p<=1$],

    [Finite Arithmetic], [$sum_(k=1)^n k$], [$n(n+1)/2$],
    [Finite Squares], [$sum_(k=1)^n k^2$], [$n(n+1)(2n+1)/6$],
    [Finite Cubes], [$sum_(k=1)^n k^3$], [$[n(n+1)/2]^2$],
    [Telescoping Ex.], [$sum_(n=1)^oo 1/(n(n+1))$], [$1$],
    [Basel Problem], [$sum_(n=1)^oo 1/n^2$], [$pi^2/6$],
  )

  #concept-block(body: [
    #inline("Key Taylor Series Expansions (around $x=0$)")
    - $ e^x = sum_(n=0)^oo x^n/(n!) = 1 + x + x^2/(2!) + ... $
    - $ sin(x) = sum_(n=0)^oo (-1)^n x^(2n+1)/((2n+1)!) = x - x^3/(3!) + ... $
    - $ cos(x) = sum_(n=0)^oo (-1)^n x^(2n)/((2n)!) = 1 - x^2/(2!) + ... $
    - $ sinh(x) = sum_(n=0)^oo x^(2n+1)/((2n+1)!) = x + x^3/(3!) + ... $
    - $ cosh(x) = sum_(n=0)^oo x^(2n)/((2n)!) = 1 + x^2/(2!) + ... $
    - $ 1/(1-x) = sum_(n=0)^oo x^n = 1 + x + x^2 + ... $ for $|x| < 1$.
    - $ ln(1+x) = sum_(n=1)^oo (-1)^(n-1) x^n/n = x - x^2/2 + ... $ for $x in (-1, 1]$.
    - $ (1+x)^alpha = 1 + alpha x + (alpha(alpha-1))/(2!) x^2 + ... $ for $|x| < 1$.
  ])

  === Appendix C: Table of Derivatives and Integrals
  #set table(
    columns: 3,
    align: (col, row) => if col > 0 { center } else { left },
  )

  #table(
    table.header(
      [*Function* $f(x)$],
      [*Derivative* $f'(x)$],
      [*Indefinite Integral* $integral f(x)"dx"$],
    ),
    [$x^n$],
    [$n x^(n-1)$],
    [$x^(n+1)/(n+1) + C$],
    [$e^(c x)$],
    [$c e^(c x)$],
    [$1/c e^(c x) + C$],
    [$a^x$],
    [$a^x ln(a)$],
    [$a^x/ln(a) + C$],
    [$ln|x|$],
    [$1/x$],
    [$x ln|x| - x + C$],
    // Trig
    [$sin(x)$],
    [$cos(x)$],
    [$-cos(x) + C$],
    [$cos(x)$],
    [$-sin(x)$],
    [$sin(x) + C$],
    [$tan(x)$],
    [$sec^2(x)$],
    [$-ln|cos(x)| + C$],
    [$cot(x)$],
    [$-csc^2(x)$],
    [$ln|sin(x)| + C$],
    [$sec(x)$],
    [$sec(x)tan(x)$],
    [$ln|sec(x)+tan(x)| + C$],
    [$csc(x)$],
    [$-csc(x)cot(x)$],
    [$-ln|csc(x)+cot(x)| + C$],
    // Hyperbolic
    [$sinh(x)$],
    [$cosh(x)$],
    [$cosh(x) + C$],
    [$cosh(x)$],
    [$sinh(x)$],
    [$sinh(x) + C$],
    [$tanh(x)$],
    [$sech^2(x)$],
    [$ln(cosh(x)) + C$],
    // Inverse Trig
    [$arcsin(x)$],
    [$1/sqrt(1-x^2)$],
    [$x arcsin(x) + sqrt(1-x^2) + C$],
    [$arccos(x)$],
    [$-1/sqrt(1-x^2)$],
    [$x arccos(x) - sqrt(1-x^2) + C$],
    [$arctan(x)$],
    [$1/(1+x^2)$],
    [$x arctan(x) - 1/2 ln(1+x^2) + C$],
    // Other
    [$x^x$],
    [$x^x(1+ln(x))$],
    [N/A],
    [$sin^2(x)$],
    [$sin(2x)$],
    [$1/2(x-sin(x)cos(x)) + C$],
    [$cos^2(x)$],
    [$-sin(2x)$],
    [$1/2(x+sin(x)cos(x)) + C$],
  )

  === Appendix D: Trigonometric & Hyperbolic Identities

  #concept-block(body: [
    #inline("Trigonometric Identities")
    - *Definitions:*
      - $sec(x) = 1/cos(x)$, $csc(x) = 1/sin(x)$, $cot(x) = 1/tan(x)$
      - $cos(x) = (e^(i x)+e^(-i x))/2$, $sin(x) = (e^(i x)-e^(-i x))/(2i)$
    - *Pythagorean:*
      - $sin^2(x) + cos^2(x) = 1$
      - $tan^2(x) + 1 = sec^2(x)$
      - $1 + cot^2(x) = csc^2(x)$
    - *Parity:* $sin(-x)=-sin(x)$, $cos(-x)=cos(x)$, $tan(-x)=-tan(x)$
    - *Angle Sum:*
      - $sin(a+-b) = sin(a)cos(b) +- cos(a)sin(b)$
      - $cos(a+-b) = cos(a)cos(b) -+ sin(a)sin(b)$
    - *Double Angle:*
      - $sin(2x) = 2sin(x)cos(x)$
      - $cos(2x) = cos^2(x)-sin^2(x) = 2cos^2(x)-1 = 1-2sin^2(x)$
    - *Power Reduction:*
      - $sin^2(x) = 1/2(1-cos(2x))$
      - $cos^2(x) = 1/2(1+cos(2x))$
    - *Product-to-Sum:*
      - $sin(a)sin(b) = 1/2(cos(a-b)-cos(a+b))$
      - $cos(a)cos(b) = 1/2(cos(a-b)+cos(a+b))$
    - *Sum-to-Product:*
      - $sin(x)+-sin(y) = 2sin((x+-y)/2)cos((x-+y)/2)$
      - $cos(x)+cos(y) = 2cos((x+y)/2)cos((x-y)/2)$
      - $cos(x)-cos(y) = -2sin((x+y)/2)sin((x-y)/2)$

    #inline("Hyperbolic Identities")
    - *Definitions:*
      - $sech(x) = 1/cosh(x)$, $csch(x) = 1/sinh(x)$, $coth(x) = 1/tanh(x)$
      - $cosh(x) = (e^x+e^(-x))/2$, $sinh(x) = (e^x-e^(-x))/2$
    - *Identity:*
      - $cosh^2(x) - sinh^2(x) = 1$
      - $1 - tanh^2(x) = sech^2(x)$
      - $coth^2(x) - 1 = csch^2(x)$
    - *Parity:* $sinh(-x)=-sinh(x)$, $cosh(-x)=cosh(x)$
    - *Angle Sum:*
      - $sinh(a+-b) = sinh(a)cosh(b)+-cosh(a)sinh(b)$
      - $cosh(a+-b) = cosh(a)cosh(b)+-sinh(a)sinh(b)$
    - *Double Angle:*
      - $sinh(2x) = 2sinh(x)cosh(x)$
      - $cosh(2x) = cosh^2(x)+sinh^2(x)$
    - *Osborn's Rule:* To convert a trig identity involving powers of sin/cos to a hyperbolic one, replace every $sin$ with $sinh$ and every $cos$ with $cosh$, but flip the sign of any term containing a product of two sines (e.g., $sin^2(x)$, $sin(a)sin(b)$).
  ])

  #concept-block(body: [
    #inline("Reference Values for Trigonometric and Hyperbolic Functions")


    #set table(align: center)
    #table(
      columns: 6,
      table.header(
        [*Degrees*],
        [*Radians*],
        [*$sin(x)$*],
        [*$cos(x)$*],
        [*$tan(x)$*],
        [*$cot(x)$*],
      ),
      // Quadrant I
      [$0°$], [$0$], [$0$], [$1$], [$0$], [undef],
      [$30°$], [$pi/6$], [$1/2$], [$sqrt(3)/2$], [$1/sqrt(3)$], [$sqrt(3)$],
      [$45°$], [$pi/4$], [$sqrt(2)/2$], [$sqrt(2)/2$], [$1$], [$1$],
      [$60°$], [$pi/3$], [$sqrt(3)/2$], [$1/2$], [$sqrt(3)$], [$1/sqrt(3)$],
      [$90°$], [$pi/2$], [$1$], [$0$], [undef], [$0$],
      // Quadrant II
      [$120°$],
      [$2pi/3$],
      [$sqrt(3)/2$],
      [$-1/2$],
      [$-sqrt(3)$],
      [$-1/sqrt(3)$],

      [$135°$], [$3pi/4$], [$sqrt(2)/2$], [$-sqrt(2)/2$], [$-1$], [$-1$],
      [$150°$],
      [$5pi/6$],
      [$1/2$],
      [$-sqrt(3)/2$],
      [$-1/sqrt(3)$],
      [$-sqrt(3)$],

      [$180°$], [$pi$], [$0$], [$-1$], [$0$], [undef],
      // Quadrant III
      [$210°$], [$7pi/6$], [$-1/2$], [$-sqrt(3)/2$], [$1/sqrt(3)$], [$sqrt(3)$],
      [$225°$], [$5pi/4$], [$-sqrt(2)/2$], [$-sqrt(2)/2$], [$1$], [$1$],
      [$240°$], [$4pi/3$], [$-sqrt(3)/2$], [$-1/2$], [$sqrt(3)$], [$1/sqrt(3)$],
      [$270°$], [$3pi/2$], [$-1$], [$0$], [undef], [$0$],
      // Quadrant IV
      [$300°$],
      [$5pi/3$],
      [$-sqrt(3)/2$],
      [$1/2$],
      [$-sqrt(3)$],
      [$-1/sqrt(3)$],

      [$315°$], [$7pi/4$], [$-sqrt(2)/2$], [$sqrt(2)/2$], [$-1$], [$-1$],
      [$330°$],
      [$11pi/6$],
      [$-1/2$],
      [$sqrt(3)/2$],
      [$-1/sqrt(3)$],
      [$-sqrt(3)$],

      [$360°$], [$2pi$], [$0$], [$1$], [$0$], [undef],
    )
    // Hyperbolic Trig Table
    #set table(align: center)
    #table(
      columns: 4,
      table.header([*$x$*], [*$sinh(x)$*], [*$cosh(x)$*], [*$tanh(x)$*]),
      [$0$], [$0$], [$1$], [$0$],
      [$-ln(phi)$], [$-1/sqrt(5)$], [$phi/sqrt(5)$], [$-1/phi$],
      [$ln(phi)$], [$1/sqrt(5)$], [$phi/sqrt(5)$], [$1/phi$],
      [$ln(2)$], [$3/4$], [$5/4$], [$3/5$],
      [$ln(3)$], [$4/3$], [$5/3$], [$4/5$],
    )
    where $phi = (1+sqrt(5))/2$ is the golden ratio.
    )
  ])

  === Appendix E: Function Properties and Transformations

  #concept-block(body: [
    #inline("Even and Odd Functions")
    - *Even:* $f(-x) = f(x)$. Symmetric about the y-axis.
    - *Odd:* $f(-x) = -f(x)$. Symmetric about the origin.
    #inline("Properties")
    - *Sum:* even + even = even, odd + odd = odd.
    - *Product:* even x even = even, odd x odd = even, even x odd = odd.
    - *Quotient:* Same rules as product.
    - *Composition:* $g circle.small f$ is even if $f$ is even. $g circle.small f$ is odd if $f$ is odd and $g$ is odd.
    - *Derivative:* The derivative of an even function is odd. The derivative of an odd function is even.
    - *Integral:* $integral_(-a)^a f(x) "dx" = 0$ if $f$ is odd. $integral_(-a)^a f(x) "dx" = 2 integral_0^a f(x) "dx"$ if $f$ is even.

    #inline("Inverse Functions")
    - *Existence:* A function $f$ has an inverse $f^(-1)$ if and only if it is bijective (one-to-one and onto). A continuous function on an interval has an inverse if and only if it is strictly monotonic.
    - *Graphs:* The graph of $f^(-1)$ is the reflection of the graph of $f$ across the line $y=x$.
    - *Derivative of an Inverse:* If $f$ is differentiable at $a$ with $f'(a) != 0$, and $f^(-1)$ is continuous at $b=f(a)$, then $f^(-1)$ is differentiable at $b$ and:
      $ (f^(-1))'(b) = 1/(f'(a)) = 1/(f'(f^(-1)(b))) $
    #inline("Logarithm as Inverse")
    - $ln(x)$ is the inverse of $e^x$.
    - $log_a (x)$ is the inverse of $a^x$.
    - *Change of Base:* $log_a (x) = ln(x)/ln(a)$.
    - *Logarithmic Power Rule:* $a^(log_b (c)) = c^(log_b (a))$.
  ])

  = Examples
  == Selected Problems and Solutions
  _This section contains worked solutions to illustrative problems that highlight key concepts and techniques from the course._

  #concept-block(body: [
    #inline("Problem 1: Convergence of Sequences")
    *Statement:* If $(a_n - a_(n+1))_n$ is a null sequence (converges to 0), is $(a_n)_n$ convergent?

    *Answer:* False.

    *Reasoning (Counterexample):* Let $a_n$ be the sequence of partial sums of the harmonic series, $a_n = sum_(k=1)^n 1/k$.
    - The difference is $a_n - a_(n+1) = (sum_(k=1)^n 1/k) - (sum_(k=1)^(n+1) 1/k) = -1/(n+1)$.
    - The sequence of differences, $(-1/(n+1))_n$, is a null sequence as $lim_(n->oo) -1/(n+1) = 0$.
    - However, the sequence $(a_n)_n$ itself is the harmonic series, which is known to be divergent.
  ])

  #concept-block(body: [
    #inline("Problem 2: Convergence of Series")
    *Statement:* If $sum_(n=1)^oo a_n$ is convergent, is $sum_(n=1)^oo (a_n)^2$ also convergent?

    *Answer:* False.

    *Reasoning (Counterexample):* Consider the alternating harmonic series. Let $a_n = (-1)^n/sqrt(n)$.
    - The series $sum_(n=1)^oo a_n = sum_(n=1)^oo (-1)^n/sqrt(n)$ is convergent by the Leibniz (Alternating Series) Test, since $1/sqrt(n)$ is positive, decreasing, and tends to 0.
    - However, the series of squares is $sum_(n=1)^oo (a_n)^2 = sum_(n=1)^oo ((-1)^n/sqrt(n))^2 = sum_(n=1)^oo 1/n$.
    - This is the harmonic series, which is divergent.
  ])

  #concept-block(body: [
    #inline("Problem 3: Power Series Identification")
    *Statement:* The power series $S(x) = sum_(k=2)^oo k(k-1)x^k$ for $|x|<1$ corresponds to which function?

    *Answer:* $2x^2 / (1-x)^3$.

    *Reasoning (Term-by-Term Differentiation):* Start with the geometric series formula, which is fundamental for manipulating power series.
    1. *Base Series:* $sum_(k=0)^oo x^k = 1/(1-x)$.
    2. *First Derivative:* Differentiate both sides with respect to $x$.
      $d/("dx") sum_(k=0)^oo x^k = sum_(k=1)^oo k x^(k-1) = d/("dx") (1/(1-x)) = 1/(1-x)^2$.
    3. *Second Derivative:* Differentiate again.
      $d/("dx") sum_(k=1)^oo k x^(k-1) = sum_(k=2)^oo k(k-1)x^(k-2) = d/("dx") (1/(1-x)^2) = 2/(1-x)^3$.
    4. *Adjust for the Target Series:* The series we found is $sum_(k=2)^oo k(k-1)x^(k-2)$. To get our target series, $S(x)$, we just need to multiply by $x^2$.
      $S(x) = x^2 sum_(k=2)^oo k(k-1)x^(k-2) = x^2 (2/(1-x)^3) = (2x^2)/(1-x)^3$.
  ])

  #concept-block(body: [
    #inline("Problem 4: Mean Value Theorem Application")
    *Statement:* Show that for a continuously differentiable function $f: [0,1] -> RR$, there exists a $c in [0,1]$ such that $f'(c) = pi/4 (1 + f(c)^2)$.
    *Hint:* Use the Mean Value Theorem.
    *Reasoning (Constructing an Auxiliary Function):* The structure of the equation suggests the derivative of an inverse trigonometric function.
    1. *Identify the Structure:* The expression $f'(c)/(1+f(c)^2)$ is reminiscent of the derivative of $arctan(y)$.
    2. *Define an Auxiliary Function:* Let's define a new function $g(x) = arctan(f(x))$. Since $f$ is differentiable and $arctan$ is differentiable, $g$ is also differentiable on $[0,1]$.
    3. *Apply the Mean Value Theorem to $g(x)$:* By the MVT, there exists a $c in (0,1)$ such that:
      $g'(c) = (g(1) - g(0))/(1-0) = arctan(f(1)) - arctan(f(0))$.
    4. *Calculate $g'(c)$ using the Chain Rule:*
      $g'(x) = d/("dx") arctan(f(x)) = 1/(1+f(x)^2) dot.c f'(x)$.
      So, $g'(c) = (f'(c))/(1+f(c)^2)$.
    5. *Equate and Solve:*
      $(f'(c))/(1+f(c)^2) = arctan(f(1)) - arctan(f(0))$.
      Let's assume for the specific problem context that $arctan(f(1)) - arctan(f(0)) = pi/4$. (This value would typically be given or derived from conditions on $f(0)$ and $f(1)$, e.g., if $f(0)=0$ and $f(1)=1$).
      Then, $(f'(c))/(1+f(c)^2) = pi/4$.
      Rearranging gives the desired result: $f'(c) = pi/4 (1+f(c)^2)$.
  ])

  #concept-block(body: [
    #inline("Problem 5: Weighted Mean Value Theorem for Integrals")
    *Statement:* Let $F, G: [a,b] -> RR$ be integrable functions, with $G$ continuous and $F(x) > 0$ for all $x in [a,b]$. Show there exists a $c in [a,b]$ such that:
    $ integral_a^b F(x)G(x) "dx" = G(c) integral_a^b F(x) "dx" $
    *Reasoning (Bounding and IVT):* The strategy is to show that the "weighted average" of $G$ is a value that lies between its minimum and maximum, then apply the Intermediate Value Theorem.
    1. *Bound G(x):* Since $G$ is continuous on a compact interval, it attains its minimum $m$ and maximum $M$. Thus, for all $x in [a,b]$:
      $ m <= G(x) <= M $
    2. *Introduce Weight F(x):* Multiply the inequality by $F(x)$. Since $F(x) > 0$, the inequalities are preserved:
      $ m F(x) <= G(x)F(x) <= M F(x) $
    3. *Integrate:* By the monotonicity of integrals, integrate across the inequality from $a$ to $b$:
      $ integral_a^b m F(x) "dx" <= integral_a^b G(x)F(x) "dx" <= integral_a^b M F(x) "dx" $
      Since $m$ and $M$ are constants, they can be pulled out:
      $ m integral_a^b F(x) "dx" <= integral_a^b G(x)F(x) "dx" <= M integral_a^b F(x) "dx" $
    4. *Isolate the Average Value:* The term $I_F = integral_a^b F(x) "dx"$ is positive because $F(x)>0$. We can divide the entire inequality by $I_F$:
      $ m <= (integral_a^b G(x)F(x) "dx") / (integral_a^b F(x) "dx") <= M $
    5. *Apply IVT:* The expression in the middle is a number that lies between the minimum ($m$) and maximum ($M$) of the continuous function $G$. By the Intermediate Value Theorem, there must exist some $c in [a,b]$ where $G$ takes on this value:
      $ G(c) = (integral_a^b G(x)F(x) "dx") / (integral_a^b F(x) "dx") $
    6. *Conclusion:* Rearranging this equation gives the desired result.
  ])
  #concept-block(body: [
    #inline("Problem 6: Squeeze Theorem Application")
    *Statement:* If it exists, calculate the following limit:
    $ lim_(x->0) x^4 sin(1/x) $
    *Reasoning (Bounding and Squeezing):* The $sin(1/x)$ term oscillates infinitely as $x -> 0$, so we cannot simply substitute $x=0$. However, the sine function is bounded, which is the key insight for applying the Squeeze Theorem.
    1. *Establish Bounds:* The sine function is always bounded between -1 and 1, regardless of its argument.
      $ -1 <= sin(1/x) <= 1 $
    2. *Multiply by the Dominant Term:* Multiply the entire inequality by $x^4$. Since $x^4 >= 0$ for all $x$, the inequality signs are preserved.
      $ -x^4 <= x^4 sin(1/x) <= x^4 $
    3. *Apply the Squeeze Theorem:* We now have our function "squeezed" between two simpler functions, $-x^4$ and $x^4$. We take the limit of the outer functions as $x -> 0$.
      - $lim_(x->0) (-x^4) = 0$
      - $lim_(x->0) (x^4) = 0$
    4. *Conclusion:* Since the function $x^4 sin(1/x)$ is squeezed between two functions that both approach 0, it must also approach 0.
      $ lim_(x->0) x^4 sin(1/x) = 0 $
  ])

  #concept-block(body: [
    #inline("Problem 7: FTC, Inverse Functions, and Taylor Polynomials")
    *Statement:* Let $f: (0, oo) -> RR$ be defined by $f(x) = integral_x^2 e^(t^2)/t "dt" + log(x/2)$.
    - (a) Calculate the derivative of $f$ and show that $f$ is invertible.
    - (b) Calculate $f(2)$ and determine the Taylor polynomial of order 1 for the *inverse function* $f^(-1)$ at the point $x_0=0$.

    #inline("Part (a): Derivative and Invertibility")
    *Reasoning:* We use the FTC to differentiate the integral term and standard rules for the logarithm. A function is invertible if it is strictly monotonic, which can be shown by checking if its derivative is always positive or always negative.
    1. *Differentiate the Integral:* The variable $x$ is in the lower bound. We must first flip the integral bounds, which negates the expression.
      $d/("dx") integral_x^2 e^(t^2)/t "dt" = d/("dx") (-integral_2^x e^(t^2)/t "dt")$
      By FTC Part 1, this derivative is $-e^(x^2)/x$.
    2. *Differentiate the Logarithm:* Using the chain rule (or log properties):
      $d/("dx") log(x/2) = 1/(x/2) dot.c (1/2) = 1/x$.
    3. *Combine Derivatives:*
      $f'(x) = -e^(x^2)/x + 1/x = (1-e^(x^2))/x$.
    4. *Check for Monotonicity:* The domain is $(0,oo)$, so the denominator $x$ is always positive. For the numerator, since $x>0$, we have $x^2>0$, which implies $e^(x^2) > e^0 = 1$. Therefore, the numerator $1-e^(x^2)$ is always negative.
    5. *Conclusion:* Since $f'(x) = ("negative")/("positive")$, we have $f'(x) < 0$ for all $x$ in the domain. This means $f$ is strictly decreasing and therefore invertible.

    #inline("Part (b): Taylor Polynomial of the Inverse")
    *Reasoning:* The first-order Taylor polynomial for a function $g$ at a point $y_0$ is $P_1(y) = g(y_0) + g'(y_0)(y-y_0)$. Here, $g=f^(-1)$ and $y_0=0$. We need to find $f^(-1)(0)$ and $(f^(-1))'(0)$.
    1. *Find $f^(-1)(0)$:* This requires finding the value $x$ such that $f(x)=0$. We test the integral bound $x=2$:
      $f(2) = integral_2^2 e^(t^2)/t "dt" + log(2/2) = 0 + log(1) = 0$.
      Since $f(2)=0$, by definition of the inverse, $f^(-1)(0) = 2$.
    2. *Find $(f^(-1))'(0)$:* We use the formula for the derivative of an inverse function:
      $(f^(-1))'(y_0) = 1/(f'(f^(-1)(y_0)))$.
      Substituting $y_0=0$ and using our result from the previous step:
      $(f^(-1))'(0) = 1/(f'(f^(-1)(0))) = 1/(f'(2))$.
    3. *Calculate $f'(2)$:* Using the derivative from part (a):
      $f'(2) = (1-e^(2^2))/2 = (1-e^4)/2$.
    4. *Compute the Inverse Derivative:*
      $(f^(-1))'(0) = 1/((1-e^4)/2) = 2/(1-e^4)$.
    5. *Assemble the Taylor Polynomial:* The polynomial for $f^(-1)$ at $x_0=0$ is:
      $P_1(x) = f^(-1)(0) + (f^(-1))'(0) (x-0)$
      $P_1(x) = 2 + (2/(1-e^4)) x$.
  ])

  #concept-block(body: [
    #inline("Problem 8: Partial Fraction Decomposition")
    *Statement:* Decompose $f(x) = (2x)/((x-2)^2(x+2))$.

    *Reasoning:* The denominator has a distinct linear factor $(x+2)$ and a repeated linear factor $(x-2)^2$. The setup must include a term for each power of the repeated factor.
    1. *Setup:*
      $ (2x)/((x-2)^2(x+2)) = A/(x-2) + B/((x-2)^2) + C/(x+2) $
    2. *Clear Denominators:* Multiply by $(x-2)^2(x+2)$:
      $ 2x = A(x-2)(x+2) + B(x+2) + C(x-2)^2 $
    3. *Solve using Strategic Substitution (Heaviside Method):*
      - Let $x=2$: $2(2) = B(2+2) => 4 = 4B => B=1$.
      - Let $x=-2$: $2(-2) = C(-2-2)^2 => -4 = 16C => C=-1/4$.
      - Let $x=0$ (using known $B, C$): $0 = A(-2)(2) + 1(2) + (-1/4)(-2)^2 => 0 = -4A + 2 - 1 => A=1/4$.
    *Final Decomposition:*
    $ (1/4)/(x-2) + 1/((x-2)^2) - (1/4)/(x+2) $
  ])

  #concept-block(body: [
    #inline("Problem 9: Double Substitution in an Improper Integral")
    *Statement:* Calculate the improper integral $I = integral_2^oo 1/(sqrt(e^x - e^2)) "dx"$.

    *Reasoning:* This integral is improper at both ends ($x->oo$ and the denominator is zero at $x=2$). The expression requires two sequential substitutions to solve.

    *1. First Substitution (to eliminate the exponential and root):*
    - Let $t = sqrt(e^x - e^2)$. This choice simplifies the denominator directly.
    - To find $"dx"$, we first solve for $x$: $t^2 = e^x - e^2 => e^x = t^2 + e^2 => x = ln(t^2+e^2)$.
    - Differentiate to find $"dx"$: $"dx" = (2t)/(t^2+e^2) "dt"$.
    - Change the integration bounds:
      - As $x -> 2^+$, $t -> sqrt(e^2-e^2) = 0^+$.
      - As $x -> oo$, $t -> sqrt(oo - e^2) = oo$.
    - Substitute into the integral:
      $ I = integral_0^oo 1/t dot.c (2t)/(t^2+e^2) "dt" = integral_0^oo 2/(t^2+e^2) "dt" $

    *2. Second Substitution (to match the arctan form):*
    - The integral now resembles the form for $arctan$. We want the denominator to be $u^2+1$.
    - Factor out $e^2$: $I = integral_0^oo 2/(e^2((t/e)^2+1)) "dt" = 2/e^2 integral_0^oo 1/((t/e)^2+1) "dt"$.
    - Let $u = t/e$. Then $"du" = 1/e "dt"$, so $"dt" = e "du"$.
    - Change the integration bounds:
      - As $t -> 0^+$, $u -> 0^+$.
      - As $t -> oo$, $u -> oo$.
    - Substitute into the integral:
      $ I = 2/e^2 integral_0^oo 1/(u^2+1) (e "du") = 2/e integral_0^oo 1/(u^2+1) "du" $

    *3. Final Integration and Evaluation:*
    - The integral is now a standard form:
      $ I = 2/e [arctan(u)]_0^oo $
    - Evaluate at the bounds:
      $ I = 2/e (lim_(u->oo) arctan(u) - arctan(0)) = 2/e (pi/2 - 0) $
    *Final Answer:* $I = pi/e$.
  ])

  #concept-block(body: [
    #inline("Problem 10: Taylor's Theorem with Even Functions")
    *Statement:* Let $f$ be an even, continuous, and twice-differentiable function on $[-1,1]$. Is it true that for all $x in [0,1]$, there exists an $eta in [0,x]$ such that $f(x) - f(0) = (f''(eta)x^2)/2$?

    *Answer:* True.

    *Reasoning (Applying Taylor's Theorem and Symmetry):*
    1. *Apply Taylor's Theorem:* For a twice-differentiable function, Taylor's Theorem with $n=1$ expanded around $a=0$ states that for any $x$, there exists an $eta$ between $0$ and $x$ such that:
      $ f(x) = f(0) + f'(0)x + (f''(eta))/(2!) x^2 $
    2. *Use the Even Function Property:* We are given that $f$ is an even function ($f(-x)=f(x)$). A key property is that the derivative of an even function is an odd function. Therefore, $f'(x)$ is odd.
    3. *Evaluate $f'(0)$:* For any odd function $g(x)$, we have $g(-x) = -g(x)$. If an odd function is defined at $x=0$, we must have $g(0) = -g(0)$, which implies $2g(0)=0$, so $g(0)=0$.
      Since $f'(x)$ is odd and differentiable (and thus defined) at $x=0$, we must have $f'(0)=0$.
    4. *Simplify the Taylor Expansion:* Substitute $f'(0)=0$ into the Taylor expansion from Step 1:
      $ f(x) = f(0) + (0)x + (f''(eta))/2 x^2 $
      $ f(x) = f(0) + (f''(eta)x^2)/2 $
    5. *Conclusion:* Rearranging the equation gives the desired result:
      $ f(x) - f(0) = (f''(eta)x^2)/2 $
  ])

  #concept-block(body: [
    #inline("Problem 11: Integration using Symmetry")
    *Statement:* Calculate the definite integral $I = integral_(-pi/2)^(pi/2) sin^7(x)cos(x) "dx"$.

    *Reasoning (Checking for an Odd Function):* Before attempting a complex substitution, it's crucial to check for symmetry, especially when integrating over an interval of the form $[-a, a]$. If the integrand is an odd function, the integral is zero.
    1. *Define the Integrand:* Let $f(x) = sin^7(x)cos(x)$.
    2. *Test for Odd/Even Property:* We evaluate $f(-x)$ using the parity of sine (odd) and cosine (even).
      - $sin(-x) = -sin(x)$
      - $cos(-x) = cos(x)$
      Substituting these into our function:
      $ f(-x) = (sin(-x))^7 cos(-x) = (-sin(x))^7 (cos(x)) $
      $ f(-x) = -sin^7(x)cos(x) = -f(x) $
    3. *Apply the Theorem:* Since $f(-x) = -f(x)$, the function is odd. The integral of any odd function over a symmetric interval $[-a, a]$ is always zero.

    *Conclusion:* The integral is 0.

  ])

  #concept-block(body: [
    #inline("Problem 12: Convergence of a Recursive Sequence")
    *Statement:* Let a sequence be defined by $a_1 = -ln(2)$ and $a_(k+1) = e^(a_k) - 1$ for $k >= 1$. Determine if the sequence converges, and if so, find its limit.

    *Reasoning (Monotone Convergence Theorem):* The strategy is to show the sequence is both monotonic and bounded, which guarantees convergence. The limit is then found by solving the fixed-point equation.
    1. *Boundedness (Show $a_k < 0$):* We prove by induction that the sequence is bounded above by 0.
      - *Base Case:* $a_1 = -ln(2) < 0$. The statement holds for $k=1$.
      - *Inductive Step:* Assume $a_k < 0$ for some $k$. Since the exponential function is strictly increasing, $e^(a_k) < e^0 = 1$.
      - Therefore, $a_(k+1) = e^(a_k) - 1 < 1 - 1 = 0$.
      - By induction, the sequence is bounded above by 0.
    2. *Monotonicity (Show $a_(k+1) >= a_k$):* We use the fundamental inequality $1+x <= e^x$, which holds for all real $x$.
      - Let $x = a_k$. The inequality gives $1 + a_k <= e^(a_k)$.
      - Rearranging this gives $a_k <= e^(a_k) - 1$.
      - By the definition of our sequence, this is exactly $a_k <= a_(k+1)$.
      - Thus, the sequence is monotonically increasing.
    3. *Convergence and Finding the Limit:*
      - Since the sequence is monotonically increasing and bounded above, it must converge to a limit $L$ by the Monotone Convergence Theorem.
      - This limit $L$ must be a fixed point of the recurrence relation. We find it by taking the limit of both sides:
        $ lim_(k->oo) a_(k+1) = lim_(k->oo) (e^(a_k) - 1) $
        $ L = e^L - 1 $
      - By inspection, $L=0$ is a solution since $e^0 - 1 = 1 - 1 = 0$. The inequality $1+x <= e^x$ becomes an equality only at $x=0$, confirming this is the unique solution.

    *Conclusion:* The sequence converges to the limit $L=0$.
  ])

  #concept-block(body: [
    #inline("Problem 13: Composition of Convex Functions")
    *Statement:* If $f$ and $g$ are strongly convex functions, is the composition $h(x) = g(f(x))$ also convex?

    *Answer:* False.

    *Reasoning (Counterexample and Analysis):* While it seems intuitive, the composition is not guaranteed to be convex. Convexity of $h(x)$ requires $h''(x) >= 0$.
    1. *Second Derivative of a Composition:* The formula is:
      $ h''(x) = g''(f(x)) [f'(x)]^2 + g'(f(x)) f''(x) $
    2. *Analysis of Terms:*
      - Since $f$ and $g$ are convex, we know $f''(x) > 0$ and $g''(f(x)) > 0$.
      - This means the first term, $g''(f(x)) [f'(x)]^2$, is always non-negative.
      - However, the second term, $g'(f(x)) f''(x)$, can be negative if $g'(f(x)) < 0$. This happens if the outer function $g$ is decreasing at the point $f(x)$. If this negative term is large enough, it can make $h''(x)$ negative.

    *Conclusion:* Since the second derivative can be negative, the composition of two convex functions is not necessarily convex. An additional condition, such as the outer function $g$ also being non-decreasing, is required to guarantee convexity.
  ])

  #concept-block(body: [
    #inline("Problem 14: Limits and Riemann Sums")
    *Statement:* Calculate the limit $lim_(n->oo) b_n$ where $b_n = 1/n sum_(k=0)^n 1/(1+k/n)$.

    *Reasoning (Identifying a Riemann Sum):* The expression has the characteristic structure of a Riemann sum, which can be evaluated as a definite integral.
    1. *Recall the Riemann Sum Definition:* The definite integral of a function $f(x)$ from $a$ to $b$ is the limit of its Riemann sums:
      $ integral_a^b f(x) "dx" = lim_(n->oo) sum_(k=1)^n f(x_k) Delta x $
      For a simple partition of $[a,b]$ into $n$ equal subintervals, $Delta x = (b-a)/n$ and the right-hand endpoints are $x_k = a + k Delta x$.
    2. *Match the Expression:* Let's match our sequence $b_n$ to this form.
      - The interval appears to be $[0,1]$, so $a=0, b=1$, and $Delta x = 1/n$.
      - The sample points are $x_k = 0 + k(1/n) = k/n$.
      - The function being evaluated is $f(x_k) = 1/(1+x_k) = 1/(1+k/n)$.
    3. *Formulate the Integral:* The expression $b_n = sum_(k=0)^n 1/(1+k/n) * (1/n)$ is almost a perfect Riemann sum for $f(x) = 1/(1+x)$ on $[0,1]$. The sum starting from $k=0$ instead of $k=1$ is a minor difference that vanishes in the limit.
    4. *Evaluate the Integral:*
      $ lim_(n->oo) b_n = integral_0^1 1/(1+x) "dx" $
      The antiderivative of $1/(1+x)$ is $ln|1+x|$.
      $ integral_0^1 1/(1+x) "dx" = [ln(1+x)]_0^1 \ = ln(1+1) - ln(1+0) = ln(2) - ln(1) = ln(2) $

    *Conclusion:* The limit is $ln(2)$.
  ])

  #concept-block(body: [
    #inline("Problem 15: Upper and Lower Integrals")
    *Statement:* For $f(x) = cases(x, &"if " x in QQ, 1-x, &"if " x in.not QQ)$ on $[0,1]$, find the lower integral $s(f)$ and upper integral $S(f)$.

    *Reasoning (Visualizing Bounding Functions):* The function $f(x)$ constantly jumps between the lines $y=x$ and $y=1-x$. Due to the density of rational and irrational numbers, in any subinterval, the function will take values arbitrarily close to both lines.

    1. *Lower Integral $s(f)$:* The infimum (greatest lower bound) of $f(x)$ on any subinterval will be determined by the lower of the two lines. This creates a "bounding function from below," which is simply $y = min{x, 1-x}$. The lower integral is the area under this bounding function.
      - Visually, this forms a triangle with vertices at (0,0), (1,0), and (1/2, 1/2).
      - $s(f) = integral_0^1 min{x, 1-x} "dx" = "Area" = 1/2 "base" dot.c "height" = 1/2(1)(1/2) = 1/4$.

    2. *Upper Integral $S(f)$:* Similarly, the supremum (least upper bound) of $f(x)$ on any subinterval is determined by the upper of the two lines, creating a "bounding function from above," $y = max{x, 1-x}$. The upper integral is the area under this function.
      - Visually, this forms two triangles, one with vertices (0,0), (0,1), (1/2, 1/2) and another with (1,0), (1,1), (1/2, 1/2). The total area is the area of the unit square minus the area of the lower triangle.
      - $S(f) = integral_0^1 max{x, 1-x} "dx" = "Area" = 1 - s(f) = 1 - 1/4 = 3/4$.

    *Conclusion:* The lower integral is $s(f)=1/4$ and the upper integral is $S(f)=3/4$. Since they are not equal, the function is not Riemann integrable.
  ])

  #concept-block(body: [
    #inline("Problem 16: Properties of Inverse Functions")
    *Statement:* Let $f: RR -> RR$ be bijective and differentiable. Which statement is *not* correct?
    - (A) It must be that $f'(x_0) != 0$ and $f^(-1)$ is not differentiable at $y_0=f(x_0)$.
    - (B) If $f'(x_0) != 0$, then $f^(-1)$ is differentiable at $y_0$.
    - (C) If $f^(-1)$ is differentiable at $y_0$, then $f'(x_0) != 0$.

    *Answer:* (A) is not correct.

    *Reasoning (The Reciprocal Slope Relationship):*
    The core idea is that the slope of the inverse function's tangent is the reciprocal of the original function's tangent slope: $(f^(-1))'(y_0) = 1/(f'(x_0))$. This relationship breaks down if and only if the original function has a horizontal tangent ($f'(x_0)=0$), which would correspond to a vertical tangent (undefined derivative) for the inverse.

    - *Analyzing the "Safe Case":*
      - *(B) If $f'(x_0) != 0$ (not horizontal)...* then the reciprocal $1/(f'(x_0))$ is well-defined. This means the inverse has a finite slope and *is differentiable*. So, (B) is correct.
      - *(C) If $f^(-1)$ is differentiable at $y_0$ (not vertical)...* then its slope $(f^(-1))'(y_0)$ is a finite number. For the equation $(f^(-1))'(y_0) = 1/(f'(x_0))$ to hold, the denominator $f'(x_0)$ cannot be zero. So, (C) is correct.

    - *Analyzing the "Catastrophe Point":*
      - The question is whether a bijective, differentiable function can ever have this "catastrophe point" where $f'(x_0)=0$.
      - *Counterexample:* Consider $f(x)=x^3$. It is bijective and differentiable everywhere. At $x_0=0$, its tangent is horizontal ($f'(0)=0$). Its inverse, $f^(-1)(y) = y^(1/3)$, has a vertical tangent at $y_0=f(0)=0$ and is therefore *not differentiable* there.
      - This counterexample shows that the scenario "$f'(x_0)=0$ and $f^(-1)$ is not differentiable" *can* happen.

    - *Evaluating Statement (A):*
      - Statement (A) claims that two conditions must hold: $f'(x_0) != 0$ AND $f^(-1)$ is not differentiable.
      - This is a contradiction. As established by (B), the condition $f'(x_0) != 0$ *guarantees* that $f^(-1)$ *is* differentiable. The statement claims the safe case and the catastrophe case happen at the same time, which is impossible. Therefore, (A) is incorrect.
  ])

  #concept-block(body: [
    #inline("Problem 17: Limit of n*a_n for a Convergent Series")
    *Statement:* Let $(a_n)$ be a sequence of positive, monotonically decreasing terms such that the series $sum_(n=1)^oo a_n$ converges. Show that $lim_(n->oo) n a_n = 0$.

    *Intuition:* If the series converges, the terms $a_n$ must go to zero "fast enough." For a decreasing sequence, this means they must decrease faster than the terms of the harmonic series ($1/n$). This problem formalizes that idea.

    *Reasoning (Cauchy Criterion and Monotonicity):*
    1. *Apply Cauchy Criterion:* Since $sum a_k$ converges, for any $epsilon > 0$, there exists an $N$ such that for all $n > N$:
      $ sum_(k=N+1)^n a_k < epsilon/2 $
    2. *Use Monotonicity:* Since $(a_n)$ is decreasing, for any $k$ in the sum (i.e., $k > N$), we have $a_k <= a_(N+1)$. A cruder but effective bound for $k$ between $n/2$ and $n$ is $a_k >= a_n$.
    3. *Bound the Sum from Below:* Consider the terms from $n/2$ to $n$ (assuming $n > 2N$).
      $ epsilon/2 > sum_(k=N+1)^n a_k > sum_(k=floor(n/2)+1)^n a_k $
      Since all terms $a_k$ in this new sum are greater than or equal to $a_n$ (by monotonicity), we can say:
      $ sum_(k=floor(n/2)+1)^n a_k >= sum_(k=floor(n/2)+1)^n a_n = (n - floor(n/2)) a_n approx (n/2) a_n $
    4. *Combine and Conclude:* We have $(n/2)a_n < epsilon/2$, which implies $n a_n < epsilon$ for all sufficiently large $n$.

    *Conclusion:* $lim_(n->oo) n a_n = 0$.
    #box(fill: luma(240), inset: 6pt, radius: 2pt)[
      *Pitfall:* The condition of monotonicity is essential. The series $sum a_n$ with terms $a_n = 1/n$ if $n$ is a perfect square and $a_n=1/n^2$ otherwise, converges. However, the subsequence for perfect squares $n_k=k^2$ gives $n_k a_(n_k) = k^2 (1/k^2) = 1$, so $n a_n$ does not go to 0.
    ]
  ])

  #concept-block(body: [
    #inline("Problem 18: Uniform Continuity on an Unbounded Domain")
    *Statement:* Show that $f(x) = sqrt(x)$ is uniformly continuous on $[0, oo)$, but $g(x)=x^2$ is not.

    *Intuition:* Uniform continuity means that for a given $epsilon$, a single $delta$ works everywhere. For $sqrt(x)$, the slope flattens out, so a small change in $x$ always produces a small change in $y$. For $x^2$, the slope gets infinitely steep, so for the same change in $y$, you need an increasingly tiny change in $x$.

    *Reasoning for $f(x)=sqrt(x)$ (Two-Part Argument):*
    1. *On a Compact Interval $[0, c]$:* The function $sqrt(x)$ is continuous on the compact interval $[0,c]$ (for any $c>0$). By the Heine-Cantor theorem, it is uniformly continuous there.
    2. *On the Tail $[c, oo)$:* For $x, y > c$, we can bound the difference directly:
      $ |sqrt(x) - sqrt(y)| = |(sqrt(x)-sqrt(y))(sqrt(x)+sqrt(y))/(sqrt(x)+sqrt(y))| \ = abs(x-y)/(sqrt(x)+sqrt(y)) $
      Since $x,y > c$, the denominator $sqrt(x)+sqrt(y) > 2sqrt(c)$.
      So, $|sqrt(x) - sqrt(y)| < abs(x-y)/(2sqrt(c))$.
      For a given $epsilon > 0$, we can choose $delta = 2sqrt(c)epsilon$. If $abs(x-y)<delta$, then $|sqrt(x)-sqrt(y)| < (2sqrt(c)epsilon)/(2sqrt(c)) = epsilon$.
    3. *Conclusion:* Since we can find a $delta$ that works on both parts of the domain, the function is uniformly continuous on $[0,oo)$.

    *Reasoning for $g(x)=x^2$ (Negation):*
    We must show that $exists epsilon > 0$ such that $forall delta > 0$, $exists x,y$ with $abs(x-y)<delta$ but $|x^2-y^2| >= epsilon$.
    Let $epsilon=1$. For any $delta>0$, choose $x = 1/delta$ and $y = 1/delta + delta/2$.
    - Then $abs(x-y) = delta/2 < delta$.
    - But $|x^2-y^2| = |y-x||y+x| = (delta/2)(1/delta + 1/delta + delta/2) = (delta/2)(2/delta + delta/2) = 1 + delta^2/4$.
    - This value is always $>= 1$. So we have found points arbitrarily close together whose function values are at least 1 apart. Thus, $x^2$ is not uniformly continuous on $[0,oo)$.
  ])

  #concept-block(body: [
    #inline("Problem 19: Asymptotic Behavior from Derivative Limit")
    *Statement:* Let $f: [0, oo) -> RR$ be a differentiable function. If $lim_(x->oo) f'(x) = L$, show that $lim_(x->oo) f(x)/x = L$.

    *Intuition:* If the slope of a function eventually approaches a constant value $L$, then for large $x$, the function must behave like a line with that slope, i.e., $f(x) approx L x$. Dividing by $x$ should yield $L$.

    *Reasoning (MVT on a Tail):*
    1. *Use Definition of Limit for $f'$:* For any $epsilon > 0$, there exists an $N$ such that for all $t > N$, we have $|f'(t) - L| < epsilon/2$. This means $L-epsilon/2 < f'(t) < L+epsilon/2$.
    2. *Apply MVT:* For any $x > N$, apply the Mean Value Theorem to $f$ on the interval $[N, x]$. There exists a $c in (N, x)$ such that:
      $ (f(x)-f(N))/(x-N) = f'(c) $
    3. *Bound the Expression:* Since $c > N$, we know $L-epsilon/2 < f'(c) < L+epsilon/2$. Therefore:
      $ L-epsilon/2 < (f(x)-f(N))/(x-N) < L+epsilon/2 $
      $ (L-epsilon/2)(x-N) < f(x)-f(N) < (L+epsilon/2)(x-N) $
    4. *Isolate $f(x)/x$:* Add $f(N)$ to all parts and divide by $x$:
      $ (L-epsilon/2)(1-N/x) + f(N)/x < f(x)/x \ < (L+epsilon/2)(1-N/x) + f(N)/x $
    5. *Take the Limit as $x->oo$:* As $x->oo$, the terms $N/x$ and $f(N)/x$ both go to 0. For sufficiently large $x$, the entire expression becomes trapped:
      $ L-epsilon < f(x)/x < L+epsilon $

    *Conclusion:* This is the definition of $lim_(x->oo) f(x)/x = L$.
  ])

  #concept-block(body: [
    #inline("Problem 20: Integral of an Inverse Function")
    *Statement:* Let $f: [a,b] -> [c,d]$ be a strictly increasing, continuous (and thus invertible) function. Prove the identity:
    $ integral_a^b f(x) "dx" + integral_(f(a))^(f(b)) f^(-1)(y) "dy" = b f(b) - a f(a) $

    *Intuition (Geometric):* Draw the graph of $f(x)$. The first integral is the area under the curve from $x=a$ to $x=b$. The graph of $f^(-1)(y)$ is the reflection of $f(x)$ across the line $y=x$. The second integral is the area "to the left" of the curve from $y=f(a)$ to $y=f(b)$. Together, these two areas perfectly fill a large rectangle of area $b f(b)$ from which a smaller rectangle of area $a f(a)$ has been removed.

    *Reasoning (Integration by Parts):*
    1. *Focus on the Second Integral:* Let's analyze $I = integral_(f(a))^(f(b)) f^(-1)(y) "dy"$.
    2. *Substitution:* Let $y=f(x)$. Then $"dy" = f'(x)"dx"$. The bounds transform: $y=f(a) => x=a$ and $y=f(b) => x=b$. The inverse function becomes $f^(-1)(y) = f^(-1)(f(x)) = x$.
      $ I = integral_a^b x f'(x) "dx" $
    3. *Integration by Parts:* Now apply IBP to this new integral. Let $u=x$ and $"dv"=f'(x)"dx"$. Then $"du"="dx"$ and $v=f(x)$.
      $ I = [u v]_a^b - integral_a^b v "du" = [x f(x)]_a^b - integral_a^b f(x) "dx" $
      $ I = (b f(b) - a f(a)) - integral_a^b f(x) "dx" $
    4. *Conclusion:* We have found that $integral_(f(a))^(f(b)) f^(-1)(y) "dy" = b f(b) - a f(a) - integral_a^b f(x) "dx"$. Rearranging this equation gives the desired identity.
  ])

  #concept-block(body: [
    #inline("Problem 21: Differentiability of an Integral Function")
    *Statement:* Let $f_n (x) = integral_0^x t^n sin(1/t) "dt"$ for $x > 0$ and $f_n (0)=0$. For which integer values of $n$ is $f_n (x)$ differentiable at $x=0$?

    *Intuition:* For the function to be differentiable at 0, the limit of the difference quotient, $lim_(h->0) f_n (h)/h$, must exist. The integral adds a power of $t$ to the integrand, which helps "dampen" the wild oscillations of $sin(1/t)$ near zero. We need to determine how much damping is needed.

    *Reasoning (Squeeze Theorem on the Difference Quotient):*
    1. *Set up the Difference Quotient:*
      $ f_n'(0) = lim_(h->0) (f_n (h) - f_n (0))/h = lim_(h->0) 1/h integral_0^h t^n sin(1/t) "dt" $
    2. *Bound the Integrand:* We know $|sin(1/t)| <= 1$. Therefore, for $t>0$, $|t^n sin(1/t)| <= t^n$.
    3. *Bound the Integral:* Using the triangle inequality for integrals:
      $ |integral_0^h t^n sin(1/t) "dt"| <= integral_0^h |t^n sin(1/t)| "dt" <= integral_0^h t^n "dt" $
    4. *Evaluate the Bounding Integral:*
      $ integral_0^h t^n "dt" = [t^(n+1)/(n+1)]_0^h = h^(n+1)/(n+1) $
    5. *Apply the Squeeze Theorem to the Limit:* We now have bounds for the difference quotient:
      $ 0 <= abs((f_n (h) - f_n (0))/h) <= 1/abs(h) abs(h^(n+1)/(n+1)) = abs(h^n)/(n+1) $
      The limit $lim_(h->0) abs(h^n)/(n+1)$ exists and is equal to 0 if and only if the exponent $n$ is greater than 0.

    *Conclusion:* The function $f_n (x)$ is differentiable at $x=0$ for all integers $n > 0$. For $n=0$, the limit of the quotient does not exist. For $n < 0$, the integral itself may not converge.
  ])

  #concept-block(body: [
    #inline("Problem 22: Bijectivity and Monotonicity")
    *Statement:* Let $f: RR -> RR$ be a continuous and bijective function. Must $f$ be strictly monotonic?

    *Answer:* Yes.

    *Intuition:* A continuous function that is not monotonic must "turn around" somewhere, creating a local maximum or minimum. But if it turns around, it must hit the same y-value at least twice, which violates injectivity (and thus bijectivity).

    *Reasoning (Proof by Contradiction using IVT):*
    1. *Assume for Contradiction:* Assume $f$ is continuous and bijective but *not* strictly monotonic.
    ...

    *Conclusion:* The initial assumption must be false. Therefore, any continuous bijective function on $RR$ must be strictly monotonic.
  ])

  #concept-block(body: [
    #inline("Problem 23: Convergence of a Power Series on its Boundary")
    *Statement:* Let $f(x) = sum_(n=0)^oo a_n x^n$ be a power series with radius of convergence $p > 0$. If $f(x)$ converges uniformly on $[-r, r]$ for all $0 <= r < p$, must $f$ be continuous on $(-p, p)$?

    *Answer:* Yes.

    *Intuition:* Uniform convergence is a very strong condition that preserves continuity. The question is whether convergence on every *closed* subinterval is enough to guarantee continuity on the entire *open* interval.

    *Reasoning (Local Nature of Continuity):*
    1. *Goal:* To show $f$ is continuous at an arbitrary point $x_0 in (-p, p)$.
    2. *Localize the Problem:* For any such $x_0$, we can always find a radius $r$ such that $0 < |x_0| < r < p$. This means $x_0$ is contained within the closed interval $[-r, r]$.
    3. *Apply the Given Information:* We are given that the power series converges uniformly on this specific closed interval $[-r, r]$.
    4. *Use the Theorem on Uniform Convergence and Continuity:* A key theorem states that the uniform limit of a sequence of continuous functions is continuous.
      - The partial sums of the power series, $S_N (x) = sum_(n=0)^N a_n x^n$, are polynomials and therefore continuous everywhere.
      - Since the convergence is uniform on $[-r, r]$, the limit function $f(x)$ must be continuous on $[-r, r]$.
    5. *Conclusion:* Since $x_0$ is in $[-r, r]$, $f$ is continuous at $x_0$. Because our choice of $x_0$ in $(-p, p)$ was arbitrary, $f$ is continuous on the entire open interval $(-p, p)$.
  ])

  #concept-block(body: [
    #inline("Problem 24: Proving Uniform Convergence with the MVT")
    *Statement:* Let $(g_n)$ be a sequence of differentiable functions on $[0,1]$ such that:
    - (i) The sequence of numbers $(g_n (0))$ converges as $n->oo$.
    - (ii) $lim_(n->oo) (sup_(x in [0,1]) |g_n'(x)|) = 0$.
    Prove that the sequence of functions $(g_n)$ converges uniformly on $[0,1]$.

    *Intuition:* Condition (i) "anchors" the sequence of functions at a single point ($x=0$). Condition (ii) tells us that the slopes of all the functions are becoming uniformly flat across the entire interval. A sequence of functions that are all anchored at the same point and are all becoming flat must converge uniformly to a constant function.

    *Reasoning (Cauchy Criterion for Uniform Convergence):*
    We will show that $(g_n)$ is a Cauchy sequence in the space of continuous functions with the supremum norm. This means we need to show that for any $epsilon > 0$, there exists an $N$ such that for all $n, m > N$, $sup_(x in [0,1]) |g_n (x) - g_m (x)| < epsilon$.

    1. *Set up the Difference:* Consider the function $h(x) = g_n (x) - g_m (x)$. We want to bound $|h(x)|$.
    2. *Apply the Mean Value Theorem:* By the MVT applied to $h(x)$ on the interval $[0, x]$, there exists a $xi_x in (0,x)$ such that:
      $ (h(x) - h(0))/(x-0) = h'(xi_x) $
      $ g_n (x) - g_m (x) - (g_n (0) - g_m (0)) = x (g_n'(xi_x) - g_m'(xi_x)) $
    3. *Bound the Expression using Triangle Inequality:*
      $ |g_n (x) - g_m (x)| \ = |(g_n (x) - g_m (x) - (g_n (0)-g_m (0))) + (g_n (0)-g_m (0))| $
      $ <= |x(g_n'(xi_x) - g_m'(xi_x))| + |g_n (0) - g_m (0)| $
      $ <= |x| |g_n'(xi_x)| + |x| |g_m'(xi_x)| + |g_n (0) - g_m (0)| $
    4. *Use the Supremum Norm:* Since $x in [0,1]$, we have $|x| <= 1$. We can bound the derivative terms by their suprema:
      $ |g_n (x) - g_m (x)| \ <= sup_(y in [0,1])|g_n'(y)| + sup_(y in [0,1])|g_m'(y)| + |g_n (0) - g_m (0)| $
    5. *Analyze the Limit:* This bound is independent of $x$. As $n, m -> oo$:
      - From condition (ii), $sup|g_n'| -> 0$ and $sup|g_m'| -> 0$.
      - From condition (i), $(g_n (0))$ is a convergent sequence of numbers, which means it is a Cauchy sequence. Therefore, $|g_n (0) - g_m (0)| -> 0$.
    *Conclusion:* The entire upper bound goes to 0 as $n, m -> oo$. This proves that $(g_n)$ is a uniform Cauchy sequence, and since the space of continuous functions on $[0,1]$ is complete, it must converge uniformly.
  ])

  #concept-block(body: [
    #inline("Problem 25: Differentiability and Boundedness")
    *Statement:* Let $f: RR -> RR$ be a continuous function. Which of the following is correct?
    (A) If $f$ is bounded and differentiable, then $f'$ is also bounded.
    (B) If $f$ is differentiable and $f'$ is bounded, then $f$ is also bounded.
    *Answer:* Neither is correct. Both statements are false.

    *Reasoning (Counterexamples):*
    1. *Counterexample for (A):* We need a function that is bounded but whose derivative is unbounded. This requires a function that oscillates infinitely fast.
      - Let $f(x) = sin(x^2)$ on $RR$.
      - *Function Boundedness:* The range of sine is $[-1,1]$, so $f(x)$ is clearly bounded.
      - *Derivative Boundedness:* Using the chain rule, $f'(x) = cos(x^2) dot.c (2x) = 2x cos(x^2)$.
      - As $x -> oo$, the $2x$ term goes to infinity, while $cos(x^2)$ oscillates. The amplitude of $f'(x)$ is $2x$, which is unbounded. Therefore, $f'$ is not bounded.

    2. *Counterexample for (B):* We need a function whose derivative is bounded, but the function itself is not. This is simpler: any line with a non-zero slope will work.
      - Let $f(x) = x$.
      - *Derivative Boundedness:* The derivative is $f'(x) = 1$. The constant function 1 is clearly bounded.
      - *Function Boundedness:* The function $f(x)=x$ is unbounded on its domain $RR$.

    *Higher-Level Intuition:*
    - A bounded function can have an arbitrarily steep slope (derivative) for very short periods, as seen with $sin(x^2)$.
    - A bounded derivative only limits the "steepness" of a function (it's Lipschitz continuous), but it doesn't prevent the function from growing or decreasing indefinitely over an infinite domain.
  ])

  #concept-block(body: [
    #inline("Problem 26: Convergent Integral vs. Limit of Function")
    *Statement:* If $f: [0, oo) -> RR$ is continuous and $integral_0^oo f(x) "dx"$ converges, must $lim_(x->oo) f(x) = 0$?

    *Answer:* False.

    *Intuition:* The total area under a curve can be finite even if the function has spikes that grow infinitely tall, as long as the spikes get progressively narrower.

    *Reasoning (Counterexample Construction):*
    1. *Construct Spikes:* Define a function $f(x)$ that is zero everywhere except for a sequence of triangular spikes. For each integer $n >= 2$, create a spike centered at $x=n$ with height $h_n=n$ and base width $w_n=2/n^3$.
    2. *Check Integral Convergence:* The area of each spike is $A_n = 1/2 dot.c w_n dot.c h_n = 1/2 dot.c (2/n^3) dot.c n = 1/n^2$. The total integral is the sum of these areas:
      $ integral_0^oo f(x) "dx" = sum_(n=2)^oo A_n = sum_(n=2)^oo 1/n^2 $
      This is a convergent p-series ($p=2>1$).
    3. *Check Function Limit:* Consider the sequence of points $x_n = n$ corresponding to the peak of each spike. The function values at these points are $f(x_n) = f(n) = h_n = n$.
      Since $lim_(n->oo) f(n) = oo$, the limit $lim_(x->oo) f(x)$ cannot be 0.

    *Conclusion:* A function can have a convergent improper integral without its limit tending to zero.
  ])

  = Final Tips & Good Luck!

  #concept-block(body: [
    #inline("Final Tips & Good Luck!")
    - *Read Carefully:* Is the interval open or closed? Is the function continuous or just integrable? Small details matter.
    - *Trust the Definitions:* When in doubt, go back to the formal $epsilon-delta$ or sequence definitions.
    - *Know Your Counterexamples:* Have key counterexamples ready (like $|x|$, Dirichlet's function, $sin(x^2)$, harmonic series) to quickly disprove false statements.

    *You've got this. Good luck!*
  ])
]